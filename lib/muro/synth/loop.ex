defmodule Muro.Synth.Loop do
  @moduledoc false

  alias Muro.Synth
  alias Muro.Synth.{Book, Oracle}

  @rounds 4

  def default_rounds, do: @rounds
  def default_depth, do: 0

  @doc """
  Version-space search on a checked environment.

  The fuel bound and the round bound are operational. A loop that stops
  because of either bound has not established `sufficient-cegis`.
  """
  def run(path, opts \\ []) when is_binary(path) and is_list(opts) do
    oracle = Keyword.get(opts, :oracle, "trace")
    depth = Keyword.get(opts, :depth, default_depth())
    max_depth = Keyword.get(opts, :max_depth, depth + 1)
    rounds = Keyword.get(opts, :max_rounds, @rounds)
    blind = Keyword.get(opts, :blind, [])
    score = Keyword.get(opts, :score, fn _ -> 0 end)
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())
    anchor = Keyword.get(opts, :anchor, Path.dirname(Path.expand(path)))

    checker =
      Keyword.get(opts, :checker, fn book, fuel -> Muro.check_file(book, fuel: fuel) end)

    cond do
      oracle not in Oracle.names() ->
        {:error, :usage, "unknown oracle #{oracle}"}

      not (is_integer(depth) and depth >= 0) ->
        {:error, :usage, "--depth must be a non-negative integer"}

      not (is_integer(max_depth) and max_depth >= depth) ->
        {:error, :usage, "the depth bound is below --depth"}

      true ->
        open(path, fuel, oracle, blind, depth, max_depth, rounds, score, anchor, checker)
    end
  end

  defp open(path, fuel, oracle, blind, depth, max_depth, rounds, score, anchor, checker) do
    case Muro.Synth.Host.open(path, fuel: fuel) do
      {:error, _kind, _msg} = err ->
        err

      {:ok, host} ->
        case Oracle.observe(host, oracle, blind) do
          {:error, _kind, _msg} = err ->
            err

          {:silent, cex} ->
            {:ok, silent(cex)}

          {:ok, spec} ->
            search(host, spec, depth, max_depth, rounds, score, anchor, checker, fuel)
        end
    end
  end

  defp search(host, spec, depth, max_depth, rounds, score, anchor, checker, fuel) do
    feat = fn feature, state -> host.eval_feature.(feature, state) end

    case conflict(spec.cover, spec.tasks, host, feat) do
      {:conflict, earlier, later, predicted, oracle, task} ->
        {:ok, insufficient(host, task, depth, feat, earlier, later, predicted, oracle)}

      :ok ->
        case fit(host, spec.tasks, depth, max_depth, score, feat, [], %{}) do
          {:empty, versions, at} ->
            {:ok, empty(versions, at)}

          {:ok, arms, versions, at} ->
            certify(
              host,
              arms,
              versions,
              at,
              max_depth,
              rounds,
              score,
              feat,
              anchor,
              checker,
              fuel,
              %{},
              %{}
            )
        end
    end
  end

  defp fit(_host, _tasks, depth, max_depth, _score, _feat, versions, _rejected)
       when depth > max_depth do
    {:empty, versions, depth - 1}
  end

  defp fit(host, tasks, depth, max_depth, score, feat, versions, rejected) do
    vs = Synth.enumerate(host.features, depth)

    case fit_tasks(tasks, vs, score, feat, rejected) do
      {:empty, sizes} when depth < max_depth ->
        fit(host, tasks, depth + 1, max_depth, score, feat, versions ++ sizes, rejected)

      {:empty, sizes} ->
        {:empty, versions ++ sizes, depth}

      {:ok, arms, sizes} ->
        {:ok, arms, versions ++ sizes, depth}
    end
  end

  defp fit_tasks(tasks, vs, score, feat, rejected) do
    initial = length(vs)

    Enum.reduce_while(tasks, {:ok, [], []}, fn task, {:ok, arms, sizes} ->
      name = arm_name(task, length(tasks), length(arms))

      kept =
        vs
        |> Synth.refine_all(task.observations, feat)
        |> Enum.reject(&MapSet.member?(Map.get(rejected, name, MapSet.new()), &1))

      if kept == [] do
        {:halt, {:empty, [initial, 0]}}
      else
        arm = %{
          name: name,
          pred: Synth.pick(kept, score),
          kept: kept,
          action: task.action,
          else: task.else,
          observations: task.observations
        }

        {:cont, {:ok, arms ++ [arm], sizes ++ [initial, length(kept)]}}
      end
    end)
  end

  defp arm_name(_task, 1, 0), do: "survivor"
  defp arm_name(task, _n, _i), do: "survivor-#{task.action}"

  defp certify(
         host,
         arms,
         versions,
         depth,
         max_depth,
         rounds,
         score,
         feat,
         anchor,
         checker,
         fuel,
         seen,
         rejected
       ) do
    {:ok, source} = Book.render(host, arms, anchor)

    case Book.check(source, anchor, fn path -> checker.(path, fuel) end) do
      :ok ->
        {:ok, checked(arms, source, versions)}

      {:error, text} ->
        feedback(
          host,
          arms,
          versions,
          depth,
          max_depth,
          rounds,
          score,
          feat,
          anchor,
          checker,
          fuel,
          seen,
          rejected,
          text
        )
    end
  end

  defp feedback(
         host,
         arms,
         versions,
         depth,
         max_depth,
         rounds,
         score,
         feat,
         anchor,
         checker,
         fuel,
         seen,
         rejected,
         text
       ) do
    cex = Book.cex_from(text, Book.obligations(host, arms))
    fed = Map.get(seen, cex.carrier, 0) + 1
    cex = %{cex | fed: fed}
    seen = Map.put(seen, cex.carrier, fed)

    arm = arm_for(host, arms, cex)
    {next, rejected} = drop_failed(arm, cex, rejected)
    shrunk = length(next) < length(arm.kept)

    cond do
      not shrunk or rounds <= 1 ->
        {:ok, residual(cex, versions)}

      next != [] ->
        pred = Synth.pick(next, score)
        arm = %{arm | pred: pred, kept: next}
        arms = replace_arm(arms, arm)

        certify(
          host,
          arms,
          versions ++ [length(next)],
          depth,
          max_depth,
          rounds - 1,
          score,
          feat,
          anchor,
          checker,
          fuel,
          seen,
          rejected
        )

      depth < max_depth ->
        # The checker removed every survivor at this depth. The next
        # depth is still allowed. Observations stay, and the refused
        # candidates stay out: enumeration there includes them.
        case fit(host, tasks_of(arms), depth + 1, max_depth, score, feat, versions, rejected) do
          {:empty, versions, _at} ->
            {:ok, residual(cex, versions)}

          {:ok, arms, versions, at} ->
            certify(
              host,
              arms,
              versions,
              at,
              max_depth,
              rounds - 1,
              score,
              feat,
              anchor,
              checker,
              fuel,
              seen,
              rejected
            )
        end

      true ->
        {:ok, residual(cex, versions)}
    end
  end

  # The oracle bit is already an observation, so filtering by it again
  # cannot shrink the space. A boolean from the checker is new: this
  # candidate failed. Remember it, including when it was the last one.
  defp drop_failed(arm, cex, rejected) do
    if is_boolean(cex.predicted) do
      rejected =
        Map.update(rejected, arm.name, MapSet.new([arm.pred]), &MapSet.put(&1, arm.pred))

      {Enum.reject(arm.kept, &(&1 == arm.pred)), rejected}
    else
      {arm.kept, rejected}
    end
  end

  defp tasks_of(arms) do
    Enum.map(arms, fn arm ->
      %{action: arm.action, else: arm.else, observations: arm.observations}
    end)
  end

  defp replace_arm(arms, arm) do
    Enum.map(arms, fn old -> if old.name == arm.name, do: arm, else: old end)
  end

  defp arm_for(host, arms, %{name: name}) when is_binary(name) do
    Enum.find(arms, hd(arms), fn arm ->
      Enum.any?(arm.observations, fn {state, _bit} ->
        Book.hold_name(host, arms, arm, state) == name
      end)
    end)
  end

  defp arm_for(_host, arms, cex) do
    Enum.find(arms, hd(arms), fn arm ->
      Enum.any?(arm.observations, &(elem(&1, 0) == cex.carrier))
    end)
  end

  defp conflict(cover, tasks, host, feat) do
    Enum.reduce_while(tasks, :ok, fn task, :ok ->
      case conflict_obs(cover, task.observations, host, feat) do
        :ok ->
          {:cont, :ok}

        {:conflict, earlier, later, predicted, oracle} ->
          {:halt, {:conflict, earlier, later, predicted, oracle, task}}
      end
    end)
  end

  defp conflict_obs(cover, obs, host, feat) do
    bits = Map.new(obs)

    vectors =
      Map.new(cover, fn state ->
        {state, Enum.map(host.features, &feat.(&1, state))}
      end)

    Enum.reduce_while(cover, [], fn state, seen ->
      bit = Map.fetch!(bits, state)
      vector = Map.fetch!(vectors, state)

      case Enum.find(seen, fn {_state, seen_vector, seen_bit} ->
             seen_vector == vector and seen_bit != bit
           end) do
        nil -> {:cont, seen ++ [{state, vector, bit}]}
        {earlier, _vector, earlier_bit} -> {:halt, {:conflict, earlier, state, earlier_bit, bit}}
      end
    end)
    |> case do
      {:conflict, _, _, _, _} = found -> found
      _seen -> :ok
    end
  end

  defp insufficient(host, task, depth, feat, earlier, later, predicted, oracle) do
    vs = Synth.enumerate(host.features, depth)
    kept = Synth.refine_all(vs, task.observations, feat)

    cex = %{
      carrier: later,
      predicted: predicted,
      oracle: oracle,
      fed: 1,
      agrees: earlier,
      pair: {task.action, task.else}
    }

    lines = [
      "muro synth: features insufficient",
      "#{later} agrees with #{earlier} on every feature",
      "carrier #{later}",
      "predicted #{predicted}",
      "oracle #{oracle}",
      "fed back 1",
      "version space #{length(vs)}",
      "version space #{length(kept)}"
    ]

    %{
      status: :insufficient,
      program: nil,
      book: nil,
      lines: lines,
      versions: [length(vs), length(kept)],
      cex: [cex]
    }
  end

  defp empty(versions, depth) do
    lines =
      ["muro synth: empty version space", "depth #{depth}"] ++
        Enum.map(versions, &"version space #{&1}")

    %{status: :empty, program: nil, book: nil, lines: lines, versions: versions, cex: []}
  end

  defp silent(cex) do
    {action, other} = cex.pair

    lines = [
      "muro synth: oracle cannot label",
      cex.reason,
      "carrier #{cex.carrier}",
      "pair #{action} #{other}"
    ]

    %{status: :silent, program: nil, book: nil, lines: lines, versions: [], cex: [cex]}
  end

  defp checked(arms, source, versions) do
    lines =
      ["muro synth: policy checked"] ++
        Enum.map(arms, &"program: #{Synth.render(&1.pred)}") ++
        preference(arms) ++
        ["homomorphism certificate is later"] ++
        Enum.map(versions, &"version space #{&1}")

    %{
      status: :policy,
      program: program_of(arms),
      book: source,
      lines: lines,
      versions: versions,
      cex: []
    }
  end

  defp program_of([arm]), do: arm.pred
  defp program_of(arms), do: Enum.map(arms, & &1.pred)

  # One arm is one predicate: true selects its action and false selects
  # the other. A chain selects the first arm that holds. The default is
  # the action only when every arm is false.
  defp preference(arms) do
    arms
    |> hd()
    |> Map.fetch!(:observations)
    |> Enum.flat_map(fn {state, _bit} ->
      {action, bit} = decision(arms, state)
      ["at #{state} the program prefers #{action}", "carrier #{state} bit #{bit}"]
    end)
  end

  defp decision([arm], state) do
    {_state, bit} = Enum.find(arm.observations, &(elem(&1, 0) == state))
    {if(bit, do: arm.action, else: arm.else), bit}
  end

  defp decision(arms, state) do
    Enum.reduce_while(arms, {List.last(arms).else, false}, fn arm, acc ->
      {_state, bit} = Enum.find(arm.observations, &(elem(&1, 0) == state))
      if bit, do: {:halt, {arm.action, true}}, else: {:cont, acc}
    end)
  end

  defp residual(cex, versions) do
    pair =
      case cex.pair do
        {action, other} -> ["pair #{action} #{other}"]
        _ -> []
      end

    lines =
      [
        "muro synth: residual counterexample",
        "carrier #{cex.carrier}",
        "predicted #{show_bit(cex.predicted)}",
        "oracle #{show_bit(cex.oracle)}",
        "fed back #{cex.fed}"
      ] ++ pair ++ Enum.map(versions, &"version space #{&1}")

    %{status: :residual, program: nil, book: nil, lines: lines, versions: versions, cex: [cex]}
  end

  defp show_bit(true), do: "true"
  defp show_bit(false), do: "false"
  defp show_bit(nil), do: "unknown"
end
