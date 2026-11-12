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
        case fit(host, spec.tasks, depth, max_depth, score, feat, []) do
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
              %{}
            )
        end
    end
  end

  defp fit(_host, _tasks, depth, max_depth, _score, _feat, versions)
       when depth > max_depth do
    {:empty, versions, depth - 1}
  end

  defp fit(host, tasks, depth, max_depth, score, feat, versions) do
    vs = Synth.enumerate(host.features, depth)

    case fit_tasks(tasks, vs, score, feat) do
      {:empty, sizes} when depth < max_depth ->
        fit(host, tasks, depth + 1, max_depth, score, feat, versions ++ sizes)

      {:empty, sizes} ->
        {:empty, versions ++ sizes, depth}

      {:ok, arms, sizes} ->
        {:ok, arms, versions ++ sizes, depth}
    end
  end

  defp fit_tasks(tasks, vs, score, feat) do
    initial = length(vs)

    Enum.reduce_while(tasks, {:ok, [], []}, fn task, {:ok, arms, sizes} ->
      kept = Synth.refine_all(vs, task.observations, feat)

      if kept == [] do
        {:halt, {:empty, [initial, 0]}}
      else
        arm = %{
          name: arm_name(task, length(tasks), length(arms)),
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
         seen
       ) do
    case Book.render(host, arms, anchor) do
      {:error, _, _} = err ->
        err

      {:ok, source} ->
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
              text
            )
        end
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
         text
       ) do
    cex = Book.cex_from(text, Book.obligations(arms))
    fed = Map.get(seen, cex.carrier, 0) + 1
    cex = %{cex | fed: fed}
    seen = Map.put(seen, cex.carrier, fed)

    arm =
      Enum.find(arms, hd(arms), fn arm ->
        Enum.any?(arm.observations, &(elem(&1, 0) == cex.carrier))
      end)

    next =
      if is_boolean(cex.oracle),
        do: Synth.refine(arm.kept, {cex.carrier, cex.oracle}, feat),
        else: arm.kept

    shrunk = length(next) < length(arm.kept)

    cond do
      not shrunk or rounds <= 1 or next == [] ->
        {:ok, residual(cex, versions)}

      true ->
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
          seen
        )
    end
  end

  defp replace_arm(arms, arm) do
    Enum.map(arms, fn old -> if old.name == arm.name, do: arm, else: old end)
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
    arm = hd(arms)

    lines =
      [
        "muro synth: policy checked",
        "program: #{Synth.render(arm.pred)}"
      ] ++
        preference(arm) ++
        ["homomorphism certificate is later"] ++
        Enum.map(versions, &"version space #{&1}")

    %{
      status: :policy,
      program: arm.pred,
      book: source,
      lines: lines,
      versions: versions,
      cex: []
    }
  end

  defp preference(arm) do
    Enum.flat_map(arm.observations, fn {state, bit} ->
      action = if bit, do: arm.action, else: arm.else
      ["at #{state} the program prefers #{action}", "carrier #{state} bit #{bit}"]
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
