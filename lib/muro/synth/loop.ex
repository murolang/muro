defmodule Muro.Synth.Loop do
  @moduledoc false

  alias Muro.Synth
  alias Muro.Synth.{Book, Oracle, Term}

  @rounds 4

  def default_rounds, do: @rounds
  def default_depth, do: 0

  @doc """
  Version-space search on a checked environment.

  `:considered_budget` and `:memory_budget` are the sized-search bounds.
  Omitted, they are `Muro.Synth.considered_budget/0` and
  `Muro.Synth.memory_budget/0`. The walk reads each bound once, at the
  start. A bound that is not an integer is a usage error.

  The fuel bound and the round bound are operational. A loop that stops
  because of either bound has not established `sufficient-cegis`.
  """
  def run(path, opts \\ []) when is_binary(path) and is_list(opts) do
    # Search memo only. The checker does not read this key.
    Process.delete(:muro_synth_reaches)

    try do
      run_checked(path, opts)
    after
      Process.delete(:muro_synth_reaches)
      Process.delete(:muro_synth_open_ms)
      Process.delete(:muro_synth_reach_ms)
      Process.delete(:muro_synth_cover)
      Process.delete(:muro_synth_render_ms)
    end
  end

  defp run_checked(path, opts) do
    oracle = Keyword.get(opts, :oracle, "trace")
    depth = Keyword.get(opts, :depth, default_depth())
    max_depth = Keyword.get(opts, :max_depth, depth + 1)
    rounds = Keyword.get(opts, :max_rounds, @rounds)
    blind = Keyword.get(opts, :blind, [])
    score = Keyword.get(opts, :score, fn _ -> 0 end)
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())
    anchor = Keyword.get(opts, :anchor, Path.dirname(Path.expand(path)))
    structural = Keyword.get(opts, :structural, true)

    checker =
      Keyword.get(opts, :checker, fn book, fuel -> Muro.check_file(book, fuel: fuel) end)

    considered = Keyword.get(opts, :considered_budget, Synth.considered_budget())
    memory = Keyword.get(opts, :memory_budget, Synth.memory_budget())

    cond do
      oracle not in Oracle.names() ->
        {:error, :usage, "unknown oracle #{oracle}"}

      not (is_integer(depth) and depth >= 0) ->
        {:error, :usage, "--depth must be a non-negative integer"}

      not (is_integer(max_depth) and max_depth >= depth) ->
        {:error, :usage, "the depth bound is below --depth"}

      not is_integer(considered) ->
        {:error, :usage, "the considered budget must be an integer"}

      not is_integer(memory) ->
        {:error, :usage, "the memory budget must be an integer"}

      true ->
        open(
          path,
          fuel,
          oracle,
          blind,
          depth,
          max_depth,
          rounds,
          score,
          anchor,
          checker,
          structural,
          %{considered_budget: considered, memory_budget: memory}
        )
    end
  end

  defp open(
         path,
         fuel,
         oracle,
         blind,
         depth,
         max_depth,
         rounds,
         score,
         anchor,
         checker,
         structural,
         limits
       ) do
    opened = System.monotonic_time(:millisecond)

    case Muro.Synth.Host.open(path, fuel: fuel, structural: structural) do
      {:error, _kind, _msg} = err ->
        err

      {:ok, host} ->
        case Oracle.observe(host, oracle, blind) do
          {:error, _kind, _msg} = err ->
            err

          {:silent, cex} ->
            {:ok, silent(cex)}

          {:ok, spec} ->
            Process.put(
              :muro_synth_open_ms,
              System.monotonic_time(:millisecond) - opened
            )

            search(host, spec, depth, max_depth, rounds, score, anchor, checker, fuel, limits)
        end
    end
  end

  defp search(host, spec, depth, max_depth, rounds, score, anchor, checker, fuel, limits) do
    search(
      host,
      spec,
      depth,
      max_depth,
      rounds,
      score,
      anchor,
      checker,
      fuel,
      length(spec.cover),
      limits
    )
  end

  defp search(host, spec, depth, max_depth, rounds, score, anchor, checker, fuel, left, limits) do
    feat = fn feature, state -> host.eval_feature.(feature, state) end

    case conflict(spec.cover, spec.tasks, host, feat) do
      {:conflict, earlier, later, predicted, oracle, task} ->
        invent(
          host,
          spec,
          depth,
          max_depth,
          rounds,
          score,
          anchor,
          checker,
          fuel,
          left,
          earlier,
          later,
          predicted,
          oracle,
          task,
          limits
        )

      :ok ->
        case fit(host, spec.tasks, depth, max_depth, score, feat, [], %{}) do
          {:empty, versions, at} when depth == 0 and at >= 1 ->
            widen_reach(
              host,
              spec,
              versions,
              at,
              depth,
              max_depth,
              rounds,
              score,
              anchor,
              checker,
              fuel,
              limits
            )

          {:empty, versions, at} ->
            {:ok, empty(host, versions, at)}

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
              %{},
              spec.oracle
            )
        end
    end
  end

  # A collapse is a missing structural test when the two terms differ.
  # One deepen walks further fields, up to the path bound, and
  # enumerates every path again before search resumes. That walk
  # does not spend an invention round. Invention then reads the
  # subterm where the two values differ, including a list element
  # and a field past the bound. Each invention round separates at
  # least the pair it was given, so the number of those rounds is
  # at most the size of the cover. When the new tests do not
  # separate the pair, the report stays `features insufficient`.
  defp invent(
         host,
         spec,
         depth,
         max_depth,
         rounds,
         score,
         anchor,
         checker,
         fuel,
         left,
         earlier,
         later,
         predicted,
         oracle,
         task,
         limits
       ) do
    case Muro.Synth.Feature.deepen(host, earlier, later) do
      {:ok, specs, path_depth} ->
        host = install_paths(host, specs, path_depth)
        search(host, spec, depth, max_depth, rounds, score, anchor, checker, fuel, left, limits)

      {:stop, specs, path_depth} ->
        host = if specs, do: install_paths(host, specs, path_depth), else: host

        invent_at(
          host,
          spec,
          depth,
          max_depth,
          rounds,
          score,
          anchor,
          checker,
          fuel,
          left,
          earlier,
          later,
          predicted,
          oracle,
          task,
          limits
        )
    end
  end

  defp install_paths(host, specs, path_depth) do
    host
    |> Muro.Synth.Host.install_features(specs)
    |> Map.put(:path_depth, path_depth)
  end

  defp invent_at(
         host,
         spec,
         depth,
         max_depth,
         rounds,
         score,
         anchor,
         checker,
         fuel,
         left,
         earlier,
         later,
         predicted,
         oracle,
         task,
         limits
       ) do
    feat = fn feature, state -> host.eval_feature.(feature, state) end

    specs =
      if host[:structural] != false and host[:structured] and left > 0 do
        Muro.Synth.Feature.invent(host, earlier, later)
      else
        []
      end

    case specs do
      [] ->
        {:ok, insufficient(host, task, depth, feat, earlier, later, predicted, oracle)}

      fresh ->
        host = Muro.Synth.Host.install_features(host, fresh)

        search(
          host,
          spec,
          depth,
          max_depth,
          rounds,
          score,
          anchor,
          checker,
          fuel,
          left - 1,
          limits
        )
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

  # Depth 0 and a depth of at least 1 were both searched, and both were
  # empty. `reaches-pos` is has-pos-reward read out to the horizon. The
  # next search enumerates by size, including a disjunction of the
  # feature tests. A search that never reached depth 1 does not install
  # the test. The deployed term is still `eval` of the predicate that
  # remains.
  defp widen_reach(
         host,
         spec,
         versions,
         at,
         _depth,
         max_depth,
         rounds,
         score,
         anchor,
         checker,
         fuel,
         limits
       ) do
    reached = System.monotonic_time(:millisecond)

    case Muro.Synth.Feature.extend_reach(host) do
      :same ->
        Process.put(:muro_synth_reach_ms, System.monotonic_time(:millisecond) - reached)
        {:ok, empty(host, versions, at)}

      {:ok, specs} ->
        Process.put(:muro_synth_reach_ms, System.monotonic_time(:millisecond) - reached)
        host = Muro.Synth.Host.install_features(host, specs)
        feat = fn feature, state -> host.eval_feature.(feature, state) end

        case fit_sized(host, spec.tasks, score, feat, versions, %{}, limits) do
          {:empty, versions, at, search} ->
            {:ok, empty(host, versions, at, search)}

          {:ok, arms, versions, at, search} ->
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
              %{},
              spec.oracle,
              search
            )
        end
    end
  end

  # One signature keeps the smallest program. The version-space count at
  # a size is the number of distinct signatures of that size or smaller.
  # A size that adds none is not recorded. The walk stops at the first
  # size that satisfies every task. A task with no program by the size
  # bound is an empty space at that bound.
  defp fit_sized(host, tasks, score, feat, versions, rejected, limits) do
    states =
      case tasks do
        [%{observations: observations} | _] -> Enum.map(observations, &elem(&1, 0))
        [] -> []
      end

    task_sigs =
      Enum.map(tasks, fn task ->
        bits = Map.new(task.observations)

        states
        |> Enum.map(&Map.fetch!(bits, &1))
        |> Synth.pack_bits()
      end)

    max_size = Synth.pred_size_bound()
    trace_features(host)
    Process.put(:muro_synth_cover, length(states))
    families = Muro.Synth.Feature.families(host.feature_specs || [], host.actions)

    case Synth.enumerate_sized(
           host.features,
           max_size,
           &Synth.signature(&1, states, feat),
           length(states),
           MapSet.new(task_sigs),
           families: families,
           considered_budget: limits.considered_budget,
           memory_budget: limits.memory_budget
         ) do
      {:empty, reason, meta} ->
        record = search_record(meta, max_size, reason)
        {:empty, versions ++ sized_space(meta), max_size, record}

      {:ok, index, meta} ->
        record = search_record(meta, max_size, nil)
        rows = cumulative(meta.sizes)

        case sized_versions(tasks, task_sigs, index, rows, versions, rejected, score) do
          {versions, {arms, size}} ->
            {:ok, arms, versions, size, record}

          {versions, nil} ->
            {:empty, versions, max_size, record}
        end
    end
  end

  defp sized_space(meta) do
    Enum.flat_map(cumulative(meta.sizes), fn {_size, cum} -> [cum, 0] end)
  end

  defp search_record(meta, max_size, stop) do
    lines =
      phase_lines() ++
        [
          "enumeration #{meta.enum_ms} ms",
          "considered #{meta.considered}",
          "distinct #{meta.distinct}",
          "predicate size bound #{max_size}"
        ] ++
        Enum.map(meta.sizes, fn [size, count] -> "size #{size} #{count}" end) ++
        if(meta.truncated, do: ["subset bound #{Synth.subset_budget()}"], else: [])

    %{
      sizes: meta.sizes,
      enum_ms: meta.enum_ms,
      considered: meta.considered,
      distinct: meta.distinct,
      truncated: meta.truncated,
      size: meta.size,
      lines: lines,
      sized: true,
      stop: stop
    }
  end

  defp phase_lines do
    open = phase("book open", Process.get(:muro_synth_open_ms))
    reach = phase("reach table", Process.get(:muro_synth_reach_ms))
    cover = phase("cover", Process.get(:muro_synth_cover))
    open ++ reach ++ cover
  end

  defp phase(_label, nil), do: []
  defp phase("cover", n) when is_integer(n), do: ["cover #{n}"]
  defp phase(label, ms) when is_integer(ms), do: ["#{label} #{ms} ms"]

  defp cumulative(sizes) do
    {rows, _cum} =
      Enum.map_reduce(sizes, 0, fn [size, count], cum ->
        cum = cum + count
        {{size, cum}, cum}
      end)

    rows
  end

  defp sized_versions(tasks, task_sigs, index, rows, versions, rejected, score) do
    Enum.reduce_while(rows, {versions, nil}, fn {size, cum}, {versions, _found} ->
      case sized_arms(tasks, task_sigs, index, size, rejected, score) do
        {:ok, arms} ->
          {:halt, {versions ++ Enum.flat_map(arms, fn _arm -> [cum, 1] end), {arms, size}}}

        :miss ->
          {:cont, {versions ++ [cum, 0], nil}}
      end
    end)
  end

  defp sized_arms(tasks, task_sigs, index, size, rejected, score) do
    tasks
    |> Enum.zip(task_sigs)
    |> Enum.reduce_while({:ok, []}, fn {task, sig}, {:ok, arms} ->
      name = arm_name(task, length(tasks), length(arms))

      case Map.fetch(index, sig) do
        {:ok, {prog, prog_size, _ord}} when prog_size <= size ->
          if rejected?(rejected, name, prog) do
            {:halt, :miss}
          else
            arm = %{
              name: name,
              pred: Synth.pick([prog], score),
              kept: [prog],
              action: task.action,
              else: task.else,
              observations: task.observations
            }

            {:cont, {:ok, arms ++ [arm]}}
          end

        _ ->
          {:halt, :miss}
      end
    end)
    |> case do
      {:ok, arms} -> {:ok, arms}
      :miss -> :miss
    end
  end

  defp rejected?(rejected, name, prog) do
    MapSet.member?(Map.get(rejected, name, MapSet.new()), prog)
  end

  defp trace_note(text) do
    if System.get_env("MURO_SYNTH_TRACE") in ["1", "true"] do
      IO.puts(:stderr, "muro synth: #{text}")
    end
  end

  defp trace_features(host) do
    if System.get_env("MURO_SYNTH_TRACE") in ["1", "true"] do
      specs = host[:feature_specs] || []

      kinds =
        specs
        |> Enum.map(& &1.kind)
        |> Enum.frequencies()
        |> Enum.map_join(" ", fn {kind, count} -> "#{kind} #{count}" end)

      IO.puts(:stderr, "muro synth: feature kinds #{kinds}")
      IO.puts(:stderr, "muro synth: feature names #{Enum.join(host.features, " ")}")
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
         rejected,
         oracle,
         search \\ nil
       ) do
    trace_note("policy render start")
    render_started = System.monotonic_time(:millisecond)

    case Book.render(host, arms, anchor, oracle) do
      {:error, _reason} ->
        advance(
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
          book_cex(),
          oracle,
          search
        )

      {:ok, source, meta} ->
        Process.put(
          :muro_synth_render_ms,
          System.monotonic_time(:millisecond) - render_started
        )

        started = System.monotonic_time(:millisecond)

        trace_note(
          "certificate start bytes #{byte_size(source)} " <>
            Enum.map_join(arms, " | ", fn arm ->
              "#{arm.name} #{Synth.render(arm.pred)}"
            end)
        )

        # The placement library checks at 8000. The search keeps its fuel.
        cert_fuel = if Map.get(meta, :class_proof), do: max(fuel, 8_000), else: fuel

        case Book.check(source, anchor, fn path -> checker.(path, cert_fuel) end) do
          :ok ->
            cert_ms = System.monotonic_time(:millisecond) - started
            {:ok, checked(arms, source, versions, Map.put(meta, :cert_ms, cert_ms), search)}

          {:error, :storage, diagnostic} ->
            {:error, :storage, diagnostic}

          {:error, text} ->
            if Map.get(meta, :class_proof) do
              refuse_class(host, arms, versions, anchor, oracle, search, text, started)
            else
              cex = Book.cex_from(text, meta.obligations ++ Book.obligations(host, arms))

              advance(
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
                cex,
                oracle,
                search
              )
            end
        end
    end
  end

  # A class proof that does not check is a refusal. It is not a
  # counterexample, and it is not a reason to split the cover.
  defp refuse_class(host, arms, versions, anchor, oracle, search, text, started) do
    reason = class_reason(text)
    Process.put(:muro_synth_class_refusal, reason)

    try do
      case Book.render(host, arms, anchor, oracle) do
        {:ok, source, meta} ->
          cert_ms = System.monotonic_time(:millisecond) - started

          {:ok, checked(arms, source, versions, Map.put(meta, :cert_ms, cert_ms), search)}

        {:error, render_reason} ->
          {:error, render_reason}
      end
    after
      Process.delete(:muro_synth_class_refusal)
    end
  end

  defp class_reason(text) do
    line =
      text
      |> String.split("\n")
      |> Enum.map(&String.trim/1)
      |> Enum.find(fn line ->
        String.match?(line, ~r/^\d+:\d+/) or String.contains?(line, "cannot") or
          String.contains?(line, "expected") or String.contains?(line, "affine") or
          String.contains?(line, "out of fuel")
      end)

    detail = if line in [nil, ""], do: "the checker rejected it", else: line
    "the class proof did not check: #{String.slice(detail, 0, 400)}"
  end

  # The generated book named no obligation. The candidate is not evidence.
  defp book_cex do
    %{carrier: "book", predicted: nil, oracle: nil, pair: nil, fed: 1, agrees: nil}
  end

  defp advance(
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
         cex,
         oracle,
         search
       ) do
    fed = Map.get(seen, cex.carrier, 0) + 1
    cex = %{cex | fed: fed}
    seen = Map.put(seen, cex.carrier, fed)

    arm = arm_for(host, arms, cex)
    {next, rejected} = drop_failed(arm, cex, rejected)
    shrunk = length(next) < length(arm.kept)

    cond do
      not shrunk or rounds <= 1 ->
        {:ok, residual(cex, versions, search)}

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
          rejected,
          oracle,
          search
        )

      depth < max_depth ->
        # The checker removed every survivor at this depth. The next
        # depth is still allowed. Observations stay, and the refused
        # candidates stay out: enumeration there includes them.
        case fit(host, tasks_of(arms), depth + 1, max_depth, score, feat, versions, rejected) do
          {:empty, versions, _at} ->
            {:ok, residual(cex, versions, search)}

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
              rejected,
              oracle,
              search
            )
        end

      true ->
        {:ok, residual(cex, versions, search)}
    end
  end

  # The oracle bit is already an observation, so filtering by it again
  # cannot shrink the space. A boolean from the checker is new: this
  # candidate failed. A book that names no obligation did not check, so
  # this candidate is not evidence either. An obligation that produced
  # no bit stays unknown, including out of fuel. Remember a dropped
  # candidate, including when it was the last one.
  defp drop_failed(arm, cex, rejected) do
    if is_boolean(cex.predicted) or book_failure?(cex) do
      rejected =
        Map.update(rejected, arm.name, MapSet.new([arm.pred]), &MapSet.put(&1, arm.pred))

      {Enum.reject(arm.kept, &(&1 == arm.pred)), rejected}
    else
      {arm.kept, rejected}
    end
  end

  defp book_failure?(%{carrier: "book", predicted: nil} = cex), do: not Map.has_key?(cex, :name)
  defp book_failure?(_cex), do: false

  defp tasks_of(arms) do
    Enum.map(arms, fn arm ->
      %{action: arm.action, else: arm.else, observations: arm.observations}
    end)
  end

  defp replace_arm(arms, arm) do
    Enum.map(arms, fn old -> if old.name == arm.name, do: arm, else: old end)
  end

  defp arm_for(_host, arms, %{kind: :certificate, arm: name}) when is_binary(name) do
    Enum.find(arms, hd(arms), &(&1.name == name))
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

  # Refinement has stopped. The two carriers still agree on every
  # installed test, and a test at the subterm where the values differ
  # did not separate them. The report names that pair, the templates,
  # and the path depth that was reached. It does not deploy a predicate.
  defp insufficient(host, task, depth, feat, earlier, later, predicted, oracle) do
    vs = Synth.enumerate(host.features, depth)
    kept = Synth.refine_all(vs, task.observations, feat)
    specs = List.wrap(host[:feature_specs])
    names = List.wrap(host[:features])
    kinds = specs |> Enum.map(&kind_word/1) |> Enum.uniq()
    path_depth = Map.get(host, :path_depth, Term.first_path_depth())
    path_bound = Term.path_bound()
    left = Term.spell(earlier)
    right = Term.spell(later)

    cex = %{
      carrier: later,
      predicted: predicted,
      oracle: oracle,
      fed: 1,
      agrees: earlier,
      pair: {task.action, task.else},
      reason: "the feature language cannot separate these carriers"
    }

    lines = [
      "muro synth: features insufficient",
      "the feature language cannot separate #{left} and #{right}",
      "#{right} agrees with #{left} on every feature",
      "carrier #{right}",
      "predicted #{predicted}",
      "oracle #{oracle}",
      "fed back 1",
      template_line(kinds),
      feature_line(names),
      depth_line(path_depth, path_bound),
      "version space #{length(vs)}",
      "version space #{length(kept)}"
    ]

    %{
      status: :insufficient,
      program: nil,
      book: nil,
      lines: lines,
      versions: [length(vs), length(kept)],
      cex: [cex],
      features: names,
      kinds: kinds,
      path_depth: path_depth,
      path_bound: path_bound
    }
  end

  defp exhausted_line(_depth, %{stop: stop}) when is_binary(stop), do: stop
  defp exhausted_line(depth, %{sized: true}), do: "predicate size #{depth} exhausted"
  defp exhausted_line(depth, _search), do: "predicate depth #{depth} exhausted"

  defp depth_line_or_stop(_depth, %{stop: stop}) when is_binary(stop), do: []
  defp depth_line_or_stop(depth, _search), do: ["depth #{depth}"]

  defp template_line(kinds), do: "templates " <> Enum.join(kinds, " ")

  defp feature_line([]), do: "features none"
  defp feature_line(names), do: "features " <> Enum.join(names, " ")

  defp depth_line(depth, bound) when depth >= bound,
    do: "path depth #{depth} of #{bound} exhausted"

  defp depth_line(depth, bound), do: "path depth #{depth} of #{bound}"

  defp kind_word(%{kind: :ctor_is}), do: "ctor-is"
  defp kind_word(%{kind: :vals_eq}), do: "vals-eq"
  defp kind_word(%{kind: :spread_eq}), do: "spread-eq"
  defp kind_word(%{kind: :pair_any}), do: "pair-any"
  defp kind_word(%{kind: :len_is}), do: "len-is"
  defp kind_word(%{kind: :nat_is}), do: "nat-is"
  defp kind_word(%{kind: :has_pos_reward}), do: "has-pos-reward"
  defp kind_word(%{kind: :is_self_loop}), do: "is-self-loop"
  defp kind_word(%{kind: :leads_terminal}), do: "leads-terminal"
  defp kind_word(%{kind: :reaches_pos}), do: "reaches-pos"
  defp kind_word(%{kind: :hint}), do: "hint"
  defp kind_word(%{kind: kind}), do: Atom.to_string(kind)

  # The observations agree with the features: no two carriers share a
  # vector and disagree. No predicate at the depths that were searched
  # matches them. The report names those depths and the templates. It
  # does not deploy a predicate.
  defp empty(host, versions, depth, search \\ nil) do
    specs = List.wrap(host[:feature_specs])
    names = List.wrap(host[:features])
    kinds = specs |> Enum.map(&kind_word/1) |> Enum.uniq()
    path_depth = Map.get(host, :path_depth, Term.first_path_depth())
    path_bound = Term.path_bound()

    lines =
      [
        "muro synth: empty version space",
        "no predicate matches the observations",
        exhausted_line(depth, search)
      ] ++
        depth_line_or_stop(depth, search) ++
        [
          template_line(kinds),
          feature_line(names),
          depth_line(path_depth, path_bound)
        ] ++ Enum.map(versions, &"version space #{&1}")

    put_search(
      %{
        status: :empty,
        program: nil,
        book: nil,
        lines: lines,
        versions: versions,
        cex: [],
        certificate: nil,
        features: names,
        kinds: kinds,
        path_depth: path_depth,
        path_bound: path_bound
      },
      search
    )
  end

  defp silent(cex) do
    {action, other} = cex.pair

    lines = [
      "muro synth: oracle cannot label",
      cex.reason,
      "carrier #{Term.spell(cex.carrier)}",
      "pair #{action} #{other}"
    ]

    %{status: :silent, program: nil, book: nil, lines: lines, versions: [], cex: [cex]}
  end

  defp checked(arms, source, versions, meta, search) do
    base =
      Enum.map(arms, &"program: #{Synth.render(&1.pred)}") ++
        preference(arms) ++
        Enum.map(versions, &"version space #{&1}")

    cert_line = "certificate check #{meta.cert_ms} ms"
    render_line = phase("policy render", Process.get(:muro_synth_render_ms))

    result =
      case meta.kind do
        :certified ->
          also = if meta.also, do: ["also #{meta.also}"], else: []

          lines =
            ["muro synth: homomorphism checked"] ++
              base ++
              ["certificate #{meta.certificate}", cert_line] ++
              render_line ++
              also

          %{
            status: :certified,
            program: program_of(arms),
            book: source,
            lines: lines,
            versions: versions,
            cex: [],
            certificate: meta.certificate,
            reason: nil,
            cert_ms: meta.cert_ms
          }

        :policy ->
          lines =
            ["muro synth: policy checked"] ++
              base ++
              ["homomorphism is not derivable", meta.reason, cert_line] ++
              render_line

          %{
            status: :policy,
            program: program_of(arms),
            book: source,
            lines: lines,
            versions: versions,
            cex: [],
            certificate: nil,
            reason: meta.reason,
            cert_ms: meta.cert_ms
          }
      end

    put_search(result, search)
  end

  defp put_search(result, nil), do: result

  # Sized-search fields, on a search that checks and on a stop. `size`
  # is how far enumeration counted, not the size of the survivor.
  # `considered` is programs counted, `distinct` is signatures,
  # `truncated` is a skipped subset, and `sizes` is each size that
  # added a signature.
  defp put_search(result, search) do
    result
    |> Map.put(:sizes, search.sizes)
    |> Map.put(:enum_ms, search.enum_ms)
    |> Map.put(:considered, search.considered)
    |> Map.put(:distinct, search.distinct)
    |> Map.put(:truncated, search.truncated)
    |> Map.put(:size, search.size)
    |> Map.put(:stop, search.stop)
    |> Map.update(:lines, search.lines, &(&1 ++ search.lines))
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

      [
        "at #{Term.spell(state)} the program prefers #{action}",
        "carrier #{Term.spell(state)} bit #{bit}"
      ]
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

  defp residual(cex, versions, search) do
    pair =
      case cex.pair do
        {action, other} -> ["pair #{action} #{other}"]
        _ -> []
      end

    title =
      if Map.get(cex, :kind) == :certificate do
        "muro synth: homomorphism is not derivable"
      else
        "muro synth: residual counterexample"
      end

    lines =
      [
        title,
        "carrier #{Term.spell(cex.carrier)}",
        "predicted #{show_bit(cex.predicted)}",
        "oracle #{show_bit(cex.oracle)}",
        "fed back #{cex.fed}"
      ] ++ pair ++ Enum.map(versions, &"version space #{&1}")

    put_search(
      %{status: :residual, program: nil, book: nil, lines: lines, versions: versions, cex: [cex]},
      search
    )
  end

  defp show_bit(true), do: "true"
  defp show_bit(false), do: "false"
  defp show_bit(nil), do: "unknown"
end
