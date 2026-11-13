defmodule Muro.Synth.Book do
  @moduledoc false

  # The run half of the predicate language. Bool, true, and false come
  # from the environment that imports this text. The file is compiled
  # into the beam, so the policy book does not look the library up from
  # the working directory and does not import a second Bool or leb.
  @pred_path Path.join(__DIR__, "pred.muro")
  @external_resource @pred_path
  @evaluator File.read!(@pred_path)
  @pred_ctors ~w(feat andp orp notp truep falsep)
  @claim_attempts 16

  @doc false
  def evaluator, do: @evaluator

  @doc """
  The book whose `survivor` is the predicate the search returned.

  `eval` of that predicate is the deployed policy. The equations
  `hold-<state>` are the observations. When the environment defines the
  homomorphism the oracle asks for, the book also defines `rank` from
  that predicate and the evidence for it. On a finite `State`, `solve`
  is a constant, or a finite prefix and then a constant or a repeating
  tail. The tail comparison rewrites that closed form.
  Otherwise the book is the policy alone.

  A name the environment already uses is not declared again. A compatible
  `andb`, `PredProg`, or `eval` is the one the policy calls. Anything
  else is given a fresh name, so a generated policy book can be an
  environment for a later search.
  """
  def render(host, arms, anchor, oracle) when is_list(arms) and is_binary(oracle) do
    case bind(host, arms) do
      :error ->
        {:error, "state equality is not a run"}

      {:ok, bound} ->
        render_bound(host, arms, anchor, oracle, bound)
    end
  end

  defp render_bound(host, arms, anchor, oracle, bound) do
    env = rel(anchor, host.path)

    body = """
    import "#{env}"
    #{carrier(host)}
    #{bound.feature_text}
    #{bound.evaluator}
    #{survivors(arms, bound)}
    def #{bound.policy} : run Π (+ s : State) → Action :=
      λ (+ s : State) →
        #{policy_term(arms, bound)}
    #{holds(arms, bound)}
    """

    case Muro.Synth.Cert.render(host, arms, oracle, bound) do
      {:ok, cert} ->
        {:ok, header(:certified) <> body <> cert.text,
         %{
           kind: :certified,
           certificate: cert.certificate,
           also: cert.also,
           reason: nil,
           obligations: cert.obligations
         }}

      {:skip, reason} ->
        {:ok, header(:policy) <> body,
         %{
           kind: :policy,
           certificate: nil,
           also: nil,
           reason: reason,
           obligations: []
         }}
    end
  end

  defp header(:certified) do
    """
    -- The survivor is the predicate the search returned.
    -- eval runs it. rank reads that predicate.
    -- The homomorphism is evidence about that run.
    -- The checker sees this book. It does not see the search.
    """
  end

  defp header(:policy) do
    """
    -- The survivor is the predicate the search returned.
    -- eval runs it. The checker sees this policy. It does not see the search.
    -- This book does not contain a homomorphism.
    """
  end

  def check(source, anchor, checker) when is_function(checker, 1) do
    check(source, anchor, checker, &temp_name/1, [])
  end

  @doc false
  def check(source, anchor, checker, namer, opts \\ [])
      when is_function(checker, 1) and is_function(namer, 1) and is_list(opts) do
    case File.mkdir_p(anchor) do
      :ok ->
        case claim(anchor, namer, source, @claim_attempts, opts) do
          {:ok, path} ->
            try do
              checker.(path)
            after
              _ = File.rm(path)
            end

          {:error, reason} ->
            storage_error(anchor, reason)
        end

      {:error, reason} ->
        storage_error(anchor, reason)
    end
  end

  defp storage_error(anchor, reason) do
    {:error, :storage, "could not write a temporary book in #{anchor}: #{inspect(reason)}"}
  end

  @doc false
  # `IO.binwrite/2` and `File.close/1` return `{:error, reason}` without
  # raising. A raise is the same failure: the partial file is removed
  # and the error is returned. The caller does not read the file, and
  # the next exclusive open is not refused because of it.
  def write_bytes(path, io, bytes, opts \\ []) when is_binary(path) and is_list(opts) do
    binwrite = Keyword.get(opts, :binwrite, &IO.binwrite/2)
    close = Keyword.get(opts, :close, &File.close/1)
    write_result = io_result(fn -> binwrite.(io, bytes) end)
    close_result = io_result(fn -> close.(io) end)

    case {write_result, close_result} do
      {:ok, :ok} ->
        :ok

      {{:raise, error, _stack}, _} ->
        _ = File.rm(path)
        {:error, error}

      {_, {:raise, error, _stack}} ->
        _ = File.rm(path)
        {:error, error}

      {{:error, reason}, _} ->
        _ = File.rm(path)
        {:error, reason}

      {:ok, {:error, reason}} ->
        _ = File.rm(path)
        {:error, reason}
    end
  end

  defp io_result(fun) when is_function(fun, 0) do
    try do
      case fun.() do
        :ok -> :ok
        {:error, reason} -> {:error, reason}
      end
    rescue
      error -> {:raise, error, __STACKTRACE__}
    end
  end

  # `System.unique_integer/1` repeats across BEAM instances. The pid and
  # the random bytes do not, and `:exclusive` refuses a name another
  # process already created.
  defp temp_name(_anchor) do
    hex = Base.encode16(:crypto.strong_rand_bytes(8), case: :lower)
    ".muro-synth-#{System.pid()}-#{hex}.muro"
  end

  defp claim(_anchor, _namer, _source, 0, _opts), do: {:error, :eexist}

  defp claim(anchor, namer, source, left, opts) do
    path = Path.join(anchor, namer.(anchor))

    case File.open(path, [:write, :exclusive]) do
      {:ok, io} ->
        # `IO.write` transcodes to latin1 and refuses Π and λ. The book is
        # already UTF-8, so the bytes go out unchanged.
        case write_bytes(path, io, source, opts) do
          :ok -> {:ok, path}
          {:error, reason} -> {:error, reason}
        end

      {:error, :eexist} ->
        claim(anchor, namer, source, left - 1, opts)

      {:error, reason} ->
        {:error, reason}
    end
  end

  @doc """
  The obligation a failing check named, if the text names one.

  The predicted bit is read from that obligation's diagnostic. A later
  obligation's `cannot convert` does not supply it.
  """
  def cex_from(text, obligations) when is_binary(text) and is_list(obligations) do
    case earliest_obligation(text, obligations) do
      nil ->
        %{carrier: "book", predicted: nil, oracle: nil, pair: nil, fed: 1, agrees: nil}

      ob ->
        region = diagnostic_region(text, ob.name)
        parsed = predicted(region)

        %{
          carrier: ob.carrier,
          predicted: predicted_bit(ob, region, parsed),
          oracle: ob.oracle,
          pair: Map.get(ob, :pair),
          fed: 1,
          agrees: nil,
          name: ob.name,
          kind: Map.get(ob, :kind),
          arm: Map.get(ob, :arm)
        }
    end
  end

  # The diagnostic is `<name> <part>:`. A shorter name is not a match
  # for a longer one: `hold-copy` does not name `hold-copy4`.
  defp earliest_obligation(text, obligations) do
    obligations
    |> Enum.reduce(nil, fn ob, best ->
      case diagnostic_at(text, ob.name) do
        nil ->
          best

        at ->
          case best do
            nil -> {ob, at}
            {_earlier, best_at} when at < best_at -> {ob, at}
            earlier -> earlier
          end
      end
    end)
    |> case do
      nil -> nil
      {ob, _at} -> ob
    end
  end

  defp diagnostic_at(text, name) do
    case Regex.run(diagnostic(name), text, return: :index) do
      [{at, _len} | _] -> at
      _ -> nil
    end
  end

  defp diagnostic(name) do
    ~r/(?<![\p{L}\p{N}_-])#{Regex.escape(name)} (?:type|body|grade|productivity):/u
  end

  # From this obligation's header up to the next definition diagnostic.
  # Errors from `check_sig` are joined by a blank line, and one
  # definition stops at its first failure, so the bit in a later
  # obligation is not this one.
  defp diagnostic_region(text, name) do
    case Regex.run(diagnostic(name), text, return: :index) do
      [{at, len} | _] ->
        rest_at = at + len
        rest = binary_part(text, rest_at, byte_size(text) - rest_at)
        header = binary_part(text, at, len)

        tail =
          case Regex.run(~r/\n+[^\n]* (?:type|body|grade|productivity):/u, rest, return: :index) do
            [{cut, _} | _] -> binary_part(rest, 0, cut)
            _ -> rest
          end

        header <> tail

      _ ->
        ""
    end
  end

  def obligations(host, arms) when is_list(arms) do
    {:ok, bound} = bind(host, arms)

    Enum.flat_map(arms, fn arm ->
      Enum.map(arm.observations, fn {state, bit} ->
        %{
          name: Map.fetch!(bound.hold, {arm.name, state}),
          carrier: state,
          oracle: bit,
          pair: {arm.action, arm.else}
        }
      end)
    end)
  end

  @doc false
  def hold_name(host, arms, arm, state) do
    {:ok, bound} = bind(host, arms)
    Map.fetch!(bound.hold, {arm.name, state})
  end

  defp predicted(text) do
    case Regex.run(~r/cannot convert\s+(\S+)\s+≁\s+(\S+)/u, text) do
      [_, got, _expected] -> bit(got)
      _ -> nil
    end
  end

  defp bit("true"), do: true
  defp bit("false"), do: false
  defp bit(_other), do: nil

  # A certificate obligation always records the bit it claimed. That
  # bit is used only when the diagnostic is a conversion failure. Out
  # of fuel stays unknown, the same as a hold obligation with no
  # claimed bit.
  defp predicted_bit(_ob, _region, parsed) when not is_nil(parsed), do: parsed

  defp predicted_bit(%{kind: :certificate} = ob, region, _parsed) do
    if Muro.Check.out_of_fuel?(region), do: nil, else: Map.get(ob, :claimed)
  end

  defp predicted_bit(ob, _region, _parsed), do: Map.get(ob, :claimed)

  defp bind(host, arms) do
    taken = taken_names(host.book)

    case feature_plan(host, arms, taken) do
      :error -> :error
      {:ok, plan} -> {:ok, bind_plan(host, arms, plan)}
    end
  end

  defp bind_plan(host, arms, plan) do
    # Reserve the placeholder before the evaluator, so a later fresh name
    # does not take the constructor this book is about to declare.
    # A discovered feature reserves its own constructor instead.
    {placeholder, taken} =
      case plan.mode do
        :placeholder -> alloc("none", plan.taken)
        _ -> {nil, plan.taken}
      end

    {evaluator, names, taken} =
      evaluator(host.book, taken, plan.feature_type, plan.feature_eval)

    names = Map.put(names, :spell, plan.spell)

    {decl, taken} =
      Enum.map_reduce(arms, taken, fn arm, taken ->
        {name, taken} = alloc(arm.name, taken)
        {{arm.name, name}, taken}
      end)

    {policy, taken} = alloc("policy", taken)

    {taken, hold} =
      Enum.reduce(arms, {taken, %{}}, fn arm, {taken, acc} ->
        Enum.reduce(arm.observations, {taken, acc}, fn {state, _bit}, {taken, acc} ->
          {name, taken} = alloc(obligation_name(arm, state, length(arms)), taken)
          {taken, Map.put(acc, {arm.name, state}, name)}
        end)
      end)

    %{
      evaluator: evaluator,
      names: names,
      decl: Map.new(decl),
      policy: policy,
      hold: hold,
      placeholder: placeholder,
      feature_text: feature_text(plan, placeholder),
      taken: taken
    }
  end

  defp evaluator(book, taken, feature_type, feature_eval) do
    names = standard_names()

    if feature_type == "Feature" and feature_eval == "eval-feature" and
         Enum.all?(Map.values(names), &(not MapSet.member?(taken, &1))) do
      {@evaluator, names, take(taken, Map.values(names))}
    else
      evaluator_custom(book, taken, feature_type, feature_eval)
    end
  end

  defp evaluator_custom(book, taken, feature_type, feature_eval) do
    {andb, taken, andb_text} = bool_helper(book, taken, "andb", 2, &andb_source/1)
    {orb, taken, orb_text} = bool_helper(book, taken, "orb", 2, &orb_source/1)
    {notb, taken, notb_text} = bool_helper(book, taken, "notb", 1, &notb_source/1)
    {pred_names, taken, pred_text} = pred_block(book, taken, feature_type)

    names =
      pred_names
      |> Map.put(:andb, andb)
      |> Map.put(:orb, orb)
      |> Map.put(:notb, notb)

    {eval, _taken, eval_text} = eval_block(book, taken, names, feature_type, feature_eval)
    names = Map.put(names, :eval, eval)
    text = IO.iodata_to_binary([andb_text, orb_text, notb_text, pred_text, eval_text])
    {text, names, take(taken, Map.values(names))}
  end

  defp bool_helper(book, taken, name, arity, source) do
    if compatible_bool?(book, name, arity) do
      {name, taken, []}
    else
      {fresh_name, taken} = alloc(name, taken)
      {fresh_name, taken, [source.(fresh_name), "\n"]}
    end
  end

  defp pred_block(book, taken, feature_type) do
    if feature_type == "Feature" and compatible_pred?(book) do
      {standard_pred(), taken, []}
    else
      {pred, taken} = alloc("PredProg", taken)

      {ctors, taken} =
        Enum.map_reduce(@pred_ctors, taken, fn name, taken -> alloc(name, taken) end)

      [feat, andp, orp, notp, truep, falsep] = ctors

      names = %{
        pred: pred,
        feat: feat,
        andp: andp,
        orp: orp,
        notp: notp,
        truep: truep,
        falsep: falsep
      }

      {names, taken, [pred_source(names, feature_type), "\n"]}
    end
  end

  defp eval_block(book, taken, names, feature_type, feature_eval) do
    if feature_type == "Feature" and feature_eval == "eval-feature" and names.pred == "PredProg" and
         compatible_eval?(book) do
      {"eval", taken, []}
    else
      {eval, taken} = alloc("eval", taken)
      {eval, taken, [eval_source(eval, names, feature_eval), "\n"]}
    end
  end

  defp compatible_bool?(book, name, arity) do
    case find_def(book, name) do
      %{mode: :run, type: ty} = d ->
        Map.get(d, :export, true) and bool_arrows?(ty, arity)

      _ ->
        false
    end
  end

  defp bool_arrows?({:pi, qty, {:var, "Bool"}, _, cod}, n) when n > 0 and qty != :erased do
    bool_arrows?(cod, n - 1)
  end

  defp bool_arrows?({:var, "Bool"}, 0), do: true
  defp bool_arrows?(_, _), do: false

  defp compatible_pred?(book) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and Map.get(&1, :name) == "PredProg")) do
      %{ctors: ctors} ->
        Enum.map(ctors, & &1.name) == @pred_ctors and Enum.all?(ctors, &compatible_ctor?/1)

      _ ->
        false
    end
  end

  defp compatible_ctor?(%{
         name: "feat",
         type: {:pi, qty, {:var, "Feature"}, _, {:var, "PredProg"}}
       })
       when qty != :erased,
       do: true

  defp compatible_ctor?(%{
         name: "andp",
         type:
           {:pi, q1, {:var, "PredProg"}, _, {:pi, q2, {:var, "PredProg"}, _, {:var, "PredProg"}}}
       })
       when q1 != :erased and q2 != :erased,
       do: true

  defp compatible_ctor?(%{
         name: "orp",
         type:
           {:pi, q1, {:var, "PredProg"}, _, {:pi, q2, {:var, "PredProg"}, _, {:var, "PredProg"}}}
       })
       when q1 != :erased and q2 != :erased,
       do: true

  defp compatible_ctor?(%{
         name: "notp",
         type: {:pi, qty, {:var, "PredProg"}, _, {:var, "PredProg"}}
       })
       when qty != :erased,
       do: true

  defp compatible_ctor?(%{name: "truep", type: {:var, "PredProg"}}), do: true
  defp compatible_ctor?(%{name: "falsep", type: {:var, "PredProg"}}), do: true
  defp compatible_ctor?(_ctor), do: false

  defp compatible_eval?(book) do
    case find_def(book, "eval") do
      %{
        mode: :run,
        type: {:pi, q1, {:var, "PredProg"}, _, {:pi, q2, carrier, _, {:var, "Bool"}}}
      } = d
      when q1 != :erased and q2 != :erased ->
        Map.get(d, :export, true) and carrier_dom?(carrier)

      _ ->
        false
    end
  end

  defp carrier_dom?({:var, "Carrier"}), do: true
  defp carrier_dom?({:var, "State"}), do: true
  defp carrier_dom?(_ty), do: false

  defp find_def(book, name) do
    Enum.find(book, fn d ->
      Map.get(d, :name) == name and Map.get(d, :kind) not in [:data, :import]
    end)
  end

  defp standard_names do
    Map.put(standard_pred(), :andb, "andb")
    |> Map.put(:orb, "orb")
    |> Map.put(:notb, "notb")
    |> Map.put(:eval, "eval")
  end

  defp standard_pred do
    %{
      pred: "PredProg",
      feat: "feat",
      andp: "andp",
      orp: "orp",
      notp: "notp",
      truep: "truep",
      falsep: "falsep"
    }
  end

  defp andb_source(name) do
    """
    def #{name} : run Π (a : Bool) → Π (b : Bool) → Bool :=
      λ (a : Bool) → λ (b : Bool) →
        match a motive (λ _ → Bool)
          | true => b
          | false => false
    """
  end

  defp orb_source(name) do
    """
    def #{name} : run Π (a : Bool) → Π (b : Bool) → Bool :=
      λ (a : Bool) → λ (b : Bool) →
        match a motive (λ _ → Bool)
          | true => true
          | false => b
    """
  end

  defp notb_source(name) do
    """
    def #{name} : run Π (a : Bool) → Bool :=
      λ (a : Bool) →
        match a motive (λ _ → Bool)
          | true => false
          | false => true
    """
  end

  defp pred_source(n, feature_type) do
    """
    data #{n.pred} : Type where
      #{n.feat} : Π (+ f : #{feature_type}) → #{n.pred}
      #{n.andp} : #{n.pred} → #{n.pred} → #{n.pred}
      #{n.orp} : #{n.pred} → #{n.pred} → #{n.pred}
      #{n.notp} : #{n.pred} → #{n.pred}
      #{n.truep} : #{n.pred}
      #{n.falsep} : #{n.pred}
    """
  end

  defp eval_source(eval, n, feature_eval) do
    """
    def #{eval} : run Π (p : #{n.pred}) → Π (+ c : Carrier) → Bool :=
      λ (p : #{n.pred}) → λ (+ c : Carrier) →
        match p motive (λ _ → Bool)
          | #{n.feat} f => #{feature_eval} f c
          | #{n.andp} q r => #{n.andb} (#{eval} q c) (#{eval} r c)
          | #{n.orp} q r => #{n.orb} (#{eval} q c) (#{eval} r c)
          | #{n.notp} q => #{n.notb} (#{eval} q c)
          | #{n.truep} => true
          | #{n.falsep} => false
    """
  end

  defp taken_names(book) do
    Enum.reduce(book, MapSet.new(), fn d, acc -> take(acc, entry_names(d)) end)
  end

  defp entry_names(%{kind: :data, name: name, ctors: ctors}),
    do: [name | Enum.map(ctors, & &1.name)]

  defp entry_names(%{kind: :import}), do: []
  defp entry_names(%{name: name}), do: [name]
  defp entry_names(_), do: []

  @doc false
  def reserve(base, taken), do: alloc(base, taken)

  defp alloc(base, taken) do
    name = fresh(base, taken)
    {name, take(taken, [name])}
  end

  # `Muro.Load` refuses two runs that spell one Elixir function.
  # `policy-2` and `policy_2` are distinct source names and one spelling.
  defp fresh(base, taken) do
    if occupied?(base, taken) do
      n = Enum.find(2..10_000, &(not occupied?("#{base}-#{&1}", taken)))
      "#{base}-#{n}"
    else
      base
    end
  end

  defp occupied?(name, taken) do
    MapSet.member?(taken, name) or
      MapSet.member?(taken, {:elixir, Muro.Emit.elixir_base(name)})
  end

  defp take(taken, names) do
    Enum.reduce(names, taken, fn name, acc ->
      acc
      |> MapSet.put(name)
      |> MapSet.put({:elixir, Muro.Emit.elixir_base(name)})
    end)
  end

  defp survivors(arms, bound) do
    Enum.map_join(arms, "\n", fn arm ->
      decl = Map.fetch!(bound.decl, arm.name)
      "def #{decl} : run #{bound.names.pred} := #{spell(arm.pred, bound.names)}"
    end)
  end

  defp spell(true, names), do: names.truep
  defp spell(false, names), do: names.falsep

  defp spell({:feat, feature}, names) do
    ctor = Map.get(names.spell, feature, feature)
    "(#{names.feat} #{ctor})"
  end

  defp spell({:not, pred}, names), do: "(#{names.notp} #{spell(pred, names)})"
  defp spell({:and, p, q}, names), do: "(#{names.andp} #{spell(p, names)} #{spell(q, names)})"
  defp spell({:or, p, q}, names), do: "(#{names.orp} #{spell(p, names)} #{spell(q, names)})"

  defp policy_term([arm], bound) do
    decl = Map.fetch!(bound.decl, arm.name)

    "(match #{bound.names.eval} #{decl} s motive (λ _ → Action) | true => #{arm.action} | false => #{arm.else})"
  end

  defp policy_term([arm | rest], bound) do
    decl = Map.fetch!(bound.decl, arm.name)

    "(match #{bound.names.eval} #{decl} s motive (λ _ → Action) | true => #{arm.action} | false => #{policy_term(rest, bound)})"
  end

  defp holds(arms, bound) do
    Enum.map_join(arms, "\n", fn arm ->
      decl = Map.fetch!(bound.decl, arm.name)

      Enum.map_join(arm.observations, "\n", fn {state, bit} ->
        name = Map.fetch!(bound.hold, {arm.name, state})
        word = if bit, do: "true", else: "false"

        "def #{name} : evidence {#{bound.names.eval} #{decl} #{Muro.Synth.Term.spell(state)} ≡ #{word} : Bool} := refl"
      end)
    end)
  end

  defp carrier(host) do
    if host.defined_carrier do
      ""
    else
      "def Carrier : spec Type := State\n"
    end
  end

  defp feature_text(%{mode: :placeholder}, name) when is_binary(name) do
    """
    data Feature : Type where
      #{name} : Feature

    def eval-feature : run Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
      λ (+ f : Feature) → λ (+ _ : Carrier) →
        match f motive (λ _ → Bool)
          | #{name} => false
    """
  end

  defp feature_text(%{text: text}, _placeholder), do: text

  # The program reads a dynamics feature. The book's own `Feature`, when
  # it has one, cannot grow a constructor, so the policy's predicate
  # talks about a fresh type. A declared hint is a constructor of that
  # type whose reading is the book's `eval-feature`.
  defp feature_plan(host, arms, taken) do
    specs =
      arms
      |> Enum.flat_map(&Muro.Synth.reads(&1.pred))
      |> Enum.uniq()
      |> Enum.map(&spec!(host, &1))

    cond do
      specs == [] and not host.defined_feature ->
        {:ok, empty_plan(taken, :placeholder)}

      Enum.any?(specs, &(&1.kind != :hint)) and host.defined_feature ->
        extend_plan(host, specs, taken)

      Enum.any?(specs, &(&1.kind != :hint)) ->
        declared_plan(host, specs, taken)

      true ->
        {:ok, empty_plan(taken, :env)}
    end
  end

  defp empty_plan(taken, mode) do
    %{
      mode: mode,
      text: "",
      spell: %{},
      feature_type: "Feature",
      feature_eval: "eval-feature",
      taken: taken
    }
  end

  defp spec!(host, name) do
    case Enum.find(host.feature_specs, &(&1.name == name)) do
      nil -> raise ArgumentError, "the search read a feature it did not discover: #{name}"
      spec -> spec
    end
  end

  defp declared_plan(host, specs, taken) do
    case vocab_text(host, specs, taken, "Feature", "eval-feature") do
      :error ->
        :error

      {:ok, text, taken, spell} ->
        {:ok,
         %{
           mode: :declared,
           text: text,
           spell: spell,
           feature_type: "Feature",
           feature_eval: "eval-feature",
           taken: taken
         }}
    end
  end

  defp extend_plan(host, specs, taken) do
    {type_name, taken} = alloc("DynFeature", taken)
    {eval_name, taken} = alloc("eval-dyn", taken)

    case vocab_text(host, specs, taken, type_name, eval_name) do
      :error ->
        :error

      {:ok, text, taken, spell} ->
        {:ok,
         %{
           mode: :extend,
           text: text,
           spell: spell,
           feature_type: type_name,
           feature_eval: eval_name,
           taken: taken
         }}
    end
  end

  defp vocab_text(host, specs, taken, type_name, eval_name) do
    case helper_block(host, specs, taken) do
      :error -> :error
      {:ok, helpers, taken} -> vocab_rows(specs, taken, type_name, eval_name, helpers)
    end
  end

  defp vocab_rows(specs, taken, type_name, eval_name, helpers) do
    {rows, taken, spell} =
      Enum.reduce(specs, {[], taken, %{}}, fn spec, {rows, taken, spell} ->
        {ctor, taken} = alloc(spec.name, taken)
        row = %{spec: spec, ctor: ctor}
        {rows ++ [row], taken, Map.put(spell, spec.name, ctor)}
      end)

    text = """
    #{helpers.text}
    data #{type_name} : Type where
    #{Enum.map_join(rows, "\n", &"  #{&1.ctor} : #{type_name}")}

    def #{eval_name} : run Π (+ f : #{type_name}) → Π (+ c : Carrier) → Bool :=
      λ (+ f : #{type_name}) → λ (+ c : Carrier) →
        match f motive (λ _ → Bool)
    #{Enum.map_join(rows, "\n", &eval_clause(&1, helpers))}
    """

    {:ok, text, taken, spell}
  end

  defp helper_block(host, specs, taken) do
    kinds = MapSet.new(specs, & &1.kind)
    need_pos = MapSet.member?(kinds, :has_pos_reward)
    need_same = MapSet.member?(kinds, :is_self_loop) or MapSet.member?(kinds, :leads_terminal)
    need_terminal = MapSet.member?(kinds, :leads_terminal)

    {pos, taken, pos_text} =
      if need_pos do
        {name, taken} = alloc("dyn-pos", taken)
        {name, taken, pos_source(name)}
      else
        {nil, taken, ""}
      end

    same_built =
      if need_same do
        {name, taken} = alloc("dyn-same", taken)

        case equality_source(name, host, taken) do
          {:ok, text, taken} -> {:ok, name, taken, text}
          :error -> :error
        end
      else
        {:ok, nil, taken, ""}
      end

    case same_built do
      :error ->
        :error

      {:ok, same, taken, same_text} ->
        helper_rest(host, specs, taken, need_terminal, pos, pos_text, same, same_text)
    end
  end

  defp helper_rest(host, specs, taken, need_terminal, pos, pos_text, same, same_text) do
    {terminal, taken, terminal_text} =
      if need_terminal do
        {name, taken} = alloc("dyn-terminal", taken)
        {name, taken, terminal_source(name, same, host.actions)}
      else
        {nil, taken, ""}
      end

    {struct_helpers, taken} = Muro.Synth.Term.render_helpers(specs, taken)
    text = Enum.join([struct_helpers.text, pos_text, same_text, terminal_text], "\n")

    {:ok,
     %{
       pos: pos,
       same: same,
       terminal: terminal,
       text: text,
       struct: struct_helpers,
       schema: host.schema
     }, taken}
  end

  # A finite structured state matches every inhabitant. An open structured
  # state compares the two terms from the schema. The nullary match is
  # only for a non-empty list of constructor names. An empty list is not
  # a match with no arms.
  defp equality_source(name, %{structured: true, inhabitants: inhab, schema: schema}, taken)
       when is_list(inhab) and inhab != [] do
    {:ok, Muro.Synth.Term.same_source(name, schema, inhab), taken}
  end

  defp equality_source(name, %{structured: true, schema: schema}, taken) do
    case Muro.Synth.Term.eq_source(name, schema, taken) do
      {:ok, text, taken} -> {:ok, text, taken}
      :open -> :error
    end
  end

  defp equality_source(name, %{states: states}, taken) when is_list(states) and states != [] do
    {:ok, same_source(name, states), taken}
  end

  defp equality_source(_name, _host, _taken), do: :error

  defp eval_clause(%{spec: %{kind: :has_pos_reward, action: action}, ctor: ctor}, helpers) do
    "      | #{ctor} => #{helpers.pos} (snd (step c #{action}))"
  end

  defp eval_clause(%{spec: %{kind: :is_self_loop, action: action}, ctor: ctor}, helpers) do
    "      | #{ctor} => #{helpers.same} c (fst (step c #{action}))"
  end

  defp eval_clause(%{spec: %{kind: :leads_terminal, action: action}, ctor: ctor}, helpers) do
    "      | #{ctor} => #{helpers.terminal} (fst (step c #{action}))"
  end

  defp eval_clause(%{spec: %{kind: :hint, name: name}, ctor: ctor}, _helpers) do
    "      | #{ctor} => eval-feature #{name} c"
  end

  defp eval_clause(%{spec: spec, ctor: ctor}, helpers) do
    if Muro.Synth.Term.structural?(spec) do
      Muro.Synth.Term.render_clause(helpers.schema, spec, ctor, helpers.struct)
    else
      "      | #{ctor} => false"
    end
  end

  defp pos_source(name) do
    """
    def #{name} : run Π (r : Nat) → Bool :=
      λ (r : Nat) →
        match r motive (λ _ → Bool)
          | 0 => false
          | suc _ => true
    """
  end

  defp same_source(name, states) do
    branches =
      Enum.map_join(states, "\n", fn state ->
        inner =
          Enum.map_join(states, "\n", fn other ->
            bit = if state == other, do: "true", else: "false"
            "          | #{other} => #{bit}"
          end)

        """
          | #{state} =>
              (match t motive (λ _ → Bool)
        #{inner})
        """
      end)

    """
    def #{name} : run Π (+ s : State) → Π (+ t : State) → Bool :=
      λ (+ s : State) → λ (+ t : State) →
        match s motive (λ _ → Bool)
    #{branches}
    """
  end

  defp terminal_source(name, same, actions) do
    """
    def #{name} : run Π (+ s : State) → Bool :=
      λ (+ s : State) →
        #{terminal_body(same, actions)}
    """
  end

  defp terminal_body(same, [action]) do
    "#{same} s (fst (step s #{action}))"
  end

  defp terminal_body(same, [action | rest]) do
    """
    (match (#{same} s (fst (step s #{action}))) motive (λ _ → Bool)
      | true => #{terminal_body(same, rest)}
      | false => false)
    """
  end

  def obligation_name(_arm, state, 1), do: "hold-#{Muro.Synth.Term.label(state)}"
  def obligation_name(arm, state, _many), do: "hold-#{arm.action}-#{Muro.Synth.Term.label(state)}"

  defp rel(from_dir, to_file) do
    from = from_dir |> Path.expand() |> Path.split()
    to = to_file |> Path.expand() |> Path.split()
    {from, to} = drop_common(from, to)
    Path.join(List.duplicate("..", length(from)) ++ to)
  end

  defp drop_common([head | from], [head | to]), do: drop_common(from, to)
  defp drop_common(from, to), do: {from, to}
end
