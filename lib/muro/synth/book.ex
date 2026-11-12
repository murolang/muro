defmodule Muro.Synth.Book do
  @moduledoc false

  # The run half of the predicate language. Bool, true, and false come
  # from the environment that imports this text. The file is compiled
  # into the beam, so the policy book does not look the library up from
  # the working directory and does not import a second Bool or leb.
  @pred_path Path.join(__DIR__, "pred.muro")
  @external_resource @pred_path
  @evaluator File.read!(@pred_path)

  @doc false
  def evaluator, do: @evaluator

  @doc """
  The book whose `survivor` is the predicate the search returned.

  `eval` of that predicate is the deployed policy. The equations
  `hold-<state>` are the observations. A homomorphism is not in this book.
  """
  def render(host, arms, anchor) when is_list(arms) do
    env = rel(anchor, host.path)

    """
    -- The survivor is the predicate the search returned.
    -- eval runs it. The checker sees this policy. It does not see the search.
    -- A homomorphism for the policy is later.
    import "#{env}"
    #{carrier(host)}
    #{features(host)}
    #{@evaluator}
    #{survivors(arms)}
    def policy : run Π (+ s : State) → Action :=
      λ (+ s : State) →
        #{policy_term(arms)}
    #{holds(arms)}
    """
    |> then(&{:ok, &1})
  end

  def check(source, anchor, checker) when is_function(checker, 1) do
    File.mkdir_p!(anchor)
    path = Path.join(anchor, ".muro-synth-#{System.unique_integer([:positive])}.muro")
    File.write!(path, source)

    try do
      checker.(path)
    after
      File.rm(path)
    end
  end

  @doc """
  The obligation a failing check named, if the text names one.
  """
  def cex_from(text, obligations) when is_binary(text) and is_list(obligations) do
    case earliest_obligation(text, obligations) do
      nil ->
        %{carrier: "book", predicted: nil, oracle: nil, pair: nil, fed: 1, agrees: nil}

      ob ->
        %{
          carrier: ob.carrier,
          predicted: predicted(text),
          oracle: ob.oracle,
          pair: Map.get(ob, :pair),
          fed: 1,
          agrees: nil,
          name: ob.name
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

  def obligations(arms) do
    Enum.flat_map(arms, fn arm ->
      Enum.map(arm.observations, fn {state, bit} ->
        %{
          name: obligation_name(arm, state, length(arms)),
          carrier: state,
          oracle: bit,
          pair: {arm.action, arm.else}
        }
      end)
    end)
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

  defp carrier(host) do
    if host.defined_carrier do
      ""
    else
      "def Carrier : spec Type := State\n"
    end
  end

  defp features(host) do
    if host.defined_feature do
      ""
    else
      """
      data Feature : Type where
        none : Feature

      def eval-feature : run Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
        λ (+ f : Feature) → λ (+ _ : Carrier) →
          match f motive (λ _ → Bool)
            | none => false
      """
    end
  end

  defp survivors(arms) do
    Enum.map_join(arms, "\n", fn arm ->
      "def #{arm.name} : run PredProg := #{Muro.Synth.render(arm.pred)}"
    end)
  end

  defp policy_term([arm]) do
    "(match eval #{arm.name} s motive (λ _ → Action) | true => #{arm.action} | false => #{arm.else})"
  end

  defp policy_term([arm | rest]) do
    "(match eval #{arm.name} s motive (λ _ → Action) | true => #{arm.action} | false => #{policy_term(rest)})"
  end

  defp holds(arms) do
    many = length(arms)

    Enum.map_join(arms, "\n", fn arm ->
      Enum.map_join(arm.observations, "\n", fn {state, bit} ->
        name = obligation_name(arm, state, many)
        word = if bit, do: "true", else: "false"

        "def #{name} : evidence {eval #{arm.name} #{state} ≡ #{word} : Bool} := refl"
      end)
    end)
  end

  def obligation_name(_arm, state, 1), do: "hold-#{state}"
  def obligation_name(arm, state, _many), do: "hold-#{arm.action}-#{state}"

  defp rel(from_dir, to_file) do
    from = from_dir |> Path.expand() |> Path.split()
    to = to_file |> Path.expand() |> Path.split()
    {from, to} = drop_common(from, to)
    Path.join(List.duplicate("..", length(from)) ++ to)
  end

  defp drop_common([head | from], [head | to]), do: drop_common(from, to)
  defp drop_common(from, to), do: {from, to}
end
