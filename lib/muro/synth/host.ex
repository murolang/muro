defmodule Muro.Synth.Host do
  @moduledoc false

  @doc """
  Load a checked environment and call its emitted `step`.

  `{:error, :book, msg}` is a book that does not check. `{:error,
  :usage, msg}` is a book that checks and does not follow the
  environment convention.
  """
  def open(path, opts \\ []) when is_binary(path) and is_list(opts) do
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())
    structural = Keyword.get(opts, :structural, true)

    case Muro.Load.file(path, fuel: fuel) do
      {:error, msg} -> {:error, :book, msg}
      {:ok, book} -> compile(path, book, structural)
    end
  end

  defp compile(path, book, structural) do
    with :ok <- present(book, "State"),
         :ok <- present(book, "Action"),
         :ok <- present(book, "step"),
         :ok <- present(book, "all-actions"),
         :ok <- present(book, "horizon"),
         :ok <- present(book, "leb"),
         {:ok, shape} <- state_shape(book),
         :ok <- signatures(book),
         {:ok, actions} <- nullary(book, "Action"),
         {:ok, features} <- features(book) do
      module = Module.concat(Muro.Synth.Host, "M#{System.unique_integer([:positive])}")
      emitted = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()
      Code.eval_string(Muro.Emit.emit_module(module, emitted))

      {states, names, schema, inhabitants, structured} =
        case shape do
          {:nullary, states} ->
            {states, states ++ actions ++ features, nil, nil, false}

          {:structured, schema, inhabitants} ->
            {inhabitants || [], actions ++ features, schema, inhabitants, true}
        end

      atoms = Map.new(names, fn name -> {name, atom(name)} end)
      sources = Map.new(atoms, fn {name, atom} -> {atom, name} end)

      host = %{
        path: Path.expand(path),
        module: module,
        book: book,
        states: states,
        actions: actions,
        features: features,
        defined_feature: named?(book, "Feature"),
        defined_carrier: named?(book, "Carrier"),
        defined_eval: named?(book, "eval-feature"),
        atoms: atoms,
        sources: sources,
        structured: structured,
        structural: structural,
        schema: schema,
        inhabitants: inhabitants
      }

      link(host)
    end
  end

  defp link(host) do
    case call(host, "all-actions", []) do
      nil ->
        {:error, :usage, "the book does not define all-actions"}

      listed ->
        # A repeated action is one arm, in first-occurrence order. The
        # default, when `default-action` is omitted, is the last element
        # of the list as written, including a repeat of an earlier action.
        decoded = listed |> decode_list() |> Enum.map(&source!(host, &1))
        actions = Enum.uniq(decoded)
        horizon = host |> call("horizon", []) |> nat_int()

        all_states =
          if exported?(host, "all-states", 0) do
            listed = host |> call("all-states", []) |> decode_list()

            case decode_states(host, listed) do
              {:ok, states} -> states
              {:error, _, _} = err -> throw(err)
            end
          else
            nil
          end

        default =
          if exported?(host, "default-action", 0) do
            source!(host, call(host, "default-action", []))
          else
            List.last(decoded)
          end

        host =
          %{
            host
            | actions: actions,
              states: host.states
          }
          |> Map.put(:horizon, horizon)
          |> Map.put(:all_states, all_states)
          |> Map.put(:default, default)
          |> Map.put(:step, fn state, action ->
            {next, reward} = call(host, "step", [state_arg(host, state), atom!(host, action)])
            {decode_state!(host, next), reward}
          end)
          |> Map.put(:leb, fn left, right ->
            truth!(call(host, "leb", [left, right]))
          end)
          |> Map.put(:eval_feature, fn feature, state ->
            truth!(call(host, "eval-feature", [atom!(host, feature), state_arg(host, state)]))
          end)

        {:ok, discover(host)}
    end
  catch
    {:error, _, _} = err -> err
  end

  @doc false
  def install_features(host, specs) when is_list(specs) do
    hint_eval = Map.get(host, :hint_eval, host.eval_feature)

    eval = fn name, state ->
      spec = Enum.find(specs, &(&1.name == name))
      Muro.Synth.Feature.eval_spec(host, hint_eval, spec, state)
    end

    host
    |> Map.put(:feature_specs, specs)
    |> Map.put(:features, Enum.map(specs, & &1.name))
    |> Map.put(:eval_feature, eval)
    |> Map.put(:hint_eval, hint_eval)
  end

  # Declared constructors are hints. Dynamics templates are read off
  # `step`. Both are filtered and reduced before the search sees them.
  # A book with neither `Feature` nor `eval-feature` has only what the
  # templates find, plus the two constants.
  defp discover(host) do
    hints = host.features
    host = Map.put(host, :hint_eval, host.eval_feature)
    specs = Muro.Synth.Feature.discover(host, hints)

    host
    |> Map.put(:hints, hints)
    |> install_features(specs)
  end

  # Parameters and indices are read from the declaration. A checking
  # book cannot write `s : State` when `State` is a family, so this
  # refusal runs before the step signature.
  defp state_shape(book) do
    case Muro.Synth.Term.schema(book, "State") do
      {:enum, _, names} ->
        {:ok, {:nullary, names}}

      {:open, "missing"} ->
        {:error, :usage, "the book does not define State"}

      {:open, "params"} ->
        {:error, :usage, "State has parameters"}

      {:open, "indices"} ->
        {:error, :usage, "State has indices"}

      {:open, "mutual"} ->
        {:error, :usage, "State is mutually inductive"}

      {:open, "function"} ->
        {:error, :usage, "State has a function field"}

      schema ->
        # A linear field still opens: search can run. The certificate
        # refuses it later. A function field and an erased constructor
        # argument are not values the cover can name.
        case Muro.Synth.Term.cert_refusal(schema) do
          "State has a function field" = msg ->
            {:error, :usage, msg}

          "State has an erased constructor argument" = msg ->
            {:error, :usage, msg}

          _ ->
            inhabitants_or_cover(book, schema)
        end
    end
  end

  defp inhabitants_or_cover(book, schema) do
    case Muro.Synth.Term.inhabitants(schema) do
      {:ok, inhabitants} ->
        {:ok, {:structured, schema, inhabitants}}

      :cap ->
        open_or(
          book,
          schema,
          "State has more than #{Muro.Synth.Term.cap()} inhabitants; declare all-states"
        )

      :open ->
        open_or(book, schema, "State constructors take arguments; declare all-states")
    end
  end

  defp open_or(book, schema, message) do
    if named?(book, "all-states") do
      {:ok, {:structured, schema, nil}}
    else
      {:error, :usage, message}
    end
  end

  defp decode_states(host, raws) do
    if host.structured do
      Enum.reduce_while(raws, {:ok, []}, fn raw, {:ok, acc} ->
        case Muro.Synth.Term.decode(raw, host.schema) do
          {:ok, term} ->
            {:cont, {:ok, acc ++ [term]}}

          :error ->
            {:halt, {:error, :usage, "all-states has a value that is not a State"}}
        end
      end)
      |> case do
        {:ok, states} -> {:ok, Enum.uniq_by(states, & &1.value)}
        other -> other
      end
    else
      {:ok, raws |> Enum.map(&source!(host, &1)) |> Enum.uniq()}
    end
  end

  defp state_arg(host, %Muro.Synth.Term{value: value}) do
    if host.structured, do: value, else: atom!(host, value)
  end

  defp state_arg(host, state), do: atom!(host, state)

  defp decode_state!(host, raw) do
    if host.structured do
      Muro.Synth.Term.decode!(raw, host.schema)
    else
      source!(host, raw)
    end
  end

  defp present(book, name) do
    if named?(book, name), do: :ok, else: {:error, :usage, "the book does not define #{name}"}
  end

  # Names are not enough. `all-actions : run Nat := 0` checks and then
  # crashes in `decode_list`. The modes and the types are the contract
  # the search calls, and a mismatch is a usage error before any call.
  defp signatures(book) do
    with :ok <- carrier_state(book),
         {:ok, step} <- public_run(book, "step"),
         :ok <- no_erased(book, "step", step),
         {:ok, reward} <- step_reward(book, step),
         {:ok, actions} <- public_run(book, "all-actions"),
         :ok <- no_erased(book, "all-actions", actions),
         :ok <- list_of(book, actions, "Action", "all-actions must be run List Action"),
         {:ok, horizon} <- public_run(book, "horizon"),
         :ok <- no_erased(book, "horizon", horizon),
         :ok <- nat_type(book, horizon, "horizon must be run Nat"),
         {:ok, leb} <- public_run(book, "leb"),
         :ok <- no_erased(book, "leb", leb),
         :ok <- leb_type(book, leb, reward),
         :ok <- optional_list(book, "all-states", "State"),
         :ok <- optional_name(book, "default-action", "Action"),
         :ok <- eval_feature_type(book) do
      :ok
    end
  end

  # `run internal` emits `defp`. An erased argument is dropped from the
  # Elixir arity. Either one makes the later `apply` raise instead of
  # refusing the environment. Every definition the search calls is a
  # public run, and every argument is passed.
  defp public_run(book, name) do
    case Enum.find(book, &(Map.get(&1, :name) == name)) do
      %{mode: :run, type: ty} = d ->
        if Map.get(d, :export, true) do
          {:ok, ty}
        else
          {:error, :usage, "#{name} is run internal; the environment requires a public run"}
        end

      %{mode: mode} ->
        {:error, :usage, "#{name} is #{mode}; the environment requires run"}

      %{kind: :data} ->
        {:error, :usage, "#{name} is spec; the environment requires run"}

      _ ->
        {:error, :usage, "the book does not define #{name}"}
    end
  end

  defp no_erased(book, name, ty) do
    if erased_arg?(unfold(book, ty)) do
      {:error, :usage, "#{name} takes an erased argument"}
    else
      :ok
    end
  end

  defp erased_arg?({:pi, :erased, _, _, _}), do: true
  defp erased_arg?({:pi, _, _, _, cod}), do: erased_arg?(cod)
  defp erased_arg?(_ty), do: false

  defp carrier_state(book) do
    cond do
      not named?(book, "Carrier") ->
        :ok

      same?(book, {:var, "Carrier"}, {:var, "State"}) ->
        :ok

      true ->
        {:error, :usage, "Carrier must convert to State"}
    end
  end

  defp step_reward(book, ty) do
    with {:pi, _, state, _, rest} <- ty,
         true <- same?(book, state, {:var, "State"}),
         {:pi, _, action, _, cod} <- rest,
         true <- same?(book, action, {:var, "Action"}),
         {:prod, next, reward} <- unfold(book, cod),
         true <- same?(book, next, {:var, "State"}) do
      {:ok, unfold(book, reward)}
    else
      _ ->
        {:error, :usage, "step must be run Π (s : State) → Π (a : Action) → State × Reward"}
    end
  end

  defp list_of(book, ty, elem, message) do
    case unfold(book, ty) do
      {:app, {:var, "List"}, arg} ->
        if same?(book, arg, {:var, elem}), do: :ok, else: {:error, :usage, message}

      _ ->
        {:error, :usage, message}
    end
  end

  defp nat_type(book, ty, message) do
    if same?(book, ty, :nat), do: :ok, else: {:error, :usage, message}
  end

  defp leb_type(book, ty, reward) do
    with {:pi, _, left, _, rest} <- ty,
         true <- same?(book, left, reward),
         {:pi, _, right, _, cod} <- rest,
         true <- same?(book, right, reward),
         true <- bool?(book, cod) do
      :ok
    else
      _ -> {:error, :usage, "leb must compare the reward step returns"}
    end
  end

  defp optional_list(book, name, elem) do
    if named?(book, name) do
      with {:ok, ty} <- public_run(book, name),
           :ok <- no_erased(book, name, ty) do
        list_of(book, ty, elem, "#{name} must be run List #{elem}")
      end
    else
      :ok
    end
  end

  defp optional_name(book, name, type_name) do
    if named?(book, name) do
      with {:ok, ty} <- public_run(book, name),
           :ok <- no_erased(book, name, ty) do
        if same?(book, ty, {:var, type_name}),
          do: :ok,
          else: {:error, :usage, "#{name} must be run #{type_name}"}
      end
    else
      :ok
    end
  end

  defp eval_feature_type(book) do
    cond do
      named?(book, "eval-feature") and not named?(book, "Feature") ->
        {:error, :usage, "the book defines eval-feature and does not define Feature"}

      not named?(book, "Feature") or not named?(book, "eval-feature") ->
        :ok

      true ->
        with {:ok, ty} <- public_run(book, "eval-feature"),
             :ok <- no_erased(book, "eval-feature", ty) do
          if eval_feature?(book, ty),
            do: :ok,
            else:
              {:error, :usage,
               "eval-feature must be run Π (f : Feature) → Π (c : Carrier) → Bool"}
        end
    end
  end

  defp eval_feature?(book, ty) do
    with {:pi, _, feature, _, rest} <- ty,
         true <- same?(book, feature, {:var, "Feature"}),
         {:pi, _, carrier, _, cod} <- rest,
         true <- carrier?(book, carrier),
         true <- bool?(book, cod) do
      true
    else
      _ -> false
    end
  end

  # `Carrier := State` unfolds to `State`. An unrelated `Carrier` does
  # not, so a State value is not passed to a function that matches on it.
  defp carrier?(book, ty) do
    same?(book, ty, {:var, "State"})
  end

  defp bool?(book, ty), do: same?(book, ty, {:var, "Bool"})

  defp same?(book, left, right), do: unfold(book, left) == unfold(book, right)

  defp unfold(book, ty), do: unfold(book, ty, MapSet.new())

  defp unfold(book, {:var, name}, seen) do
    if MapSet.member?(seen, name) do
      {:var, name}
    else
      case alias_of(book, name) do
        nil -> {:var, name}
        body -> unfold(book, body, MapSet.put(seen, name))
      end
    end
  end

  defp unfold(book, {:prod, left, right}, seen) do
    {:prod, unfold(book, left, seen), unfold(book, right, seen)}
  end

  defp unfold(book, {:app, fun, arg}, seen) do
    {:app, unfold(book, fun, seen), unfold(book, arg, seen)}
  end

  defp unfold(book, {:pi, qty, dom, name, cod}, seen) do
    {:pi, qty, unfold(book, dom, seen), name, unfold(book, cod, seen)}
  end

  defp unfold(_book, ty, _seen), do: ty

  defp alias_of(book, name) do
    Enum.find_value(book, fn
      %{name: ^name, mode: :spec, type: :typ, body: body} = d ->
        if Map.get(d, :kind) == :data, do: nil, else: body

      _ ->
        nil
    end)
  end

  defp features(book) do
    cond do
      named?(book, "eval-feature") and not named?(book, "Feature") ->
        {:error, :usage, "the book defines eval-feature and does not define Feature"}

      not named?(book, "Feature") ->
        {:ok, []}

      not named?(book, "eval-feature") ->
        {:error, :usage, "the book defines Feature and does not define eval-feature"}

      true ->
        nullary(book, "Feature")
    end
  end

  defp nullary(book, data) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == data)) do
      nil ->
        {:error, :usage, "the book does not define #{data}"}

      %{ctors: ctors} ->
        bad = Enum.reject(ctors, &nullary_ctor?/1)

        if bad == [] do
          {:ok, Enum.map(ctors, & &1.name)}
        else
          {:error, :usage, "#{data} constructors take arguments"}
        end
    end
  end

  defp nullary_ctor?(%{type: {:pi, _, _, _, _}}), do: false
  defp nullary_ctor?(%{type: _type}), do: true

  defp named?(book, name), do: Enum.any?(book, &(Map.get(&1, :name) == name))

  defp call(host, name, args) do
    fun = String.to_atom(Muro.Emit.elixir_base(name))
    apply(host.module, fun, args)
  end

  defp exported?(host, name, arity) do
    function_exported?(host.module, String.to_atom(Muro.Emit.elixir_base(name)), arity)
  end

  defp atom(name), do: String.to_atom(Muro.Emit.elixir_atom_name(name))
  defp atom!(host, name), do: Map.fetch!(host.atoms, name)

  defp source!(host, atom) do
    case Map.fetch(host.sources, atom) do
      {:ok, name} -> name
      :error -> raise ArgumentError, "not a constructor of this book: #{inspect(atom)}"
    end
  end

  defp decode_list(tail) when tail in [nil, nil], do: []
  defp decode_list({:cons, head, tail}), do: [head | decode_list(tail)]

  defp nat_int(0), do: 0
  defp nat_int({:suc, n}), do: 1 + nat_int(n)
  defp nat_int(n) when is_integer(n) and n >= 0, do: n

  defp truth!(true), do: true
  defp truth!(false), do: false
end
