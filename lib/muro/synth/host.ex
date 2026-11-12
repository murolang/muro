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

    case Muro.Load.file(path, fuel: fuel) do
      {:error, msg} -> {:error, :book, msg}
      {:ok, book} -> compile(path, book)
    end
  end

  defp compile(path, book) do
    with :ok <- present(book, "State"),
         :ok <- present(book, "Action"),
         :ok <- present(book, "step"),
         :ok <- present(book, "all-actions"),
         :ok <- present(book, "horizon"),
         :ok <- present(book, "leb"),
         :ok <- signatures(book),
         {:ok, states} <- nullary(book, "State"),
         {:ok, actions} <- nullary(book, "Action"),
         {:ok, features} <- features(book) do
      module = Module.concat(Muro.Synth.Host, "M#{System.unique_integer([:positive])}")
      emitted = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()
      Code.eval_string(Muro.Emit.emit_module(module, emitted))
      names = states ++ actions ++ features
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
        sources: sources
      }

      link(host)
    end
  end

  defp link(host) do
    case call(host, "all-actions", []) do
      nil ->
        {:error, :usage, "the book does not define all-actions"}

      listed ->
        actions = listed |> decode_list() |> Enum.map(&source!(host, &1))
        horizon = host |> call("horizon", []) |> nat_int()

        all_states =
          if exported?(host, "all-states", 0) do
            host |> call("all-states", []) |> decode_list() |> Enum.map(&source!(host, &1))
          else
            nil
          end

        default =
          if exported?(host, "default-action", 0) do
            source!(host, call(host, "default-action", []))
          else
            List.last(actions)
          end

        {:ok,
         %{
           host
           | actions: actions,
             states: host.states
         }
         |> Map.put(:horizon, horizon)
         |> Map.put(:all_states, all_states)
         |> Map.put(:default, default)
         |> Map.put(:step, fn state, action ->
           {next, reward} = call(host, "step", [atom!(host, state), atom!(host, action)])
           {source!(host, next), reward}
         end)
         |> Map.put(:leb, fn left, right ->
           truth!(call(host, "leb", [left, right]))
         end)
         |> Map.put(:eval_feature, fn feature, state ->
           truth!(call(host, "eval-feature", [atom!(host, feature), atom!(host, state)]))
         end)}
    end
  end

  defp present(book, name) do
    if named?(book, name), do: :ok, else: {:error, :usage, "the book does not define #{name}"}
  end

  # Names are not enough. `all-actions : run Nat := 0` checks and then
  # crashes in `decode_list`. The modes and the types are the contract
  # the search calls, and a mismatch is a usage error before any call.
  defp signatures(book) do
    with {:ok, step} <- run_type(book, "step"),
         {:ok, reward} <- step_reward(book, step),
         {:ok, actions} <- run_type(book, "all-actions"),
         :ok <- list_of(book, actions, "Action", "all-actions must be run List Action"),
         {:ok, horizon} <- run_type(book, "horizon"),
         :ok <- nat_type(book, horizon, "horizon must be run Nat"),
         {:ok, leb} <- run_type(book, "leb"),
         :ok <- leb_type(book, leb, reward),
         :ok <- optional_list(book, "all-states", "State"),
         :ok <- optional_name(book, "default-action", "Action"),
         :ok <- eval_feature_type(book) do
      :ok
    end
  end

  defp run_type(book, name) do
    case Enum.find(book, &(Map.get(&1, :name) == name)) do
      %{mode: :run, type: ty} -> {:ok, ty}
      %{mode: mode} -> {:error, :usage, "#{name} is #{mode}; the environment requires run"}
      _ -> {:error, :usage, "the book does not define #{name}"}
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
    case Enum.find(book, &(Map.get(&1, :name) == name)) do
      nil ->
        :ok

      %{mode: :run, type: ty} ->
        list_of(book, ty, elem, "#{name} must be run List #{elem}")

      %{mode: mode} ->
        {:error, :usage, "#{name} is #{mode}; the environment requires run"}
    end
  end

  defp optional_name(book, name, type_name) do
    case Enum.find(book, &(Map.get(&1, :name) == name)) do
      nil ->
        :ok

      %{mode: :run, type: ty} ->
        if same?(book, ty, {:var, type_name}),
          do: :ok,
          else: {:error, :usage, "#{name} must be run #{type_name}"}

      %{mode: mode} ->
        {:error, :usage, "#{name} is #{mode}; the environment requires run"}
    end
  end

  defp eval_feature_type(book) do
    cond do
      not named?(book, "Feature") or not named?(book, "eval-feature") ->
        :ok

      true ->
        case run_type(book, "eval-feature") do
          {:ok, ty} ->
            if eval_feature?(book, ty),
              do: :ok,
              else:
                {:error, :usage,
                 "eval-feature must be run Π (f : Feature) → Π (c : Carrier) → Bool"}

          {:error, _, _} = err ->
            err
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

  defp carrier?(book, ty) do
    same?(book, ty, {:var, "State"}) or
      (named?(book, "Carrier") and same?(book, ty, {:var, "Carrier"}))
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
