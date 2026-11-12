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
