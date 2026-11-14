defmodule Muro.Temporal.Elab do
  @moduledoc """
  A checked source process, seen as the fragment the temporal layer decides.

  | Elixir | Agda |
  | --- | --- |
  | `elab/2` | `Muro.Temporal.Bridge.elab` |
  | `fragment?/2` | `Muro.Temporal.Bridge.frag?` |

  A payload is a nat literal, a bit, a nullary constructor, or the echo of a
  binder in scope. A pair, a record, a vector, a fielded constructor, and a
  computed `put` are `payload outside the temporal fragment`. A `rec` whose
  name is also bound by another `rec` in the same process is
  `mu of a repeated binder`.
  """

  @fragment "payload outside the temporal fragment"

  @doc """
  Transcribes `Bridge.elab`. `{:ok, proc}` or `{:error, message}`.
  """
  def elab(proc, book) when is_list(book) do
    if unique_mus?(proc) do
      elab(proc, book, MapSet.new(), binders(proc))
    else
      {:error, "mu of a repeated binder"}
    end
  end

  @doc """
  Transcribes `Bridge.frag?`.
  """
  def fragment?(proc, book) when is_list(book) do
    match?({:ok, _}, elab(proc, book))
  end

  defp elab(:done, _book, _scope, _names), do: {:ok, :done}
  defp elab(:stop, _book, _scope, _names), do: {:ok, :stop}
  defp elab({:call, name}, _book, _scope, _names), do: {:ok, {:var, name}}

  defp elab({:rec, name, body}, book, scope, names) do
    with {:ok, body} <- elab(body, book, scope, names), do: {:ok, {:mu, name, body}}
  end

  defp elab({:put, _ty, val, body}, book, scope, names) do
    with {:ok, body} <- elab(body, book, scope, names) do
      case classify(val, book, scope, names) do
        {:atom, atom, show} -> {:ok, {:put, atom, show, body}}
        {:echo, name} -> {:ok, {:echo, name, "put #{name}", body}}
        {:error, _} = err -> err
      end
    end
  end

  defp elab({:get, ty, name, {:match, scrut, arms}}, book, scope, names) do
    if scrut == name do
      elab_get_match(ty, name, arms, book, scope, names)
    else
      {:error, @fragment}
    end
  end

  defp elab({:get, ty, name, body}, book, scope, names) do
    with :ok <- atomic_type(book, ty),
         {:ok, body} <- elab(body, book, bind(scope, name), names) do
      {:ok, {:get, tag_of(ty), name, ty, get_show(name, ty), body}}
    end
  end

  defp elab({:iget, name, p, q}, book, scope, names) do
    scope = bind(scope, name)

    with {:ok, p} <- elab(p, book, scope, names),
         {:ok, q} <- elab(q, book, scope, names) do
      {:ok, {:iget, name, :bit, get_show(name, :bit), p, q}}
    end
  end

  defp elab({:pick0, body}, book, scope, names) do
    with {:ok, body} <- elab(body, book, scope, names), do: {:ok, {:pick0, "pick0", body}}
  end

  defp elab({:pick1, body}, book, scope, names) do
    with {:ok, body} <- elab(body, book, scope, names), do: {:ok, {:pick1, "pick1", body}}
  end

  defp elab({:cover, p, q}, book, scope, names) do
    with {:ok, p} <- elab(p, book, scope, names),
         {:ok, q} <- elab(q, book, scope, names) do
      {:ok, {:cover, "cover", p, q}}
    end
  end

  # The reason is not a temporal slot. The arm does not see the payload
  # the receive would have bound.
  defp elab({:on_fail, recv, _reason, arm}, book, scope, names) do
    with {:ok, recv} <- elab(recv, book, scope, names),
         {:ok, arm} <- elab(arm, book, scope, names) do
      {:ok, {:on_fail, recv, arm}}
    end
  end

  defp elab(_other, _book, _scope, _names), do: {:error, @fragment}

  defp elab_get_match(ty, name, arms, book, scope, names) do
    with :ok <- atomic_type(book, ty) do
      scope = bind(scope, name)
      show = get_show(name, ty)

      case ty do
        :bit ->
          with {:ok, p, q} <- bit_arms(arms),
               {:ok, p} <- elab(p, book, scope, names),
               {:ok, q} <- elab(q, book, scope, names) do
            {:ok, {:iget, name, :bit, show, p, q}}
          end

        {:dat, dname, _} ->
          with {:ok, pairs} <- data_arms(book, dname, arms),
               {:ok, pairs} <- elab_pairs(pairs, book, scope, names) do
            {:ok, {:mget, {:dat, dname}, name, ty, show, pairs}}
          end

        _ ->
          {:error, @fragment}
      end
    end
  end

  defp elab_pairs(pairs, book, scope, names) do
    Enum.reduce_while(pairs, {:ok, []}, fn {ctor, proc}, {:ok, acc} ->
      case elab(proc, book, scope, names) do
        {:ok, proc} -> {:cont, {:ok, acc ++ [{ctor, proc}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp bit_arms([p, q] = arms) do
    cond do
      named_arms?(arms) -> bit_named(arms)
      field_arm?(p) or field_arm?(q) -> {:error, @fragment}
      true -> {:ok, p, q}
    end
  end

  defp bit_arms(arms) do
    if named_arms?(arms), do: bit_named(arms), else: {:error, @fragment}
  end

  defp bit_named(arms) do
    if Enum.any?(arms, &field_arm?/1) do
      {:error, @fragment}
    else
      p = Enum.find_value(arms, fn {:arm, n, [], body} -> if n in ["b0", :b0], do: body end)
      q = Enum.find_value(arms, fn {:arm, n, [], body} -> if n in ["b1", :b1], do: body end)
      if p && q, do: {:ok, p, q}, else: {:error, @fragment}
    end
  end

  defp field_arm?({:arm, _, [_ | _], _}), do: true
  defp field_arm?({:prod, _, _}), do: true
  defp field_arm?(_), do: false

  defp data_arms(book, dname, arms) do
    cond do
      arms == [] ->
        {:error, @fragment}

      named_arms?(arms) ->
        if Enum.any?(arms, &field_arm?/1) do
          {:error, @fragment}
        else
          {:ok,
           Enum.map(arms, fn
             {:arm, cname, [], body} -> {to_string(cname), body}
           end)}
        end

      true ->
        ctors = ctor_names(book, dname)

        if length(ctors) == length(arms) do
          {:ok, Enum.zip(ctors, arms)}
        else
          {:error, "match branch count does not match constructors"}
        end
    end
  end

  defp named_arms?(arms) do
    Enum.all?(arms, fn
      {:arm, _, _, _} -> true
      {:prod, _, _} -> true
      _ -> false
    end)
  end

  defp classify({:nat, n}, _book, _scope, _names) when is_integer(n),
    do: {:atom, {:nat, n}, "put #{n}"}

  defp classify(:b0, _book, _scope, _names), do: {:atom, {:bit, false}, "put b0"}
  defp classify(:b1, _book, _scope, _names), do: {:atom, {:bit, true}, "put b1"}

  defp classify({:var, name}, book, scope, names) do
    cond do
      MapSet.member?(scope, name) and Enum.count(names, &(&1 == name)) != 1 ->
        {:error, "echo of a repeated binder"}

      MapSet.member?(scope, name) ->
        {:echo, name}

      nullary_ctor?(book, name) ->
        {:atom, {:con, to_string(name)}, "put #{name}"}

      true ->
        {:error, @fragment}
    end
  end

  defp classify({:con, _name, [_ | _]}, _book, _scope, _names), do: {:error, @fragment}

  defp classify({:con, name, []}, book, _scope, _names) do
    if nullary_ctor?(book, name) do
      {:atom, {:con, to_string(name)}, "put #{name}"}
    else
      {:error, @fragment}
    end
  end

  defp classify(_other, _book, _scope, _names), do: {:error, @fragment}

  defp binders(proc), do: Enum.reverse(binders(proc, []))

  defp unique_mus?(proc) do
    names = mu_names(proc, [])
    names == Enum.uniq(names)
  end

  defp mu_names({:rec, name, body}, acc), do: mu_names(body, [name | acc])
  defp mu_names({:put, _, _, body}, acc), do: mu_names(body, acc)
  defp mu_names({:get, _, _, {:match, _, arms}}, acc), do: mu_names_arms(arms, acc)
  defp mu_names({:get, _, _, body}, acc), do: mu_names(body, acc)
  defp mu_names({:iget, _, p, q}, acc), do: mu_names(q, mu_names(p, acc))
  defp mu_names({:pick0, body}, acc), do: mu_names(body, acc)
  defp mu_names({:pick1, body}, acc), do: mu_names(body, acc)
  defp mu_names({:cover, p, q}, acc), do: mu_names(q, mu_names(p, acc))
  defp mu_names({:on_fail, recv, _, arm}, acc), do: mu_names(arm, mu_names(recv, acc))
  defp mu_names(:done, acc), do: acc
  defp mu_names(:stop, acc), do: acc
  defp mu_names({:call, _}, acc), do: acc
  defp mu_names(_, acc), do: acc

  defp mu_names_arms(arms, acc) do
    Enum.reduce(arms, acc, fn
      {:arm, _, _, body}, acc -> mu_names(body, acc)
      body, acc -> mu_names(body, acc)
    end)
  end

  defp binders(:done, acc), do: acc
  defp binders(:stop, acc), do: acc
  defp binders({:call, _}, acc), do: acc
  defp binders({:rec, _, body}, acc), do: binders(body, acc)
  defp binders({:put, _, _, body}, acc), do: binders(body, acc)

  defp binders({:get, _, name, {:match, _, arms}}, acc),
    do: binders_arms(arms, cons_name(name, acc))

  defp binders({:get, _, name, body}, acc), do: binders(body, cons_name(name, acc))

  defp binders({:iget, name, p, q}, acc) do
    acc = binders(p, cons_name(name, acc))
    binders(q, acc)
  end

  defp binders({:pick0, body}, acc), do: binders(body, acc)
  defp binders({:pick1, body}, acc), do: binders(body, acc)
  defp binders({:cover, p, q}, acc), do: binders(q, binders(p, acc))
  defp binders({:on_fail, recv, _, arm}, acc), do: binders(arm, binders(recv, acc))
  defp binders(_, acc), do: acc

  defp binders_arms(arms, acc) do
    Enum.reduce(arms, acc, fn
      {:arm, _, _, body}, acc -> binders(body, acc)
      {:prod, _, _}, acc -> acc
      body, acc -> binders(body, acc)
    end)
  end

  defp cons_name(:_, acc), do: acc
  defp cons_name(name, acc), do: [name | acc]

  defp atomic_type(_book, :nat), do: :ok
  defp atomic_type(_book, :bit), do: :ok

  defp atomic_type(book, {:dat, name, _args}) do
    if nullary_data?(book, name), do: :ok, else: {:error, @fragment}
  end

  defp atomic_type(_book, _ty), do: {:error, @fragment}

  defp tag_of(:nat), do: :nat
  defp tag_of(:bit), do: :bit
  defp tag_of({:dat, name, _}), do: {:dat, name}

  defp get_show(:_, ty), do: "get #{ty_show(ty)}"
  defp get_show(name, ty), do: "get (#{name} : #{ty_show(ty)})"

  defp ty_show(:nat), do: "Nat"
  defp ty_show(:bit), do: "Bit"
  defp ty_show(:unit), do: "Unit"
  defp ty_show({:dat, name, []}), do: name

  defp ty_show({:dat, name, args}) do
    rest = Enum.map_join(args, " ", &ty_show/1)
    "#{name} #{rest}"
  end

  defp ty_show(_), do: "?"

  defp bind(scope, :_), do: scope
  defp bind(scope, name), do: MapSet.put(scope, name)

  defp nullary_ctor?(book, name) do
    name = to_string(name)

    Enum.any?(book, fn
      %{kind: :data, params: params, ctors: ctors} ->
        Enum.any?(ctors, fn c ->
          c.name == name and nullary_after?(c.type, length(params))
        end)

      _ ->
        false
    end)
  end

  defp nullary_data?(book, name) do
    case Enum.find(book, &(&1[:kind] == :data and &1.name == name)) do
      nil ->
        false

      %{params: params, ctors: ctors} ->
        ctors != [] and
          Enum.all?(ctors, fn c -> nullary_after?(c.type, length(params)) end)
    end
  end

  def ctor_names(book, dname) do
    case Enum.find(book, &(&1[:kind] == :data and &1.name == dname)) do
      nil -> []
      %{ctors: ctors} -> Enum.map(ctors, & &1.name)
    end
  end

  defp nullary_after?({:pi, _, _, _, body}, n) when n > 0, do: nullary_after?(body, n - 1)
  defp nullary_after?({:pi, _, _, _, _}, 0), do: false
  defp nullary_after?(_type, 0), do: true
  defp nullary_after?(_type, _n), do: false
end
