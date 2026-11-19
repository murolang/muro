defmodule Muro.Fill.Enum do
  @moduledoc false

  # Type-directed enumeration of named terms. A Π goal is always a λ.
  # A function in scope is applied when the goal is its result: saturated,
  # and only a visible binder that is not erased. The definition being
  # filled is not in `env.defs`, so a candidate does not call it.
  # Size counts a variable, a constructor, an application, a lambda, or a
  # match. A match motive is the goal and is not counted. The scrutinee is
  # a binder, so it contributes one.

  @cache {__MODULE__, :cache}
  @computing {__MODULE__, :computing}

  def clear do
    Process.delete(@cache)
    Process.delete(@computing)
    :ok
  end

  def terms(env, goal, size) when is_integer(size) and size >= 1 do
    key = {goal, sig(env), size}

    case Map.fetch(Process.get(@cache, %{}), key) do
      {:ok, found} ->
        found

      :error ->
        computing = Process.get(@computing, MapSet.new())

        if MapSet.member?(computing, key) do
          []
        else
          Process.put(@computing, MapSet.put(computing, key))
          found = compute(env, goal, size)
          Process.put(@computing, computing)
          Process.put(@cache, Map.put(Process.get(@cache, %{}), key, found))
          found
        end
    end
  end

  def terms(_env, _goal, _size), do: []

  def refers?(term, name) when is_binary(name), do: refers?(term, name, MapSet.new())

  defp compute(env, {:pi, q, a, x, b}, size) when size >= 2 do
    env2 = %{env | binders: env.binders ++ [%{name: x, qty: q, type: a}]}

    for body <- terms(env2, b, size - 1) do
      {:lam, q, a, x, body}
    end
  end

  defp compute(_env, {:pi, _, _, _, _}, _size), do: []
  defp compute(_env, :typ, size) when size != 1, do: []
  defp compute(env, goal, 1), do: atoms(env, goal)

  defp compute(env, goal, size) when size > 1 do
    ctor_apps(env, goal, size) ++ fun_apps(env, goal, size) ++ matches(env, goal, size)
  end

  defp compute(_env, _goal, _size), do: []

  defp atoms(env, goal) do
    builtins(goal) ++
      ctor_atoms(env, goal) ++
      type_names(env, goal) ++
      def_atoms(env, goal) ++
      binder_atoms(env, goal)
  end

  defp builtins(:nat), do: [:ze]
  defp builtins(:unit), do: [:one]
  defp builtins({:idt, _, _, _}), do: [:rfl]
  defp builtins(:typ), do: [:nat, :unit, :empty]
  defp builtins(_goal), do: []

  defp type_names(env, :typ) do
    for %{params: [], indices: []} = data <- env.datas, do: {:var, data.name}
  end

  defp type_names(_env, _goal), do: []

  defp ctor_atoms(env, goal) do
    case data_of(env, goal) do
      {:ok, data, args} ->
        for ctor <- data.ctors,
            {:ok, [], result} <- [fields_of(ctor, data, args)],
            result_ok?(result, goal, env),
            do: {:var, ctor.name}

      :error ->
        []
    end
  end

  defp def_atoms(env, goal) do
    for d <- env.defs, alpha?(d.type, goal, env), do: {:var, d.name}
  end

  defp binder_atoms(env, goal) do
    for b <- visible(env.binders), b.qty != :erased, alpha?(b.type, goal, env) do
      {:var, b.name}
    end
  end

  defp ctor_apps(env, goal, size) do
    suc_apps(env, goal, size) ++ data_apps(env, goal, size)
  end

  defp suc_apps(env, :nat, size) when size >= 2 do
    Enum.map(terms(env, :nat, size - 1), &{:su, &1})
  end

  defp suc_apps(_env, _goal, _size), do: []

  defp data_apps(env, goal, size) do
    case data_of(env, goal) do
      {:ok, data, args} ->
        Enum.flat_map(data.ctors, fn ctor ->
          case fields_of(ctor, data, args) do
            {:ok, [_ | _] = fields, result} ->
              if result_ok?(result, goal, env),
                do: applications({:var, ctor.name}, fields, env, size),
                else: []

            _ ->
              []
          end
        end)

      :error ->
        []
    end
  end

  defp fun_apps(env, goal, size) do
    def_apps(env, goal, size) ++ binder_apps(env, goal, size)
  end

  defp def_apps(env, goal, size) do
    Enum.flat_map(env.defs, fn d ->
      saturated({:var, d.name}, d.type, env, env, goal, size)
    end)
  end

  # Definitions first, then binders from the outside in. An affine or
  # linear head is consumed, so an argument is not that same variable.
  defp binder_apps(env, goal, size) do
    Enum.flat_map(visible(env.binders), fn binder ->
      if binder.qty == :erased do
        []
      else
        env2 = consume(env, binder.name, binder.qty)
        saturated({:var, binder.name}, binder.type, env, env2, goal, size)
      end
    end)
  end

  defp saturated(head, type, goal_env, arg_env, goal, size) do
    case telescope(type) do
      {[_ | _] = fields, result} ->
        if concrete?(fields) and result_ok?(result, goal, goal_env) do
          applications(head, fields, arg_env, size)
        else
          []
        end

      _ ->
        []
    end
  end

  defp applications(head, fields, env, size) do
    budget = size - 1
    n = length(fields)

    if budget < n do
      []
    else
      for split <- compositions(n, budget),
          args <- arg_tuples(fields, split, env) do
        Enum.reduce(args, head, fn arg, fun -> {:app, fun, arg} end)
      end
    end
  end

  defp arg_tuples([], [], _env), do: [[]]

  defp arg_tuples([{_q, x, ty} | rest], [s | ss], env) do
    for arg <- terms(env, ty, s),
        rest2 = Enum.map(rest, fn {q2, y, ty2} -> {q2, y, subst(ty2, x, arg)} end),
        tail <- arg_tuples(rest2, ss, env) do
      [arg | tail]
    end
  end

  defp arg_tuples(_fields, _split, _env), do: []

  defp matches(env, goal, size) when size >= 4 do
    Enum.flat_map(visible(env.binders), fn binder ->
      match_scrut(env, goal, size, binder)
    end)
  end

  defp matches(_env, _goal, _size), do: []

  defp match_scrut(env, goal, size, %{name: name, qty: qty, type: :nat})
       when qty != :erased and name != "_" do
    if refers?(goal, name) do
      []
    else
      nat_match(env, goal, size, name, qty)
    end
  end

  defp match_scrut(env, goal, size, %{name: name, qty: qty} = binder)
       when qty != :erased and name != "_" do
    data_match(env, goal, size, binder)
  end

  defp match_scrut(_env, _goal, _size, _binder), do: []

  defp nat_match(env, goal, size, name, qty) do
    budget = size - 2

    if budget < 2 do
      []
    else
      zero_env = consume(env, name, qty)
      suc_name = fresh(zero_env, "k")

      suc_env = %{
        zero_env
        | binders: zero_env.binders ++ [%{name: suc_name, qty: :affine, type: :nat}]
      }

      for [zero_size, suc_size] <- compositions(2, budget),
          zero <- terms(zero_env, goal, zero_size),
          suc <- terms(suc_env, goal, suc_size) do
        {:mnat, {:var, name}, "_", goal, zero, suc_name, suc}
      end
    end
  end

  defp data_match(env, goal, size, %{name: name, qty: qty, type: ty}) do
    with {:data, dname, args} <- type_head(ty),
         {:ok, %{indices: [], ctors: [_ | _] = ctors} = data} <- fetch_data(env, dname),
         true <- length(args) == length(data.params),
         false <- refers?(goal, name),
         opened = Enum.map(ctors, &fields_of(&1, data, args)),
         true <- Enum.all?(opened, &match?({:ok, _, _}, &1)) do
      budget = size - 2

      if budget < length(ctors) do
        []
      else
        base = consume(env, name, qty)
        specs = Enum.zip(ctors, opened)

        for split <- compositions(length(ctors), budget),
            branches <- branch_bodies(specs, split, base, goal) do
          {:mdata, {:var, name}, "_", goal, branches}
        end
      end
    else
      _ -> []
    end
  end

  defp branch_bodies([], [], _env, _goal), do: [[]]

  defp branch_bodies([{ctor, {:ok, fields, _result}} | rest], [size | sizes], env, goal) do
    {env2, binders} = push_fields(env, fields)

    for body <- terms(env2, goal, size),
        tail <- branch_bodies(rest, sizes, env, goal) do
      [{ctor.name, binders, body} | tail]
    end
  end

  defp branch_bodies(_specs, _sizes, _env, _goal), do: []

  defp push_fields(env, fields) do
    Enum.reduce(fields, {env, []}, fn {qty, name, ty}, {env, names} ->
      name = if name == "_", do: fresh(env, "a"), else: name
      env = %{env | binders: env.binders ++ [%{name: name, qty: qty, type: ty}]}
      {env, names ++ [name]}
    end)
  end

  defp compositions(1, budget) when budget >= 1, do: [[budget]]

  defp compositions(n, budget) when n > 1 and budget >= n do
    for i <- 1..(budget - (n - 1)),
        rest <- compositions(n - 1, budget - i) do
      [i | rest]
    end
  end

  defp compositions(_n, _budget), do: []

  defp data_of(env, goal) do
    case type_head(goal) do
      {:data, name, args} ->
        case fetch_data(env, name) do
          {:ok, %{indices: []} = data} when length(args) == length(data.params) ->
            {:ok, data, args}

          _ ->
            :error
        end

      _ ->
        :error
    end
  end

  defp fetch_data(env, name) do
    case Enum.find(env.datas, &(&1.name == name)) do
      nil -> :error
      data -> {:ok, data}
    end
  end

  defp fields_of(ctor, data, args) do
    ty =
      Enum.reduce(Enum.zip(data.params, args), ctor.type, fn {{_qty, name, _ty}, arg}, ty ->
        subst(ty, name, arg)
      end)

    {fields, result} = telescope(ty)

    if concrete?(fields), do: {:ok, fields, result}, else: :skip
  end

  defp telescope(ty, acc \\ []) do
    case ty do
      {:pi, qty, dom, name, cod} -> telescope(cod, [{qty, name, dom} | acc])
      other -> {Enum.reverse(acc), other}
    end
  end

  defp concrete?(fields), do: Enum.all?(fields, fn {qty, _, _} -> qty != :erased end)

  defp result_ok?(result, goal, env) do
    alpha?(result, goal, env) or flexible?(result) or same_head?(result, goal)
  end

  defp flexible?({:var, _}), do: true
  defp flexible?({:def, _}), do: true

  defp flexible?(term) do
    {head, _args} = spine(term, [])
    match?({:var, _}, head) or match?({:def, _}, head)
  end

  defp same_head?(left, right) do
    case {type_head(left), type_head(right)} do
      {{:builtin, name}, {:builtin, name}} -> true
      {{:data, name, _}, {:data, name, _}} -> true
      {:idt, :idt} -> true
      _ -> false
    end
  end

  defp type_head(:nat), do: {:builtin, :nat}
  defp type_head(:unit), do: {:builtin, :unit}
  defp type_head(:empty), do: {:builtin, :empty}
  defp type_head(:typ), do: {:builtin, :typ}
  defp type_head({:idt, _, _, _}), do: :idt
  defp type_head({:pi, _, _, _, _}), do: :pi

  defp type_head(term) do
    {head, args} = spine(term, [])

    case head do
      {:var, name} -> {:data, name, args}
      {:def, name} -> {:data, name, args}
      _ -> :other
    end
  end

  defp spine({:app, fun, arg}, acc), do: spine(fun, [arg | acc])
  defp spine(head, acc), do: {head, acc}

  # Outermost first. A repeated name keeps the inner binding only.
  defp visible(binders) do
    {kept, _seen} =
      Enum.reduce(Enum.reverse(binders), {[], MapSet.new()}, fn binder, {acc, seen} ->
        if binder.name == "_" or MapSet.member?(seen, binder.name) do
          {acc, MapSet.put(seen, binder.name)}
        else
          {[binder | acc], MapSet.put(seen, binder.name)}
        end
      end)

    kept
  end

  defp consume(env, name, qty) when qty in [:affine, :linear] do
    index =
      env.binders
      |> Enum.with_index()
      |> Enum.reverse()
      |> Enum.find_value(fn {binder, index} -> if binder.name == name, do: index end)

    %{env | binders: List.delete_at(env.binders, index)}
  end

  defp consume(env, _name, _qty), do: env

  defp fresh(env, base) do
    taken = MapSet.new(Enum.map(env.binders, & &1.name))
    fresh_from(taken, base, 0)
  end

  defp fresh_from(taken, base, 0) do
    if MapSet.member?(taken, base), do: fresh_from(taken, base, 1), else: base
  end

  defp fresh_from(taken, base, n) do
    name = base <> Integer.to_string(n)
    if MapSet.member?(taken, name), do: fresh_from(taken, base, n + 1), else: name
  end

  defp alpha?(left, right, env) do
    names = env.binders |> Enum.reverse() |> Enum.map(& &1.name)

    case {Muro.Ast.to_db(left, names), Muro.Ast.to_db(right, names)} do
      {{:ok, left_db}, {:ok, right_db}} -> erase(left_db) == erase(right_db)
      _ -> false
    end
  end

  def erase({:lam, qty, dom, _name, body}), do: {:lam, qty, erase(dom), erase(body)}
  def erase({:pi, qty, dom, _name, cod}), do: {:pi, qty, erase(dom), erase(cod)}
  def erase({:app, fun, arg}), do: {:app, erase(fun), erase(arg)}
  def erase({:su, term}), do: {:su, erase(term)}
  def erase({:idt, ty, left, right}), do: {:idt, erase(ty), erase(left), erase(right)}

  def erase({:mnat, scrut, motive, zero, suc}),
    do: {:mnat, erase(scrut), erase(motive), erase(zero), erase(suc)}

  def erase({:mdata, scrut, motive, branches}) do
    {:mdata, erase(scrut), erase(motive),
     Enum.map(branches, fn {name, n, body} -> {name, n, erase(body)} end)}
  end

  def erase({:munit, scrut, motive, arm}), do: {:munit, erase(scrut), erase(motive), erase(arm)}
  def erase({:memp, scrut, motive}), do: {:memp, erase(scrut), erase(motive)}
  def erase({:var, index}) when is_integer(index), do: {:var, index}
  def erase({:def, name}), do: {:def, name}
  def erase(other), do: other

  def subst({:var, name}, name, replacement), do: replacement
  def subst({:var, other}, _name, _replacement), do: {:var, other}

  def subst({:lam, qty, dom, name, body}, name, replacement) do
    {:lam, qty, subst(dom, name, replacement), name, body}
  end

  def subst({:lam, qty, dom, binder, body}, name, replacement) do
    {:lam, qty, subst(dom, name, replacement), binder, subst(body, name, replacement)}
  end

  def subst({:pi, qty, dom, name, cod}, name, replacement) do
    {:pi, qty, subst(dom, name, replacement), name, cod}
  end

  def subst({:pi, qty, dom, binder, cod}, name, replacement) do
    {:pi, qty, subst(dom, name, replacement), binder, subst(cod, name, replacement)}
  end

  def subst({:app, fun, arg}, name, replacement) do
    {:app, subst(fun, name, replacement), subst(arg, name, replacement)}
  end

  def subst({:su, term}, name, replacement), do: {:su, subst(term, name, replacement)}

  def subst({:mnat, scrut, motive, motive_body, zero, suc_name, suc}, name, replacement) do
    {:mnat, subst(scrut, name, replacement), motive,
     subst_shadow(motive_body, motive, name, replacement), subst(zero, name, replacement),
     suc_name, subst_shadow(suc, suc_name, name, replacement)}
  end

  def subst({:mdata, scrut, motive, motive_body, branches}, name, replacement) do
    {:mdata, subst(scrut, name, replacement), motive,
     subst_shadow(motive_body, motive, name, replacement),
     Enum.map(branches, fn {ctor, binders, body} ->
       {ctor, binders, subst_many(body, binders, name, replacement)}
     end)}
  end

  def subst({:idt, ty, left, right}, name, replacement) do
    {:idt, subst(ty, name, replacement), subst(left, name, replacement),
     subst(right, name, replacement)}
  end

  def subst(term, _name, _replacement), do: term

  defp subst_shadow(term, binder, binder, _replacement), do: term
  defp subst_shadow(term, _binder, name, replacement), do: subst(term, name, replacement)

  defp subst_many(term, binders, name, replacement) do
    if Enum.member?(binders, name), do: term, else: subst(term, name, replacement)
  end

  defp refers?({:var, name}, name, bound), do: not MapSet.member?(bound, name)
  defp refers?({:var, _other}, _name, _bound), do: false
  defp refers?({:def, name}, name, bound), do: not MapSet.member?(bound, name)
  defp refers?({:def, _other}, _name, _bound), do: false

  defp refers?({:lam, _qty, dom, binder, body}, name, bound) do
    refers?(dom, name, bound) or refers?(body, name, MapSet.put(bound, binder))
  end

  defp refers?({:pi, _qty, dom, binder, cod}, name, bound) do
    refers?(dom, name, bound) or refers?(cod, name, MapSet.put(bound, binder))
  end

  defp refers?({:app, fun, arg}, name, bound) do
    refers?(fun, name, bound) or refers?(arg, name, bound)
  end

  defp refers?({:su, term}, name, bound), do: refers?(term, name, bound)

  defp refers?({:mnat, scrut, motive, motive_body, zero, suc_name, suc}, name, bound) do
    refers?(scrut, name, bound) or refers?(motive_body, name, MapSet.put(bound, motive)) or
      refers?(zero, name, bound) or refers?(suc, name, MapSet.put(bound, suc_name))
  end

  defp refers?({:mdata, scrut, motive, motive_body, branches}, name, bound) do
    refers?(scrut, name, bound) or refers?(motive_body, name, MapSet.put(bound, motive)) or
      Enum.any?(branches, fn {_ctor, binders, body} ->
        bound2 = Enum.reduce(binders, bound, &MapSet.put(&2, &1))
        refers?(body, name, bound2)
      end)
  end

  defp refers?({:idt, ty, left, right}, name, bound) do
    refers?(ty, name, bound) or refers?(left, name, bound) or refers?(right, name, bound)
  end

  defp refers?(_other, _name, _bound), do: false

  defp sig(env), do: Enum.map(env.binders, fn b -> {b.name, b.qty, b.type} end)
end
