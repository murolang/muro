defmodule Muro.Check do
  @moduledoc """
  Bidirectional checker. Each clause is tagged with its Agda ⊢ constructor
  from `Muro.Check` (`⇒-var-run`, `⇐-refl`, …). There is no promotion.
  """

  alias Muro.{Ast, Place, Print, Subst}

  # Default fuel. Fuel bounds reduction (whnf, conversion, isData, the
  # index-clash test); everything else is structural recursion on the
  # term, as in Agda's Muro.Check.
  # Running out is reported as an error, never as a silently unreduced term.
  @fuel 2000
  @out_of_fuel "out of fuel (the checker gave up reducing; raise the fuel)"

  @doc "The default fuel of `check_sig/2` and `check_def/3`."
  def default_fuel, do: @fuel

  # -- lookup ----------------------------------------------------------------

  defp lookup_def(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind, :def) != :data and Map.get(&1, :name) == name)) do
      nil ->
        {:error, "unknown definition #{name}"}

      # A session shares the book name space and is not a term.
      %{kind: :session} ->
        {:skip, "#{name} is a session, not a definition"}

      %{kind: :conform} ->
        {:skip, "#{name} is a conformance, not a definition"}

      %{kind: :place} ->
        {:skip, "#{name} is a place, not a definition"}

      %{kind: :scheme} ->
        {:skip, "#{name} is a scheme, not a definition"}

      %{kind: :endpoint} ->
        {:skip, "#{name} is an endpoint, not a definition"}

      %{kind: :read} ->
        {:skip, "#{name} is a reading, not a definition"}

      %{kind: :meet} ->
        {:skip, "#{name} is a meeting, not a definition"}

      %{kind: :talk} ->
        {:skip, "#{name} is a talk, not a definition"}

      %{kind: :seat} ->
        {:skip, "#{name} is a seat, not a definition"}

      %{kind: :link} ->
        {:skip, "#{name} is a link, not a definition"}

      %{kind: :relay} ->
        {:skip, "#{name} is an endpoint function, not a definition"}

      d ->
        {:ok, d}
    end
  end

  defp lookup_data(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
      nil -> {:error, "unknown data type #{name}"}
      d -> {:ok, d}
    end
  end

  defp lookup_ctor(book, name) do
    Enum.find_value(book, fn
      %{kind: :data, name: dname, ctors: cs} = d ->
        case Enum.find_index(cs, &(&1.name == name)) do
          nil -> nil
          i -> {d, dname, i, Enum.at(cs, i)}
        end

      _ ->
        nil
    end)
    |> case do
      nil -> {:error, "unknown constructor #{name}"}
      found -> {:ok, found}
    end
  end

  defp data_name?(book, name), do: match?({:ok, _}, lookup_data(book, name))
  defp ctor_name?(book, name), do: match?({:ok, _}, lookup_ctor(book, name))

  # A session value may be this application when the definition is `run`.
  # Evidence and spec stay out of the payload.
  defp run_def?(book, name) do
    Enum.any?(book, fn d ->
      Map.get(d, :name) == name and Map.get(d, :mode) == :run and term_def?(d)
    end)
  end

  defp term_def?(book, name) do
    Enum.any?(book, fn d ->
      Map.get(d, :name) == name and Map.get(d, :mode) in [:run, :spec, :evidence] and
        term_def?(d)
    end)
  end

  defp term_def?(%{kind: kind})
       when kind in [
              :data,
              :session,
              :conform,
              :place,
              :scheme,
              :move,
              :endpoint,
              :read,
              :meet,
              :talk,
              :seat,
              :link,
              :relay,
              :import,
              :param
            ],
       do: false

  defp term_def?(_), do: true

  # -- context: newest at index 0 -------------------------------------------

  defp ext(gamma, q, a) do
    [{q, Subst.wk(a)} | Enum.map(gamma, fn {q1, a1} -> {q1, Subst.wk(a1)} end)]
  end

  defp bound(gamma, x) do
    case Enum.at(gamma, x) do
      nil -> {:error, "unbound variable"}
      {q, ty} -> {:ok, {q, ty}}
    end
  end

  # The quantity of the predecessor bound by a match on Nat (Agda:
  # Env.predQty): reusable under a reusable variable, affine otherwise.
  defp pred_qty(gamma, {:var, x}) do
    case Enum.at(gamma, x) do
      {:reuse, _} -> :reuse
      _ -> :affine
    end
  end

  defp pred_qty(_gamma, _e), do: :affine

  # -- rec state -------------------------------------------------------------
  # Each member of a recursive block descends on an argument position of
  # its own (`poss`, name to position). The variable bound by the leading
  # λ at the position of the definition being checked is rec_ok; a field
  # of a match on a rec_ok or smaller variable is smaller (structurally
  # below that argument). A call to a member must be the head of a maximal
  # application spine whose argument at the callee's position is a smaller
  # variable, or the rec_ok argument itself when the callee comes earlier
  # in the book (`order`). check_def tries each assignment of non-erased
  # positions (Agda: RecSt, checkBody).

  defp empty_rec,
    do: %{
      self: nil,
      poss: %{},
      order: %{},
      next_arg: nil,
      smaller: [],
      rec_ok: [],
      names: [],
      guard: false,
      block: MapSet.new()
    }

  defp def_rec(name, poss, block, order) do
    %{
      self: name,
      poss: poss,
      order: order,
      next_arg: Map.get(poss, name),
      smaller: [],
      rec_ok: [],
      names: [],
      guard: false,
      block: block
    }
  end

  defp block_of(%{block: %MapSet{} = block}), do: block

  defp block_of(%{self: name}) when is_binary(name), do: MapSet.new([name])
  defp block_of(_), do: MapSet.new()

  defp in_block?(rs, name), do: MapSet.member?(block_of(rs), name)

  defp push_name(rs, x), do: %{rs | names: [x | Map.get(rs, :names, [])]}

  defp names_of(rs, gamma) do
    names = Map.get(rs, :names, [])
    n = length(gamma)

    cond do
      length(names) >= n -> Enum.take(names, n)
      true -> names ++ Enum.map(length(names)..(n - 1)//1, fn i -> "x#{i}" end)
    end
  end

  defp shown(rs, gamma, t), do: Print.term(t, names_of(rs, gamma))

  defp ext_rec(rs, new_small, new_ok) do
    %{
      rs
      | smaller: [new_small | rs.smaller],
        rec_ok: [new_ok | rs.rec_ok],
        next_arg: nil
    }
  end

  # A leading λ of a definition body binds argument pos when next_arg is 0;
  # erased binders count as positions too (Agda: lamRec).
  defp lam_rec(rs) do
    %{ext_rec(rs, false, rs.next_arg == 0) | next_arg: step_arg(rs.next_arg)}
  end

  defp step_arg(k) when is_integer(k) and k > 0, do: k - 1
  defp step_arg(_), do: nil

  defp at(list, i), do: Enum.at(list, i) == true

  defp scrut_ok(rs, {:var, x}), do: at(rs.rec_ok, x) or at(rs.smaller, x)
  defp scrut_ok(_, _), do: false

  defp smaller_var?(rs, {:var, x}), do: at(rs.smaller, x)
  defp smaller_var?(_, _), do: false

  # The argument the definition being checked descends on, unchanged.
  defp arg_var?(rs, {:var, x}), do: at(rs.rec_ok, x) and not at(rs.smaller, x)
  defp arg_var?(_, _), do: false

  defp earlier?(rs, name) do
    case {Map.fetch(rs.order, name), Map.fetch(rs.order, rs.self)} do
      {{:ok, i}, {:ok, s}} -> i < s
      _ -> false
    end
  end

  # -- uses ------------------------------------------------------------------

  defp u0s(n), do: List.duplicate(:u0, n)
  defp one_hot(n, x, u), do: List.replace_at(u0s(n), x, u)

  defp add_use(:u0, u), do: {:ok, u}
  defp add_use(u, :u0), do: {:ok, u}
  defp add_use(:u1, :u1), do: {:error, "affine variable used twice"}
  defp add_use(:uw, _), do: {:ok, :uw}
  defp add_use(_, :uw), do: {:ok, :uw}

  defp add_uses(us, vs) do
    Enum.zip(us, vs)
    |> Enum.reduce_while({:ok, []}, fn {u, v}, {:ok, acc} ->
      case add_use(u, v) do
        {:ok, w} -> {:cont, {:ok, acc ++ [w]}}
        err -> {:halt, err}
      end
    end)
  end

  defp max_use(:uw, _), do: :uw
  defp max_use(_, :uw), do: :uw
  defp max_use(:u1, _), do: :u1
  defp max_use(_, :u1), do: :u1
  defp max_use(_, _), do: :u0

  defp max_uses(us, vs), do: Enum.zip_with(us, vs, &max_use/2)

  defp combine(m, u, v) when m in [:run, :evidence], do: add_uses(u, v)
  defp combine(:spec, u, _), do: {:ok, List.duplicate(:u0, length(u))}

  defp combine_alt(m, u, v) when m in [:run, :evidence], do: max_uses(u, v)
  defp combine_alt(:spec, u, _), do: List.duplicate(:u0, length(u))

  defp check_bound(m, :erased, u) when m in [:run, :evidence] and u in [:u1, :uw],
    do: {:error, "erased variable used computationally"}

  defp check_bound(m, :affine, :uw) when m in [:run, :evidence],
    do: {:error, "affine variable used as reusable"}

  # checkArrow (agda/Muro/Arrow.agda). :linear is Mark m1. Its
  # quantity is affine, so a reusable use fails checkBound first.
  # checkMark then refuses a drop in run and evidence.
  defp check_bound(m, :linear, :uw) when m in [:run, :evidence],
    do: {:error, "affine variable used as reusable"}

  defp check_bound(m, :linear, :u0) when m in [:run, :evidence],
    do: {:error, "linear variable unused"}

  defp check_bound(_, _, _), do: :ok

  # The λ mark and the Π mark are the same mark. :linear is m1;
  # :affine is m0, whether the binder was written %0 or left unmarked.
  defp qty_agree(:linear, q) when q != :linear, do: {:error, "λ/Π multiplicity mismatch"}
  defp qty_agree(q, :linear) when q != :linear, do: {:error, "λ/Π multiplicity mismatch"}
  defp qty_agree(q, q), do: :ok
  defp qty_agree(_, _), do: {:error, "λ/Π quantity mismatch"}

  # Using a definition of `from` while checking in `to`.
  # spec ↛ evidence, evidence ↛ run, spec ↛ run.
  defp allowed_def?(from, to) do
    cond do
      from == to -> true
      from == :run -> true
      from == :evidence and to == :spec -> true
      true -> false
    end
  end

  defp infer_var_tax(k, book, gamma, n, x, mode) do
    case bound(gamma, x) do
      {:error, _} = err ->
        err

      {:ok, {:erased, _}} ->
        {:error, "no promotion: erased variable in #{mode} mode"}

      {:ok, {q, ty}} ->
        u = if q == :reuse, do: :uw, else: :u1

        if mode == :run do
          case run_ty(k, book, ty) do
            {:ok, true} -> {:ok, {ty, one_hot(n, x, u)}}
            {:ok, false} -> {:error, "no promotion: variable has a spec type"}
            err -> err
          end
        else
          {:ok, {ty, one_hot(n, x, u)}}
        end
    end
  end

  defp nctx(gamma), do: length(gamma)

  # -- apps / rec ------------------------------------------------------------

  defp apps(t), do: apps(t, [])
  defp apps({:app, f, a}, acc), do: apps(f, [a | acc])
  defp apps(f, acc), do: {f, acc}

  defp ctor_head_book?(book, t) do
    case elem(apps(t), 0) do
      :ze -> true
      {:su, _} -> true
      :one -> true
      {:def, n} -> ctor_name?(book, n)
      _ -> false
    end
  end

  @no_descent "recursive call does not descend on a smaller argument"

  # A maximal application spine headed by a member of the block: the
  # argument at the callee's position must be a smaller variable, or the
  # descended-on argument itself for a callee earlier in the book. A
  # shorter spine has no such argument. head? is infer's: an inner
  # application (the head of a larger spine) is not the maximal spine and
  # is not checked (Agda: checkRec). Spec descends the same way. An
  # evidence self-call under the ν guard is the coinductive step.
  defp check_rec(_mode, true, _rs, _t), do: :ok
  defp check_rec(:evidence, false, %{guard: true}, _t), do: :ok

  defp check_rec(mode, false, rs, t) when mode in [:run, :evidence, :spec] do
    case apps(t) do
      {{:def, name}, args} ->
        if in_block?(rs, name) do
          a = Enum.at(args, Map.get(rs.poss, name, length(args)))

          if a != nil and (smaller_var?(rs, a) or (arg_var?(rs, a) and earlier?(rs, name))),
            do: :ok,
            else: {:error, @no_descent}
        else
          :ok
        end

      _ ->
        :ok
    end
  end

  # The definition being checked may not occur unapplied: passed along, it
  # could be applied to anything. head? is infer's: at the head of a spine
  # it is applied (Agda: selfApplied). Evidence under the ν guard may name
  # itself; that occurrence is the coinductive step. Spec has no such step.
  defp self_applied(_mode, true, _rs, _name), do: :ok

  defp self_applied(mode, false, rs, name) do
    cond do
      not in_block?(rs, name) ->
        :ok

      # The step of an indexed ν. The self-call is the coinductive step.
      mode == :evidence and rs.guard ->
        :ok

      true ->
        {:error, "recursive definition must be applied to its arguments"}
    end
  end

  # The non-erased argument positions of a definition's type, read
  # syntactically: the candidates for the position a self-call descends on.
  defp arg_positions({:pi, q, _, _, b}, j) do
    if(q == :erased, do: [], else: [j]) ++ arg_positions(b, j + 1)
  end

  defp arg_positions(_, _), do: []

  # -- whnf ------------------------------------------------------------------

  # Weak-head normalisation, fuelled. `{:ok, t}` is a weak-head normal form
  # (or a stuck term); `{:error, msg}` is out of fuel.
  # `:all` unfolds every definition. `:run` unfolds only a `run` definition,
  # which is the value a computed session payload may send.
  defp whnf(k, book, t), do: whnf(k, book, t, :all)

  defp whnf(0, _book, _t, _unfold), do: {:error, @out_of_fuel}

  defp whnf(k, book, {:app, f, a}, unfold) do
    case whnf(k - 1, book, f, unfold) do
      {:ok, {:lam, _, _, _, t}} -> whnf(k - 1, book, Subst.inst(t, a), unfold)
      {:ok, f1} -> {:ok, {:app, f1, a}}
      err -> err
    end
  end

  defp whnf(k, book, {:mnat, e, p, z, s}, unfold) do
    case whnf(k - 1, book, e, unfold) do
      {:ok, :ze} -> whnf(k - 1, book, z, unfold)
      {:ok, {:su, u}} -> whnf(k - 1, book, Subst.inst(s, u), unfold)
      {:ok, e1} -> {:ok, {:mnat, e1, p, z, s}}
      err -> err
    end
  end

  defp whnf(k, book, {:matom, e, p, bs}, unfold) do
    case whnf(k - 1, book, e, unfold) do
      {:ok, {:atom, name}} ->
        case Enum.find(bs, fn {n, _} -> n == name end) do
          {_, b} -> whnf(k - 1, book, b, unfold)
          nil -> {:ok, {:matom, {:atom, name}, p, bs}}
        end

      {:ok, e1} ->
        {:ok, {:matom, e1, p, bs}}

      err ->
        err
    end
  end

  defp whnf(k, book, {:mdata, e, p, bs}, unfold) do
    with {:ok, e1} <- whnf(k - 1, book, e, unfold) do
      case ctor_spine(book, e1) do
        {:ok, {_dname, ci, args}} ->
          case Enum.at(bs, ci) do
            {_n, _ar, b} -> whnf(k - 1, book, Subst.inst_n(b, args), unfold)
            nil -> {:ok, {:mdata, e1, p, bs}}
          end

        :error ->
          {:ok, {:mdata, e1, p, bs}}
      end
    end
  end

  defp whnf(k, book, {:munit, e, p, u}, unfold) do
    case whnf(k - 1, book, e, unfold) do
      {:ok, :one} -> whnf(k - 1, book, u, unfold)
      {:ok, e1} -> {:ok, {:munit, e1, p, u}}
      err -> err
    end
  end

  defp whnf(k, book, {:memp, e, p}, unfold) do
    with {:ok, e1} <- whnf(k - 1, book, e, unfold), do: {:ok, {:memp, e1, p}}
  end

  defp whnf(k, book, {:def, name}, unfold) do
    case lookup_def(book, name) do
      {:ok, %{mode: :run} = d} ->
        whnf(k - 1, book, d.body, unfold)

      {:ok, d} when unfold == :all ->
        whnf(k - 1, book, d.body, unfold)

      _ ->
        {:ok, {:def, name}}
    end
  end

  defp whnf(k, book, {:ann, e, _}, unfold), do: whnf(k - 1, book, e, unfold)

  # ι-letp
  defp whnf(k, book, {:letp, e, t}, unfold) do
    case whnf(k - 1, book, e, unfold) do
      {:ok, {:pair, a, b}} -> whnf(k - 1, book, Subst.inst2(t, a, b), unfold)
      {:ok, e1} -> {:ok, {:letp, e1, t}}
      err -> err
    end
  end

  defp whnf(k, book, {:ucons, e}, unfold) do
    case whnf(k - 1, book, e, unfold) do
      # ι-ucons-r
      {:ok, {:unf, _s, {:pair, h, t}}} ->
        {:ok, {:pair, h, t}}

      # ι-ucons-p
      {:ok, {:unf, s, {:lam, q, a, x, {:pair, h, t}}}} ->
        {:ok, {:pair, Subst.inst(h, s), {:unf, Subst.inst(t, s), {:lam, q, a, x, {:pair, h, t}}}}}

      # ι-ucons-0
      {:ok, {:unf, {:pair, a, b}, {:lam, q, dom, x, {:var, 0}}}} ->
        {:ok, {:pair, a, {:unf, b, {:lam, q, dom, x, {:var, 0}}}}}

      {:ok, {:unf, s, f}} ->
        {:ok, {:ucons, {:unf, s, f}}}

      {:ok, e1} ->
        {:ok, {:ucons, e1}}

      err ->
        err
    end
  end

  defp whnf(_, _, t, _), do: {:ok, t}

  @doc """
  Full normal form of a de Bruijn term. Fuel bounds every reduction step.
  Out of fuel is an error. A stuck term is returned as that term.

  Only a `run` definition is unfolded. An evidence or spec definition
  stays stuck, so a session payload cannot be computed from one.
  """
  def normalize(book, term, fuel \\ @fuel) do
    nf(fuel, book, term, :run)
  end

  defp nf(k, book, term, unfold) do
    with {:ok, t} <- whnf(k, book, term, unfold), do: deepen(k, book, t, unfold)
  end

  defp deepen(k, book, {:su, u}, unfold) do
    with {:ok, u1} <- nf(fuel_dec(k), book, u, unfold), do: {:ok, {:su, u1}}
  end

  defp deepen(k, book, {:pair, a, b}, unfold) do
    with {:ok, a1} <- nf(fuel_dec(k), book, a, unfold),
         {:ok, b1} <- nf(fuel_dec(k), book, b, unfold) do
      {:ok, {:pair, a1, b1}}
    end
  end

  defp deepen(k, book, {:app, f, a}, unfold) do
    with {:ok, f1} <- nf(fuel_dec(k), book, f, unfold),
         {:ok, a1} <- nf(fuel_dec(k), book, a, unfold) do
      {:ok, {:app, f1, a1}}
    end
  end

  defp deepen(_k, _book, t, _unfold), do: {:ok, t}

  defp fuel_dec(k) when k > 0, do: k - 1
  defp fuel_dec(_), do: 0

  # Fuelled, as Agda's isData: fuel also bounds the descent into data
  # parameters (a spec definition may be recursive: X : Type := D X).
  defp is_data(0, _book, _t), do: {:error, @out_of_fuel}

  defp is_data(k, book, t) do
    with {:ok, t1} <- whnf(k, book, t) do
      {h, as} = apps(t1)
      k = k - 1

      case h do
        :nat ->
          {:ok, as == []}

        :unit ->
          {:ok, as == []}

        :empty ->
          {:ok, as == []}

        :i64 ->
          {:ok, as == []}

        :f32ty ->
          {:ok, as == []}

        {:tensor, _, _} ->
          {:ok, as == []}

        {:def, n} ->
          case lookup_data(book, n) do
            {:ok, d} -> all_data(k, book, Enum.take(as, length(d.params)))
            _ -> {:ok, false}
          end

        {:prod, a, b} when as == [] ->
          all_data(k, book, [a, b])

        _ ->
          {:ok, false}
      end
    end
  end

  # Copyable (Agda's isCopy): Data, a Π, or a product of copyable types.
  # A + binder asks this; an argument at a + position whose type is
  # copyable and not Data has its uses scaled to ω (scale_omega).
  defp is_copy(0, _book, _t), do: {:error, @out_of_fuel}

  defp is_copy(k, book, t) do
    with {:ok, t1} <- whnf(k, book, t) do
      case t1 do
        {:pi, _, _, _, _} ->
          {:ok, true}

        {:prod, a, b} ->
          case is_copy(k - 1, book, a) do
            {:ok, true} -> is_copy(k - 1, book, b)
            other -> other
          end

        _ ->
          is_data(k, book, t1)
      end
    end
  end

  @not_copy "+ requires a copyable type: Data, a pair of them, or a function"

  defp guard_copy(k, book, a) do
    case is_copy(k, book, a) do
      {:ok, true} -> :ok
      {:ok, false} -> {:error, @not_copy}
      err -> err
    end
  end

  # Uses of an argument at a + position: unchanged for Data (a value
  # copies by value), scaled to ω otherwise (a closure duplicates what it
  # captured), so check_bound refuses captured affine variables.
  defp reuse_arg_uses(k, book, a, au) do
    case is_data(k, book, a) do
      {:ok, true} -> {:ok, au}
      {:ok, false} -> with :ok <- guard_copy(k, book, a), do: {:ok, scale_omega(au)}
      err -> err
    end
  end

  defp scale_omega(us),
    do:
      Enum.map(us, fn
        :u1 -> :uw
        u -> u
      end)

  defp all_data(_k, _book, []), do: {:ok, true}

  defp all_data(k, book, [a | as]) do
    case is_data(k, book, a) do
      {:ok, true} -> all_data(k, book, as)
      other -> other
    end
  end

  # Shape of a run type after one whnf, read syntactically as Agda's
  # runTy: a variable, a leaf type, a Π whose codomain is one, a product
  # of two, ν F with F one (the bound variable counts as a run type), a
  # data type or an application of one.
  # Each Π codomain, product side, and ν body is reduced before it is read,
  # so a definition naming a type counts as the type it names.
  defp run_ty(0, _book, _t), do: {:error, @out_of_fuel}

  defp run_ty(k, book, t) do
    with {:ok, t1} <- whnf(k, book, t), do: run_ty_w(k - 1, book, t1)
  end

  defp run_ty_w(k, book, {:pi, _, _, _, b}), do: run_ty(k, book, b)
  defp run_ty_w(k, book, {:nu, f}), do: run_ty(k, book, f)

  defp run_ty_w(k, book, {:prod, a, b}) do
    case run_ty(k, book, a) do
      {:ok, true} -> run_ty(k, book, b)
      other -> other
    end
  end

  defp run_ty_w(_k, book, t), do: {:ok, run_ty_n(book, t)}

  defp run_ty_n(_book, {:var, _}), do: true
  defp run_ty_n(_book, :atom), do: true
  defp run_ty_n(_book, :nat), do: true
  defp run_ty_n(_book, :unit), do: true
  defp run_ty_n(_book, :empty), do: true
  defp run_ty_n(_book, :i64), do: true
  defp run_ty_n(_book, :f32ty), do: true
  defp run_ty_n(_book, {:tensor, _, _}), do: true
  defp run_ty_n(book, {:pi, _, _, _, b}), do: run_ty_n(book, b)
  defp run_ty_n(book, {:nu, f}), do: run_ty_n(book, f)
  defp run_ty_n(book, {:prod, a, b}), do: run_ty_n(book, a) and run_ty_n(book, b)
  defp run_ty_n(book, {:app, f, _}), do: run_ty_n(book, f)
  defp run_ty_n(book, {:def, n}), do: data_name?(book, n)
  defp run_ty_n(_book, _), do: false

  # -- conversion ------------------------------------------------------------

  defp syn_eq(a, b), do: a == b

  defp conv(0, _, _, _, _), do: {:error, @out_of_fuel}

  defp conv(k, book, names, u, v) do
    if syn_eq(u, v) do
      :ok
    else
      stuck_cong(k, book, names, u, v)
    end
  end

  # The same def at arguments that are not constructor-headed: compare the
  # arguments first. Arguments that differ do not decide it, since the def
  # may match on a later argument; both sides are then unfolded.
  defp stuck_cong(k, book, names, u, v) do
    case {apps(u), apps(v)} do
      {{{:def, i}, [a | as]}, {{:def, j}, [b | bs]}} ->
        if i == j and not ctor_head_book?(book, a) and not ctor_head_book?(book, b) do
          with :ok <- conv(k - 1, book, names, a, b),
               :ok <- conv_args(k - 1, book, names, as, bs) do
            :ok
          else
            _ -> conv_whnf(k - 1, book, names, u, v)
          end
        else
          conv_whnf(k - 1, book, names, u, v)
        end

      _ ->
        conv_whnf(k - 1, book, names, u, v)
    end
  end

  defp conv_whnf(k, book, names, u, v) do
    with {:ok, u1} <- whnf(k, book, u),
         {:ok, v1} <- whnf(k, book, v),
         do: conv_n(k, book, names, u1, v1)
  end

  defp conv_args(_k, _book, _names, [], []), do: :ok
  defp conv_args(_k, _book, _names, _, []), do: {:error, "conv: spine length mismatch"}
  defp conv_args(_k, _book, _names, [], _), do: {:error, "conv: spine length mismatch"}

  defp conv_args(k, book, names, [a | as], [b | bs]) do
    with :ok <- conv(k, book, names, a, b), do: conv_args(k, book, names, as, bs)
  end

  defp conv_n(_k, _book, _names, a, b) when a == b, do: :ok
  defp conv_n(k, book, names, {:su, a}, {:su, b}), do: conv(k, book, names, a, b)
  defp conv_n(_k, _book, _names, {:var, i}, {:var, j}) when i == j, do: :ok

  defp conv_n(k, book, names, {:pi, q, a, x, b}, {:pi, q, a1, _, b1}) do
    with :ok <- conv(k, book, names, a, a1), do: conv(k, book, [x | names], b, b1)
  end

  defp conv_n(k, book, names, {:lam, q, a, x, t}, {:lam, q, a1, _, t1}) do
    with :ok <- conv(k, book, names, a, a1), do: conv(k, book, [x | names], t, t1)
  end

  defp conv_n(k, book, names, {:app, f, a}, {:app, g, b}) do
    with :ok <- conv(k, book, names, f, g), do: conv(k, book, names, a, b)
  end

  defp conv_n(k, book, names, {:idt, a, x, y}, {:idt, a1, x1, y1}) do
    with :ok <- conv(k, book, names, a, a1),
         :ok <- conv(k, book, names, x, x1),
         do: conv(k, book, names, y, y1)
  end

  defp conv_n(k, book, names, {:mnat, e, p, z, s}, {:mnat, e1, p1, z1, s1}) do
    with :ok <- conv(k, book, names, e, e1),
         :ok <- conv(k, book, names, p, p1),
         :ok <- conv(k, book, names, z, z1),
         do: conv(k, book, names, s, s1)
  end

  defp conv_n(k, book, names, {:memp, e, p}, {:memp, e1, p1}) do
    with :ok <- conv(k, book, names, e, e1), do: conv(k, book, names, p, p1)
  end

  defp conv_n(k, book, names, {:munit, e, p, u}, {:munit, e1, p1, u1}) do
    with :ok <- conv(k, book, names, e, e1),
         :ok <- conv(k, book, names, p, p1),
         do: conv(k, book, names, u, u1)
  end

  defp conv_n(k, book, names, {:rwt, e, p, t}, {:rwt, e1, p1, t1}) do
    with :ok <- conv(k, book, names, e, e1),
         :ok <- conv(k, book, names, p, p1),
         do: conv(k, book, names, t, t1)
  end

  defp conv_n(k, book, names, {:ann, e, a}, {:ann, e1, a1}) do
    with :ok <- conv(k, book, names, e, e1), do: conv(k, book, names, a, a1)
  end

  defp conv_n(k, book, names, {:prod, a, b}, {:prod, a1, b1}) do
    with :ok <- conv(k, book, names, a, a1), do: conv(k, book, names, b, b1)
  end

  defp conv_n(k, book, names, {:pair, a, b}, {:pair, a1, b1}) do
    with :ok <- conv(k, book, names, a, a1), do: conv(k, book, names, b, b1)
  end

  defp conv_n(k, book, names, {:letp, e, t}, {:letp, e1, t1}) do
    with :ok <- conv(k, book, names, e, e1), do: conv(k, book, ["b", "a" | names], t, t1)
  end

  defp conv_n(k, book, names, {:nu, f}, {:nu, f1}), do: conv(k, book, names, f, f1)

  defp conv_n(k, book, names, {:bisim, s, t}, {:bisim, s1, t1}) do
    with :ok <- conv(k, book, names, s, s1), do: conv(k, book, names, t, t1)
  end

  defp conv_n(k, book, names, {:unf, s, f}, {:unf, s1, f1}) do
    with :ok <- conv(k, book, names, s, s1), do: conv(k, book, names, f, f1)
  end

  defp conv_n(k, book, names, {:ucons, s}, {:ucons, s1}), do: conv(k, book, names, s, s1)

  defp conv_n(k, book, names, {:tensor, d, s}, {:tensor, d1, s1}) do
    with :ok <- conv(k, book, names, d, d1), do: conv(k, book, names, s, s1)
  end

  defp conv_n(k, book, names, {:addi, x, y}, {:addi, x1, y1}) do
    with :ok <- conv(k, book, names, x, x1), do: conv(k, book, names, y, y1)
  end

  defp conv_n(k, book, names, {:muli, x, y}, {:muli, x1, y1}) do
    with :ok <- conv(k, book, names, x, x1), do: conv(k, book, names, y, y1)
  end

  defp conv_n(k, book, names, {:addt, t, u}, {:addt, t1, u1}) do
    with :ok <- conv(k, book, names, t, t1), do: conv(k, book, names, u, u1)
  end

  defp conv_n(k, book, names, {:toi64, t}, {:toi64, t1}), do: conv(k, book, names, t, t1)

  defp conv_n(k, book, names, {:packi, x, y}, {:packi, x1, y1}) do
    with :ok <- conv(k, book, names, x, x1), do: conv(k, book, names, y, y1)
  end

  defp conv_n(k, book, names, {:mdata, e, p, bs}, {:mdata, e1, p1, bs1}) do
    with :ok <- conv(k, book, names, e, e1),
         :ok <- conv(k, book, names, p, p1) do
      conv_mdata_bs(k, book, names, bs, bs1)
    end
  end

  defp conv_n(_k, _book, names, u, v),
    do: {:error, "cannot convert #{Print.term(u, names)} ≁ #{Print.term(v, names)}"}

  defp conv_mdata_bs(_k, _book, _names, [], []), do: :ok

  defp conv_mdata_bs(k, book, names, [{n, ar, b} | bs], [{n, ar, b1} | bs1]) do
    with :ok <- conv(k, book, names, b, b1), do: conv_mdata_bs(k, book, names, bs, bs1)
  end

  defp conv_mdata_bs(_, _, _, _, _), do: {:error, "match branches do not convert"}

  defp view_pi(k, book, t, names) do
    case whnf(k, book, t) do
      {:ok, {:pi, q, a, _, b}} -> {:ok, {q, a, b}}
      {:ok, t1} -> {:error, "expected Π, got #{Print.term(t1, names)}"}
      err -> err
    end
  end

  defp view_id(k, book, t, names) do
    case whnf(k, book, t) do
      {:ok, {:idt, a, x, y}} -> {:ok, {a, x, y}}
      {:ok, t1} -> {:error, "expected Id, got #{Print.term(t1, names)}"}
      err -> err
    end
  end

  defp nx_dtype_ok(k, book, t) do
    case whnf(k, book, t) do
      {:ok, :i64} -> :ok
      {:ok, :f32ty} -> :ok
      {:ok, _} -> {:error, "Tensor dtype must be I64 or F32"}
      err -> err
    end
  end

  defp float_id_ok(k, book, a) do
    forbidden = {:error, "kernel identity is not defined on F32"}

    case whnf(k, book, a) do
      {:ok, :f32ty} ->
        forbidden

      {:ok, {:tensor, d, _}} ->
        case whnf(k, book, d) do
          {:ok, :f32ty} -> forbidden
          {:ok, _} -> :ok
          err -> err
        end

      {:ok, _} ->
        :ok

      err ->
        err
    end
  end

  # packI shape: toI64 (suc (suc 0))
  defp i64two, do: {:toi64, {:su, {:su, :ze}}}

  defp view_prod(k, book, t, names) do
    case whnf(k, book, t) do
      {:ok, {:prod, a, b}} -> {:ok, {a, b}}
      {:ok, t1} -> {:error, "expected ×, got #{Print.term(t1, names)}"}
      err -> err
    end
  end

  defp view_nu(k, book, t, names) do
    case whnf(k, book, t) do
      {:ok, {:nu, f}} -> {:ok, f}
      {:ok, t1} -> {:error, "expected ν, got #{Print.term(t1, names)}"}
      err -> err
    end
  end

  # ⇒-bisim: σ ~ τ unfolds to {head σ ≡ head τ} × (tail σ ~ tail τ).
  defp payload_ty(k, book, f) do
    case view_prod(k, book, Subst.inst(f, :unit), []) do
      {:ok, {a, _}} -> {:ok, a}
      err -> err
    end
  end

  defp expand_bisim(k, book, rs, gamma, s, t) do
    with {:ok, {ts, _}} <- infer(k, book, rs, gamma, :spec, s),
         {:ok, f} <- view_nu(k, book, ts, names_of(rs, gamma)),
         {:ok, a} <- payload_ty(k, book, f),
         {:ok, {tt, _}} <- infer(k, book, rs, gamma, :spec, t),
         :ok <- conv(k, book, names_of(rs, gamma), ts, tt) do
      {:ok, Subst.bisim(a, s, t)}
    end
  end

  defp step_rec(rs, true), do: %{rs | guard: true}
  defp step_rec(rs, false), do: rs

  defp apply_fam(t, []), do: t
  defp apply_fam({:lam, _, _, _, b}, [i | is]), do: apply_fam(Subst.inst(b, i), is)
  defp apply_fam(t, [i | is]), do: apply_fam({:app, t, i}, is)

  # A bare ν unfold is a stream: ν X. A × X with A free of X. A declared
  # family (fam) is the pair the body checked, not this shape.
  defp bare_stream(_k, _book, true, _ty), do: :ok

  defp bare_stream(k, book, false, ty) do
    case whnf(k, book, ty) do
      {:ok, {:nu, {:prod, b, {:var, 0}}}} ->
        if occurs?(0, b),
          do: {:error, "bare ν is not a stream"},
          else: :ok

      _ ->
        {:error, "bare ν is not a stream"}
    end
  end

  # Codomain of an unfold step, and whether the goal is an applied family.
  defp unf_step(k, book, rs, gamma, ty, seed_ty) do
    names = names_of(rs, gamma)

    with {:ok, t1} <- whnf(k, book, ty) do
      unf_step_of(k, book, rs, gamma, names, t1, seed_ty)
    end
  end

  defp unf_step_of(_k, _book, _rs, _gamma, _names, {:nu, f}, seed_ty) do
    {:ok, {Subst.inst(f, seed_ty), false}}
  end

  defp unf_step_of(k, book, rs, gamma, _names, {:bisim, s, u}, seed_ty) do
    with {:ok, expanded} <- expand_bisim(k, book, rs, gamma, s, u),
         {:ok, {{:prod, head, _tail}, true}} <-
           unf_step(k, book, rs, gamma, expanded, seed_ty) do
      # Keep the surface relation in every type position, not only at a
      # definition's codomain. The indexed ν still supplies the head goal.
      {:ok, {{:prod, head, {:bisim, Subst.tail(s), Subst.tail(u)}}, true}}
    end
  end

  defp unf_step_of(_k, _book, _rs, _gamma, names, t, _seed_ty) do
    case apps(t) do
      {{:nu, {:lam, _, _, _, _} = f}, [_ | _] = idxs} ->
        {:ok, {apply_fam(Subst.inst(f, {:nu, f}), idxs), true}}

      _ ->
        {:error, "expected ν, got #{Print.term(t, names)}"}
    end
  end

  # Kind of a ν body. Stream (a product) is Type. A λ-telescope of any
  # length is the Π of its domains; Y does not occur in the kind.
  defp nu_kind(f), do: telescope(f, 0)

  defp telescope({:lam, q, a, x, t}, y) do
    with {:ok, a1} <- drop_var(a, y),
         {:ok, b} <- telescope(t, y + 1) do
      {:ok, {:pi, q, a1, x, b}}
    end
  end

  defp telescope(_, _), do: {:ok, :typ}

  # Agda's nuBodyProd: under its telescope a ν body is a product, since
  # an unfold step is a pair and uncons reads one back.
  defp nu_body_prod?({:lam, _, _, _, t}), do: nu_body_prod?(t)
  defp nu_body_prod?({:prod, _, _}), do: true
  defp nu_body_prod?(_), do: false

  defp drop_var(t, at) do
    try do
      {:ok,
       Subst.ren(
         fn
           i when i == at -> throw(:nu_kind_hit)
           i when i > at -> i - 1
           i -> i
         end,
         t
       )}
    catch
      :nu_kind_hit -> {:error, "ν kind mentions its binder"}
    end
  end

  defp view_data(k, book, t, names) do
    with {:ok, t1} <- whnf(k, book, t) do
      {h, args} = apps(t1)

      case h do
        {:def, n} ->
          case lookup_data(book, n) do
            {:ok, d} ->
              np = length(d.params)
              ni = length(Map.get(d, :indices, []))

              if length(args) == np + ni do
                {:ok, {d, n, Enum.take(args, np), Enum.drop(args, np)}}
              else
                {:error, "data applied to the wrong number of arguments"}
              end

            _ ->
              {:error, "expected data type, got #{Print.term(h, names)}"}
          end

        _ ->
          {:error, "expected data type, got #{Print.term(h, names)}"}
      end
    end
  end

  defp ctor_spine(book, t) do
    {h, args} = apps(t)

    case h do
      {:def, n} ->
        case lookup_ctor(book, n) do
          {:ok, {_d, dname, ci, _c}} -> {:ok, {dname, ci, args}}
          _ -> :error
        end

      _ ->
        :error
    end
  end

  defp is_d_type?(book, dname, t) do
    case elem(apps(t), 0) do
      {:def, n} -> n == dname and data_name?(book, n)
      _ -> false
    end
  end

  # ⇒-unf productivity: a member of the recursive block may not occur in the pair's head.
  defp has_self?(%MapSet{} = block, {:def, name}), do: MapSet.member?(block, name)
  defp has_self?(self, {:def, name}) when self == name, do: true
  defp has_self?(self, {:app, f, a}), do: has_self?(self, f) or has_self?(self, a)
  defp has_self?(self, {:su, t}), do: has_self?(self, t)
  defp has_self?(self, {:pair, a, b}), do: has_self?(self, a) or has_self?(self, b)
  defp has_self?(self, {:letp, e, t}), do: has_self?(self, e) or has_self?(self, t)
  defp has_self?(self, {:unf, s, f}), do: has_self?(self, s) or has_self?(self, f)
  defp has_self?(self, {:ucons, s}), do: has_self?(self, s)
  defp has_self?(self, {:tensor, d, s}), do: has_self?(self, d) or has_self?(self, s)
  defp has_self?(self, {:addi, x, y}), do: has_self?(self, x) or has_self?(self, y)
  defp has_self?(self, {:muli, x, y}), do: has_self?(self, x) or has_self?(self, y)
  defp has_self?(self, {:addt, t, u}), do: has_self?(self, t) or has_self?(self, u)
  defp has_self?(self, {:toi64, t}), do: has_self?(self, t)
  defp has_self?(self, {:packi, x, y}), do: has_self?(self, x) or has_self?(self, y)
  defp has_self?(self, {:lam, _, a, _, t}), do: has_self?(self, a) or has_self?(self, t)
  defp has_self?(self, {:pi, _, a, _, b}), do: has_self?(self, a) or has_self?(self, b)
  defp has_self?(self, {:prod, a, b}), do: has_self?(self, a) or has_self?(self, b)
  defp has_self?(self, {:nu, f}), do: has_self?(self, f)
  defp has_self?(self, {:bisim, s, t}), do: has_self?(self, s) or has_self?(self, t)

  defp has_self?(self, {:matom, e, p, bs}) do
    has_self?(self, e) or has_self?(self, p) or
      Enum.any?(bs, fn {_, b} -> has_self?(self, b) end)
  end

  defp has_self?(self, {:mdata, e, p, bs}) do
    has_self?(self, e) or has_self?(self, p) or
      Enum.any?(bs, fn {_, _, b} -> has_self?(self, b) end)
  end

  defp has_self?(self, {:mnat, e, p, z, s}),
    do: has_self?(self, e) or has_self?(self, p) or has_self?(self, z) or has_self?(self, s)

  defp has_self?(self, {:memp, e, p}), do: has_self?(self, e) or has_self?(self, p)

  defp has_self?(self, {:munit, e, p, u}),
    do: has_self?(self, e) or has_self?(self, p) or has_self?(self, u)

  defp has_self?(self, {:idt, a, x, y}),
    do: has_self?(self, a) or has_self?(self, x) or has_self?(self, y)

  defp has_self?(self, {:rwt, e, p, t}),
    do: has_self?(self, e) or has_self?(self, p) or has_self?(self, t)

  defp has_self?(self, {:ann, e, a}), do: has_self?(self, e) or has_self?(self, a)

  defp has_self?(_, _), do: false

  defp occurs?(x, {:var, y}), do: x == y
  defp occurs?(x, {:pi, _, a, _, b}), do: occurs?(x, a) or occurs?(x + 1, b)
  defp occurs?(x, {:lam, _, a, _, t}), do: occurs?(x, a) or occurs?(x + 1, t)
  defp occurs?(x, {:app, f, a}), do: occurs?(x, f) or occurs?(x, a)
  defp occurs?(x, {:su, t}), do: occurs?(x, t)
  defp occurs?(x, {:prod, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:pair, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:letp, e, t}), do: occurs?(x, e) or occurs?(x + 2, t)
  defp occurs?(x, {:nu, f}), do: occurs?(x + 1, f)
  defp occurs?(x, {:bisim, s, t}), do: occurs?(x, s) or occurs?(x, t)

  defp occurs?(x, {:matom, e, p, bs}) do
    occurs?(x, e) or occurs?(x + 1, p) or Enum.any?(bs, fn {_, b} -> occurs?(x, b) end)
  end

  defp occurs?(x, {:mdata, e, p, bs}) do
    occurs?(x, e) or occurs?(x + 1, p) or
      Enum.any?(bs, fn {_, ar, b} -> occurs?(x + ar, b) end)
  end

  defp occurs?(x, {:unf, s, f}), do: occurs?(x, s) or occurs?(x, f)
  defp occurs?(x, {:ucons, s}), do: occurs?(x, s)
  defp occurs?(x, {:idt, a, b, c}), do: occurs?(x, a) or occurs?(x, b) or occurs?(x, c)
  defp occurs?(x, {:tensor, d, s}), do: occurs?(x, d) or occurs?(x, s)
  defp occurs?(x, {:addi, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:muli, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:addt, t, u}), do: occurs?(x, t) or occurs?(x, u)
  defp occurs?(x, {:toi64, t}), do: occurs?(x, t)
  defp occurs?(x, {:packi, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(_, _), do: false

  defp spos?(_x, {:var, _}), do: true
  defp spos?(x, {:prod, a, b}), do: spos?(x, a) and spos?(x, b)
  defp spos?(x, {:pi, _, a, _, b}), do: not occurs?(x, a) and spos?(x + 1, b)
  defp spos?(x, {:nu, f}), do: not occurs?(x + 1, f)
  defp spos?(x, {:lam, _, a, _, t}), do: not occurs?(x, a) and spos?(x + 1, t)
  defp spos?(x, {:app, _, _} = t), do: spos_app?(x, t)
  defp spos?(x, t), do: not occurs?(x, t)

  # Y (tail s) is positive: the recursive variable is the head, and it
  # does not occur in the arguments.
  defp spos_app?(x, t) do
    case apps(t) do
      {{:var, y}, args} when y == x -> Enum.all?(args, &(not occurs?(x, &1)))
      _ -> not occurs?(x, t)
    end
  end

  defp strict_pos?(f), do: spos?(0, f)

  defp check_unfold(_k, _book, :spec, _rs, _f), do: :ok

  defp check_unfold(k, book, _m, rs, f) do
    with {:ok, f1} <- whnf(k, book, f), do: go_unfold(f1, block_of(rs))
  end

  defp go_unfold({:lam, _, _, _, t}, self), do: go_unfold(t, self)

  defp go_unfold({:pair, h, _}, self) do
    if has_self?(self, h),
      do: {:error, "unguarded recursive call"},
      else: :ok
  end

  defp go_unfold(_, _), do: {:error, "unfold body must be a pair"}

  # Agda's checkNu: on run/evidence, a definition whose type reduces to a
  # ν (bare, a family applied to any number of indices, or ~) is an
  # unfold, or it does not mention its own block. A call into the block
  # is productive only as the tail of an unfold step (check_unfold).
  defp check_nu(_k, _book, _block, :spec, _ty, _body), do: :ok
  defp check_nu(0, _book, _block, _mode, _ty, _body), do: {:error, @out_of_fuel}

  defp check_nu(k, book, block, mode, ty, body) do
    with {:ok, ty1} <- whnf(k, book, ty) do
      case {ty1, body} do
        {{:pi, _, _, _, b}, {:lam, _, _, _, t}} ->
          check_nu(k - 1, book, block, mode, b, t)

        {_, {:unf, _, _}} ->
          :ok

        _ ->
          if nu_type?(ty1) and has_self?(block, body),
            do: {:error, "ν value calls its own block outside an unfold"},
            else: :ok
      end
    end
  end

  defp nu_type?({:bisim, _, _}), do: true
  defp nu_type?(t), do: match?({{:nu, _}, _}, apps(t))

  # -- infer / check ---------------------------------------------------------

  # ⇒-def, without the self-application test (infer asks it). Also data
  # formers and bare constructors, which share the name space.
  defp infer_def(k, book, gamma, m, name) do
    n = nctx(gamma)

    case lookup_def(book, name) do
      {:ok, d} ->
        cond do
          not allowed_def?(d.mode, m) ->
            {:error, "no promotion: #{d.mode} definition #{name} in #{m} mode"}

          m == :run ->
            case run_ty(k, book, d.type) do
              {:ok, true} -> {:ok, {d.type, u0s(n)}}
              {:ok, false} -> {:error, "no promotion: definition #{name} has a spec type"}
              err -> err
            end

          true ->
            {:ok, {d.type, u0s(n)}}
        end

      {:skip, msg} ->
        {:error, msg}

      {:error, _} ->
        case lookup_data(book, name) do
          {:ok, d} when m == :spec ->
            {:ok, {dty_type(d.params, Map.get(d, :indices, [])), u0s(n)}}

          {:ok, _} ->
            {:error, "no promotion: a data former is an erased term"}

          {:error, _} ->
            case lookup_ctor(book, name) do
              {:ok, _} ->
                {:error, "constructor requires an expected data type"}

              err ->
                err
            end
        end
    end
  end

  # head?: the term is the head of an application spine. Only the app and
  # def cases read it (descent); every other case passes on through
  # infer/6 and check, which is not a head (Agda: infer′'s Bool).
  defp infer(k, book, rs, gamma, mode, t), do: infer(k, book, rs, gamma, mode, t, false)

  defp infer(k, book, rs, gamma, mode, t, head?) do
    n = nctx(gamma)

    case {mode, t} do
      {_, {:hole, loc}} ->
        {:error, Print.hole_message(loc, gamma, names_of(rs, gamma), nil)}

      # ⇒-var-run / ⇒-var-evid / ⇒-var-spec
      {:run, {:var, x}} ->
        infer_var_tax(k, book, gamma, n, x, :run)

      {:evidence, {:var, x}} ->
        infer_var_tax(k, book, gamma, n, x, :evidence)

      {:spec, {:var, x}} ->
        case bound(gamma, x) do
          {:error, _} = err -> err
          {:ok, {_, ty}} -> {:ok, {ty, u0s(n)}}
        end

      # ⇒-ze
      {_, :ze} ->
        {:ok, {:nat, u0s(n)}}

      # ⇒-su
      {m, {:su, t1}} ->
        with {:ok, u} <- check(k, book, rs, gamma, m, t1, :nat),
             do: {:ok, {:nat, u}}

      # ⇒-tt
      {_, :one} ->
        {:ok, {:unit, u0s(n)}}

      {m, :nat} when m in [:run, :evidence] ->
        {:error, "no promotion: Nat is an erased term"}

      {m, :unit} when m in [:run, :evidence] ->
        {:error, "no promotion: Unit is an erased term"}

      {m, :empty} when m in [:run, :evidence] ->
        {:error, "no promotion: Empty is an erased term"}

      {m, :typ} when m in [:run, :evidence] ->
        {:error, "no promotion: Type is an erased term"}

      # ⇒-nat / ⇒-unit / ⇒-empty  (spec only)
      {:spec, :nat} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, :unit} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, :empty} ->
        {:ok, {:typ, u0s(n)}}

      # Atom is a type. A literal is a value of that type.
      {m, :atom} when m in [:run, :evidence] ->
        {:error, "no promotion: Atom is an erased term"}

      {:spec, :atom} ->
        {:ok, {:typ, u0s(n)}}

      {_, {:atom, _name}} ->
        {:ok, {:atom, u0s(n)}}

      {m, {:matom, e, p, bs}} ->
        with {:ok, eu} <- check(k, book, rs, gamma, m, e, :atom),
             :ok <-
               check_ty(
                 k,
                 book,
                 push_name(ext_rec(rs, false, false), "a"),
                 ext(gamma, :affine, :atom),
                 p
               ),
             {:ok, bu} <- check_atom_arms(k, book, rs, gamma, m, p, bs),
             {:ok, uses} <- combine(m, eu, bu) do
          {:ok, {Subst.inst(p, e), uses}}
        end

      # ⇒-mData
      {m, {:mdata, e, p, bs}} ->
        with {:ok, {et, eu}} <- infer(k, book, rs, gamma, m, e),
             {:ok, {d, dname, params, idxs}} <- view_data(k, book, et, names_of(rs, gamma)),
             :ok <- match_arity(bs, d.ctors),
             :ok <- check_motive(k, book, rs, gamma, d, dname, params, p),
             mot_fun = first_mot_lam(d, dname, params, p),
             {:ok, bu} <-
               check_branches(
                 k,
                 book,
                 rs,
                 gamma,
                 m,
                 dname,
                 scrut_ok(rs, e),
                 params,
                 idxs,
                 mot_fun,
                 d.ctors,
                 bs
               ),
             {:ok, uses} <- combine(m, eu, bu) do
          {:ok, {Subst.apps_from(mot_fun, idxs ++ [e]), uses}}
        end

      {:spec, :typ} ->
        {:error, "Type has no type (no Type : Type)"}

      # ⇒-pi
      {m, {:pi, _, _, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: Π is an erased term"}

      # The codomain must be small (: Type). With check_ty instead,
      # Π (x : A) → Type : Type and Type is a retract of a small type.
      {:spec, {:pi, q, a, x, b}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             {:ok, _} <-
               check(
                 k,
                 book,
                 push_name(ext_rec(rs, false, false), x),
                 ext(gamma, q, a),
                 :spec,
                 b,
                 :typ
               ),
             do: {:ok, {:typ, u0s(n)}}

      # ⇒-lam
      {m, {:lam, q, a, x, t1}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             :ok <-
               if(q == :reuse,
                 do: guard_copy(k, book, a),
                 else: :ok
               ),
             {:ok, {b, [u0 | us]}} <-
               infer(k, book, push_name(lam_rec(rs), x), ext(gamma, q, a), m, t1),
             :ok <- check_bound(m, q, u0) do
          {:ok, {{:pi, q, a, x, b}, us}}
        end

      # ⇒-app-aff / ⇒-app-era / ⇒-app-reuse: the head as a head; the
      # descent check is the outermost app's, on the maximal spine
      {m, {:app, f, a}} ->
        with {:ok, {ft, fu}} <- infer(k, book, rs, gamma, m, f, true),
             {:ok, {q, a_ty, b}} <- view_pi(k, book, ft, names_of(rs, gamma)),
             {:ok, uses} <- infer_arg(k, book, rs, gamma, m, q, a_ty, fu, a, f),
             :ok <- check_rec(m, head?, rs, {:app, f, a}) do
          {:ok, {Subst.inst(b, a), uses}}
        end

      {m, {:idt, _, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: identity type is an erased term"}

      # ⇒-idt
      {:spec, {:idt, a, x, y}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             :ok <- float_id_ok(k, book, a),
             {:ok, _} <- check(k, book, rs, gamma, :spec, x, a),
             {:ok, _} <- check(k, book, rs, gamma, :spec, y, a),
             do: {:ok, {:typ, u0s(n)}}

      {_, :rfl} ->
        {:error, "refl requires an expected identity type"}

      # ⇒-rwt. The equation is evidence, or spec inside a spec term
      # (Agda: rwtMode); its uses are discarded.
      {m, {:rwt, eq, p, t1}} ->
        with {:ok, {et, _}} <- infer(k, book, rs, gamma, rwt_mode(m), eq),
             {:ok, {a, lft, r}} <- view_id(k, book, et, names_of(rs, gamma)),
             :ok <-
               check_ty(
                 k,
                 book,
                 push_name(ext_rec(rs, false, false), "z"),
                 ext(gamma, :affine, a),
                 p
               ),
             {:ok, tu} <- check(k, book, rs, gamma, m, t1, Subst.inst(p, r)) do
          {:ok, {Subst.inst(p, lft), tu}}
        end

      # ⇒-mNat
      {m, {:mnat, e, p, z, s}} ->
        with {:ok, eu} <- check(k, book, rs, gamma, m, e, :nat),
             :ok <-
               check_ty(
                 k,
                 book,
                 push_name(ext_rec(rs, false, false), "n"),
                 ext(gamma, :affine, :nat),
                 p
               ),
             {:ok, zu} <- check(k, book, rs, gamma, m, z, Subst.inst(p, :ze)),
             ok? = scrut_ok(rs, e),
             pq = pred_qty(gamma, e),
             {:ok, [u0 | sus]} <-
               check(
                 k,
                 book,
                 push_name(ext_rec(rs, ok?, ok?), "n"),
                 ext(gamma, pq, :nat),
                 m,
                 s,
                 Subst.mot_suc(p)
               ),
             :ok <- check_bound(m, pq, u0),
             {:ok, uses} <- combine(m, eu, combine_alt(m, zu, sus)) do
          {:ok, {Subst.inst(p, e), uses}}
        end

      # ⇒-mEmp
      {m, {:memp, e, p}} ->
        with {:ok, eu} <- check(k, book, rs, gamma, m, e, :empty),
             :ok <-
               check_ty(
                 k,
                 book,
                 push_name(ext_rec(rs, false, false), "e"),
                 ext(gamma, :affine, :empty),
                 p
               ) do
          {:ok, {Subst.inst(p, e), eu}}
        end

      # ⇒-mUnit
      {m, {:munit, e, p, u}} ->
        with {:ok, eu} <- check(k, book, rs, gamma, m, e, :unit),
             :ok <-
               check_ty(
                 k,
                 book,
                 push_name(ext_rec(rs, false, false), "x"),
                 ext(gamma, :affine, :unit),
                 p
               ),
             {:ok, uu} <- check(k, book, rs, gamma, m, u, Subst.inst(p, :one)),
             {:ok, uses} <- combine(m, eu, uu) do
          {:ok, {Subst.inst(p, e), uses}}
        end

      # ⇒-def / ⇒-dty; unapplied, the definition being checked is refused
      {m, {:def, name}} ->
        with :ok <- self_applied(m, head?, rs, name),
             do: infer_def(k, book, gamma, m, name)

      # ⇒-ann
      {m, {:ann, e, a}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             {:ok, u} <- check(k, book, rs, gamma, m, e, a),
             do: {:ok, {a, u}}

      # ⇒-prod
      {m, {:prod, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: × is an erased term"}

      # components small
      {:spec, {:prod, a, b}} ->
        with {:ok, _} <- check(k, book, rs, gamma, :spec, a, :typ),
             {:ok, _} <- check(k, book, rs, gamma, :spec, b, :typ),
             do: {:ok, {:typ, u0s(n)}}

      # ⇒-nu
      {m, {:nu, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: ν is an erased term"}

      # body small. A λ-telescope is a family: Y and the body share its kind.
      {:spec, {:nu, f}} ->
        with {:ok, knd} <- nu_kind(f),
             :ok <- if(nu_body_prod?(f), do: :ok, else: {:error, "ν body is not a product"}),
             {:ok, _} <-
               check(
                 k,
                 book,
                 push_name(ext_rec(rs, false, false), "x"),
                 ext(gamma, :affine, knd),
                 :spec,
                 f,
                 Subst.wk(knd)
               ),
             :ok <-
               if(strict_pos?(f),
                 do: :ok,
                 else: {:error, "ν body is not strictly positive"}
               ),
             do: {:ok, {knd, u0s(n)}}

      {m, {:bisim, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: ~ is an erased term"}

      {:spec, {:bisim, s, t}} ->
        with {:ok, expanded} <- expand_bisim(k, book, rs, gamma, s, t),
             {:ok, _} <- check(k, book, rs, gamma, :spec, expanded, :typ),
             do: {:ok, {:typ, u0s(n)}}

      # ⇒-pair
      {m, {:pair, a, b}} ->
        with {:ok, {ta, au}} <- infer(k, book, rs, gamma, m, a),
             {:ok, {tb, bu}} <- infer(k, book, rs, gamma, m, b),
             {:ok, uses} <- combine(m, au, bu) do
          {:ok, {{:prod, ta, tb}, uses}}
        end

      # ⇒-letp: as ⇐-letp, but the body is inferred and its type must not
      # mention the two components (Subst.strengthen2).
      {m, {:letp, e, t}} ->
        with {:ok, {e_ty, eu}} <- infer(k, book, rs, gamma, m, e),
             {:ok, {a1, b1}} <- view_prod(k, book, e_ty, names_of(rs, gamma)),
             {:ok, {t_ty, [ub, ua | tus]}} <-
               infer(
                 k,
                 book,
                 push_name(push_name(ext_rec(ext_rec(rs, false, false), false, false), "a"), "b"),
                 ext(ext(gamma, :affine, a1), :affine, Subst.wk(b1)),
                 m,
                 t
               ),
             {:ok, c} <- Subst.strengthen2(t_ty),
             :ok <- check_bound(m, :affine, ub),
             :ok <- check_bound(m, :affine, ua),
             {:ok, uses} <- combine(m, eu, tus) do
          {:ok, {c, uses}}
        end

      # ⇒-unf
      {m, {:unf, seed, f}} ->
        with {:ok, {s_ty, seed_u}} <- infer(k, book, rs, gamma, m, seed),
             {:ok, {ft, fu}} <- infer(k, book, rs, gamma, m, f),
             {:ok, {_q, s1, body}} <- view_pi(k, book, ft, names_of(rs, gamma)),
             :ok <- conv(k, book, names_of(rs, gamma), s1, s_ty),
             {:ok, {a, s2}} <- view_prod(k, book, Subst.inst(body, seed), names_of(rs, gamma)),
             :ok <- conv(k, book, names_of(rs, gamma), s2, s_ty),
             :ok <- check_unfold(k, book, m, rs, f),
             {:ok, uses} <- combine(m, seed_u, fu) do
          {:ok, {{:nu, {:prod, Subst.wk(a), {:var, 0}}}, uses}}
        end

      # ⇒-ucons. The same step an unfold checks: a bare ν substitutes the
      # scrutinee's type for Y, and an applied family (Always, ~)
      # substitutes ν F for Y and keeps the indices.
      {m, {:ucons, s}} ->
        with {:ok, {tt, u}} <- infer(k, book, rs, gamma, m, s),
             {:ok, {goal, _fam}} <- unf_step(k, book, rs, gamma, tt, tt) do
          {:ok, {goal, u}}
        end

      # ⇒-i64 / ⇒-f32ty / ⇒-tensor
      {m, :i64} when m in [:run, :evidence] ->
        {:error, "no promotion: I64 is an erased term"}

      {m, :f32ty} when m in [:run, :evidence] ->
        {:error, "no promotion: F32 is an erased term"}

      {m, {:tensor, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: Tensor is an erased term"}

      {:spec, :i64} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, :f32ty} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, {:tensor, d, s}} ->
        with :ok <- check_ty(k, book, rs, gamma, d),
             :ok <- nx_dtype_ok(k, book, d),
             {:ok, _} <- check(k, book, rs, gamma, :spec, s, :i64) do
          {:ok, {:typ, u0s(n)}}
        end

      # ⇒-addi / ⇒-muli
      {m, {:addi, x, y}} ->
        with {:ok, xu} <- check(k, book, rs, gamma, m, x, :i64),
             {:ok, yu} <- check(k, book, rs, gamma, m, y, :i64),
             {:ok, uses} <- combine(m, xu, yu) do
          {:ok, {:i64, uses}}
        end

      {m, {:muli, x, y}} ->
        with {:ok, xu} <- check(k, book, rs, gamma, m, x, :i64),
             {:ok, yu} <- check(k, book, rs, gamma, m, y, :i64),
             {:ok, uses} <- combine(m, xu, yu) do
          {:ok, {:i64, uses}}
        end

      # ⇒-addt
      {m, {:addt, t, u}} ->
        with {:ok, {tt, tu}} <- infer(k, book, rs, gamma, m, t),
             {:ok, tt1} <- whnf(k, book, tt) do
          case tt1 do
            {:tensor, d, s} ->
              with {:ok, uu} <- check(k, book, rs, gamma, m, u, {:tensor, d, s}),
                   {:ok, uses} <- combine(m, tu, uu) do
                {:ok, {{:tensor, d, s}, uses}}
              end

            t1 ->
              {:error, "addt expected a Tensor, got #{Print.term(t1, names_of(rs, gamma))}"}
          end
        end

      # ⇒-toi64
      {m, {:toi64, n1}} ->
        with {:ok, u} <- check(k, book, rs, gamma, m, n1, :nat),
             do: {:ok, {:i64, u}}

      # ⇒-packi
      {m, {:packi, x, y}} ->
        with {:ok, xu} <- check(k, book, rs, gamma, m, x, :i64),
             {:ok, yu} <- check(k, book, rs, gamma, m, y, :i64),
             {:ok, uses} <- combine(m, xu, yu) do
          {:ok, {{:tensor, :i64, i64two()}, uses}}
        end

      {_, t1} ->
        {:error, "cannot infer #{shown(rs, gamma, t1)}"}
    end
  end

  # An application f a in evidence mode whose head is an evidence
  # definition instantiates a theorem: the argument is still checked in
  # the mode of the application, but its uses are not computational and
  # are discarded (Agda: Env.appUses / evidCall).
  defp evid_call?(book, :evidence, f) do
    case elem(apps(f), 0) do
      {:def, name} ->
        case lookup_def(book, name) do
          {:ok, %{mode: :evidence}} -> true
          _ -> false
        end

      _ ->
        false
    end
  end

  defp evid_call?(_book, _m, _f), do: false

  defp app_uses(book, m, f, fu, au) do
    if evid_call?(book, m, f), do: {:ok, fu}, else: combine(m, fu, au)
  end

  defp infer_arg(k, book, rs, gamma, m, :erased, a, fu, arg, _f) do
    with {:ok, _} <- check(k, book, rs, gamma, :spec, arg, a) do
      if m in [:run, :evidence], do: {:ok, fu}, else: {:ok, u0s(nctx(gamma))}
    end
  end

  defp infer_arg(k, book, rs, gamma, m, :affine, a, fu, arg, f) do
    with {:ok, au} <- check(k, book, rs, gamma, m, arg, a),
         do: app_uses(book, m, f, fu, au)
  end

  # Mark m1 has the affine quantity (Arrow.qty-affine): one use of the
  # argument, not erased and not scaled.
  defp infer_arg(k, book, rs, gamma, m, :linear, a, fu, arg, f) do
    infer_arg(k, book, rs, gamma, m, :affine, a, fu, arg, f)
  end

  defp infer_arg(k, book, rs, gamma, m, :reuse, a, fu, arg, f) do
    with {:ok, au} <- check(k, book, rs, gamma, m, arg, a),
         {:ok, au1} <- reuse_arg_uses(k, book, a, au),
         do: app_uses(book, m, f, fu, au1)
  end

  # A type is Type, a kind Π (x : A) → K, or a small type (⇒ Type).
  # Kinds are not small: Π (x : A) → Type is wf but has no type.
  # Syntax-directed, as ⊢ wf: a kind is recognised by its shape, anything
  # else must infer a type convertible to Type. (Reducing first would
  # accept terms that merely reduce to Type or to a kind, such as
  # (λ (x : Nat) → Type) 0, which have no derivation.)
  defp check_ty(k, book, rs, gamma, a) do
    case a do
      # type-Type
      :typ ->
        :ok

      # type-pi
      {:pi, q, a1, x, b} ->
        with :ok <- check_ty(k, book, rs, gamma, a1),
             do: check_ty(k, book, push_name(ext_rec(rs, false, false), x), ext(gamma, q, a1), b)

      # type-el
      a1 ->
        with {:ok, {t, _}} <- infer(k, book, rs, gamma, :spec, a1),
             do: conv(k, book, names_of(rs, gamma), t, :typ)
    end
  end

  defp check(k, book, rs, gamma, mode, e, a) do
    case e do
      {:hole, loc} ->
        {:error, Print.hole_message(loc, gamma, names_of(rs, gamma), a)}

      # ⇐-lam
      {:lam, q, a_ann, x, t} ->
        case view_pi(k, book, a, names_of(rs, gamma)) do
          {:ok, {q1, a1, b}} ->
            with :ok <- qty_agree(q, q1),
                 :ok <- check_ty(k, book, rs, gamma, a_ann),
                 :ok <- conv(k, book, names_of(rs, gamma), a_ann, a1),
                 :ok <-
                   if(q == :reuse,
                     do: guard_copy(k, book, a1),
                     else: :ok
                   ),
                 {:ok, [u0 | us]} <-
                   check(
                     k,
                     book,
                     push_name(lam_rec(rs), x),
                     ext(gamma, q, a1),
                     mode,
                     t,
                     b
                   ),
                 :ok <- check_bound(mode, q, u0) do
              {:ok, us}
            end

          {:error, _} ->
            infer_conv(k, book, rs, gamma, mode, e, a)
        end

      # ⇐-refl; not in run, so run code never builds a proof
      :rfl when mode == :run ->
        {:error, "no promotion: refl in run mode"}

      :rfl ->
        with {:ok, {sort, x, y}} <- view_id(k, book, a, names_of(rs, gamma)),
             :ok <- float_id_ok(k, book, sort),
             :ok <- conv(k, book, names_of(rs, gamma), x, y),
             do: {:ok, u0s(nctx(gamma))}

      # ⇐-pair
      {:pair, x, y} ->
        with {:ok, {a1, b1}} <- view_prod(k, book, a, names_of(rs, gamma)),
             {:ok, au} <- check(k, book, rs, gamma, mode, x, a1),
             {:ok, bu} <- check(k, book, rs, gamma, mode, y, b1),
             do: combine(mode, au, bu)

      # ⇐-letp: the scrutinee is inferred and read as a product; the body
      # is checked under two affine binders (a at 1, b at 0) against the
      # expected type weakened twice; each binder's uses are bounded and
      # the rest combined with the scrutinee's.
      {:letp, e, t} ->
        with {:ok, {e_ty, eu}} <- infer(k, book, rs, gamma, mode, e),
             {:ok, {a1, b1}} <- view_prod(k, book, e_ty, names_of(rs, gamma)),
             {:ok, [ub, ua | tus]} <-
               check(
                 k,
                 book,
                 push_name(push_name(ext_rec(ext_rec(rs, false, false), false, false), "a"), "b"),
                 ext(ext(gamma, :affine, a1), :affine, Subst.wk(b1)),
                 mode,
                 t,
                 Subst.wk(Subst.wk(a))
               ),
             :ok <- check_bound(mode, :affine, ub),
             :ok <- check_bound(mode, :affine, ua),
             do: combine(mode, eu, tus)

      # ⇐-unf. Bare ν substitutes the seed for Y (Stream). An applied
      # family substitutes ν F for Y and applies the indices, so the
      # recursive component is the predicate at the tail.
      {:unf, seed, {:lam, q, a_ann, x, t}} ->
        with {:ok, {s_ty, seed_u}} <- infer(k, book, rs, gamma, mode, seed),
             :ok <- conv(k, book, names_of(rs, gamma), a_ann, s_ty),
             {:ok, {goal, fam}} <- unf_step(k, book, rs, gamma, a, s_ty),
             :ok <- bare_stream(k, book, fam, a),
             :ok <- if(q == :reuse, do: guard_copy(k, book, s_ty), else: :ok),
             {:ok, [u0 | us]} <-
               check(
                 k,
                 book,
                 push_name(ext_rec(step_rec(rs, fam), false, false), x),
                 ext(gamma, q, s_ty),
                 mode,
                 t,
                 Subst.wk(goal)
               ),
             :ok <- check_bound(mode, q, u0),
             :ok <- check_unfold(k, book, mode, rs, {:lam, q, a_ann, x, t}),
             do: combine(mode, seed_u, us)

      {:unf, seed, f} ->
        with {:ok, {s_ty, seed_u}} <- infer(k, book, rs, gamma, mode, seed),
             {:ok, {goal, fam}} <- unf_step(k, book, rs, gamma, a, s_ty),
             :ok <- bare_stream(k, book, fam, a),
             {:ok, fu} <-
               check(
                 k,
                 book,
                 step_rec(rs, fam),
                 gamma,
                 mode,
                 f,
                 {:pi, :affine, s_ty, "_", Subst.wk(goal)}
               ),
             :ok <- check_unfold(k, book, mode, rs, f),
             do: combine(mode, seed_u, fu)

      # ⇐-ctor / ⇐-conv
      _ ->
        case {view_data(k, book, a, names_of(rs, gamma)), ctor_spine(book, e)} do
          {{:ok, {_d, dname, params, idxs}}, {:ok, {dname2, _ci, _args}}}
          when dname == dname2 ->
            expected = Subst.apps_from({:def, dname}, params ++ idxs)
            check_ctor_app(k, book, rs, gamma, mode, dname, params, e, expected)

          _ ->
            infer_conv(k, book, rs, gamma, mode, e, a)
        end
    end
  end

  # ⇐-conv: infer, then convert to the expected type.
  defp infer_conv(k, book, rs, gamma, mode, e, a) do
    with {:ok, {b, u}} <- infer(k, book, rs, gamma, mode, e),
         :ok <- conv(k, book, names_of(rs, gamma), b, a),
         do: {:ok, u}
  end

  # -- signature -------------------------------------------------------------

  defp fail_at(d, part, result) do
    case result do
      {:error, e} ->
        {:error, "#{Print.loc_prefix(Map.get(d, :loc))}#{d.name} #{part}: #{e}"}

      other ->
        other
    end
  end

  @doc """
  Check one definition of a de Bruijn book. `fuel` bounds reduction; running
  out is an error (`out of fuel …`), not a verdict.
  """
  def check_def(book, d, fuel \\ @fuel)

  # The other end is `Muro.Session.dual`. An omitted mark is the named
  # session's mark. A written mark that disagrees is refused. A cycle
  # of duals has no protocol.
  def check_def(book, %{kind: :session, name: name} = d, _fuel) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with :ok <- Muro.Session.decl_ok(d, book) do
      params = Map.get(d, :params, [])

      # A parameterised declaration is the template. It is opened at a use.
      # `dual` and `seen` still resolve, including a forward `dual`.
      if params != [] and not match?({:dual, _}, d.proto) and
           not match?({:seen, _, _, _}, d.proto) do
        :ok
      else
        case resolve_session(book, name, MapSet.new()) do
          {:ok, session} ->
            case Muro.Session.proto_ok(session.proto, book) do
              :ok -> :ok
              {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
            end

          {:error, msg} ->
            {:error, "#{loc}#{name}: #{msg}"}
        end
      end
    else
      {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
    end
  end

  # Muro.Session.decide, then `finishes` when the session is `%1`. The
  # evidence an evidence payload owes is decided there.
  # A protocol mismatch is reported before an abandoned linear channel.
  def check_def(book, %{kind: :conform, name: name, session: sname, proc: proc} = d, _fuel) do
    with {:ok, session} <- open_session(book, sname),
         :ok <- session_sits(book, session, proc, Map.get(d, :steps)) do
      :ok
    else
      {:error, at, msg} -> {:error, "#{Print.loc_prefix(at)}#{name}: #{msg}"}
      {:error, msg} -> {:error, "#{Print.loc_prefix(Map.get(d, :loc))}#{name}: #{msg}"}
    end
  end

  # A place is ambient or a node name. The node name is a string.
  def check_def(_book, %{kind: :place}, _fuel), do: :ok

  # A scheme is spec. `fixed` names a place declared in the book.
  def check_def(book, %{kind: :scheme, name: name, scheme: scheme} = d, _fuel) do
    case resolve_scheme(book, scheme) do
      {:ok, _} ->
        :ok

      {:error, msg} ->
        {:error, "#{Print.loc_prefix(Map.get(d, :loc))}#{name}: #{msg}"}
    end
  end

  # Muro.Place.conform. The stated mark is stay or cross. A mark whose
  # boundary disagrees with `bounds` is refused. A move is evidence.
  def check_def(book, %{kind: :move, mark: mark, scheme: sname, place: pname} = d, _fuel) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with {:ok, scheme} <- fetch_scheme(book, sname),
         {:ok, resolved} <- resolve_scheme(book, scheme.scheme),
         {:ok, placed} <- fetch_place(book, pname) do
      actual = Place.conform(resolved, placed.place)

      if actual == mark do
        :ok
      else
        {:error, "#{loc}expected #{actual}"}
      end
    else
      {:error, msg} -> {:error, "#{loc}#{msg}"}
    end
  end

  # Muro.Located. The endpoint is the session's mark, its protocol, and
  # the scheme. Spec holds that. The scheme's place must resolve.
  def check_def(book, %{kind: :endpoint, name: name, session: sname, scheme: sch} = d, _fuel) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with {:ok, _} <- open_session(book, sname),
         {:ok, scheme} <- fetch_scheme(book, sch),
         {:ok, _} <- resolve_scheme(book, scheme.scheme) do
      :ok
    else
      {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
    end
  end

  # Muro.Located.Sits. The process conforms, and `%1` finishes, before the
  # move is checked. The stated mark is stay or cross. A mark whose
  # boundary disagrees with `Place.conform` is refused. A reading is evidence.
  def check_def(
        book,
        %{kind: :read, name: name, mark: mark, endpoint: ename, place: pname, proc: proc} = d,
        _fuel
      ) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with {:ok, endpoint} <- fetch_endpoint(book, ename),
         {:ok, session} <- fetch_session(book, endpoint.session),
         {:ok, scheme} <- fetch_scheme(book, endpoint.scheme),
         {:ok, resolved} <- resolve_scheme(book, scheme.scheme),
         {:ok, placed} <- fetch_place(book, pname),
         :ok <- session_sits(book, session, proc, Map.get(d, :steps)),
         :ok <- move_sits(resolved, placed.place, mark) do
      :ok
    else
      {:error, at, msg} -> {:error, "#{Print.loc_prefix(at)}#{name}: #{msg}"}
      {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
    end
  end

  # Where a party of a description sits. The description expands, and
  # the place is declared. A party with no session may still sit.
  # A seat is spec.
  def check_def(book, %{kind: :seat, name: name, place: pname, talk: talk} = d, _fuel) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with {:ok, _} <- resolve_talk_name(book, talk, MapSet.new()),
         {:ok, _} <- fetch_place(book, pname) do
      :ok
    else
      {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
    end
  end

  # The boundary is `Place.decide` of the two places. Both seats are
  # that description, and the parties have a session, before the
  # stated mark is checked. The payload stays on the session. Evidence.
  def check_def(
        book,
        %{kind: :link, name: name, mark: mark, left: left, right: right, talk: talk} = d,
        _fuel
      ) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with {:ok, l} <- fetch_seat(book, left),
         {:ok, r} <- fetch_seat(book, right),
         :ok <- one_description(l.talk, r.talk, talk),
         {:ok, tree} <- resolve_talk_name(book, talk, MapSet.new()),
         {:ok, _} <- Muro.Talk.seen(l.party, r.party, tree),
         {:ok, lp} <- fetch_place(book, l.place),
         {:ok, rp} <- fetch_place(book, r.place),
         :ok <- boundary_sits(lp.place, rp.place, mark) do
      :ok
    else
      {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
    end
  end

  # The description expands. A name that refers to itself has no
  # description. A party with no session is refused on the session.
  # A talk is spec.
  def check_def(book, %{kind: :talk, name: name, body: body} = d, _fuel) do
    case expand_talk(book, body, MapSet.new([name])) do
      {:ok, _} ->
        :ok

      {:error, msg} ->
        {:error, "#{Print.loc_prefix(Map.get(d, :loc))}#{name}: #{msg}"}
    end
  end

  # Muro.Meet.decide when no buffer is written. Both names are processes.
  # The protocol of one is the other end of the other, and then the
  # payload types meet. A protocol that is not the other end is reported
  # before a type they do not share. `buffer N` is Muro.Async: the same
  # processes across two queues of that length. Those protocols need not
  # be dual. Each side still has to conform.
  def check_def(book, %{kind: :meet, name: name, left: left, right: right} = d, _fuel) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with {:ok, lp} <- fetch_process(book, left),
         {:ok, rp} <- fetch_process(book, right),
         :ok <- guard_sits(book, lp, left),
         :ok <- guard_sits(book, rp, right),
         {:ok, l} <- process_session(book, lp),
         {:ok, r} <- process_session(book, rp),
         :ok <- meet_ends(book, l, r, left, right, Map.get(d, :buffer)) do
      :ok
    else
      {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
    end
  end

  def check_def(book, %{kind: :data} = d, fuel), do: check_data(book, d, fuel)

  # Muro.Linear. The function is evidence. A linear endpoint is used
  # once. An affine endpoint is used at most once. The body is not a term.
  def check_def(book, %{kind: :relay} = d, _fuel), do: check_relay(book, d)

  def check_def(book, %{mode: mode, type: ty, body: body} = d, k) do
    with :ok <- fail_at(d, "type", check_ty(k, book, empty_rec(), [], ty)),
         :ok <- fail_at(d, "type", run_decl(k, book, mode, ty)),
         {:ok, _} <- fail_at(d, "body", check_body(k, book, d)),
         :ok <-
           fail_at(
             d,
             "productivity",
             check_nu(k, book, MapSet.put(component(book, d.name), d.name), mode, ty, body)
           ) do
      :ok
    end
  end

  defp meet_ends(book, l, r, _left, _right, nil) do
    with :ok <- other_end(l.proto, r.proto) do
      Muro.Meet.meets(l.proc, r.proc, book, l.proto)
    end
  end

  defp meet_ends(book, l, r, left, right, k) when is_integer(k) do
    Muro.Async.meets(l.proc, r.proc, book, k, left, right)
  end

  # The meeting is not a second report of a process that already failed.
  defp guard_sits(book, defn, name) do
    case sits_participant(book, defn) do
      :ok -> :ok
      _ -> {:error, "skipped because #{name} does not conform"}
    end
  end

  defp sits_participant(book, %{kind: :conform, session: sname, proc: proc} = d) do
    case open_session(book, sname) do
      {:ok, session} -> session_sits(book, session, proc, Map.get(d, :steps))
      err -> err
    end
  end

  defp sits_participant(book, %{kind: :read, endpoint: ename, proc: proc} = d) do
    with {:ok, endpoint} <- fetch_endpoint(book, ename),
         {:ok, session} <- fetch_session(book, endpoint.session) do
      session_sits(book, session, proc, Map.get(d, :steps))
    end
  end

  # `%1` is Mark lin. An unmarked session, and `%0`, are affine.
  defp linear_session?(session), do: Map.get(session, :mult, :affine) == :linear

  # Conforms, then Ends when the session is `%1`. A protocol mismatch is
  # reported before an abandoned channel. Mirrors `held` and `finished`.
  defp session_sits(book, session, proc, steps) do
    with :ok <- check_proc_vars(proc, MapSet.new(), book, steps),
         :ok <- Muro.Session.proc_ok(proc) do
      case Muro.Session.conform_at(proc, session.proto, book, steps) do
        :ok ->
          if linear_session?(session) and Muro.Session.finishes(proc) == :no do
            {:error, "linear channel abandoned"}
          else
            :ok
          end

        {:error, at, msg} when not is_nil(at) ->
          {:error, at, msg}

        {:error, _at, msg} ->
          {:error, msg}
      end
    end
  end

  # Check that all variables used in a process are bound.
  # A constructor of a declared data type is not a variable.
  defp check_proc_vars(proc, ctx, book, span)

  defp check_proc_vars(:done, _ctx, _book, _span), do: :ok
  defp check_proc_vars(:stop, _ctx, _book, _span), do: :ok

  defp check_proc_vars({:put, _ty, val, p}, ctx, book, span) do
    with :ok <- check_val_vars(val, ctx, book, Muro.Session.step_at(span)),
         do: check_proc_vars(p, ctx, book, Muro.Session.step_down(span, 0))
  end

  defp check_proc_vars({:get, _ty, name, p}, ctx, book, span) do
    # Anonymous binder _ doesn't add to context
    new_ctx = if name == :_, do: ctx, else: MapSet.put(ctx, name)
    check_proc_vars(p, new_ctx, book, Muro.Session.step_down(span, 0))
  end

  defp check_proc_vars({:pick0, p}, ctx, book, span),
    do: check_proc_vars(p, ctx, book, Muro.Session.step_down(span, 0))

  defp check_proc_vars({:pick1, p}, ctx, book, span),
    do: check_proc_vars(p, ctx, book, Muro.Session.step_down(span, 0))

  defp check_proc_vars({:cover, p, q}, ctx, book, span) do
    with :ok <- check_proc_vars(p, ctx, book, Muro.Session.step_down(span, 0)),
         do: check_proc_vars(q, ctx, book, Muro.Session.step_down(span, 1))
  end

  defp check_proc_vars({:iget, name, p, q}, ctx, book, span) do
    ctx1 = if name == :_, do: ctx, else: MapSet.put(ctx, name)

    with :ok <- check_proc_vars(p, ctx1, book, Muro.Session.step_down(span, 0)),
         do: check_proc_vars(q, ctx1, book, Muro.Session.step_down(span, 1))
  end

  # A recursion variable is not a payload. The value context is unchanged.
  defp check_proc_vars({:rec, _name, body}, ctx, book, span),
    do: check_proc_vars(body, ctx, book, Muro.Session.step_down(span, 0))

  defp check_proc_vars({:call, _name}, _ctx, _book, _span), do: :ok

  # The scrutinee is the value `get` just bound. Each arm is that continuation.
  # A named arm's binders are in scope in its body.
  defp check_proc_vars({:match, name, arms}, ctx, book, span) do
    if MapSet.member?(ctx, name) do
      arms
      |> Enum.with_index()
      |> Enum.reduce_while(:ok, fn {arm, i}, :ok ->
        case check_arm_vars(arm, ctx, book, Muro.Session.step_down(span, i)) do
          :ok -> {:cont, :ok}
          err -> {:halt, err}
        end
      end)
    else
      at_step(span, "match does not cover the received value")
    end
  end

  defp check_arm_vars({:arm, _ctor, binders, body}, ctx, book, span) when is_list(binders) do
    ctx1 = Enum.reduce(binders, ctx, &MapSet.put(&2, &1))
    check_proc_vars(body, ctx1, book, span)
  end

  defp check_arm_vars(arm, ctx, book, span), do: check_proc_vars(arm, ctx, book, span)

  # A bound name is in scope. An unbound name is in scope when it is a
  # constructor. Conformance then decides whether that constructor
  # inhabits the payload.
  defp check_val_vars(val, ctx, book, at)

  defp check_val_vars({:var, name}, ctx, book, at) do
    label = ctor_label(name)

    cond do
      MapSet.member?(ctx, name) -> :ok
      ctor_name?(book, label) -> :ok
      run_def?(book, label) -> :ok
      evidence_def?(book, label) -> at_step(at, "evidence is not a value")
      term_def?(book, label) -> at_step(at, "#{label} is not a run definition")
      true -> at_step(at, "unbound variable #{name}")
    end
  end

  defp check_val_vars({:con, name, args}, ctx, book, at) when is_list(args) do
    cond do
      ctor_name?(book, name) or run_def?(book, name) ->
        Enum.reduce_while(args, :ok, fn arg, :ok ->
          case check_val_vars(arg, ctx, book, at) do
            :ok -> {:cont, :ok}
            err -> {:halt, err}
          end
        end)

      evidence_def?(book, name) ->
        at_step(at, "evidence is not a value")

      term_def?(book, name) ->
        at_step(at, "#{name} is not a run definition")

      true ->
        at_step(at, "unbound variable #{name}")
    end
  end

  defp check_val_vars({:nat, _}, _ctx, _book, _at), do: :ok
  defp check_val_vars(:b0, _ctx, _book, _at), do: :ok
  defp check_val_vars(:b1, _ctx, _book, _at), do: :ok
  defp check_val_vars(:tt, _ctx, _book, _at), do: :ok

  defp check_val_vars({:tup, a, b}, ctx, book, at) do
    with :ok <- check_val_vars(a, ctx, book, at), do: check_val_vars(b, ctx, book, at)
  end

  defp check_val_vars({:rec, fields}, ctx, book, at) when is_list(fields) do
    Enum.reduce_while(fields, :ok, fn {_name, val}, :ok ->
      case check_val_vars(val, ctx, book, at) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp check_val_vars({:rep, ix, elem}, ctx, book, at) do
    with :ok <- check_val_vars(ix, ctx, book, at), do: check_val_vars(elem, ctx, book, at)
  end

  defp check_val_vars(_, _ctx, _book, _at), do: :ok

  # `at` is a `{line, col}` of the step, or a span, or nil for the definition.
  defp at_step(%{at: at}, msg), do: at_step(at, msg)

  defp at_step({line, col}, msg) when is_integer(line) and is_integer(col),
    do: {:error, {line, col}, msg}

  defp at_step({file, line, col}, msg) when is_binary(file), do: {:error, {file, line, col}, msg}
  defp at_step(_, msg), do: {:error, msg}

  defp evidence_def?(book, name) do
    Enum.any?(book, fn d ->
      Map.get(d, :name) == name and Map.get(d, :mode) == :evidence and term_def?(d)
    end)
  end

  defp ctor_label(name) when is_atom(name), do: Atom.to_string(name)
  defp ctor_label(name) when is_binary(name), do: name
  defp ctor_label(_), do: ""

  # The boundary is `Place.conform`. The payload stays on the session.
  defp move_sits(scheme, place, mark) do
    actual = Place.conform(scheme, place)

    if actual == mark do
      :ok
    else
      {:error, "expected #{actual}"}
    end
  end

  # Ground the declared sessions, then `Muro.Linear.check`. A closed
  # endpoint function is its declared type. Its body is not unfolded.
  defp check_relay(book, %{name: name, type: ty, body: body} = d) do
    loc = Print.loc_prefix(Map.get(d, :loc))

    with {:ok, protos} <- session_protos(book),
         relays = relay_types(book, protos),
         {:ok, ty} <- Muro.Linear.ground_ty(protos, ty),
         {:ok, body} <- Muro.Linear.ground_tm(protos, body),
         :ok <- Muro.Linear.check(relays, ty, body) do
      :ok
    else
      {:error, msg} -> {:error, "#{loc}#{name}: #{msg}"}
    end
  end

  defp session_protos(book) do
    Enum.reduce_while(book, {:ok, %{}}, fn
      %{kind: :session, name: name} = s, {:ok, acc} ->
        if Map.get(s, :params, []) != [] do
          {:cont, {:ok, Map.put(acc, name, :arity)}}
        else
          case fetch_session(book, name) do
            {:ok, %{proto: proto}} -> {:cont, {:ok, Map.put(acc, name, proto)}}
            {:error, msg} -> {:halt, {:error, msg}}
          end
        end

      _, acc ->
        {:cont, acc}
    end)
  end

  defp relay_types(book, protos) do
    Enum.flat_map(book, fn
      %{kind: :relay, name: name, type: ty} ->
        case Muro.Linear.ground_ty(protos, ty) do
          {:ok, gty} -> [{name, gty}]
          _ -> []
        end

      _ ->
        []
    end)
  end

  defp fetch_session(book, name), do: resolve_session(book, name, MapSet.new())

  # Walk `dual` to a protocol. The mark of an omitted dual is the mark
  # at the end of that walk. `dual (dual S)` is `S`. A `seen` session is
  # the protocol one party has with another in the description. Its mark
  # is the mark written on the session. The talk cycle is its own set.
  defp resolve_session(book, name, seen) do
    if MapSet.member?(seen, name) do
      {:error, "dual cycle"}
    else
      case Enum.find(book, &(Map.get(&1, :kind) == :session and &1.name == name)) do
        nil ->
          {:error, "unknown session #{name}"}

        %{proto: {:dual, other}} = s ->
          with {:ok, base} <- resolve_dual_target(book, other, MapSet.put(seen, name)),
               {:ok, mark} <- agreed_mark(s.mult, base.mult) do
            {:ok, %{s | proto: Muro.Session.dual(base.proto), mult: mark, params: []}}
          end

        %{proto: {:seen, p, q, talk}} = s ->
          with {:ok, tree} <- resolve_talk_name(book, talk, MapSet.new()),
               {:ok, proto} <- Muro.Talk.seen(p, q, tree) do
            {:ok, %{s | proto: proto}}
          end

        s ->
          cond do
            Map.get(s, :params, []) != [] ->
              {:error, "wrong number of session arguments"}

            true ->
              case Muro.Session.elaborate(s, book) do
                {:ok, proto} -> {:ok, %{s | proto: proto}}
                {:error, _} = err -> err
              end
          end
      end
    end
  end

  # `dual ping` may name a later session. `dual (stream 0)` opens that call.
  defp resolve_dual_target(book, name, seen) when is_binary(name) do
    resolve_session(book, name, seen)
  end

  defp resolve_dual_target(book, {:sess, name, args}, _seen) do
    Muro.Session.open_applied(book, name, args)
  end

  defp resolve_dual_target(_book, _, _), do: {:error, "unknown session"}

  defp open_session(book, name) when is_binary(name),
    do: resolve_session(book, name, MapSet.new())

  defp open_session(book, {:sess, name, args}) do
    Muro.Session.open_applied(book, name, args)
  end

  # Names expand before `seen`. Two names of one body are one description.
  # The stack is the talks currently being expanded, not the dual walk.
  defp resolve_talk_name(book, name, stack) do
    if MapSet.member?(stack, name) do
      {:error, "talk cycle"}
    else
      case Enum.find(book, &(Map.get(&1, :kind) == :talk and &1.name == name)) do
        nil ->
          {:error, "unknown talk #{name}"}

        %{body: body} ->
          expand_talk(book, body, MapSet.put(stack, name))
      end
    end
  end

  defp expand_talk(_book, :over, _stack), do: {:ok, :over}

  # `say` names one payload type and one continuation. `offer` still
  # has two arms. A name expands to the tree it stands for.
  defp expand_talk(book, {:say, a, b, ty, t}, stack) do
    with {:ok, u} <- expand_talk(book, t, stack) do
      {:ok, {:say, a, b, ty, u}}
    end
  end

  defp expand_talk(book, {:offer, a, b, t0, t1}, stack) do
    with {:ok, u0} <- expand_talk(book, t0, stack),
         {:ok, u1} <- expand_talk(book, t1, stack) do
      {:ok, {:offer, a, b, u0, u1}}
    end
  end

  defp expand_talk(book, {:ref, name}, stack), do: resolve_talk_name(book, name, stack)

  defp agreed_mark(:inherit, mark), do: {:ok, mark}
  defp agreed_mark(mark, mark), do: {:ok, mark}
  defp agreed_mark(_stated, actual), do: {:error, "expected #{show_mark(actual)}"}

  defp show_mark(:linear), do: "%1"
  defp show_mark(:affine), do: "%0"

  # One direction is enough: `dual` is an involution.
  # The first step where the right protocol is not that dual is the refusal.
  defp other_end(proto, other), do: ends_walk(proto, other, [])

  defp ends_walk(left, right, path) do
    if right == Muro.Session.dual(left) do
      :ok
    else
      case peel_ends(left, right) do
        {:one, label, l, r} ->
          ends_walk(l, r, path ++ [label])

        {:two, label, l0, r0, l1, r1} ->
          case ends_walk(l0, r0, path ++ [label, "arm b0"]) do
            :ok -> ends_walk(l1, r1, path ++ [label, "arm b1"])
            err -> err
          end

        {:many, label, pairs} ->
          Enum.reduce_while(pairs, :ok, fn {arm, l, r}, :ok ->
            case ends_walk(l, r, path ++ [label, "arm #{arm}"]) do
              :ok -> {:cont, :ok}
              err -> {:halt, err}
            end
          end)

        :diff ->
          {:error, proto_diverged(left, right, path)}
      end
    end
  end

  defp proto_diverged(left, right, path) do
    where = if path == [], do: "", else: " after " <> Enum.join(path, ", ")

    "diverged#{where}: left: #{Muro.Session.step_proto(left)}; right: #{Muro.Session.step_proto(right)}; protocol: #{Muro.Session.show_proto(left)}"
  end

  defp peel_ends({:send, a, s}, {:recv, a, t}), do: {:one, "send #{pay_atom(a)}", s, t}
  defp peel_ends({:recv, a, s}, {:send, a, t}), do: {:one, "recv #{pay_atom(a)}", s, t}

  defp peel_ends({:dsend, x, a, {:case, sl, arms}}, {:drecv, x, a, {:case, sr, arms2}}) do
    peel_case("send", x, a, sl, sr, arms, arms2)
  end

  defp peel_ends({:drecv, x, a, {:case, sl, arms}}, {:dsend, x, a, {:case, sr, arms2}}) do
    peel_case("recv", x, a, sl, sr, arms, arms2)
  end

  defp peel_ends({:dsend, x, a, s}, {:drecv, x, a, t}), do: {:one, dep_label("send", x, a), s, t}
  defp peel_ends({:drecv, x, a, s}, {:dsend, x, a, t}), do: {:one, dep_label("recv", x, a), s, t}
  defp peel_ends({:esend, x, e, s}, {:erecv, x, e, t}), do: {:one, ev_label("send", x, e), s, t}
  defp peel_ends({:erecv, x, e, s}, {:esend, x, e, t}), do: {:one, ev_label("recv", x, e), s, t}

  defp peel_ends({:choose, s, t}, {:branch, u, v}), do: {:two, "choose", s, u, t, v}
  defp peel_ends({:branch, s, t}, {:choose, u, v}), do: {:two, "branch", s, u, t, v}

  defp peel_ends({:isend, x, s, t}, {:irecv, x, u, v}),
    do: {:two, "send (#{x} : Bit)", s, u, t, v}

  defp peel_ends({:irecv, x, s, t}, {:isend, x, u, v}),
    do: {:two, "recv (#{x} : Bit)", s, u, t, v}

  defp peel_ends({:rec, x, s}, {:rec, x, t}), do: {:one, "rec #{x}", s, t}
  defp peel_ends(_, _), do: :diff

  defp peel_case(dir, x, a, sl, sr, arms, arms2) do
    left = Enum.map(arms, fn {c, s} -> {c, s} end)
    right = Enum.map(arms2, fn {c, s} -> {c, s} end)

    if sl == sr and Enum.map(left, &elem(&1, 0)) == Enum.map(right, &elem(&1, 0)) do
      pairs =
        Enum.zip(left, right)
        |> Enum.map(fn {{c, s}, {_c, t}} -> {c, s, t} end)

      {:many, dep_label(dir, x, a), pairs}
    else
      :diff
    end
  end

  defp pay_atom(ty),
    do: Muro.Session.step_proto({:send, ty, :end}) |> String.replace_prefix("send ", "")

  defp dep_label(dir, x, a), do: "#{dir} (#{x} : #{pay_atom(a)})"

  defp ev_label(dir, x, e),
    do: Muro.Session.step_proto({if(dir == "send", do: :esend, else: :erecv), x, e, :end})

  defp fetch_process(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) in [:conform, :read] and &1.name == name)) do
      nil -> {:error, "unknown process #{name}"}
      p -> {:ok, p}
    end
  end

  defp process_session(book, %{kind: :conform, session: sname, proc: proc}) do
    with {:ok, session} <- open_session(book, sname) do
      {:ok, %{proc: proc, proto: session.proto}}
    end
  end

  defp process_session(book, %{kind: :read, endpoint: ename, proc: proc}) do
    with {:ok, endpoint} <- fetch_endpoint(book, ename),
         {:ok, session} <- fetch_session(book, endpoint.session) do
      {:ok, %{proc: proc, proto: session.proto}}
    end
  end

  defp fetch_endpoint(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :endpoint and &1.name == name)) do
      nil -> {:error, "unknown endpoint #{name}"}
      e -> {:ok, e}
    end
  end

  defp fetch_place(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :place and &1.name == name)) do
      nil -> {:error, "unknown place #{name}"}
      p -> {:ok, p}
    end
  end

  defp fetch_seat(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :seat and &1.name == name)) do
      nil -> {:error, "unknown seat #{name}"}
      s -> {:ok, s}
    end
  end

  # Both seats are the description the link names.
  defp one_description(talk, talk, talk), do: :ok
  defp one_description(_left, _right, _talk), do: {:error, "expected one description"}

  # `decide` of the two places. The same place stays. Two places cross once.
  defp boundary_sits(p, q, mark) do
    actual = Place.decide(p, q)

    if actual == mark do
      :ok
    else
      {:error, "expected #{actual}"}
    end
  end

  defp fetch_scheme(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :scheme and &1.name == name)) do
      nil -> {:error, "unknown scheme #{name}"}
      s -> {:ok, s}
    end
  end

  defp resolve_scheme(_book, :any), do: {:ok, :any}

  defp resolve_scheme(book, {:fixed, pname}) do
    case fetch_place(book, pname) do
      {:ok, %{place: p}} -> {:ok, {:fixed, p}}
      {:error, _} = err -> err
    end
  end

  # A run definition has a run type, used or not (Agda: runDecl).
  defp run_decl(k, book, :run, ty) do
    case run_ty(k, book, ty) do
      {:ok, true} -> :ok
      {:ok, false} -> {:error, "no promotion: a run definition has a spec type"}
      err -> err
    end
  end

  defp run_decl(_k, _book, _mode, _ty), do: :ok

  # Run, evidence, and spec definitions that reach each other are one
  # block and descend on one shared argument (Agda: component).
  defp rec_mode?(mode), do: mode in [:run, :evidence, :spec]

  # A session, a conformance, a place, a scheme, a move, an endpoint, a
  # reading, a meeting, a description, a seat, and a link have a mode
  # and no term, so they are outside the descent block.
  defp rec_names(book) do
    for %{mode: mode, name: name} = d <- book,
        rec_mode?(mode),
        Map.get(d, :kind) not in [
          :session,
          :conform,
          :place,
          :scheme,
          :move,
          :endpoint,
          :read,
          :meet,
          :talk,
          :seat,
          :link,
          :relay
        ],
        do: name
  end

  defp mentions(t), do: mentions(t, []) |> Enum.uniq()

  defp mentions({:def, n}, acc), do: [n | acc]
  defp mentions({:app, f, a}, acc), do: mentions(a, mentions(f, acc))
  defp mentions({:pi, _, a, _, b}, acc), do: mentions(b, mentions(a, acc))
  defp mentions({:lam, _, a, _, t}, acc), do: mentions(t, mentions(a, acc))
  defp mentions({:su, t}, acc), do: mentions(t, acc)
  defp mentions({:prod, a, b}, acc), do: mentions(b, mentions(a, acc))
  defp mentions({:pair, a, b}, acc), do: mentions(b, mentions(a, acc))
  defp mentions({:letp, e, t}, acc), do: mentions(t, mentions(e, acc))
  defp mentions({:unf, s, f}, acc), do: mentions(f, mentions(s, acc))
  defp mentions({:ucons, s}, acc), do: mentions(s, acc)
  defp mentions({:nu, f}, acc), do: mentions(f, acc)
  defp mentions({:bisim, s, t}, acc), do: mentions(t, mentions(s, acc))
  defp mentions({:ann, e, a}, acc), do: mentions(a, mentions(e, acc))
  defp mentions({:idt, a, x, y}, acc), do: mentions(y, mentions(x, mentions(a, acc)))
  defp mentions({:rwt, e, p, t}, acc), do: mentions(t, mentions(p, mentions(e, acc)))
  defp mentions({:tensor, d, s}, acc), do: mentions(s, mentions(d, acc))
  defp mentions({:addi, x, y}, acc), do: mentions(y, mentions(x, acc))
  defp mentions({:muli, x, y}, acc), do: mentions(y, mentions(x, acc))
  defp mentions({:addt, t, u}, acc), do: mentions(u, mentions(t, acc))
  defp mentions({:toi64, t}, acc), do: mentions(t, acc)
  defp mentions({:packi, x, y}, acc), do: mentions(y, mentions(x, acc))

  defp mentions({:matom, e, p, bs}, acc) do
    acc = mentions(p, mentions(e, acc))
    Enum.reduce(bs, acc, fn {_, b}, acc -> mentions(b, acc) end)
  end

  defp mentions({:mdata, e, p, bs}, acc) do
    acc = mentions(p, mentions(e, acc))
    Enum.reduce(bs, acc, fn {_, _, b}, acc -> mentions(b, acc) end)
  end

  defp mentions({:mnat, e, p, z, s}, acc),
    do: mentions(s, mentions(z, mentions(p, mentions(e, acc))))

  defp mentions({:memp, e, p}, acc), do: mentions(p, mentions(e, acc))

  defp mentions({:munit, e, p, u}, acc), do: mentions(u, mentions(p, mentions(e, acc)))

  defp mentions(_, acc), do: acc

  defp rec_callees(book, name, names) do
    case Enum.find(book, &(&1[:name] == name and rec_mode?(&1[:mode]))) do
      nil -> []
      d -> mentions(Map.get(d, :body)) |> Enum.filter(&(&1 in names))
    end
  end

  defp reaches?(edges, src, tgt), do: walk(edges, src, tgt, MapSet.new())

  defp walk(_edges, cur, tgt, _vis) when cur == tgt, do: true

  defp walk(edges, cur, tgt, vis) do
    if MapSet.member?(vis, cur) do
      false
    else
      vis = MapSet.put(vis, cur)
      Enum.any?(Map.get(edges, cur, []), &walk(edges, &1, tgt, vis))
    end
  end

  defp component(book, name) do
    names = rec_names(book)
    edges = Map.new(names, fn n -> {n, rec_callees(book, n, names)} end)

    names
    |> Enum.filter(fn j -> reaches?(edges, name, j) and reaches?(edges, j, name) end)
    |> MapSet.new()
  end

  # The candidate assignments of the block: a non-erased position for each
  # member, members in book order, the first member's choice first. Empty
  # when a member has none (Agda: sharedArgs, choices).
  defp shared_positions(book, block) do
    members =
      Enum.filter(book, fn d ->
        name = Map.get(d, :name)
        name != nil and rec_mode?(d[:mode]) and MapSet.member?(block, name)
      end)

    case members do
      [] -> []
      _ -> members |> Enum.map(&{&1.name, arg_positions(&1.type, 0)}) |> choices()
    end
  end

  defp choices([]), do: [%{}]

  defp choices([{name, ps} | rest]) do
    tails = choices(rest)
    for p <- ps, t <- tails, do: Map.put(t, name, p)
  end

  defp book_order(book, block) do
    book
    |> Enum.with_index()
    |> Enum.filter(fn {d, _} -> MapSet.member?(block, d[:name]) end)
    |> Map.new(fn {d, i} -> {d.name, i} end)
  end

  defp all_ok?(k, book, block, order, poss) do
    Enum.all?(book, fn d ->
      name = Map.get(d, :name)

      if name != nil and rec_mode?(d[:mode]) and MapSet.member?(block, name) do
        match?(
          {:ok, _},
          check(k, book, def_rec(name, poss, block, order), [], d.mode, d.body, d.type)
        )
      else
        true
      end
    end)
  end

  defp find_pos(_k, _book, _block, _order, []), do: nil

  defp find_pos(k, book, block, order, [poss | rest]) do
    if all_ok?(k, book, block, order, poss),
      do: poss,
      else: find_pos(k, book, block, order, rest)
  end

  defp mutual_block?(block), do: MapSet.size(block) > 1

  defp choose_positions(k, book, block, order, pss) do
    case find_pos(k, book, block, order, pss) do
      nil -> if mutual_block?(block), do: [], else: pss
      poss -> [poss]
    end
  end

  # No assignment works for a block of two or more. The first candidate is
  # checked so its error is the one reported. A success there is still an
  # error: that member passed under an assignment another member fails
  # (Agda: refuseShared).
  defp refuse_shared(at, [poss | _]) do
    case at.(poss) do
      {:error, msg} -> {:error, msg}
      {:ok, _} -> {:error, @no_descent}
    end
  end

  # The body is checked under the first assignment that works for the
  # whole block. A single definition keeps its later candidates, and the
  # first failure is the one reported. A block of two or more with no such
  # assignment is refused. A definition with no self-call passes the first
  # attempt. The assignment only affects the descent check, so a type
  # error is the same for every one (Agda: checkBody). Spec descends on
  # the same positions as run and evidence.
  defp check_body(k, book, %{name: name, mode: mode, type: ty, body: body}) do
    block = if(rec_mode?(mode), do: component(book, name), else: MapSet.new([name]))
    order = book_order(book, block)

    shared =
      if rec_mode?(mode),
        do: shared_positions(book, block),
        else: Enum.map(arg_positions(ty, 0), &%{name => &1})

    positions =
      if rec_mode?(mode) do
        choose_positions(k, book, block, order, shared)
      else
        shared
      end

    at = fn poss -> check(k, book, def_rec(name, poss, block, order), [], mode, body, ty) end

    cond do
      rec_mode?(mode) and mutual_block?(block) and shared != [] and positions == [] ->
        refuse_shared(at, shared)

      positions == [] ->
        at.(Map.new(block, &{&1, 0}))

      true ->
        [p | ps] = positions

        case at.(p) do
          {:ok, u} -> {:ok, u}
          {:error, msg} -> retry_body(at, msg, ps)
        end
    end
  end

  defp retry_body(_at, msg, []), do: {:error, msg}

  defp retry_body(at, msg, [p | ps]) do
    case at.(p) do
      {:ok, u} -> {:ok, u}
      {:error, _} -> retry_body(at, msg, ps)
    end
  end

  @doc """
  Check a named book. Options: `fuel: n` (default `default_fuel/0`).

  Each definition is checked against the whole book, on its own process,
  with that same fuel. `:ok` means every definition checked. `{:error, msg}`
  is every failure, in book order, separated by a blank line. Fuel is the
  only bound; a definition is not cut off by a wall-clock timeout.
  """
  def check_sig(named_book, opts \\ []) do
    fuel = Keyword.get(opts, :fuel, @fuel)

    with {:ok, book} <- Ast.book_to_db(named_book) do
      errors =
        book
        |> Task.async_stream(fn d -> check_def(book, d, fuel) end,
          ordered: true,
          timeout: :infinity
        )
        |> Enum.flat_map(fn
          {:ok, :ok} -> []
          {:ok, {:error, msg}} -> [msg]
          {:exit, reason} -> exit(reason)
        end)

      case errors do
        [] -> :ok
        msgs -> {:error, Enum.join(msgs, "\n\n")}
      end
    end
  end

  defp rwt_mode(:spec), do: :spec
  defp rwt_mode(_), do: :evidence

  defp match_arity(bs, ctors) do
    if length(bs) == length(ctors) do
      :ok
    else
      {:error, "match branch count does not match constructors"}
    end
  end

  defp dty_type(params, indices) do
    idx_pis =
      Enum.reduce(Enum.reverse(indices), :typ, fn {q, x, a}, acc ->
        {:pi, q, a, x, acc}
      end)

    Enum.reduce(Enum.reverse(params), idx_pis, fn {q, x, _a}, acc ->
      {:pi, q, :typ, x, acc}
    end)
  end

  defp inst_params(_k, _book, t, []), do: {:ok, t}

  defp inst_params(k, book, t, [p | ps]) do
    case whnf(k, book, t) do
      {:ok, {:pi, _, _, _, b}} -> inst_params(k, book, Subst.inst(b, p), ps)
      {:ok, _} -> {:error, "constructor type has too few parameter binders"}
      err -> err
    end
  end

  # ⇐-ctor: a constructor spine against the data type dname at params. The
  # spine is walked from the head (Agda: inferCtorSpine): the constructor's
  # type instantiated at the parameters, then one Π per argument; an erased
  # field is checked in spec and contributes no uses.
  defp infer_ctor_spine(k, book, _rs, gamma, _m, dname, params, {:def, cname}) do
    case lookup_ctor(book, cname) do
      {:ok, {_d, dn, _ci, c}} when dn == dname ->
        with {:ok, rest} <- inst_params(k, book, c.type, params),
             do: {:ok, {rest, u0s(nctx(gamma))}}

      {:ok, _} ->
        {:error, "constructor of another data type"}

      err ->
        err
    end
  end

  defp infer_ctor_spine(k, book, rs, gamma, m, dname, params, {:app, f, a}) do
    with {:ok, {ty, fu}} <- infer_ctor_spine(k, book, rs, gamma, m, dname, params, f),
         {:ok, ty1} <- whnf(k, book, ty) do
      case ty1 do
        {:pi, q, a_ty, _, b} ->
          with {:ok, au} <- check(k, book, rs, gamma, field_mode(q, m), a, a_ty),
               {:ok, au1} <- field_uses(k, book, q, a_ty, au),
               {:ok, uses} <- combine_arg(q, m, au1, fu),
               do: {:ok, {Subst.inst(b, a), uses}}

        _ ->
          {:error, "too many constructor arguments"}
      end
    end
  end

  defp infer_ctor_spine(_k, _book, _rs, _gamma, _m, _dname, _params, _e),
    do: {:error, "not a constructor spine"}

  # Agda's fieldUses: a + field scales as a + argument does.
  defp field_uses(k, book, :reuse, a_ty, au), do: reuse_arg_uses(k, book, a_ty, au)
  defp field_uses(_k, _book, _q, _a_ty, au), do: {:ok, au}

  defp field_mode(:erased, _m), do: :spec
  defp field_mode(_q, m), do: m

  defp combine_arg(:erased, :spec, _au, fu), do: {:ok, u0s(length(fu))}
  defp combine_arg(:erased, _m, _au, fu), do: {:ok, fu}
  defp combine_arg(_q, m, au, fu), do: combine(m, au, fu)

  # After the arguments, the residual telescope must be exhausted and be
  # the expected data type.
  defp check_ctor_app(k, book, rs, gamma, m, dname, params, e, expected) do
    with {:ok, {r, u}} <- infer_ctor_spine(k, book, rs, gamma, m, dname, params, e),
         {:ok, r1} <- whnf(k, book, r) do
      case r1 do
        {:pi, _, _, _, _} -> {:error, "too few constructor arguments"}
        _ -> with :ok <- conv(k, book, names_of(rs, gamma), r1, expected), do: {:ok, u}
      end
    end
  end

  defp check_atom_arms(k, book, rs, gamma, m, p, bs) do
    wanted = Ast.atoms(book)
    got = Enum.map(bs, fn {n, _} -> n end)

    cond do
      dup = Enum.find(got, fn n -> Enum.count(got, &(&1 == n)) > 1 end) ->
        {:error, "duplicate branch for :#{dup}"}

      missing = Enum.find(wanted, &(&1 not in got)) ->
        {:error, "missing branch for :#{missing}"}

      true ->
        Enum.reduce_while(bs, {:ok, u0s(nctx(gamma))}, fn {name, body}, {:ok, acc} ->
          case check(k, book, rs, gamma, m, body, Subst.inst(p, {:atom, name})) do
            {:ok, u} -> {:cont, {:ok, combine_alt(m, acc, u)}}
            err -> {:halt, err}
          end
        end)
    end
  end

  defp check_branches(_k, _book, _rs, gamma, _m, _dname, _sm, _params, _idxs, _mot, [], []) do
    {:ok, u0s(nctx(gamma))}
  end

  defp check_branches(k, book, rs, gamma, m, dname, sm, params, idxs, mot, [c | cs], bs) do
    with {:ok, rest} <- inst_params(k, book, c.type, params) do
      np = nparams_of(book, dname)

      case clashes(k, book, np, idxs, rest) do
        {:error, e} ->
          {:error, e}

        # a clash: the constructor cannot produce the scrutinee's indices,
        # its branch is consumed and not checked
        {:ok, true} ->
          case bs do
            [] ->
              {:error, "missing branch for #{c.name}"}

            [{bname, ar, _body} | bs1] ->
              case branch_arity(bname, ar, rest) do
                :ok ->
                  check_branches(k, book, rs, gamma, m, dname, sm, params, idxs, mot, cs, bs1)

                err ->
                  err
              end
          end

        {:ok, false} ->
          case bs do
            [] ->
              {:error, "missing branch for #{c.name}"}

            [{bname, ar, body} | bs1] ->
              cond do
                bname != c.name ->
                  {:error, "expected constructor #{c.name}, got #{bname}"}

                true ->
                  case branch_arity(bname, ar, rest) do
                    :ok ->
                      wrapped = wrap_tel(rest, body)

                      with {:ok, u} <-
                             check_br(
                               k,
                               book,
                               rs,
                               gamma,
                               m,
                               dname,
                               c.name,
                               sm,
                               rest,
                               wrapped,
                               mot,
                               []
                             ),
                           {:ok, v} <-
                             check_branches(
                               k,
                               book,
                               rs,
                               gamma,
                               m,
                               dname,
                               sm,
                               params,
                               idxs,
                               mot,
                               cs,
                               bs1
                             ) do
                        {:ok, combine_alt(m, u, v)}
                      end

                    err ->
                      err
                  end
              end
          end
      end
    end
  end

  defp check_branches(_, _, _, _, _, _, _, _, _, _, [], [_ | _]),
    do: {:error, "match branch count does not match constructors"}

  defp wrap_tel({:pi, q, a, x, b}, body), do: {:lam, q, a, x, wrap_tel(b, body)}
  defp wrap_tel(_, body), do: body

  # Erased and non-erased binders both count: wrap_tel adds one λ per Π.
  defp pi_count({:pi, _, _, _, b}), do: 1 + pi_count(b)
  defp pi_count(_), do: 0

  defp branch_arity(bname, ar, rest) do
    n = pi_count(rest)

    if ar == n do
      :ok
    else
      {:error, "branch #{bname} binds #{ar} variables, constructor has #{n} fields"}
    end
  end

  defp nparams_of(book, dname) do
    case lookup_data(book, dname) do
      {:ok, d} -> length(d.params)
      _ -> 0
    end
  end

  # A branch of match against the constructor's telescope ty: one λ per
  # Π, then the body against the motive at the constructor's own target
  # indices and the constructor applied to the arguments (Agda: checkBr /
  # checkBrPi). sm: the scrutinee is a variable a self-call may descend on
  # (scrut_ok), so a field of type D … is smaller; the fields of a
  # computed scrutinee are not smaller than anything.
  defp check_br(k, book, rs, gamma, m, dname, cname, sm, ty, br, mot, args) do
    with {:ok, ty1} <- whnf(k, book, ty) do
      check_br_n(k, book, rs, gamma, m, dname, cname, sm, ty1, br, mot, args)
    end
  end

  defp check_br_n(k, book, rs, gamma, m, dname, cname, sm, ty1, br, mot, args) do
    case ty1 do
      {:pi, q, a, _, b} ->
        case br do
          {:lam, q1, a1, x, t} ->
            rec? = sm and is_d_type?(book, dname, a)
            rs2 = push_name(ext_rec(rs, rec?, rec?), x)
            args1 = Enum.map(args, &Subst.wk/1) ++ [{:var, 0}]

            with :ok <- qty_agree(q, q1),
                 :ok <- check_ty(k, book, rs, gamma, a1),
                 :ok <- conv(k, book, names_of(rs, gamma), a1, a),
                 :ok <- if(q == :reuse, do: guard_copy(k, book, a1), else: :ok),
                 {:ok, [u0 | us]} <-
                   check_br(
                     k,
                     book,
                     rs2,
                     ext(gamma, q, a),
                     m,
                     dname,
                     cname,
                     sm,
                     b,
                     t,
                     Subst.wk(mot),
                     args1
                   ),
                 :ok <- check_bound(m, q, u0) do
              {:ok, us}
            end

          _ ->
            {:error, "match branch expected a λ for a constructor argument"}
        end

      _ ->
        np = nparams_of(book, dname)
        {_, targs} = apps(ty1)
        idxs = Enum.drop(targs, np)
        ctor_tm = Subst.apps_from({:def, cname}, args)
        check(k, book, rs, gamma, m, br, Subst.apps_from(mot, idxs ++ [ctor_tm]))
    end
  end

  defp first_mot_lam(d, dname, params, p) do
    case Map.get(d, :indices, []) do
      [] -> {:lam, :affine, Subst.apps_from({:def, dname}, params), "x", p}
      [{q, x, t} | _] -> {:lam, q, t, x, p}
    end
  end

  defp check_motive(k, book, rs, gamma, d, dname, params, p) do
    case Map.get(d, :indices, []) do
      [] ->
        dty = Subst.apps_from({:def, dname}, params)
        check_ty(k, book, push_name(ext_rec(rs, false, false), "x"), ext(gamma, :affine, dty), p)

      [{q, x, t} | rest] ->
        gamma1 = ext(gamma, q, t)
        args = Enum.map(params, &Subst.wk/1) ++ [{:var, 0}]
        tail = motive_tail(dname, args, rest)

        with {:ok, _} <-
               check(k, book, push_name(ext_rec(rs, false, false), x), gamma1, :spec, p, tail),
             do: :ok
    end
  end

  defp motive_tail(dname, args, []),
    do: {:pi, :affine, Subst.apps_from({:def, dname}, args), "x", :typ}

  defp motive_tail(dname, args, [{q, x, t} | rest]) do
    {:pi, q, t, x, motive_tail(dname, Enum.map(args, &Subst.wk/1) ++ [{:var, 0}], rest)}
  end

  # The index-clash test (Agda: clashes). `{:ok, true}`: some target index
  # of the constructor's telescope tel is a numeral that differs from the
  # scrutinee's index at that position (su against ze, under any number of
  # matching su), so the constructor cannot occur; `{:ok, false}`
  # otherwise. Each comparison reduces both sides, so it spends fuel.
  defp clashes(k, book, np, expected, {:pi, _, _, _, b}),
    do: clashes(k, book, np, expected, b)

  defp clashes(k, book, np, expected, t) do
    with {:ok, t1} <- whnf(k, book, t) do
      {_h, args} = apps(t1)
      clash_idxs(k, book, expected, Enum.drop(args, np))
    end
  end

  defp clash_idxs(_k, _book, [], []), do: {:ok, false}

  defp clash_idxs(k, book, [e | es], [t | ts]) do
    case clash_idx(k, book, e, t) do
      {:ok, true} -> {:ok, true}
      {:ok, false} -> clash_idxs(k, book, es, ts)
      err -> err
    end
  end

  defp clash_idxs(_, _, _, _), do: {:error, "index telescope length mismatch"}

  defp clash_idx(0, _book, _e, _t), do: {:error, @out_of_fuel}

  defp clash_idx(k, book, e, t) do
    with {:ok, e1} <- whnf(k - 1, book, e),
         {:ok, t1} <- whnf(k - 1, book, t) do
      case {e1, t1} do
        {{:su, e2}, {:su, t2}} -> clash_idx(k - 1, book, e2, t2)
        {{:su, _}, :ze} -> {:ok, true}
        {:ze, {:su, _}} -> {:ok, true}
        {_, _} -> {:ok, false}
      end
    end
  end

  # A field is strictly positive in D when, after unfolding, D is absent,
  # or D is the head of a spine whose arguments do not contain D, or D
  # occurs only to the right of a Π whose domain does not contain D.
  # A product is positive on both sides. D inside an argument of D is
  # refused. Another data type is not opaque: its parameters are
  # instantiated and every field is held to the same test, so D stored
  # there and placed in a domain is refused. A type already on `seen`
  # is the inductive occurrence. A field that does not reduce in the
  # fuel is refused (Agda: posField).
  defp field_pos?(k, book, dname, t), do: field_pos?(k, book, dname, t, MapSet.new())

  defp field_pos?(0, _book, _dname, _t, _seen), do: false

  defp field_pos?(k, book, dname, t, seen) do
    case whnf(k, book, t) do
      {:ok, {:pi, _, a, _, b}} ->
        absent?(k, book, dname, a, seen) and field_pos?(k - 1, book, dname, b, seen)

      {:ok, {:prod, a, b}} ->
        field_pos?(k - 1, book, dname, a, seen) and field_pos?(k - 1, book, dname, b, seen)

      {:ok, t1} ->
        {head, args} = apps(t1)

        cond do
          is_d_type?(book, dname, t1) ->
            Enum.all?(args, &absent?(k, book, dname, &1, seen))

          match?({:def, _}, head) and data_name?(book, elem(head, 1)) ->
            Enum.all?(args, &absent?(k, book, dname, &1, seen)) and
              pos_data?(k - 1, book, dname, seen, elem(head, 1), args)

          true ->
            absent_go?(k - 1, book, dname, t1, seen)
        end

      _ ->
        false
    end
  end

  # j already on the stack is an inductive occurrence, not a fresh copy of D.
  defp pos_data?(0, _book, _dname, _seen, _j, _args), do: false

  defp pos_data?(k, book, dname, seen, j, args) do
    if MapSet.member?(seen, j) do
      true
    else
      case lookup_data(book, j) do
        {:ok, d} ->
          seen = MapSet.put(seen, j)
          params = Enum.take(args, length(d.params))

          Enum.all?(d.ctors, fn c ->
            case inst_params(k, book, c.type, params) do
              {:ok, rest} -> pos_tel?(k, book, dname, seen, rest)
              _ -> false
            end
          end)

        _ ->
          false
      end
    end
  end

  defp pos_tel?(k, book, dname, seen, {:pi, _, a, _, b}),
    do: field_pos?(k, book, dname, a, seen) and pos_tel?(k, book, dname, seen, b)

  defp pos_tel?(_k, _book, _dname, _seen, _), do: true

  defp absent?(0, _book, _dname, _t, _seen), do: false

  defp absent?(k, book, dname, t, seen) do
    case whnf(k, book, t) do
      {:ok, t1} -> absent_go?(k - 1, book, dname, t1, seen)
      _ -> false
    end
  end

  defp absent_go?(k, book, dname, {:pi, _, a, _, b}, seen),
    do: absent?(k, book, dname, a, seen) and absent?(k, book, dname, b, seen)

  defp absent_go?(k, book, dname, {:prod, a, b}, seen),
    do: absent?(k, book, dname, a, seen) and absent?(k, book, dname, b, seen)

  defp absent_go?(k, book, dname, {:lam, _, a, _, t}, seen),
    do: absent?(k, book, dname, a, seen) and absent?(k, book, dname, t, seen)

  defp absent_go?(k, book, dname, {:app, f, a}, seen),
    do: absent?(k, book, dname, f, seen) and absent?(k, book, dname, a, seen)

  defp absent_go?(k, book, dname, {:pair, a, b}, seen),
    do: absent?(k, book, dname, a, seen) and absent?(k, book, dname, b, seen)

  defp absent_go?(k, book, dname, {:idt, a, x, y}, seen),
    do:
      absent?(k, book, dname, a, seen) and absent?(k, book, dname, x, seen) and
        absent?(k, book, dname, y, seen)

  defp absent_go?(k, book, dname, {:ann, e, a}, seen),
    do: absent?(k, book, dname, e, seen) and absent?(k, book, dname, a, seen)

  defp absent_go?(k, book, dname, {:su, t}, seen), do: absent?(k, book, dname, t, seen)

  defp absent_go?(k, book, dname, {:letp, e, t}, seen),
    do: absent?(k, book, dname, e, seen) and absent?(k, book, dname, t, seen)

  defp absent_go?(k, book, dname, {:nu, f}, seen), do: absent?(k, book, dname, f, seen)

  defp absent_go?(k, book, dname, {:unf, s, f}, seen),
    do: absent?(k, book, dname, s, seen) and absent?(k, book, dname, f, seen)

  defp absent_go?(k, book, dname, {:ucons, s}, seen), do: absent?(k, book, dname, s, seen)

  defp absent_go?(k, book, dname, {:matom, e, p, bs}, seen) do
    absent?(k, book, dname, e, seen) and absent?(k, book, dname, p, seen) and
      Enum.all?(bs, fn {_, b} -> absent?(k, book, dname, b, seen) end)
  end

  # A stuck match still has subterms. Absent only when every one is
  # (Agda: absentGo on mNat, mData, mEmp, mUnit, rwt).
  defp absent_go?(k, book, dname, {:mnat, e, p, z, s}, seen),
    do:
      absent?(k, book, dname, e, seen) and absent?(k, book, dname, p, seen) and
        absent?(k, book, dname, z, seen) and absent?(k, book, dname, s, seen)

  defp absent_go?(k, book, dname, {:mdata, e, p, bs}, seen) do
    absent?(k, book, dname, e, seen) and absent?(k, book, dname, p, seen) and
      Enum.all?(bs, fn {_, _, b} -> absent?(k, book, dname, b, seen) end)
  end

  defp absent_go?(k, book, dname, {:memp, e, p}, seen),
    do: absent?(k, book, dname, e, seen) and absent?(k, book, dname, p, seen)

  defp absent_go?(k, book, dname, {:munit, e, p, u}, seen),
    do:
      absent?(k, book, dname, e, seen) and absent?(k, book, dname, p, seen) and
        absent?(k, book, dname, u, seen)

  defp absent_go?(k, book, dname, {:rwt, e, p, t}, seen),
    do:
      absent?(k, book, dname, e, seen) and absent?(k, book, dname, p, seen) and
        absent?(k, book, dname, t, seen)

  defp absent_go?(k, book, dname, {:tensor, d, s}, seen),
    do: absent?(k, book, dname, d, seen) and absent?(k, book, dname, s, seen)

  defp absent_go?(k, book, dname, {:addi, a, b}, seen),
    do: absent?(k, book, dname, a, seen) and absent?(k, book, dname, b, seen)

  defp absent_go?(k, book, dname, {:muli, a, b}, seen),
    do: absent?(k, book, dname, a, seen) and absent?(k, book, dname, b, seen)

  defp absent_go?(k, book, dname, {:addt, t, u}, seen),
    do: absent?(k, book, dname, t, seen) and absent?(k, book, dname, u, seen)

  defp absent_go?(k, book, dname, {:toi64, t}, seen), do: absent?(k, book, dname, t, seen)

  defp absent_go?(k, book, dname, {:packi, a, b}, seen),
    do: absent?(k, book, dname, a, seen) and absent?(k, book, dname, b, seen)

  defp absent_go?(k, book, dname, {:bisim, s, t}, seen),
    do: absent?(k, book, dname, s, seen) and absent?(k, book, dname, t, seen)

  defp absent_go?(k, book, dname, {:def, n}, seen) do
    cond do
      n == dname -> false
      not data_name?(book, n) -> true
      MapSet.member?(seen, n) -> true
      true -> absent_decl?(k, book, dname, MapSet.put(seen, n), n)
    end
  end

  # No subterms: a variable, a sort, a literal, a hole.
  defp absent_go?(_k, _book, _dname, _, _seen), do: true

  defp absent_decl?(k, book, dname, seen, j) do
    case lookup_data(book, j) do
      {:ok, d} ->
        np = length(d.params)

        Enum.all?(d.ctors, fn c ->
          case drop_pis(np, c.type) do
            {:ok, rest} -> absent_tel?(k, book, dname, seen, rest)
            _ -> false
          end
        end)

      _ ->
        false
    end
  end

  defp drop_pis(0, t), do: {:ok, t}
  defp drop_pis(n, {:pi, _, _, _, b}) when n > 0, do: drop_pis(n - 1, b)
  defp drop_pis(_, _), do: :error

  defp absent_tel?(k, book, dname, seen, {:pi, _, a, _, b}),
    do: absent?(k, book, dname, a, seen) and absent_tel?(k, book, dname, seen, b)

  defp absent_tel?(_k, _book, _dname, _seen, _), do: true

  defp check_tel_pos(0, _book, _dname, _np, _ni, _t), do: {:error, @out_of_fuel}

  defp check_tel_pos(k, book, dname, np, ni, t) do
    case whnf(k, book, t) do
      {:error, e} ->
        {:error, e}

      {:ok, {:pi, _, a, _, b}} ->
        if field_pos?(k, book, dname, a) do
          check_tel_pos(k - 1, book, dname, np, ni, b)
        else
          {:error, "constructor is not strictly positive"}
        end

      {:ok, t1} ->
        {_h, args} = apps(t1)

        cond do
          not is_d_type?(book, dname, t1) ->
            {:error, "constructor does not target the data type"}

          length(args) != np + ni ->
            {:error, "constructor target has the wrong number of arguments"}

          true ->
            :ok
        end
    end
  end

  # Constructor fields must be small types. Parameters are (A : Type) and
  # are skipped; a field of type Type would make the data type a large
  # inductive in Type, and match with motive Type would retract Type into it.
  defp check_ctor_fields(k, book, rs, gamma, np, {:pi, q, a, x, b}) when np > 0,
    do:
      check_ctor_fields(
        k,
        book,
        push_name(ext_rec(rs, false, false), x),
        ext(gamma, q, a),
        np - 1,
        b
      )

  defp check_ctor_fields(_k, _book, _rs, _gamma, np, _t) when np > 0,
    do: {:error, "constructor type has too few parameter binders"}

  defp check_ctor_fields(k, book, rs, gamma, 0, {:pi, q, a, x, b}) do
    with {:ok, _} <- check(k, book, rs, gamma, :spec, a, :typ),
         :ok <- if(q == :reuse, do: guard_copy(k, book, a), else: :ok),
         do:
           check_ctor_fields(
             k,
             book,
             push_name(ext_rec(rs, false, false), x),
             ext(gamma, q, a),
             0,
             b
           )
  end

  defp check_ctor_fields(_k, _book, _rs, _gamma, 0, _t), do: :ok

  defp check_ctor_rest(k, book, dname, np, ni, t), do: skip_params(k, book, dname, np, ni, np, t)

  defp skip_params(k, book, dname, np, ni, 0, t), do: check_tel_pos(k, book, dname, np, ni, t)

  defp skip_params(k, book, dname, np, ni, c, {:pi, _, _, _, b}) when c > 0,
    do: skip_params(k, book, dname, np, ni, c - 1, b)

  defp skip_params(_, _, _, _, _, c, _) when c > 0,
    do: {:error, "constructor type has too few parameter binders"}

  defp check_data(book, %{name: name, params: params, ctors: ctors} = d, k) do
    np = length(params)
    ni = length(Map.get(d, :indices, []))

    Enum.reduce_while(ctors, :ok, fn c, :ok ->
      result =
        with :ok <- check_ty(k, book, empty_rec(), [], c.type),
             :ok <- check_ctor_fields(k, book, empty_rec(), [], np, c.type) do
          check_ctor_rest(k, book, name, np, ni, c.type)
        end

      case fail_at(d, "#{c.name} type", result) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end
end
