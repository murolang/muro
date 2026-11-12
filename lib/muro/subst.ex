defmodule Muro.Subst do
  @moduledoc """
  Rename / substitute / instantiate de Bruijn terms. Mirrors Muro.Subst.
  """

  def lift(rho) do
    fn
      0 -> 0
      i -> rho.(i - 1) + 1
    end
  end

  defp lift_n(rho, 0), do: rho
  defp lift_n(rho, n) when n > 0, do: lift_n(lift(rho), n - 1)

  defp lifts_n(sigma, 0), do: sigma
  defp lifts_n(sigma, n) when n > 0, do: lifts_n(lifts(sigma), n - 1)

  def ren(rho, t) do
    case t do
      {:var, i} ->
        {:var, rho.(i)}

      :typ ->
        :typ

      {:pi, q, a, x, b} ->
        {:pi, q, ren(rho, a), x, ren(lift(rho), b)}

      {:lam, q, a, x, u} ->
        {:lam, q, ren(rho, a), x, ren(lift(rho), u)}

      {:hole, loc} ->
        {:hole, loc}

      {:app, f, a} ->
        {:app, ren(rho, f), ren(rho, a)}

      :nat ->
        :nat

      :ze ->
        :ze

      {:nat, n} when is_integer(n) ->
        {:nat, n}

      {:su, u} ->
        {:su, ren(rho, u)}

      :unit ->
        :unit

      :one ->
        :one

      :empty ->
        :empty

      :atom ->
        :atom

      {:atom, n} ->
        {:atom, n}

      :string ->
        :string

      {:slit, bin} ->
        {:slit, bin}

      {:scat, a, b} ->
        {:scat, ren(rho, a), ren(rho, b)}

      {:slen, a} ->
        {:slen, ren(rho, a)}

      {:seq, a, b} ->
        {:seq, ren(rho, a), ren(rho, b)}

      :bytes ->
        :bytes

      :slice ->
        :slice

      {:blit, bin} ->
        {:blit, bin}

      {:bcat, a, b} ->
        {:bcat, ren(rho, a), ren(rho, b)}

      {:blen, a} ->
        {:blen, ren(rho, a)}

      {:beq, a, b} ->
        {:beq, ren(rho, a), ren(rho, b)}

      {:xlen, a} ->
        {:xlen, ren(rho, a)}

      {:xeq, a, b} ->
        {:xeq, ren(rho, a), ren(rho, b)}

      {:bsub, a, b, c} ->
        {:bsub, ren(rho, a), ren(rho, b), ren(rho, c)}

      {:bget, a, b} ->
        {:bget, ren(rho, a), ren(rho, b)}

      {:aget, a, b} ->
        {:aget, ren(rho, a), ren(rho, b)}

      {:bunc, a} ->
        {:bunc, ren(rho, a)}

      {:bfold, ty, z, f, s} ->
        {:bfold, ren(rho, ty), ren(rho, z), ren(rho, f), ren(rho, s)}

      {:afold, ty, z, f, s} ->
        {:afold, ren(rho, ty), ren(rho, z), ren(rho, f), ren(rho, s)}

      {:sbytes, a} ->
        {:sbytes, ren(rho, a)}

      {:btil, a, b} ->
        {:btil, ren(rho, a), ren(rho, b)}

      {:baft, a, b} ->
        {:baft, ren(rho, a), ren(rho, b)}

      {:matom, e, p, bs} ->
        {:matom, ren(rho, e), ren(lift(rho), p), Enum.map(bs, fn {n, b} -> {n, ren(rho, b)} end)}

      {:mdata, e, p, bs} ->
        {:mdata, ren(rho, e), ren(lift(rho), p),
         Enum.map(bs, fn {n, ar, b} -> {n, ar, ren(lift_n(rho, ar), b)} end)}

      {:mnat, e, p, z, s} ->
        {:mnat, ren(rho, e), ren(lift(rho), p), ren(rho, z), ren(lift(rho), s)}

      {:memp, e, p} ->
        {:memp, ren(rho, e), ren(lift(rho), p)}

      {:munit, e, p, u} ->
        {:munit, ren(rho, e), ren(lift(rho), p), ren(rho, u)}

      {:idt, a, x, y} ->
        {:idt, ren(rho, a), ren(rho, x), ren(rho, y)}

      :rfl ->
        :rfl

      {:rwt, e, p, u} ->
        {:rwt, ren(rho, e), ren(lift(rho), p), ren(rho, u)}

      {:def, n} ->
        {:def, n}

      {:ann, e, a} ->
        {:ann, ren(rho, e), ren(rho, a)}

      {:prod, a, b} ->
        {:prod, ren(rho, a), ren(rho, b)}

      {:pair, a, b} ->
        {:pair, ren(rho, a), ren(rho, b)}

      {:letp, e, t} ->
        {:letp, ren(rho, e), ren(lift(lift(rho)), t)}

      {:nu, f} ->
        {:nu, ren(lift(rho), f)}

      {:bisim, s, t} ->
        {:bisim, ren(rho, s), ren(rho, t)}

      {:unf, s, f} ->
        {:unf, ren(rho, s), ren(rho, f)}

      {:ucons, s} ->
        {:ucons, ren(rho, s)}

      :i64 ->
        :i64

      :f32ty ->
        :f32ty

      {:tensor, d, s} ->
        {:tensor, ren(rho, d), ren(rho, s)}

      {:addi, x, y} ->
        {:addi, ren(rho, x), ren(rho, y)}

      {:muli, x, y} ->
        {:muli, ren(rho, x), ren(rho, y)}

      {:addt, t, u} ->
        {:addt, ren(rho, t), ren(rho, u)}

      {:toi64, t} ->
        {:toi64, ren(rho, t)}

      {:packi, x, y} ->
        {:packi, ren(rho, x), ren(rho, y)}

      {:word, op, args} ->
        {:word, op, Enum.map(args, &ren(rho, &1))}
    end
  end

  def wk(t), do: ren(fn i -> i + 1 end, t)

  # Undo a double weakening (Agda: strengthen₂ = renM unwk₂). The renaming
  # refuses the two nearest variables; ren carries the refusal out.
  def strengthen2(t) do
    {:ok,
     ren(
       fn
         i when i < 2 -> throw({__MODULE__, :bound})
         i -> i - 2
       end,
       t
     )}
  catch
    {__MODULE__, :bound} ->
      {:error, "let: the body's type mentions a component of the pair"}
  end

  def closed(t), do: t

  def lifts(sigma) do
    fn
      0 -> {:var, 0}
      i -> wk(sigma.(i - 1))
    end
  end

  def sub(sigma, t) do
    case t do
      {:var, i} ->
        sigma.(i)

      :typ ->
        :typ

      {:pi, q, a, x, b} ->
        {:pi, q, sub(sigma, a), x, sub(lifts(sigma), b)}

      {:lam, q, a, x, u} ->
        {:lam, q, sub(sigma, a), x, sub(lifts(sigma), u)}

      {:hole, loc} ->
        {:hole, loc}

      {:app, f, a} ->
        {:app, sub(sigma, f), sub(sigma, a)}

      :nat ->
        :nat

      :ze ->
        :ze

      {:nat, n} when is_integer(n) ->
        {:nat, n}

      {:su, u} ->
        {:su, sub(sigma, u)}

      :unit ->
        :unit

      :one ->
        :one

      :empty ->
        :empty

      :atom ->
        :atom

      {:atom, n} ->
        {:atom, n}

      :string ->
        :string

      {:slit, bin} ->
        {:slit, bin}

      {:scat, a, b} ->
        {:scat, sub(sigma, a), sub(sigma, b)}

      {:slen, a} ->
        {:slen, sub(sigma, a)}

      {:seq, a, b} ->
        {:seq, sub(sigma, a), sub(sigma, b)}

      :bytes ->
        :bytes

      :slice ->
        :slice

      {:blit, bin} ->
        {:blit, bin}

      {:bcat, a, b} ->
        {:bcat, sub(sigma, a), sub(sigma, b)}

      {:blen, a} ->
        {:blen, sub(sigma, a)}

      {:beq, a, b} ->
        {:beq, sub(sigma, a), sub(sigma, b)}

      {:xlen, a} ->
        {:xlen, sub(sigma, a)}

      {:xeq, a, b} ->
        {:xeq, sub(sigma, a), sub(sigma, b)}

      {:bsub, a, b, c} ->
        {:bsub, sub(sigma, a), sub(sigma, b), sub(sigma, c)}

      {:bget, a, b} ->
        {:bget, sub(sigma, a), sub(sigma, b)}

      {:aget, a, b} ->
        {:aget, sub(sigma, a), sub(sigma, b)}

      {:bunc, a} ->
        {:bunc, sub(sigma, a)}

      {:bfold, ty, z, f, s} ->
        {:bfold, sub(sigma, ty), sub(sigma, z), sub(sigma, f), sub(sigma, s)}

      {:afold, ty, z, f, s} ->
        {:afold, sub(sigma, ty), sub(sigma, z), sub(sigma, f), sub(sigma, s)}

      {:sbytes, a} ->
        {:sbytes, sub(sigma, a)}

      {:btil, a, b} ->
        {:btil, sub(sigma, a), sub(sigma, b)}

      {:baft, a, b} ->
        {:baft, sub(sigma, a), sub(sigma, b)}

      {:matom, e, p, bs} ->
        {:matom, sub(sigma, e), sub(lifts(sigma), p),
         Enum.map(bs, fn {n, b} -> {n, sub(sigma, b)} end)}

      {:mdata, e, p, bs} ->
        {:mdata, sub(sigma, e), sub(lifts(sigma), p),
         Enum.map(bs, fn {n, ar, b} -> {n, ar, sub(lifts_n(sigma, ar), b)} end)}

      {:mnat, e, p, z, s} ->
        {:mnat, sub(sigma, e), sub(lifts(sigma), p), sub(sigma, z), sub(lifts(sigma), s)}

      {:memp, e, p} ->
        {:memp, sub(sigma, e), sub(lifts(sigma), p)}

      {:munit, e, p, u} ->
        {:munit, sub(sigma, e), sub(lifts(sigma), p), sub(sigma, u)}

      {:idt, a, x, y} ->
        {:idt, sub(sigma, a), sub(sigma, x), sub(sigma, y)}

      :rfl ->
        :rfl

      {:rwt, e, p, u} ->
        {:rwt, sub(sigma, e), sub(lifts(sigma), p), sub(sigma, u)}

      {:def, n} ->
        {:def, n}

      {:ann, e, a} ->
        {:ann, sub(sigma, e), sub(sigma, a)}

      {:prod, a, b} ->
        {:prod, sub(sigma, a), sub(sigma, b)}

      {:pair, a, b} ->
        {:pair, sub(sigma, a), sub(sigma, b)}

      {:letp, e, t} ->
        {:letp, sub(sigma, e), sub(lifts(lifts(sigma)), t)}

      {:nu, f} ->
        {:nu, sub(lifts(sigma), f)}

      {:bisim, s, t} ->
        {:bisim, sub(sigma, s), sub(sigma, t)}

      {:unf, s, f} ->
        {:unf, sub(sigma, s), sub(sigma, f)}

      {:ucons, s} ->
        {:ucons, sub(sigma, s)}

      :i64 ->
        :i64

      :f32ty ->
        :f32ty

      {:tensor, d, s} ->
        {:tensor, sub(sigma, d), sub(sigma, s)}

      {:addi, x, y} ->
        {:addi, sub(sigma, x), sub(sigma, y)}

      {:muli, x, y} ->
        {:muli, sub(sigma, x), sub(sigma, y)}

      {:addt, t, u} ->
        {:addt, sub(sigma, t), sub(sigma, u)}

      {:toi64, t} ->
        {:toi64, sub(sigma, t)}

      {:packi, x, y} ->
        {:packi, sub(sigma, x), sub(sigma, y)}

      {:word, op, args} ->
        {:word, op, Enum.map(args, &sub(sigma, &1))}
    end
  end

  def inst(t, u) do
    sub(
      fn
        0 -> u
        i -> {:var, i - 1}
      end,
      t
    )
  end

  # Open two binders at once (Agda: inst₂): the inner one (0) gets b.
  def inst2(t, a, b), do: inst(inst(t, wk(b)), a)

  # Open n binders at once (Agda: appsFrom b args, β-reduced): the inner
  # binder (0) gets the last argument. The arguments live outside all n
  # binders, so they are substituted simultaneously. Opening them one at a
  # time with inst would need each argument weakened by the binders still
  # open over it, as inst2 does; without that, every field after the first
  # lands one variable too low.
  def inst_n(t, args) do
    n = length(args)
    rev = Enum.reverse(args)

    sub(
      fn
        i when i < n -> Enum.at(rev, i)
        i -> {:var, i - n}
      end,
      t
    )
  end

  def apps_from(f, args), do: Enum.reduce(args, f, fn a, acc -> {:app, acc, a} end)

  def mot_suc(p) do
    sub(
      fn
        0 -> {:su, {:var, 0}}
        i -> {:var, i}
      end,
      p
    )
  end

  @doc """
  `Stream A = ν X. A × X`.
  """
  def stream(a), do: {:nu, {:prod, wk(a), {:var, 0}}}

  # fst t = let (a, _) = t in a. snd t = let (_, b) = t in b.
  def head(t), do: {:letp, {:ucons, t}, {:var, 1}}
  def tail(t), do: {:letp, {:ucons, t}, {:var, 0}}

  @doc """
  `Always P s` unfolds to `P (head s) × Always P (tail s)`.
  The binder is a predicate at a stream.
  """
  def always(a, p, s) do
    body =
      {:prod, {:app, wk(wk(p)), head({:var, 0})}, {:app, {:var, 1}, tail({:var, 0})}}

    fam = {:lam, :affine, wk(stream(a)), "s", body}
    {:app, {:nu, fam}, s}
  end

  @doc """
  `σ ~ τ` unfolds to `{head σ ≡ head τ} × (tail σ ~ tail τ)`.
  """
  def bisim(a, s, t) do
    st = stream(a)

    inner =
      {:lam, :affine, wk(wk(st)), "t",
       {:prod, {:idt, wk(wk(wk(a))), head({:var, 1}), head({:var, 0})},
        {:app, {:app, {:var, 2}, tail({:var, 1})}, tail({:var, 0})}}}

    fam = {:lam, :affine, wk(st), "s", inner}
    {:app, {:app, {:nu, fam}, s}, t}
  end
end
