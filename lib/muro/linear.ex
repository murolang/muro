defmodule Muro.Linear do
  @moduledoc """
  The Elixir mirror of `agda/Muro/Linear.agda`.

  A binder is affine by default. A session endpoint may be bound
  linearly, and then it is used exactly once. The obligation is the
  multiplicity of the value. `dual` keeps it. A meeting keeps it and
  refuses a linear endpoint that is not consumed once.

  Neither multiplicity is a quantity. Nothing here is added to the
  core term. The endpoint function is evidence, so emit drops it.
  """

  alias Muro.Session

  @doc """
  Check an endpoint function at evidence. `relays` is `{name, type}`
  for each closed endpoint function. A name in the body is that
  declared type. The body is not unfolded.
  """
  def check(relays, ty, body) when is_list(relays) do
    case infer(:evidence, [], relays, body) do
      {:ok, got, _} ->
        if eq_ety?(ty, got), do: :ok, else: {:error, mismatch(ty, got)}

      {:error, _} = err ->
        err
    end
  end

  @doc """
  The two processes meet, and each endpoint is consumed at `mult`.
  Affine accepts abandonment. Linear requires one use.
  """
  def meet_proc(mult, p, q) when mult in [:aff, :lin] do
    with :ok <- endpoint_use(mult, p, :left) do
      endpoint_use(mult, q, :right)
    end
  end

  # A linear endpoint that is not consumed is this meeting. A `%1` binder
  # in a term still says `linear variable unused`.
  defp endpoint_use(:lin, proc, side) do
    case consume(proc) do
      :u0 -> {:error, "linear endpoint not consumed: #{side}"}
      :uw -> {:error, "affine variable used as reusable"}
      _ -> :ok
    end
  end

  defp endpoint_use(mult, proc, _side), do: check_mult(:evidence, mult, consume(proc))

  @doc """
  Replace session names with protocols. An unknown name is refused.
  """
  def ground_ty(protos, {:sess, q, name}) when is_binary(name) and q in [:aff, :lin] do
    case Map.fetch(protos, name) do
      {:ok, :arity} -> {:error, "wrong number of session arguments"}
      {:ok, proto} -> {:ok, {:sess, q, proto}}
      :error -> {:error, "unknown session #{name}"}
    end
  end

  def ground_ty(protos, {:arr, q, a, b}) when q in [:aff, :lin] do
    with {:ok, a} <- ground_ty(protos, a),
         {:ok, b} <- ground_ty(protos, b) do
      {:ok, {:arr, q, a, b}}
    end
  end

  def ground_ty(_protos, {:done} = ty), do: {:ok, ty}
  def ground_ty(_protos, _), do: {:error, "endpoint type mismatch"}

  @doc false
  def ground_tm(protos, {:lam, q, x, a, t}) when q in [:aff, :lin] and is_binary(x) do
    with {:ok, a} <- ground_ty(protos, a),
         {:ok, t} <- ground_tm(protos, t) do
      {:ok, {:lam, q, x, a, t}}
    end
  end

  def ground_tm(protos, {:app, f, a}) do
    with {:ok, f} <- ground_tm(protos, f),
         {:ok, a} <- ground_tm(protos, a) do
      {:ok, {:app, f, a}}
    end
  end

  def ground_tm(protos, {:dual, t}) do
    with {:ok, t} <- ground_tm(protos, t), do: {:ok, {:dual, t}}
  end

  def ground_tm(protos, {:meet, t, u}) do
    with {:ok, t} <- ground_tm(protos, t),
         {:ok, u} <- ground_tm(protos, u) do
      {:ok, {:meet, t, u}}
    end
  end

  def ground_tm(_protos, {:var, name} = t) when is_binary(name), do: {:ok, t}
  def ground_tm(_protos, _), do: {:error, "unbound endpoint"}

  # One use when the process finishes, none when it abandons.
  # A cover is one use when both arms are.
  defp consume(:done), do: :u1
  defp consume(:stop), do: :u0
  defp consume({:put, _, _, p}), do: consume(p)
  defp consume({:get, _, _, p}), do: consume(p)
  defp consume({:pick0, p}), do: consume(p)
  defp consume({:pick1, p}), do: consume(p)
  defp consume({:cover, p, q}), do: once(consume(p), consume(q))
  defp consume({:iget, _, p, q}), do: once(consume(p), consume(q))
  # Every arm is consumed. An empty match is one use. One abandoned arm is none.
  defp consume({:match, _, arms}), do: arms_use(arms)
  # A jump does not finish. `rec X. done` does, and it is one use.
  defp consume({:rec, _, body}), do: consume(body)
  defp consume({:call, _}), do: :u0

  defp arms_use([]), do: :u1
  defp arms_use([p | ps]), do: once(consume(Session.arm_body(p)), arms_use(ps))

  defp once(:u1, :u1), do: :u1
  defp once(_, _), do: :u0

  defp carries?({:sess, :lin, _}), do: true
  defp carries?({:sess, :aff, _}), do: false
  defp carries?({:arr, _, a, b}), do: carries?(a) or carries?(b)
  defp carries?({:done}), do: false

  defp arrow_ok?(:lin, a, b), do: carries?(a) or carries?(b)
  defp arrow_ok?(:aff, a, b), do: not carries?(a) and not carries?(b)

  defp bind_ok?(:lin, {:sess, :lin, _}), do: true
  defp bind_ok?(:lin, _), do: false
  defp bind_ok?(:aff, {:sess, :lin, _}), do: false
  defp bind_ok?(:aff, _), do: true

  defp infer(_mode, ctx, relays, {:var, name}) do
    case lookup_ctx(ctx, name) do
      {:ok, i, ty} ->
        {:ok, ty, one_hot(i, :u1, length(ctx))}

      :error ->
        case List.keyfind(relays, name, 0) do
          {_, ty} -> {:ok, ty, u0s(length(ctx))}
          nil -> {:error, "unbound endpoint"}
        end
    end
  end

  defp infer(mode, ctx, relays, {:lam, q, x, a, t}) do
    with :ok <- guard("a linear binder binds a session endpoint", bind_ok?(q, a)),
         {:ok, b, [u | us]} <- infer(mode, [{x, a} | ctx], relays, t),
         :ok <- guard("linear arrow is ⊸", arrow_ok?(q, a, b)),
         :ok <- check_mult(mode, q, u) do
      {:ok, {:arr, q, a, b}, us}
    end
  end

  defp infer(mode, ctx, relays, {:app, f, a}) do
    with {:ok, fty, uf} <- infer(mode, ctx, relays, f),
         {:ok, dom, cod, uf} <- arrow_of(fty, uf),
         {:ok, aty, ua} <- infer(mode, ctx, relays, a),
         :ok <- guard(mismatch(dom, aty), eq_ety?(dom, aty)),
         {:ok, us} <- combine(mode, uf, ua) do
      {:ok, cod, us}
    end
  end

  defp infer(mode, ctx, relays, {:dual, t}) do
    with {:ok, ty, u} <- infer(mode, ctx, relays, t) do
      case ty do
        {:sess, q, s} -> {:ok, {:sess, q, Session.dual(s)}, u}
        _ -> {:error, "dual of a session endpoint"}
      end
    end
  end

  defp infer(mode, ctx, relays, {:meet, t, u}) do
    with {:ok, at, ut} <- infer(mode, ctx, relays, t),
         {:ok, au, uu} <- infer(mode, ctx, relays, u),
         {:ok, q} <- meet_ty(at, au),
         {:ok, us} <- combine(mode, ut, uu),
         :ok <- check_mult(mode, q, spent(t)),
         :ok <- check_mult(mode, q, spent(u)) do
      {:ok, {:done}, us}
    end
  end

  defp infer(_mode, _ctx, _relays, _), do: {:error, "unbound endpoint"}

  # `with` cannot match a bare 3-tuple against an `{:ok, _, _}` from infer.
  defp arrow_of({:arr, _q, dom, cod}, uses), do: {:ok, dom, cod, uses}
  defp arrow_of(_, _), do: {:error, "expected an arrow"}

  defp meet_ty({:sess, q, s}, {:sess, q, t}) do
    if t == Session.dual(s), do: {:ok, q}, else: {:error, "expected the other end"}
  end

  defp meet_ty({:sess, _, _}, {:sess, _, _}), do: {:error, "multiplicity mismatch"}
  defp meet_ty(_, _), do: {:error, "a meeting meets session endpoints"}

  defp spent({:var, _}), do: :u1
  defp spent({:dual, t}), do: spent(t)
  defp spent({:app, _, a}), do: spent(a)
  defp spent({:lam, _, _, _, _}), do: :u0
  defp spent({:meet, _, _}), do: :uw

  defp eq_ety?({:sess, q, s}, {:sess, q, t}), do: s == t
  defp eq_ety?({:arr, q, a, b}, {:arr, q, c, d}), do: eq_ety?(a, c) and eq_ety?(b, d)
  defp eq_ety?({:done}, {:done}), do: true
  defp eq_ety?(_, _), do: false

  defp mismatch({:arr, q, _, _}, {:arr, r, _, _}) when q != r, do: "λ/arrow multiplicity mismatch"
  defp mismatch(_, _), do: "endpoint type mismatch"

  # Affine is `checkBound` for the affine quantity.
  # Linear is `checkArrow` for `%1`: that check, then the must-use.
  defp check_mult(mode, :aff, u), do: check_bound(mode, u)

  defp check_mult(mode, :lin, :uw) when mode in [:run, :evidence],
    do: {:error, "affine variable used as reusable"}

  defp check_mult(mode, :lin, :u0) when mode in [:run, :evidence],
    do: {:error, "linear variable unused"}

  defp check_mult(_mode, :lin, _), do: :ok

  defp check_bound(mode, :uw) when mode in [:run, :evidence],
    do: {:error, "affine variable used as reusable"}

  defp check_bound(_, _), do: :ok

  defp combine(:spec, u, _v), do: {:ok, u0s(length(u))}
  defp combine(_mode, u, v), do: add_uses(u, v)

  defp add_uses([], []), do: {:ok, []}

  defp add_uses([x | xs], [y | ys]) do
    with {:ok, z} <- add_use(x, y),
         {:ok, zs} <- add_uses(xs, ys) do
      {:ok, [z | zs]}
    end
  end

  defp add_uses(_, _), do: {:error, "affine variable used twice"}

  defp add_use(:u0, u), do: {:ok, u}
  defp add_use(u, :u0), do: {:ok, u}
  defp add_use(:u1, :u1), do: {:error, "affine variable used twice"}
  defp add_use(:uw, _), do: {:ok, :uw}
  defp add_use(_, :uw), do: {:ok, :uw}

  defp lookup_ctx([{name, ty} | _], name), do: {:ok, 0, ty}

  defp lookup_ctx([{_, _} | rest], name) do
    case lookup_ctx(rest, name) do
      {:ok, i, ty} -> {:ok, i + 1, ty}
      :error -> :error
    end
  end

  defp lookup_ctx([], _), do: :error

  defp one_hot(0, u, n), do: [u | u0s(n - 1)]
  defp one_hot(i, u, n) when i > 0, do: [:u0 | one_hot(i - 1, u, n - 1)]

  defp u0s(0), do: []
  defp u0s(n) when n > 0, do: [:u0 | u0s(n - 1)]

  defp guard(_msg, true), do: :ok
  defp guard(msg, false), do: {:error, msg}
end
