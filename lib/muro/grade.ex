defmodule Muro.Grade do
  @moduledoc """
  Grades on an affine binder. The rules are `agda/Muro/Grade.agda`.

  A binder may carry `(c, t)`. `c` is the computational grade. `t` is
  the type grade. An unmarked binder stays affine. The pair is evidence:
  the emitters replace it with the affine quantity.

  The kernel quantity is the coarse reading the existing checker already
  has. `0` is erased, `1` is the `%1` mark, `ω` and any exact count of
  two or more are `+`, and an interval whose upper bound is at most one
  is affine. The walker then checks the exact count and the type grade.
  """

  @type point :: non_neg_integer() | :w
  @type grade :: point() | {:iv, point(), point()}

  @doc """
  The quantity the kernel already checks. An atom is unchanged.
  """
  def kernel_qty(q) when q in [:affine, :reuse, :erased, :linear], do: q
  def kernel_qty({:grade, c, _t}), do: kernel_comp(c)
  def kernel_qty(_q), do: :affine

  defp kernel_comp(0), do: :erased
  defp kernel_comp(1), do: :linear
  defp kernel_comp(:w), do: :reuse
  defp kernel_comp(n) when is_integer(n) and n >= 2, do: :reuse

  defp kernel_comp({:iv, lo, hi}) do
    cond do
      lo == 0 and hi == 0 -> :erased
      lo == 1 and hi == 1 -> :linear
      upper_at_most_one?(hi) -> :affine
      true -> :reuse
    end
  end

  defp kernel_comp(_), do: :affine

  defp upper_at_most_one?(n) when is_integer(n), do: n <= 1
  defp upper_at_most_one?(_), do: false

  @doc "Whether a term or a book entry carries a grade pair."
  def any?({:grade, _, _}), do: true
  def any?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&any?/1)
  def any?(t) when is_list(t), do: Enum.any?(t, &any?/1)
  def any?(t) when is_map(t), do: Enum.any?(t, fn {_k, v} -> any?(v) end)
  def any?(_), do: false

  @doc """
  Replace every grade pair with the affine quantity. Emission of a graded
  book is the emission of that book with the pairs removed.
  """
  def erase({:grade, _, _}), do: :affine

  def erase(t) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.map(&erase/1) |> List.to_tuple()
  end

  def erase(t) when is_list(t), do: Enum.map(t, &erase/1)
  def erase(t) when is_map(t), do: Map.new(t, fn {k, v} -> {k, erase(v)} end)
  def erase(t), do: t

  def erase_book(book) when is_list(book), do: Enum.map(book, &erase/1)

  @doc """
  Check the type in spec and the body in `mode`. Both must be closed.
  Spec forgets the computational grade.
  """
  def check(mode, ty, body) do
    with {:ok, tu} <- walk(:spec, [], ty),
         :ok <- closed(tu),
         {:ok, bu} <- walk(mode, [], body),
         :ok <- closed(bu) do
      :ok
    end
  end

  @doc "Walk one closed term. A constructor type is checked in spec."
  def closed(mode, term) do
    with {:ok, uses} <- walk(mode, [], term), do: closed(uses)
  end

  def show(n) when is_integer(n), do: Integer.to_string(n)
  def show(:w), do: "ω"
  def show({:iv, lo, hi}), do: "[#{show(lo)}, #{show(hi)}]"

  defp show_count(n) when is_integer(n), do: Integer.to_string(n)
  defp show_count(:w), do: "ω"

  defp closed(uses) do
    if uses == %{}, do: :ok, else: {:error, "a grade does not cover this term"}
  end

  # gamma is the nearest binder first. :absent carries no grade.
  # A count is a non-negative integer or :w.
  defp walk(mode, _gamma, {:var, x}) when mode in [:run, :evidence], do: {:ok, %{x => {1, 0}}}
  defp walk(:spec, _gamma, {:var, x}), do: {:ok, %{x => {0, 1}}}

  defp walk(mode, gamma, {:lam, q, a, _x, t}) do
    with {:ok, au} <- walk(:spec, gamma, a),
         {:ok, bu} <- walk(mode, [q | gamma], t),
         {spent, rest} = pop(bu),
         :ok <- constrain(mode, q, spent) do
      {:ok, add(au, rest)}
    end
  end

  defp walk(_mode, gamma, {:pi, q, a, _x, b}) do
    with {:ok, au} <- walk(:spec, gamma, a),
         {:ok, bu} <- walk(:spec, [q | gamma], b),
         {spent, rest} = pop(bu),
         :ok <- constrain(:spec, q, spent) do
      {:ok, add(au, rest)}
    end
  end

  defp walk(mode, gamma, {:app, f, a}) do
    with {:ok, fu} <- walk(mode, gamma, f),
         {:ok, au} <- walk(arg_mode(f, mode), gamma, a) do
      {:ok, add(fu, au)}
    end
  end

  defp walk(mode, gamma, {:mnat, e, p, z, s}) do
    with {:ok, eu} <- walk(mode, gamma, e),
         {:ok, pu} <- under(:spec, gamma, p, 1),
         {:ok, zu} <- walk(mode, gamma, z),
         {:ok, su} <- walk_pred(mode, gamma, e, s) do
      {:ok, add(add(eu, pu), max_uses(zu, su))}
    end
  end

  defp walk(mode, gamma, {:mdata, e, p, bs}) do
    with {:ok, eu} <- walk(mode, gamma, e),
         {:ok, pu} <- under(:spec, gamma, p, 1),
         {:ok, bu} <- walk_data(mode, gamma, bs) do
      {:ok, add(add(eu, pu), bu)}
    end
  end

  defp walk(mode, gamma, {:memp, e, p}) do
    with {:ok, eu} <- walk(mode, gamma, e),
         {:ok, pu} <- under(:spec, gamma, p, 1) do
      {:ok, add(eu, pu)}
    end
  end

  defp walk(mode, gamma, {:munit, e, p, u}) do
    with {:ok, eu} <- walk(mode, gamma, e),
         {:ok, pu} <- under(:spec, gamma, p, 1),
         {:ok, uu} <- walk(mode, gamma, u) do
      {:ok, add(add(eu, pu), uu)}
    end
  end

  defp walk(mode, gamma, {:matom, e, p, bs}) do
    with {:ok, eu} <- walk(mode, gamma, e),
         {:ok, pu} <- under(:spec, gamma, p, 1),
         {:ok, bu} <- max_bodies(mode, gamma, bs) do
      {:ok, add(add(eu, pu), bu)}
    end
  end

  defp walk(_mode, gamma, {:idt, a, x, y}) do
    with {:ok, au} <- walk(:spec, gamma, a),
         {:ok, xu} <- walk(:spec, gamma, x),
         {:ok, yu} <- walk(:spec, gamma, y) do
      {:ok, add(au, add(xu, yu))}
    end
  end

  # The kernel discards the equation's uses. The motive is a type.
  defp walk(mode, gamma, {:rwt, _eq, p, t}) do
    with {:ok, pu} <- under(:spec, gamma, p, 1),
         {:ok, tu} <- walk(mode, gamma, t) do
      {:ok, add(pu, tu)}
    end
  end

  defp walk(mode, gamma, {:ann, e, a}) do
    with {:ok, eu} <- walk(mode, gamma, e),
         {:ok, au} <- walk(:spec, gamma, a) do
      {:ok, add(eu, au)}
    end
  end

  defp walk(_mode, gamma, {:prod, a, b}) do
    with {:ok, au} <- walk(:spec, gamma, a),
         {:ok, bu} <- walk(:spec, gamma, b) do
      {:ok, add(au, bu)}
    end
  end

  defp walk(mode, gamma, {:pair, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:su, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:bisim, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:unf, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:ucons, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:scat, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:slen, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:seq, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:bcat, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:blen, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:beq, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:xlen, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:xeq, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:bsub, a, b, c}), do: walk_add(mode, gamma, [a, b, c])
  defp walk(mode, gamma, {:bget, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:aget, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:bunc, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:sbytes, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:btil, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:baft, a, b}), do: walk_add(mode, gamma, [a, b])

  defp walk(mode, gamma, {tag, ty, z, f, s}) when tag in [:bfold, :afold] do
    with {:ok, tu} <- walk(:spec, gamma, ty),
         {:ok, ru} <- walk_add(mode, gamma, [z, f, s]) do
      {:ok, add(tu, ru)}
    end
  end

  defp walk(mode, gamma, {:tensor, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:addi, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:muli, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:addt, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:toi64, t}), do: walk(mode, gamma, t)
  defp walk(mode, gamma, {:packi, a, b}), do: walk_add(mode, gamma, [a, b])
  defp walk(mode, gamma, {:word, _op, args}), do: walk_add(mode, gamma, args)

  defp walk(mode, gamma, {:letp, e, t}) do
    with {:ok, eu} <- walk(mode, gamma, e),
         {:ok, tu} <- under(mode, gamma, t, 2) do
      {:ok, add(eu, tu)}
    end
  end

  defp walk(_mode, gamma, {:nu, f}), do: under(:spec, gamma, f, 1)

  defp walk(_mode, _gamma, leaf)
       when leaf in [
              :typ,
              :nat,
              :ze,
              :unit,
              :one,
              :empty,
              :rfl,
              :atom,
              :string,
              :bytes,
              :slice,
              :i64,
              :f32ty
            ],
       do: {:ok, %{}}

  defp walk(_mode, _gamma, {:nat, n}) when is_integer(n), do: {:ok, %{}}
  defp walk(_mode, _gamma, {:atom, _}), do: {:ok, %{}}
  defp walk(_mode, _gamma, {:slit, _}), do: {:ok, %{}}
  defp walk(_mode, _gamma, {:blit, _}), do: {:ok, %{}}
  defp walk(_mode, _gamma, {:def, _}), do: {:ok, %{}}
  defp walk(_mode, _gamma, {:hole, _}), do: {:ok, %{}}

  defp walk(_mode, _gamma, _other), do: {:error, "a grade does not cover this term"}

  # A literal erased λ checks its argument as a type. A named function
  # is not adjusted: the grade is the binder's own occurrences.
  defp arg_mode({:lam, q, _, _, _}, mode) do
    if kernel_qty(q) == :erased, do: :spec, else: mode
  end

  defp arg_mode(_, mode), do: mode

  defp walk_pred(mode, gamma, scrut, s) do
    q = pred_grade(gamma, scrut)

    with {:ok, su} <- walk(mode, [q | gamma], s),
         {spent, rest} = pop(su),
         :ok <- constrain(mode, q, spent) do
      {:ok, rest}
    end
  end

  # The predecessor of a variable inherits that grade. Any other
  # scrutinee is the affine interval, and its type grade is ω.
  defp pred_grade(gamma, {:var, x}) do
    case Enum.at(gamma, x) do
      {:grade, _, _} = q -> q
      _ -> {:grade, {:iv, 0, 1}, :w}
    end
  end

  defp pred_grade(_gamma, _e), do: {:grade, {:iv, 0, 1}, :w}

  defp under(mode, gamma, term, n) do
    with {:ok, uses} <- walk(mode, push_absent(gamma, n), term) do
      pop_n(uses, n)
    end
  end

  defp push_absent(gamma, 0), do: gamma
  defp push_absent(gamma, n), do: push_absent([:absent | gamma], n - 1)

  defp pop_n(uses, 0), do: {:ok, uses}

  defp pop_n(uses, n) do
    {_spent, rest} = pop(uses)
    pop_n(rest, n - 1)
  end

  defp walk_data(mode, gamma, branches) do
    Enum.reduce_while(branches, {:ok, %{}}, fn {_name, arity, body}, {:ok, acc} ->
      case under(mode, gamma, body, arity) do
        {:ok, uses} -> {:cont, {:ok, max_uses(acc, uses)}}
        err -> {:halt, err}
      end
    end)
  end

  defp max_bodies(mode, gamma, branches) do
    Enum.reduce_while(branches, {:ok, %{}}, fn {_name, body}, {:ok, acc} ->
      case walk(mode, gamma, body) do
        {:ok, uses} -> {:cont, {:ok, max_uses(acc, uses)}}
        err -> {:halt, err}
      end
    end)
  end

  defp walk_add(mode, gamma, terms) do
    Enum.reduce_while(terms, {:ok, %{}}, fn t, {:ok, acc} ->
      case walk(mode, gamma, t) do
        {:ok, uses} -> {:cont, {:ok, add(acc, uses)}}
        err -> {:halt, err}
      end
    end)
  end

  defp pop(uses) do
    spent = Map.get(uses, 0, {0, 0})

    rest =
      uses
      |> Map.delete(0)
      |> Map.new(fn {i, v} -> {i - 1, v} end)

    {spent, rest}
  end

  defp add(left, right) do
    Map.merge(left, right, fn _i, {c1, t1}, {c2, t2} ->
      {add_count(c1, c2), add_count(t1, t2)}
    end)
  end

  defp max_uses(left, right) do
    Map.merge(left, right, fn _i, {c1, t1}, {c2, t2} ->
      {max_count(c1, c2), max_count(t1, t2)}
    end)
  end

  defp add_count(:w, _), do: :w
  defp add_count(_, :w), do: :w
  defp add_count(a, b), do: a + b

  defp max_count(:w, _), do: :w
  defp max_count(_, :w), do: :w
  defp max_count(a, b), do: max(a, b)

  # Spec forgets the computational grade. A quantity that is not a grade
  # is the kernel's, and the kernel already accepted it.
  defp constrain(:spec, {:grade, _c, t}, {_comp, typ}), do: satisfy_type(t, typ)

  defp constrain(mode, {:grade, c, t}, {comp, typ}) when mode in [:run, :evidence] do
    with :ok <- satisfy(c, comp), do: satisfy_type(t, typ)
  end

  defp constrain(_mode, _qty, _spent), do: :ok

  defp satisfy(g, k) do
    if sat?(g, k), do: :ok, else: {:error, refuse(g, k)}
  end

  defp satisfy_type(g, k) do
    if sat?(g, k), do: :ok, else: {:error, type_refuse(g, k)}
  end

  defp sat?(n, k) when is_integer(n) and is_integer(k), do: n == k
  defp sat?(n, :w) when is_integer(n), do: false
  defp sat?(:w, _), do: true
  defp sat?({:iv, :w, :w}, _), do: true
  defp sat?({:iv, lo, hi}, k) when is_integer(k), do: point_le(lo, k) and point_le(k, hi)
  defp sat?({:iv, _lo, hi}, :w), do: hi == :w
  defp sat?(_, _), do: false

  defp point_le(a, b) when is_integer(a) and is_integer(b), do: a <= b
  # ω is the top of the chain, so a point is ≤ ω, and ω is not ≤ a finite point.
  defp point_le(_a, :w), do: true
  defp point_le(:w, b) when is_integer(b), do: false

  defp refuse(0, _), do: "erased variable used computationally"
  defp refuse(1, 0), do: "linear variable unused"
  defp refuse(1, :w), do: "affine variable used as reusable"
  defp refuse({:iv, 0, 1}, :w), do: "affine variable used as reusable"
  defp refuse(g, k), do: "grade #{show(g)} does not allow #{show_count(k)} uses"

  defp type_refuse(g, k), do: "type grade #{show(g)} does not allow #{show_count(k)} uses"
end
