defmodule Muro.Reducers.CountTest do
  use ExUnit.Case, async: true

  alias Muro.{Ast, Parser}
  alias Muro.Policies.Chain
  alias Muro.Reducers.Lam

  @names ~w(affine discard copy_discard copy_ready copy2 copy4 copy8)

  setup_all do
    src = File.read!("examples/lam_uses.muro")
    assert {:ok, book} = Parser.parse(src)

    defs =
      Map.new(book, fn defn ->
        assert {:ok, body} = Ast.to_db(defn.body)
        {defn.name, body}
      end)

    terms = Map.new(@names, fn name -> {name, inline(Map.fetch!(defs, name), defs)} end)
    {:ok, terms: terms}
  end

  test "the policy is asked at every term, and a copied redex costs fewer substitutions", %{
    terms: terms
  } do
    states = Map.values(terms)
    oracle = fn _pred, term -> arg_better?(term) end

    score = fn _pred -> 1 end
    feats = fn _states -> [:reuse, :arg_redex, :discard] end

    assert {:converged, pred} =
             Chain.deepen(0, 1, score, oracle, fn _ -> states end, feats, &feat/2)

    chain = [{pred, :arg}]
    choose = fn term -> Chain.eval_chain(chain, :spine, &feat/2, term) end
    spine = fn _term -> :spine end

    counts =
      Map.new(terms, fn {name, term} ->
        assert {:ok, whnf} = Lam.follow(term, spine)
        assert {:ok, lva} = Lam.follow(term, choose)
        {name, %{whnf: whnf, lva: lva}}
      end)

    # One use, or a copied λ that is already a value: the two ways match.
    assert counts["affine"].lva == counts["affine"].whnf
    assert counts["discard"].lva == counts["discard"].whnf
    assert counts["copy_discard"].lva == counts["copy_discard"].whnf
    assert counts["copy_ready"].lva == counts["copy_ready"].whnf

    # A copied argument that is itself a λ application: asking the policy
    # at every term substitutes it once.
    assert counts["copy2"].lva < counts["copy2"].whnf
    assert counts["copy4"].lva < counts["copy4"].whnf
    assert counts["copy8"].lva < counts["copy8"].whnf

    assert counts["copy8"].whnf - counts["copy8"].lva >
             counts["copy2"].whnf - counts["copy2"].lva

    assert pred ==
             {:and, {:feat, :reuse}, {:and, {:feat, :arg_redex}, {:not, {:feat, :discard}}}}
  end

  defp arg_better?(term) do
    with {:ok, spine_n} <- Lam.follow(term, fn _ -> :spine end),
         {:ok, arg_n} <- arg_then_spine(term) do
      arg_n < spine_n
    else
      _ -> false
    end
  end

  defp arg_then_spine(term) do
    case Lam.act(term, :arg) do
      {:ok, next} ->
        case Lam.follow(next, fn _ -> :spine end) do
          {:ok, n} -> {:ok, n + 1}
          other -> other
        end

      :error ->
        Lam.follow(term, fn _ -> :spine end)
    end
  end

  defp feat(:reuse, term) do
    match?({:ok, _path, {:app, {:lam, :reuse, _, _, _}, _}}, Lam.head_app(term))
  end

  defp feat(:arg_redex, term) do
    case Lam.head_app(term) do
      {:ok, _path, {:app, {:lam, _, _, _, _}, arg}} -> Lam.head_path(arg) != :error
      _ -> false
    end
  end

  defp feat(:discard, term) do
    case Lam.head_app(term) do
      {:ok, _path, {:app, {:lam, _, _, _, body}, _}} -> not occurs?(0, body)
      _ -> false
    end
  end

  defp occurs?(i, {:var, j}), do: i == j
  defp occurs?(i, {:lam, _, a, _, b}), do: occurs?(i, a) or occurs?(i + 1, b)
  defp occurs?(i, {:pi, _, a, _, b}), do: occurs?(i, a) or occurs?(i + 1, b)
  defp occurs?(i, {:app, f, a}), do: occurs?(i, f) or occurs?(i, a)
  defp occurs?(i, {:su, t}), do: occurs?(i, t)
  defp occurs?(_, _), do: false

  defp inline({:def, name}, defs), do: inline(Map.fetch!(defs, name), defs)
  defp inline({:app, f, a}, defs), do: {:app, inline(f, defs), inline(a, defs)}
  defp inline({:lam, q, a, x, b}, defs), do: {:lam, q, inline(a, defs), x, inline(b, defs)}
  defp inline({:pi, q, a, x, b}, defs), do: {:pi, q, inline(a, defs), x, inline(b, defs)}
  defp inline(other, _defs), do: other
end
