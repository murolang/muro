defmodule Muro.Reducers.LamTest do
  use ExUnit.Case, async: true

  alias Muro.Ast
  alias Muro.Reducers.Lam
  alias Muro.Parser
  alias Muro.Policies.Chain

  # (λ (x : Nat) → 0) ((λ (y : Nat) → y) 0)
  # The outer λ discards its argument. The head contraction is 0.
  # The inner one leaves (λ (x : Nat) → 0) 0, then 0.
  defp discard do
    term!("""
    def discard : run Nat := (λ (x : Nat) → 0) ((λ (y : Nat) → y) 0)
    """)
  end

  defp ident do
    term!("""
    def ident : run Nat := (λ (x : Nat) → x) ((λ (y : Nat) → y) 0)
    """)
  end

  defp done, do: term!("def done : run Nat := 0")

  defp under do
    term!("""
    def under : run Π (x : Nat) → Nat := λ (x : Nat) → (λ (y : Nat) → y) x
    """)
  end

  test "a head contraction that discards its argument stops sooner" do
    term = discard()
    assert Lam.candidates(term) == [[], [:arg]]
    assert Lam.head_path(term) == {:ok, []}
    assert Lam.act(term, :spine) == {:ok, :ze}
    assert Lam.steps(term, :spine) == 1
    assert Lam.steps(term, :other) == 2
    assert Lam.fewer?(term, :spine, :other)
    refute Lam.fewer?(term, :other, :spine)
    assert Lam.reduce(term, [:fun]) == :error
  end

  test "an identity ties the two contractions, and a stopped head ties them" do
    term = ident()
    assert Lam.steps(term, :spine) == 2
    assert Lam.steps(term, :other) == 2
    assert Lam.fewer?(term, :spine, :other)
    assert Lam.fewer?(term, :other, :spine)

    assert Lam.stopped?(done())
    assert Lam.steps(done(), :spine) == 0
    assert Lam.steps(done(), :other) == 0
  end

  test "a λ is stopped, and the application under it still contracts" do
    term = under()
    assert Lam.stopped?(term)
    assert Lam.candidates(term) == [[:body]]
    assert {:ok, body} = Lam.act(term, :other)
    assert body == {:lam, :affine, :nat, "x", {:var, 0}}
  end

  test "the head feature is the policy, and it checks" do
    term = discard()
    stopped = done()

    feat = fn :head, t -> not Lam.stopped?(t) end
    oracle = fn _pred, t -> not Lam.stopped?(t) end
    traj = fn _pred -> [term, stopped] end
    feats = fn _states -> [:head] end

    score = fn
      {:feat, _} -> 1
      _ -> 0
    end

    assert {:converged, pred} = Chain.run(score, oracle, traj, feats, feat, 0)

    src = Chain.policy([{pred, :spine}], :other, fn :head -> "s" end)

    path =
      Path.join(
        System.tmp_dir!(),
        "muro_contract_policy_#{System.unique_integer([:positive])}.muro"
      )

    File.write!(path, src)
    assert Muro.check_file(path) == :ok
    assert {:ok, out} = Muro.emit_file(path, Muro.LamPolicy)
    Code.eval_string(out)
    assert apply(Muro.LamPolicy, :policy, [true]) == :spine
    assert apply(Muro.LamPolicy, :policy, [false]) == :other

    action = apply(Muro.LamPolicy, :policy, [feat.(:head, term)])
    assert Lam.act(term, action) == {:ok, :ze}
  end

  defp term!(src) do
    assert {:ok, [defn]} = Parser.parse(src)
    assert {:ok, db} = Ast.to_db(defn.body)
    db
  end
end
