defmodule Muro.GuardTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Parser}

  defp book(head, fact \\ "{0 ≡ suc(0) : Nat}") do
    src = """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A
    def zeros : run Stream Nat := unfold 0 (λ (_ : Nat) → (0, 0))
    def eq : evidence {0 ≡ 0 : Nat} := refl
    def Fact : spec Type := #{fact}
    def P : spec Π (_ : Nat) → Type := λ (_ : Nat) → Fact
    def bad : evidence Π (h : Always Nat P zeros → Fact) → Always Nat P zeros :=
      λ (h : Always Nat P zeros → Fact) →
        unfold tt (λ (_ : Unit) → (#{head}, bad h))
    """

    assert {:ok, book} = Parser.parse(src)
    book
  end

  defp reject(book) do
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "bad body: unguarded recursive call"
  end

  test "an unwrapped recursive head is rejected" do
    reject(book("h (bad h)"))
  end

  test "rewrite does not hide a recursive head" do
    reject(book("rewrite eq motive (λ _ → Fact) in h (bad h)"))
  end

  test "a Nat match does not hide a recursive head" do
    reject(
      book("""
      match 0 motive (λ _ → Fact)
        | 0 => h (bad h)
        | suc n => h (bad h)
      """)
    )
  end

  test "Empty elimination does not hide a recursive head" do
    reject(book("matchEmpty (h (bad h)) motive (λ _ → Empty)", "Empty"))
  end

  test "an annotation does not hide a recursive head" do
    reject(wrap_head(book("h (bad h)"), &{:ann, &1, {:var, "Fact"}}))
  end

  test "a Unit match does not hide a recursive head" do
    reject(wrap_head(book("h (bad h)"), &{:munit, :one, "_", {:var, "Fact"}, &1}))
  end

  test "a nonrecursive rewritten head still checks" do
    assert Check.check_sig(book("rewrite eq motive (λ _ → Fact) in refl", "{0 ≡ 0 : Nat}")) ==
             :ok
  end

  defp wrap_head(book, wrap) do
    Enum.map(book, fn
      %{name: "bad", body: {:lam, q, a, x, {:unf, seed, {:lam, q1, s, y, {:pair, h, t}}}}} = d ->
        %{d | body: {:lam, q, a, x, {:unf, seed, {:lam, q1, s, y, {:pair, wrap.(h), t}}}}}

      d ->
        d
    end)
  end
end
