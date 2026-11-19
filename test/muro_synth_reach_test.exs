defmodule Muro.SynthReachTest do
  use ExUnit.Case, async: true

  alias Muro.Synth.{Reach, Term}

  @schema {:data, "State", [%{name: "at", fields: [:nat]}]}

  test "a closed cover's refl chain agrees one horizon at a time" do
    {text, zero} = tabulated()

    assert text =~ "def dyn-reach-holds"
    assert text =~ "dyn-best-pos #{zero.spell} 0"
    assert text =~ "dyn-best-pos #{zero.spell} 1"
    assert text =~ "dyn-any #{zero.spell} 0"
    assert text =~ "dyn-best-pos #{zero.spell} 2"
    assert text =~ "dyn-any #{zero.spell} 1"
    assert text =~ "def dyn-any-rec"
    assert text =~ "def dyn-known"

    path = write!(chain_book(text))
    assert Muro.check_file(path) == :ok
  end

  test "a flipped table cell fails dyn-reach-holds" do
    {text, _zero} = tabulated()
    flipped = flip_known!(text)
    refute flipped == text

    path = write!(base_book(flipped))
    assert {:error, diagnostic} = Muro.check_file(path)
    assert diagnostic =~ "dyn-reach-holds-at-0-1"
    assert diagnostic =~ "cannot convert false ≁ true"

    cited = cited_line(path, diagnostic)
    assert cited =~ "def dyn-reach-holds-at-0-1"
    assert cited =~ "dyn-best-pos (at 0) 1 ≡ dyn-any (at 0) 0"
  end

  test "an open cover is the recurrence and does not consult dyn-known" do
    here = %Term{value: :here, spell: "here", label: "here"}
    schema = {:open, "opaque"}

    assert :open =
             Term.cover_match(
               schema,
               "s",
               [here],
               fn _src -> "Bool" end,
               fn _spell -> "true" end,
               fn src -> src end
             )

    host = %{
      schema: schema,
      horizon: 1,
      actions: ["go"],
      all_states: [here],
      step: fn state, "go" -> {state, 1} end
    }

    {text, _taken} =
      Reach.sources(host, "dyn-best-pos", "dyn-one", "dyn-any", "dyn-pos", MapSet.new())

    assert text =~ "def dyn-best-pos"
    assert text =~ "| suc j => dyn-any s j"
    refute text =~ "dyn-known"
    refute text =~ "dyn-any-rec"
    refute text =~ "dyn-reach-holds"

    path =
      write!("""
      import "std:bool.muro"

      data State : Type where
        here : State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (a : Action) →
          match s motive (λ _ → State × Nat)
            | here =>
                (match a motive (λ _ → State × Nat)
                  | go => (here, suc 0))

      def dyn-pos : run Π (r : Nat) → Bool :=
        λ (r : Nat) →
          match r motive (λ _ → Bool)
            | 0 => false
            | suc _ => true

      #{text}
      def pays : evidence {dyn-best-pos here (suc 0) ≡ true : Bool} := refl
      """)

    assert Muro.check_file(path) == :ok
  end

  test "a state off the cover is decided by the recurrence" do
    zero = Term.decode!({:at, 0}, @schema)

    host = %{
      schema: @schema,
      horizon: 1,
      actions: ["go", "stay"],
      all_states: [zero],
      step: fn ^zero, action when action in ["go", "stay"] -> {zero, 0} end
    }

    {text, _taken} =
      Reach.sources(host, "dyn-best-pos", "dyn-one", "dyn-any", "dyn-pos", MapSet.new())

    assert text =~ "def dyn-known"
    assert text =~ "dyn-any-rec"
    assert text =~ "dyn-best-pos (at 0) 0"
    assert text =~ "dyn-best-pos (at 0) 1"

    path =
      write!("""
      import "std:bool.muro"

      data State : Type where
        at : Π (_ : Nat) → State

      data Action : Type where
        go : Action
        stay : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (a : Action) →
          match s motive (λ _ → State × Nat)
            | at n =>
                (match a motive (λ _ → State × Nat)
                  | go =>
                      (match n motive (λ _ → State × Nat)
                        | 0 => (at 0, 0)
                        | suc k => (at (suc k), suc 0))
                  | stay =>
                      (match n motive (λ _ → State × Nat)
                        | 0 => (at 0, 0)
                        | suc k => (at (suc k), 0)))

      def dyn-pos : run Π (r : Nat) → Bool :=
        λ (r : Nat) →
          match r motive (λ _ → Bool)
            | 0 => false
            | suc _ => true

      #{text}
      def on-cover : evidence {dyn-best-pos (at 0) (suc 0) ≡ false : Bool} := refl
      def off-cover : evidence {dyn-best-pos (at (suc 0)) (suc 0) ≡ true : Bool} := refl
      """)

    assert Muro.check_file(path) == :ok
  end

  defp tabulated do
    zero = Term.decode!({:at, 0}, @schema)
    one = Term.decode!({:at, 1}, @schema)

    host = %{
      schema: @schema,
      horizon: 2,
      actions: ["go", "stay"],
      all_states: [zero, one],
      step: fn state, action ->
        case {state.value, action} do
          {{:at, 0}, "go"} -> {one, 1}
          {{:at, 0}, "stay"} -> {zero, 0}
          {{:at, _n}, "go"} -> {one, 0}
          {{:at, _n}, "stay"} -> {state, 0}
        end
      end
    }

    {text, _taken} =
      Reach.sources(host, "dyn-best-pos", "dyn-one", "dyn-any", "dyn-pos", MapSet.new())

    {text, zero}
  end

  defp chain_book(text) do
    base_book(text) <>
      """
      def any-step-0 : evidence {dyn-any (at 0) 0 ≡ dyn-any-rec (at 0) 0 : Bool} := refl
      def any-step-1 : evidence {dyn-any (at 0) 1 ≡ dyn-any-rec (at 0) 1 : Bool} := refl
      """
  end

  defp base_book(text) do
    """
    import "std:bool.muro"

    data State : Type where
      at : Π (_ : Nat) → State

    data Action : Type where
      go : Action
      stay : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match s motive (λ _ → State × Nat)
          | at n =>
              (match a motive (λ _ → State × Nat)
                | go =>
                    (match n motive (λ _ → State × Nat)
                      | 0 => (at (suc 0), suc 0)
                      | suc _ => (at (suc 0), 0))
                | stay =>
                    (match n motive (λ _ → State × Nat)
                      | 0 => (at 0, 0)
                      | suc m => (at (suc m), 0)))

    def dyn-pos : run Π (r : Nat) → Bool :=
      λ (r : Nat) →
        match r motive (λ _ → Bool)
          | 0 => false
          | suc _ => true

    #{text}
    """
  end

  defp flip_known!(text) do
    [head, rest] = String.split(text, "def dyn-known", parts: 2)
    [known, tail] = String.split(rest, "def dyn-one", parts: 2)
    assert known =~ "| 0 => true"

    head <>
      "def dyn-known" <>
      String.replace(known, "| 0 => true", "| 0 => false", global: false) <> "def dyn-one" <> tail
  end

  defp cited_line(path, diagnostic) do
    [_, line, _] = Regex.run(~r/#{Regex.escape(path)}:(\d+):(\d+):/, diagnostic)
    diagnostic_line = String.to_integer(line)

    path
    |> File.read!()
    |> String.split("\n")
    |> Enum.at(diagnostic_line - 1)
  end

  defp write!(src) do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_reach_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.mkdir_p!(dir)
    path = Path.join(dir, "reach.muro")
    File.write!(path, src)
    path
  end
end
