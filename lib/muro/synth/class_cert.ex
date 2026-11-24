defmodule Muro.Synth.ClassCert do
  @moduledoc false

  # A reach-family survivor is optimal for a binary placement MDP by one
  # truth table over its atoms. The table does not mention states. Any
  # other survivor keeps the cover split. This book does not call a Finder.

  alias Muro.Synth.Cert
  alias Muro.Synth.Names

  @atom_cap 16
  # A cover this small still gets the per-state agreement table. queens4
  # has 18 states. A larger cover certifies from the recurrence: the
  # table and the per-state observation refls grow with the states, and
  # the class lemma does not.
  @agreement_cap 64
  @bad "the reach-family ranking prefers an action that does not reach while another action does"
  @stems ["reaches-pos", "has-pos-reward"]
  @placement Path.expand("../../../examples/cshrl/lib/placement.muro", __DIR__)
  @need ~w(board-blocked board-full board-extend board-length board-column board-snoc board-same board-judge horizon bottom all-actions step)

  @doc false
  # True when this ranking will be a class proof and the cover is too
  # large for the per-state agreement. The reach runs then stay the
  # recurrence, and the book does not emit a hold per state.
  def recur_only?(host, arms, oracle) when is_list(arms) and is_binary(oracle) do
    actions = ctors(host, "Action")

    oracle != "successor" and arms != [] and actions != [] and
      Enum.all?(arms, &family?(&1.pred, actions)) and
      Enum.all?(
        arms,
        &(is_binary(&1.action) and is_binary(&1.else) and &1.action in actions and
            &1.else in actions)
      ) and
      placement?(host, actions) and cover_count(host) > @agreement_cap
  end

  def render(host, arms, oracle, bound) do
    actions = ctors(host, "Action")

    cond do
      reason = Process.get(:muro_synth_class_refusal) ->
        {:skip, reason}

      oracle == "successor" or arms == [] ->
        :fallthrough

      not Enum.all?(arms, &family?(&1.pred, actions)) ->
        :fallthrough

      not placement?(host, actions) ->
        :fallthrough

      not dyn?(bound) ->
        :fallthrough

      not Enum.all?(arms, &(&1.action in actions and &1.else in actions)) ->
        :fallthrough

      true ->
        case scan(actions, arms) do
          {:skip, reason} -> {:skip, reason}
          :ok -> emit(host, arms, bound, actions)
        end
    end
  end

  @doc false
  def family?(pred, actions) when is_list(actions), do: family_pred?(pred, actions)

  @doc false
  def scan(actions, arms) when is_list(actions) and is_list(arms) do
    cond do
      arms == [] or not Enum.all?(arms, &family?(&1.pred, actions)) ->
        :ok

      not Enum.all?(arms, &(&1.action in actions and &1.else in actions)) ->
        :ok

      true ->
        atoms = atoms_of(actions, arms)

        cond do
          length(atoms) > @atom_cap ->
            {:skip, "the reach-family truth table has #{length(atoms)} atoms"}

          bad?(actions, arms, atoms) ->
            {:skip, @bad}

          true ->
            :ok
        end
    end
  end

  defp emit(host, arms, bound, actions) do
    reward = solved_reward(File.read!(host.path))
    dyn = bound.dyn
    atoms = atoms_of(actions, arms)
    hyps = hyps(atoms)
    names = bound.names

    ctx = %{
      actions: actions,
      atoms: atoms,
      hyps: hyps,
      arms: arms,
      bound: bound,
      names: names,
      one: dyn.one,
      pos: dyn.pos,
      best: dyn.best,
      any: dyn.any,
      orb: names.orb,
      andb: names.andb,
      notb: names.notb,
      lor: "class-orb-true",
      lof: "class-orb-false",
      lat: "class-andb-true",
      laf: "class-andb-false",
      lnt: "class-notb-true",
      lnf: "class-notb-false",
      bits: %{},
      index: nil,
      winner: nil,
      goal: nil,
      eq_true: nil,
      eq_false: []
    }

    text =
      [
        "-- Class proof of the synthesized reach-family ranking.\n" <>
          "-- It does not use a Finder and it does not split the cover.\n" <>
          if(Process.get(:muro_synth_class_recur) == true,
            do: "-- The cover is past the per-state agreement, so the proof is the recurrence.\n",
            else: ""
          ),
        hypotheses(actions, reward),
        transport(names),
        tie_lemmas(),
        bridge_eqs(dyn),
        reach_defs(actions, dyn),
        conflict_def(dyn),
        arm_eqs(arms, bound, ctx),
        rank_def(bound, arms, actions),
        named_ranks(arms, bound, actions),
        win_defs(arms, actions, bound, ctx),
        apply_def(arms, bound, actions),
        preserves_def()
      ]
      |> Enum.join("\n")

    {:ok,
     %{
       text: text,
       obligations: [],
       certificate: "CoindHomo",
       also: nil,
       imports: [@placement],
       class_proof: true
     }}
  end

  defp placement?(host, actions) do
    src = File.read!(host.path)

    Enum.all?(@need, &defined?(host, &1)) and
      ctors(host, "State") == ["ongoing", "dead", "solved"] and
      actions == host.actions and actions != [] and
      String.contains?(src, "def bottom : run Reward := 0") and
      String.contains?(src, "def Reward : spec Type := Nat") and solved_reward(src) != nil
  end

  defp solved_reward(src) do
    case Regex.run(~r/solved\s+\w+\s*,\s*(\d+)/, src) do
      [_, n] ->
        k = String.to_integer(n)
        if k > 0, do: k, else: nil

      _ ->
        nil
    end
  end

  defp dyn?(%{dyn: %{one: one, pos: pos, best: best, any: any}})
       when is_binary(one) and is_binary(pos) and is_binary(best) and is_binary(any),
       do: true

  defp dyn?(_), do: false

  defp cover_count(host) do
    case host[:all_states] do
      states when is_list(states) -> length(states)
      _ -> 0
    end
  end

  defp defined?(host, name), do: Enum.any?(host.book, &(Map.get(&1, :name) == name))

  defp ctors(host, data) do
    case Enum.find(host.book, &(Map.get(&1, :kind) == :data and &1.name == data)) do
      %{ctors: ctors} -> Enum.map(ctors, & &1.name)
      _ -> []
    end
  end

  defp hypotheses(actions, reward) do
    branches =
      Enum.map_join(actions, "\n", fn action ->
        "      | #{action} => #{elem_proof(actions, action)}"
      end)

    """
    def Config : spec Type := List Nat
    def solved-reward : run Reward := #{reward}
    def class-dead : run State := dead
    def class-ongoing : run Π (#{Names.current("c")} : Config) → State :=
      λ (#{Names.current("c")} : Config) → ongoing #{Names.current("c")}
    def class-solved : run Π (#{Names.current("c")} : Config) → State :=
      λ (#{Names.current("c")} : Config) → solved #{Names.current("c")}
    def class-blocked : run Π (+ #{Names.current("c")} : Config) → Bool := board-blocked
    def class-full : run Π (#{Names.current("c")} : Config) → Bool := board-full
    def class-place : run Π (+ #{Names.current("c")} : Config) → Π (+ #{Names.current("a")} : Action) → Config := board-extend
    def class-length : run Π (#{Names.current("c")} : Config) → Nat := board-length

    def state-view : evidence Π (#{Names.current("s")} : State) → StateView #{Names.current("s")} :=
      λ (#{Names.current("s")} : State) →
        match #{Names.current("s")} motive (λ (#{Names.current("t")} : State) → StateView #{Names.current("t")})
          | ongoing #{Names.current("c")} => view-ongoing #{Names.current("c")}
          | dead => view-dead
          | solved #{Names.current("c")} => view-solved #{Names.current("c")}

    def zero-lt-R : evidence le (suc bottom) solved-reward := tt

    def board-same-nat : evidence Π (#{Names.current("m")} : Nat) → Π (#{Names.current("n")} : Nat) →
                                  {board-same #{Names.current("m")} #{Names.current("n")} ≡ nat-eq #{Names.current("m")} #{Names.current("n")} : Bool} :=
      λ (#{Names.current("m")} : Nat) →
        match #{Names.current("m")} motive (λ (#{Names.current("x")} : Nat) → Π (#{Names.current("n")} : Nat) → {board-same #{Names.current("x")} #{Names.current("n")} ≡ nat-eq #{Names.current("x")} #{Names.current("n")} : Bool})
          | 0 => λ (#{Names.current("n")} : Nat) →
              match #{Names.current("n")} motive (λ (#{Names.current("y")} : Nat) → {board-same 0 #{Names.current("y")} ≡ nat-eq 0 #{Names.current("y")} : Bool})
                | 0 => refl
                | suc _ => refl
          | suc #{Names.current("m1")} => λ (#{Names.current("n")} : Nat) →
              match #{Names.current("n")} motive (λ (#{Names.current("y")} : Nat) → {board-same (suc #{Names.current("m1")}) #{Names.current("y")} ≡ nat-eq (suc #{Names.current("m1")}) #{Names.current("y")} : Bool})
                | 0 => refl
                | suc #{Names.current("n1")} => board-same-nat #{Names.current("m1")} #{Names.current("n1")}

    def full-is-length : evidence Π (#{Names.current("c")} : Config) →
                                  {class-full #{Names.current("c")} ≡ nat-eq (class-length #{Names.current("c")}) horizon : Bool} :=
      λ (#{Names.current("c")} : Config) → board-same-nat (class-length #{Names.current("c")}) horizon

    def step-dead : evidence Π (#{Names.current("a")} : Action) →
                             {step class-dead #{Names.current("a")} ≡ (class-dead, bottom) : State × Reward} :=
      λ (#{Names.current("a")} : Action) → refl

    def step-solved : evidence Π (#{Names.current("c")} : Config) → Π (#{Names.current("a")} : Action) →
                               {step (class-solved #{Names.current("c")}) #{Names.current("a")} ≡ (class-solved #{Names.current("c")}, solved-reward) : State × Reward} :=
      λ (#{Names.current("c")} : Config) → λ (#{Names.current("a")} : Action) → refl

    def step-ongoing : evidence Π (#{Names.current("c")} : Config) → Π (#{Names.current("a")} : Action) →
                                {step (class-ongoing #{Names.current("c")}) #{Names.current("a")} ≡ class-judge (class-place #{Names.current("c")} #{Names.current("a")}) : State × Reward} :=
      λ (#{Names.current("c")} : Config) → λ (#{Names.current("a")} : Action) → refl

    def length-snoc : evidence Π (#{Names.current("xs")} : List Nat) → Π (#{Names.current("x")} : Nat) →
                               {board-length (board-snoc #{Names.current("xs")} #{Names.current("x")}) ≡ suc (board-length #{Names.current("xs")}) : Nat} :=
      λ (#{Names.current("xs")} : List Nat) → λ (#{Names.current("x")} : Nat) →
        match #{Names.current("xs")} motive (λ (#{Names.current("ys")} : List Nat) → {board-length (board-snoc #{Names.current("ys")} #{Names.current("x")}) ≡ suc (board-length #{Names.current("ys")}) : Nat})
          | nil => refl
          | cons #{Names.current("y")} #{Names.current("ys")} =>
              rewrite length-snoc #{Names.current("ys")} #{Names.current("x")} motive (λ #{Names.current("z")} → {suc #{Names.current("z")} ≡ suc (suc (board-length #{Names.current("ys")})) : Nat}) in
              refl

    def length-place : evidence Π (#{Names.current("c")} : Config) → Π (#{Names.current("a")} : Action) →
                                {class-length (class-place #{Names.current("c")} #{Names.current("a")}) ≡ suc (class-length #{Names.current("c")}) : Nat} :=
      λ (#{Names.current("c")} : Config) → λ (#{Names.current("a")} : Action) → length-snoc #{Names.current("c")} (board-column #{Names.current("a")})

    def in-actions : evidence Π (#{Names.current("a")} : Action) → Elem #{Names.current("a")} all-actions :=
      λ (#{Names.current("a")} : Action) →
        match #{Names.current("a")} motive (λ (#{Names.current("x")} : Action) → Elem #{Names.current("x")} all-actions)
    #{branches}
    """
  end

  defp elem_proof(actions, target), do: elem_from(actions, target)

  defp elem_from([target | rest], target), do: "elem-here #{target} #{list_term(rest)}"

  defp elem_from([head | rest], target) do
    "elem-there #{target} #{head} #{list_term(rest)} (#{elem_from(rest, target)})"
  end

  defp list_term([]), do: "nil"
  defp list_term([head | tail]), do: "(cons #{head} #{list_term(tail)})"

  defp transport(names) do
    o = names.orb
    a = names.andb
    n = names.notb

    """
    def class-orb-true : evidence Π (#{Names.current("a")} : Bool) → Π (#{Names.current("b")} : Bool) →
                                  Π (#{Names.current("h")} : {#{Names.current("a")} ≡ true : Bool}) →
                                  {#{o} #{Names.current("a")} #{Names.current("b")} ≡ true : Bool} :=
      λ (#{Names.current("a")} : Bool) → λ (#{Names.current("b")} : Bool) → λ (#{Names.current("h")} : {#{Names.current("a")} ≡ true : Bool}) →
        rewrite #{Names.current("h")} motive (λ #{Names.current("z")} → {#{o} #{Names.current("z")} #{Names.current("b")} ≡ true : Bool}) in refl

    def class-orb-false : evidence Π (#{Names.current("a")} : Bool) → Π (#{Names.current("b")} : Bool) → Π (#{Names.current("c")} : Bool) →
                                   Π (#{Names.current("ha")} : {#{Names.current("a")} ≡ false : Bool}) →
                                   Π (#{Names.current("hb")} : {#{Names.current("b")} ≡ #{Names.current("c")} : Bool}) →
                                   {#{o} #{Names.current("a")} #{Names.current("b")} ≡ #{Names.current("c")} : Bool} :=
      λ (#{Names.current("a")} : Bool) → λ (#{Names.current("b")} : Bool) → λ (#{Names.current("c")} : Bool) →
      λ (#{Names.current("ha")} : {#{Names.current("a")} ≡ false : Bool}) → λ (#{Names.current("hb")} : {#{Names.current("b")} ≡ #{Names.current("c")} : Bool}) →
        rewrite #{Names.current("ha")} motive (λ #{Names.current("z")} → {#{o} #{Names.current("z")} #{Names.current("b")} ≡ #{Names.current("c")} : Bool}) in
          (rewrite #{Names.current("hb")} motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ #{Names.current("c")} : Bool}) in refl)

    def class-andb-true : evidence Π (#{Names.current("a")} : Bool) → Π (#{Names.current("b")} : Bool) → Π (#{Names.current("c")} : Bool) →
                                   Π (#{Names.current("ha")} : {#{Names.current("a")} ≡ true : Bool}) →
                                   Π (#{Names.current("hb")} : {#{Names.current("b")} ≡ #{Names.current("c")} : Bool}) →
                                   {#{a} #{Names.current("a")} #{Names.current("b")} ≡ #{Names.current("c")} : Bool} :=
      λ (#{Names.current("a")} : Bool) → λ (#{Names.current("b")} : Bool) → λ (#{Names.current("c")} : Bool) →
      λ (#{Names.current("ha")} : {#{Names.current("a")} ≡ true : Bool}) → λ (#{Names.current("hb")} : {#{Names.current("b")} ≡ #{Names.current("c")} : Bool}) →
        rewrite #{Names.current("ha")} motive (λ #{Names.current("z")} → {#{a} #{Names.current("z")} #{Names.current("b")} ≡ #{Names.current("c")} : Bool}) in
          (rewrite #{Names.current("hb")} motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ #{Names.current("c")} : Bool}) in refl)

    def class-andb-false : evidence Π (#{Names.current("a")} : Bool) → Π (#{Names.current("b")} : Bool) →
                                    Π (#{Names.current("h")} : {#{Names.current("a")} ≡ false : Bool}) →
                                    {#{a} #{Names.current("a")} #{Names.current("b")} ≡ false : Bool} :=
      λ (#{Names.current("a")} : Bool) → λ (#{Names.current("b")} : Bool) → λ (#{Names.current("h")} : {#{Names.current("a")} ≡ false : Bool}) →
        rewrite #{Names.current("h")} motive (λ #{Names.current("z")} → {#{a} #{Names.current("z")} #{Names.current("b")} ≡ false : Bool}) in refl

    def class-notb-true : evidence Π (#{Names.current("a")} : Bool) → Π (#{Names.current("h")} : {#{Names.current("a")} ≡ false : Bool}) →
                                   {#{n} #{Names.current("a")} ≡ true : Bool} :=
      λ (#{Names.current("a")} : Bool) → λ (#{Names.current("h")} : {#{Names.current("a")} ≡ false : Bool}) →
        rewrite #{Names.current("h")} motive (λ #{Names.current("z")} → {#{n} #{Names.current("z")} ≡ true : Bool}) in refl

    def class-notb-false : evidence Π (#{Names.current("a")} : Bool) → Π (#{Names.current("h")} : {#{Names.current("a")} ≡ true : Bool}) →
                                    {#{n} #{Names.current("a")} ≡ false : Bool} :=
      λ (#{Names.current("a")} : Bool) → λ (#{Names.current("h")} : {#{Names.current("a")} ≡ true : Bool}) →
        rewrite #{Names.current("h")} motive (λ #{Names.current("z")} → {#{n} #{Names.current("z")} ≡ false : Bool}) in refl
    """
  end

  defp tie_lemmas do
    """
    def class-hit-ask : run Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("y")} : Action) → Bool :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("y")} : Action) → hit #{Names.current("s")} #{Names.current("y")} horizon

    def class-cons-false : evidence Π (+ #{Names.current("ask")} : Π (+ #{Names.current("y")} : Action) → Bool) →
                                    Π (+ #{Names.current("x")} : Action) →
                                    Π (#{Names.current("rest")} : List Action) →
                                    Π (#{Names.current("hf")} : {#{Names.current("ask")} #{Names.current("x")} ≡ false : Bool}) →
                                    Π (#{Names.current("hr")} : {hit-fold #{Names.current("ask")} #{Names.current("rest")} ≡ false : Bool}) →
                                    {hit-fold #{Names.current("ask")} (cons #{Names.current("x")} #{Names.current("rest")}) ≡ false : Bool} :=
      λ (+ #{Names.current("ask")} : Π (+ #{Names.current("y")} : Action) → Bool) → λ (+ #{Names.current("x")} : Action) → λ (#{Names.current("rest")} : List Action) →
      λ (#{Names.current("hf")} : {#{Names.current("ask")} #{Names.current("x")} ≡ false : Bool}) →
      λ (#{Names.current("hr")} : {hit-fold #{Names.current("ask")} #{Names.current("rest")} ≡ false : Bool}) →
        rewrite (fold-cons-eq #{Names.current("ask")} #{Names.current("x")} #{Names.current("rest")})
          motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ false : Bool})
        in
        rewrite #{Names.current("hf")}
          motive (λ #{Names.current("b")} →
            {(match #{Names.current("b")} motive (λ _ → Bool)
               | true => true
               | false => hit-fold #{Names.current("ask")} #{Names.current("rest")}) ≡ false : Bool})
        in #{Names.current("hr")}
    """
  end

  defp bridge_eqs(dyn) do
    """
    def class-pos-eq : evidence Π (#{Names.current("q")} : Reward) → {#{dyn.pos} #{Names.current("q")} ≡ class-pos #{Names.current("q")} : Bool} :=
      λ (#{Names.current("q")} : Reward) →
        match #{Names.current("q")} motive (λ #{Names.current("x")} → {#{dyn.pos} #{Names.current("x")} ≡ class-pos #{Names.current("x")} : Bool})
          | 0 => refl
          | suc _ => refl

    def class-best-eq : evidence Π (+ #{Names.current("t")} : State) → Π (+ #{Names.current("n")} : Nat) →
                                 {#{dyn.best} #{Names.current("t")} #{Names.current("n")} ≡
                                  (match #{Names.current("n")} motive (λ _ → Bool)
                                    | 0 => false
                                    | suc #{Names.current("j")} => #{dyn.any} #{Names.current("t")} #{Names.current("j")}) : Bool} :=
      λ (+ #{Names.current("t")} : State) → λ (+ #{Names.current("n")} : Nat) → refl

    def class-one-eq : evidence Π (+ #{Names.current("t")} : State) → Π (+ #{Names.current("b")} : Action) → Π (+ #{Names.current("n")} : Nat) →
                                {#{dyn.one} #{Names.current("t")} #{Names.current("b")} #{Names.current("n")} ≡
                                 (match (#{dyn.pos} (snd (step #{Names.current("t")} #{Names.current("b")}))) motive (λ _ → Bool)
                                   | true => true
                                   | false => #{dyn.best} (fst (step #{Names.current("t")} #{Names.current("b")})) #{Names.current("n")}) : Bool} :=
      λ (+ #{Names.current("t")} : State) → λ (+ #{Names.current("b")} : Action) → λ (+ #{Names.current("n")} : Nat) → refl

    def class-any-eq : evidence Π (+ #{Names.current("t")} : State) → Π (+ #{Names.current("n")} : Nat) →
                                {#{dyn.any} #{Names.current("t")} #{Names.current("n")} ≡
                                 hit-fold (λ (+ #{Names.current("b")} : Action) → #{dyn.one} #{Names.current("t")} #{Names.current("b")} #{Names.current("n")}) all-actions : Bool} :=
      λ (+ #{Names.current("t")} : State) → λ (+ #{Names.current("n")} : Nat) → refl
    """
  end

  defp reach_defs(actions, dyn) do
    arms =
      Enum.map_join(actions, "\n", fn action ->
        "      | #{action} => #{dyn.one} #{Names.current("s")} #{action} horizon"
      end)

    eqs =
      Enum.map_join(actions, "\n", fn action ->
        "      | #{action} => #{bridge(dyn, Names.current("s"), action)}"
      end)

    """
    def class-reach : run Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("a")} : Action) → Bool :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("a")} : Action) →
        match #{Names.current("a")} motive (λ _ → Bool)
    #{arms}

    def class-reach-eq : evidence Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("a")} : Action) →
                                  {class-reach #{Names.current("s")} #{Names.current("a")} ≡ hit #{Names.current("s")} #{Names.current("a")} horizon : Bool} :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("a")} : Action) →
        match #{Names.current("a")} motive (λ #{Names.current("x")} → {class-reach #{Names.current("s")} #{Names.current("x")} ≡ hit #{Names.current("s")} #{Names.current("x")} horizon : Bool})
    #{eqs}
    """
  end

  defp conflict_def(dyn) do
    """
    def class-atom-conflict : evidence Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("a")} : Action) →
                                       Π (#{Names.current("hp")} : {#{dyn.pos} (snd (step #{Names.current("s")} #{Names.current("a")})) ≡ true : Bool}) →
                                       Π (#{Names.current("hn")} : {#{dyn.one} #{Names.current("s")} #{Names.current("a")} horizon ≡ false : Bool}) →
                                       Empty :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("a")} : Action) →
      λ (#{Names.current("hp")} : {#{dyn.pos} (snd (step #{Names.current("s")} #{Names.current("a")})) ≡ true : Bool}) →
      λ (#{Names.current("hn")} : {#{dyn.one} #{Names.current("s")} #{Names.current("a")} horizon ≡ false : Bool}) →
        reach-conflict #{Names.current("s")} #{Names.current("a")}
          (rewrite (sym Bool (#{dyn.pos} (snd (step #{Names.current("s")} #{Names.current("a")}))) (class-pos (snd (step #{Names.current("s")} #{Names.current("a")})))
                     (class-pos-eq (snd (step #{Names.current("s")} #{Names.current("a")}))))
            motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ true : Bool})
          in #{Names.current("hp")})
          (rewrite (sym Bool (#{dyn.one} #{Names.current("s")} #{Names.current("a")} horizon) (hit #{Names.current("s")} #{Names.current("a")} horizon) (#{bridge(dyn, Names.current("s"), Names.current("a"))}))
            motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ false : Bool})
          in #{Names.current("hn")})
    """
  end

  defp bridge(dyn, state, action) do
    "rec-is-hit horizon #{dyn.pos} #{dyn.one} #{dyn.best} #{dyn.any} class-pos-eq class-best-eq class-one-eq class-any-eq #{state} #{action}"
  end

  defp arm_eqs(arms, bound, ctx) do
    Enum.map_join(Enum.with_index(arms), "\n", fn {arm, index} ->
      decl = Map.fetch!(bound.decl, arm.name)
      formula = term(arm.pred, ctx)

      """
      def class-arm-eq-#{index} : evidence Π (+ #{Names.current("s")} : State) →
                                         {#{bound.names.eval} #{decl} #{Names.current("s")} ≡ #{formula} : Bool} :=
        λ (+ #{Names.current("s")} : State) → refl
      """
    end)
  end

  defp rank_def(bound, arms, actions) do
    """
    def rank : spec Π (#{Names.current("s")} : State) → Π (#{Names.current("a")} : Action) → Π (#{Names.current("b")} : Action) → Type :=
      λ (#{Names.current("s")} : State) → λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) →
        #{Cert.cascade(bound, arms, actions)}
    """
  end

  # The apply motive names these suffixes. Inlining the action match
  # there makes the checker compare one copy of the ranking per branch.
  defp named_ranks(arms, bound, actions) do
    prefs =
      Enum.map_join(actions, "\n", fn action ->
        """
        def class-pref-#{action} : spec Π (#{Names.current("y")} : Action) → Π (#{Names.current("z")} : Action) → Type :=
          λ (#{Names.current("y")} : Action) → λ (#{Names.current("z")} : Action) →
            #{Cert.preference(actions, action, Names.current("y"), Names.current("z"))}
        """
      end)

    ranks =
      arms
      |> Enum.with_index()
      |> Enum.reverse()
      |> Enum.map_join("\n", fn {arm, index} ->
        ev = "#{bound.names.eval} #{Map.fetch!(bound.decl, arm.name)} #{Names.current("s")}"
        rest = Enum.drop(arms, index + 1)

        false_ty =
          if rest == [] do
            "class-pref-#{arm.else} #{Names.current("a")} #{Names.current("b")}"
          else
            "class-rank-#{index + 1} #{Names.current("s")} #{Names.current("a")} #{Names.current("b")}"
          end

        """
        def class-rank-#{index} : spec Π (#{Names.current("s")} : State) → Π (#{Names.current("a")} : Action) → Π (#{Names.current("b")} : Action) → Type :=
          λ (#{Names.current("s")} : State) → λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) →
            (match #{ev} motive (λ _ → Type)
              | true => class-pref-#{arm.action} #{Names.current("a")} #{Names.current("b")}
              | false => #{false_ty})
        """
      end)

    prefs <> "\n" <> ranks
  end

  defp win_defs(arms, _actions, bound, ctx) do
    yes =
      Enum.map_join(Enum.with_index(arms), "\n", fn {arm, index} ->
        win_def(index, arm.action, arms, bound, ctx)
      end)

    no = else_def(List.last(arms).else, arms, bound, ctx)
    yes <> "\n" <> no
  end

  defp win_def(index, winner, arms, bound, ctx) do
    params = win_params(index, arms, bound)
    goal = goal(Names.current("a"), winner)

    body =
      table(ctx.atoms, %{
        ctx
        | bits: %{},
          index: index,
          winner: winner,
          goal: goal,
          eq_true: Names.current("e#{index}"),
          eq_false: Enum.map(0..(index - 1)//1, &Names.current("e#{&1}"))
      })

    """
    def class-win-#{index} : evidence Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("a")} : Action) →
    #{param_types(params)}
                                    #{goal} :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("a")} : Action) →
    #{param_lams(params)}
        #{body}
    """
  end

  defp else_def(winner, arms, bound, ctx) do
    params =
      Enum.map(Enum.with_index(arms), fn {arm, index} ->
        {Names.current("e#{index}"), eval_eq(bound, arm, false)}
      end)

    goal = goal(Names.current("a"), winner)

    body =
      table(ctx.atoms, %{
        ctx
        | bits: %{},
          index: :else,
          winner: winner,
          goal: goal,
          eq_true: nil,
          eq_false: Enum.map(0..(length(arms) - 1)//1, &Names.current("e#{&1}"))
      })

    """
    def class-win-else : evidence Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("a")} : Action) →
    #{param_types(params)}
                                  #{goal} :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("a")} : Action) →
    #{param_lams(params)}
        #{body}
    """
  end

  defp win_params(index, arms, bound) do
    prior =
      Enum.map(0..(index - 1)//1, fn j ->
        {Names.current("e#{j}"), eval_eq(bound, Enum.at(arms, j), false)}
      end)

    [{Names.current("e#{index}"), eval_eq(bound, Enum.at(arms, index), true)} | prior]
  end

  defp eval_eq(bound, arm, bit) do
    decl = Map.fetch!(bound.decl, arm.name)
    word = if bit, do: "true", else: "false"
    "{#{bound.names.eval} #{decl} #{Names.current("s")} ≡ #{word} : Bool}"
  end

  defp param_types(params) do
    Enum.map_join(params, "\n", fn {name, type} ->
      "                              Π (#{name} : #{type}) →"
    end)
  end

  defp param_lams(params) do
    Enum.map_join(params, "\n", fn {name, type} ->
      "      λ (#{name} : #{type}) →"
    end)
  end

  defp apply_def(arms, bound, actions) do
    """
    def class-apply : evidence Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("a")} : Action) → Π (+ #{Names.current("b")} : Action) →
                               Π (#{Names.current("r")} : rank #{Names.current("s")} #{Names.current("a")} #{Names.current("b")}) →
                               Dom Reward le (action-value #{Names.current("s")} #{Names.current("a")}) (action-value #{Names.current("s")} #{Names.current("b")}) :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("a")} : Action) → λ (+ #{Names.current("b")} : Action) → λ (#{Names.current("r")} : rank #{Names.current("s")} #{Names.current("a")} #{Names.current("b")}) →
        #{cascade(arms, bound, actions, Names.current("r"), 0, [])}
    """
  end

  defp cascade([arm | rest], bound, actions, proof, index, prior) do
    ev = eval_app(bound, arm)
    ename = Names.current("e#{index}")
    dom = goal(Names.current("a"), Names.current("b"))
    true_ty = "class-pref-#{arm.action} #{Names.current("a")} #{Names.current("b")}"

    false_ty =
      if rest == [] do
        "class-pref-#{arm.else} #{Names.current("a")} #{Names.current("b")}"
      else
        "class-rank-#{index + 1} #{Names.current("s")} #{Names.current("a")} #{Names.current("b")}"
      end

    win = fn left ->
      args = Enum.join([ename | prior], " ")
      "class-win-#{index} #{Names.current("s")} #{left} #{args}"
    end

    false_body =
      if rest == [] do
        args = Enum.join(prior ++ [ename], " ")

        else_call = fn left ->
          "class-win-else #{Names.current("s")} #{left} #{args}"
        end

        "#{split(actions, arm.else, else_call)} #{Names.current("q")}"
      else
        cascade(rest, bound, actions, Names.current("q"), index + 1, prior ++ [ename])
      end

    inner = """
    (match #{Names.current("bit")} motive (λ _ → Type)
      | true => #{true_ty}
      | false => #{false_ty})
    """

    """
    (match #{ev} motive (λ #{Names.current("bit")} → {#{ev} ≡ #{Names.current("bit")} : Bool} → Π (#{Names.current("q")} : #{String.trim(inner)}) → #{dom})
      | true => λ (#{ename} : {#{ev} ≡ true : Bool}) → λ (#{Names.current("q")} : #{true_ty}) →
          #{split(actions, arm.action, win)} #{Names.current("q")}
      | false => λ (#{ename} : {#{ev} ≡ false : Bool}) → λ (#{Names.current("q")} : #{false_ty}) →
          #{false_body})
    refl
    #{proof}
    """
    |> String.trim()
  end

  defp eval_app(bound, arm) do
    "#{bound.names.eval} #{Map.fetch!(bound.decl, arm.name)} #{Names.current("s")}"
  end

  defp split(actions, winner, call) do
    pref = "class-pref-#{winner} #{Names.current("y")} #{Names.current("b")}"

    branches =
      Enum.map_join(actions, "\n", fn left ->
        "| #{left} => #{b_match(actions, left, winner, call)}"
      end)

    """
    (match #{Names.current("a")} motive (λ #{Names.current("y")} → Π (#{Names.current("r")} : #{pref}) → #{goal(Names.current("y"), Names.current("b"))})
      #{branches})
    """
    |> String.trim()
  end

  defp b_match(actions, left, winner, call) do
    cells = "class-pref-#{winner} #{left} #{Names.current("z")}"

    branches =
      Enum.map_join(actions, "\n", fn right ->
        "| #{right} => #{split_leaf(left, right, winner, call)}"
      end)

    """
    (match #{Names.current("b")} motive (λ #{Names.current("z")} → Π (#{Names.current("r")} : #{cells}) → #{goal(left, Names.current("z"))})
      #{branches})
    """
    |> String.trim()
  end

  defp split_leaf(left, right, winner, call) do
    cond do
      left == right ->
        "λ (#{Names.current("u")} : Unit) → class-same #{Names.current("s")} #{left}"

      right == winner ->
        "λ (#{Names.current("u")} : Unit) → #{call.(left)}"

      true ->
        "λ (#{Names.current("r")} : Empty) → matchEmpty #{Names.current("r")} motive (λ _ → #{goal(left, right)})"
    end
  end

  defp preserves_def do
    """
    def preserves : evidence CoindHomo rank :=
      λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) → λ (#{Names.current("s")} : State) → λ (#{Names.current("r")} : rank #{Names.current("s")} #{Names.current("a")} #{Names.current("b")}) →
        class-apply #{Names.current("s")} #{Names.current("a")} #{Names.current("b")} #{Names.current("r")}
    """
  end

  # Split an atom only when the two sides are different cases. The
  # winner's reach bit comes first, so one true branch covers every
  # row in which that action reaches. The table stays linear in the
  # atoms instead of exponential in them.
  defp table(atoms, ctx), do: table_split(prefer_winner(atoms, ctx), ctx)

  defp prefer_winner(atoms, ctx) do
    winner = {:reach, ctx.winner}
    {hit, rest} = Enum.split_with(atoms, &(&1 == winner))
    hit ++ rest
  end

  defp table_split([], ctx), do: leaf(ctx)

  defp table_split([atom | rest] = atoms, ctx) do
    if prune?(atoms, ctx) do
      leaf(ctx)
    else
      term = atom_term(atom, ctx)
      hyp = Map.fetch!(ctx.hyps, atom)

      """
      (match #{term} motive (λ #{Names.current("bit")} → {#{term} ≡ #{Names.current("bit")} : Bool} → #{ctx.goal})
        | true => λ (#{hyp} : {#{term} ≡ true : Bool}) →
            #{table(rest, put_bit(ctx, atom, true))}
        | false => λ (#{hyp} : {#{term} ≡ false : Bool}) →
            #{table(rest, put_bit(ctx, atom, false))})
      refl
      """
      |> String.trim()
    end
  end

  defp prune?(rest, ctx) do
    case one_class(rest, ctx) do
      {:ok, class} -> ready?(class, ctx)
      :no -> false
    end
  end

  defp one_class(rest, ctx) do
    rest
    |> completions()
    |> Enum.reduce_while(:empty, fn extra, acc ->
      class =
        classify(Map.merge(ctx.bits, extra), ctx.actions, ctx.arms, ctx.index, ctx.winner)

      cond do
        class == :bad -> {:halt, :bad}
        acc in [:empty, class] -> {:cont, class}
        true -> {:halt, :mixed}
      end
    end)
    |> case do
      class when class in [:win, :tie, :conflict, :mismatch] -> {:ok, class}
      _ -> :no
    end
  end

  defp completions([]), do: [%{}]

  defp completions([atom | rest]) do
    Enum.flat_map(completions(rest), fn base ->
      [Map.put(base, atom, false), Map.put(base, atom, true)]
    end)
  end

  defp ready?(:win, ctx), do: Map.get(ctx.bits, {:reach, ctx.winner}) == true

  defp ready?(:tie, ctx) do
    Enum.all?(ctx.actions, &(Map.get(ctx.bits, {:reach, &1}) == false))
  end

  defp ready?(:conflict, ctx) do
    case conflict_action(ctx.bits, ctx.actions) do
      nil ->
        false

      action ->
        Map.has_key?(ctx.hyps, {:pos, action}) and Map.has_key?(ctx.hyps, {:reach, action})
    end
  end

  defp ready?(:mismatch, ctx), do: mismatch_closed?(ctx)

  # The leaf reads the all-false completion of whatever was not split.
  # Prune only when that completion's proof does not need a later bit.
  defp mismatch_closed?(ctx) do
    case gap_of(ctx) do
      {:ok, pred} -> match?({:ok, _}, formula_closed?(pred, ctx))
      :no -> false
    end
  end

  defp gap_of(ctx) do
    found =
      Enum.find_value(Enum.with_index(ctx.arms), fn {arm, j} ->
        case holds_closed(arm.pred, ctx) do
          :missing ->
            :missing

          {:ok, bit} ->
            cond do
              ctx.index == :else and bit -> {:ok, arm.pred}
              is_integer(ctx.index) and j < ctx.index and bit -> {:ok, arm.pred}
              ctx.index == j and not bit -> {:ok, arm.pred}
              true -> nil
            end
        end
      end)

    case found do
      {:ok, pred} -> {:ok, pred}
      _ -> :no
    end
  end

  defp holds_closed({:not, pred}, ctx) do
    case holds_closed(pred, ctx) do
      {:ok, bit} -> {:ok, not bit}
      :missing -> :missing
    end
  end

  defp holds_closed({:and, left, right}, ctx) do
    case holds_closed(left, ctx) do
      :missing -> :missing
      {:ok, false} -> {:ok, false}
      {:ok, true} -> holds_closed(right, ctx)
    end
  end

  defp holds_closed({:or, left, right}, ctx) do
    case holds_closed(left, ctx) do
      :missing -> :missing
      {:ok, true} -> {:ok, true}
      {:ok, false} -> holds_closed(right, ctx)
    end
  end

  defp holds_closed({:feat, name}, ctx), do: fetch_bit(ctx, feat_atom(name, ctx.actions))

  defp holds_closed({:self, stem, action, _}, ctx), do: fetch_bit(ctx, stem_atom(stem, action))

  defp holds_closed({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> other_closed(stem, ctx)
  end

  defp holds_closed(_pred, _ctx), do: :missing

  defp other_closed([], _stem, _ctx), do: {:ok, false}

  defp other_closed([action | rest], stem, ctx) do
    case Map.fetch(ctx.bits, stem_atom(stem, action)) do
      :error -> :missing
      {:ok, true} -> {:ok, true}
      {:ok, false} -> other_closed(rest, stem, ctx)
    end
  end

  defp formula_closed?({:not, pred}, ctx) do
    case formula_closed?(pred, ctx) do
      {:ok, bit} -> {:ok, not bit}
      :missing -> :missing
    end
  end

  defp formula_closed?({:and, left, right}, ctx) do
    case formula_closed?(left, ctx) do
      :missing -> :missing
      {:ok, false} -> {:ok, false}
      {:ok, true} -> formula_closed?(right, ctx)
    end
  end

  defp formula_closed?({:or, left, right}, ctx) do
    case formula_closed?(left, ctx) do
      :missing -> :missing
      {:ok, true} -> {:ok, true}
      {:ok, false} -> formula_closed?(right, ctx)
    end
  end

  defp formula_closed?({:feat, name}, ctx), do: fetch_bit(ctx, feat_atom(name, ctx.actions))

  defp formula_closed?({:self, stem, action, _}, ctx), do: fetch_bit(ctx, stem_atom(stem, action))

  defp formula_closed?({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> other_closed(stem, ctx)
  end

  defp formula_closed?(_pred, _ctx), do: :missing

  defp fetch_bit(ctx, atom) do
    case Map.fetch(ctx.bits, atom) do
      {:ok, bit} -> {:ok, bit}
      :error -> :missing
    end
  end

  defp put_bit(ctx, atom, bit), do: %{ctx | bits: Map.put(ctx.bits, atom, bit)}

  defp leaf(ctx) do
    case classify(ctx.bits, ctx.actions, ctx.arms, ctx.index, ctx.winner) do
      :conflict ->
        conflict_leaf(conflict_action(ctx.bits, ctx.actions), ctx)

      :win ->
        win_leaf(ctx)

      :tie ->
        tie_leaf(ctx)

      :mismatch ->
        mismatch_leaf(ctx)

      :bad ->
        raise "class proof: a bad row survived the scan"
    end
  end

  defp win_leaf(ctx) do
    hyp = Map.fetch!(ctx.hyps, {:reach, ctx.winner})

    """
    class-from-true #{Names.current("s")} #{ctx.winner} #{Names.current("a")}
      (λ (+ #{Names.current("b")} : Action) → class-reach #{Names.current("s")} #{Names.current("b")})
      (λ (+ #{Names.current("b")} : Action) → class-reach-eq #{Names.current("s")} #{Names.current("b")})
      #{hyp}
    """
    |> String.trim()
  end

  defp tie_leaf(ctx) do
    "class-from-miss #{Names.current("s")} #{Names.current("a")} #{ctx.winner} (#{tie_proof(ctx)})"
  end

  defp tie_proof(ctx) do
    ask = "(class-hit-ask #{Names.current("s")})"

    chain =
      Enum.reduce(Enum.reverse(ctx.actions), "fold-nil-eq #{ask}", fn action, acc ->
        rest = Enum.drop(ctx.actions, Enum.find_index(ctx.actions, &(&1 == action)) + 1)

        "class-cons-false #{ask} #{action} #{list_term(rest)} (#{reach_false(action, ctx)}) (#{acc})"
      end)

    """
    rewrite (any-fold #{Names.current("s")} horizon)
      motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ false : Bool})
    in
      #{chain}
    """
    |> String.trim()
  end

  # The equation from rec-is-hit is {dyn-one ≡ hit}. sym flips it, so the
  # hypothesis is checked on the dyn-one side and the result is the hit
  # side. The other direction makes the checker unfold both runs at the
  # horizon, one action list per successor.
  defp reach_false(action, ctx) do
    hyp = Map.fetch!(ctx.hyps, {:reach, action})
    one = "#{ctx.one} #{Names.current("s")} #{action} horizon"

    """
    rewrite (sym Bool (#{one}) (hit #{Names.current("s")} #{action} horizon) (#{bridge_ctx(ctx, Names.current("s"), action)}))
      motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ false : Bool})
    in #{hyp}
    """
    |> String.trim()
  end

  defp bridge_ctx(ctx, state, action) do
    bridge(%{pos: ctx.pos, one: ctx.one, best: ctx.best, any: ctx.any}, state, action)
  end

  defp conflict_leaf(action, ctx) do
    hp = Map.fetch!(ctx.hyps, {:pos, action})
    hn = Map.fetch!(ctx.hyps, {:reach, action})

    "matchEmpty (class-atom-conflict #{Names.current("s")} #{action} #{hp} #{hn}) motive (λ _ → #{ctx.goal})"
  end

  defp mismatch_leaf(ctx) do
    case first_gap(ctx) do
      :current ->
        {bit, proof} = prove(Enum.at(ctx.arms, ctx.index).pred, ctx)
        if bit, do: raise("class proof: the deciding arm holds on a mismatch row")
        contra_true(ctx, ctx.index, proof)

      {:earlier, j} ->
        {bit, proof} = prove(Enum.at(ctx.arms, j).pred, ctx)
        unless bit, do: raise("class proof: an earlier arm fails on a mismatch row")
        contra_false(ctx, j, proof)
    end
  end

  defp contra_true(ctx, index, proof) do
    ev = eval_term(ctx, index)

    """
    matchEmpty
      (class-ft
        (rewrite (sym Bool #{ev} false
                   (rewrite (class-arm-eq-#{index} #{Names.current("s")})
                      motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ false : Bool})
                    in #{paren(proof)}))
           motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ true : Bool})
         in #{ctx.eq_true}))
      motive (λ _ → #{ctx.goal})
    """
    |> String.trim()
  end

  defp contra_false(ctx, index, proof) do
    ev = eval_term(ctx, index)
    ef = Enum.at(ctx.eq_false, index)

    """
    matchEmpty
      (class-ft
        (rewrite (sym Bool #{ev} false #{ef})
           motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ true : Bool})
         in
           (rewrite (class-arm-eq-#{index} #{Names.current("s")})
              motive (λ #{Names.current("z")} → {#{Names.current("z")} ≡ true : Bool})
            in #{paren(proof)})))
      motive (λ _ → #{ctx.goal})
    """
    |> String.trim()
  end

  defp eval_term(ctx, index) do
    "(#{eval_app(ctx.bound, Enum.at(ctx.arms, index))})"
  end

  defp first_gap(ctx) do
    Enum.find_value(Enum.with_index(ctx.arms), fn {arm, j} ->
      bit = holds?(arm.pred, ctx.bits, ctx.actions)

      cond do
        ctx.index == :else and bit -> {:earlier, j}
        is_integer(ctx.index) and j < ctx.index and bit -> {:earlier, j}
        ctx.index == j and not bit -> :current
        true -> nil
      end
    end)
  end

  defp goal(left, right) do
    "Dom Reward le (action-value #{Names.current("s")} #{left}) (action-value #{Names.current("s")} #{right})"
  end

  defp hyps(atoms) do
    Map.new(Enum.with_index(atoms), fn {atom, index} ->
      {atom, Names.current("ha#{index}")}
    end)
  end

  defp family_pred?(true, _), do: false
  defp family_pred?(false, _), do: false
  defp family_pred?({:feat, name}, actions), do: feat_atom(name, actions) != :no
  defp family_pred?({:self, stem, action, _}, actions), do: stem in @stems and action in actions
  defp family_pred?({:other, stem, action, _}, actions), do: stem in @stems and action in actions
  defp family_pred?({:not, pred}, actions), do: family_pred?(pred, actions)

  defp family_pred?({:and, left, right}, actions) do
    family_pred?(left, actions) and family_pred?(right, actions)
  end

  defp family_pred?({:or, left, right}, actions) do
    family_pred?(left, actions) and family_pred?(right, actions)
  end

  defp family_pred?(_, _), do: false

  defp atoms_of(actions, arms) do
    pos =
      arms
      |> Enum.flat_map(&pos_actions(&1.pred, actions))
      |> Enum.uniq()

    Enum.map(actions, &{:reach, &1}) ++ Enum.map(Enum.filter(actions, &(&1 in pos)), &{:pos, &1})
  end

  defp pos_actions({:feat, name}, actions) do
    case feat_atom(name, actions) do
      {:pos, action} -> [action]
      _ -> []
    end
  end

  defp pos_actions({:self, "has-pos-reward", action, _}, actions) do
    if action in actions, do: [action], else: []
  end

  defp pos_actions({:other, "has-pos-reward", action, _}, actions) do
    Enum.reject(actions, &(&1 == action))
  end

  defp pos_actions({:not, pred}, actions), do: pos_actions(pred, actions)

  defp pos_actions({:and, left, right}, actions),
    do: pos_actions(left, actions) ++ pos_actions(right, actions)

  defp pos_actions({:or, left, right}, actions),
    do: pos_actions(left, actions) ++ pos_actions(right, actions)

  defp pos_actions(_, _), do: []

  defp feat_atom(name, actions) do
    cond do
      String.starts_with?(name, "reaches-pos-") ->
        action = String.replace_prefix(name, "reaches-pos-", "")
        if action in actions, do: {:reach, action}, else: :no

      String.starts_with?(name, "has-pos-reward-") ->
        action = String.replace_prefix(name, "has-pos-reward-", "")
        if action in actions, do: {:pos, action}, else: :no

      true ->
        :no
    end
  end

  defp stem_atom("reaches-pos", action), do: {:reach, action}
  defp stem_atom("has-pos-reward", action), do: {:pos, action}

  defp bad?(actions, arms, atoms) do
    last = Integer.pow(2, length(atoms)) - 1
    branches = Enum.map(0..(length(arms) - 1)//1, &{:arm, &1}) ++ [:else]

    Enum.any?(0..last, fn row ->
      bits = row_bits(atoms, row)

      Enum.any?(branches, fn branch ->
        {index, winner} = branch_of(branch, arms)
        classify(bits, actions, arms, index, winner) == :bad
      end)
    end)
  end

  defp branch_of({:arm, index}, arms), do: {index, Enum.at(arms, index).action}
  defp branch_of(:else, arms), do: {:else, List.last(arms).else}

  defp row_bits(atoms, row) do
    Map.new(Enum.with_index(atoms), fn {atom, index} ->
      {atom, rem(div(row, Integer.pow(2, index)), 2) == 1}
    end)
  end

  defp classify(bits, actions, arms, index, winner) do
    cond do
      conflict_action(bits, actions) -> :conflict
      Map.get(bits, {:reach, winner}, false) -> :win
      Enum.all?(actions, &(not Map.get(bits, {:reach, &1}, false))) -> :tie
      matching?(bits, actions, arms, index) -> :bad
      true -> :mismatch
    end
  end

  defp conflict_action(bits, actions) do
    Enum.find(actions, fn action ->
      Map.get(bits, {:pos, action}, false) and not Map.get(bits, {:reach, action}, false)
    end)
  end

  defp matching?(bits, actions, arms, index) do
    Enum.all?(Enum.with_index(arms), fn {arm, j} ->
      bit = holds?(arm.pred, bits, actions)

      cond do
        index == :else -> not bit
        j < index -> not bit
        j == index -> bit
        true -> true
      end
    end)
  end

  defp holds?(pred, bits, actions) do
    case pred do
      {:not, inner} ->
        not holds?(inner, bits, actions)

      {:and, left, right} ->
        holds?(left, bits, actions) and holds?(right, bits, actions)

      {:or, left, right} ->
        holds?(left, bits, actions) or holds?(right, bits, actions)

      {:feat, name} ->
        Map.fetch!(bits, feat_atom(name, actions))

      {:self, stem, action, _} ->
        Map.fetch!(bits, stem_atom(stem, action))

      {:other, stem, action, _} ->
        actions
        |> Enum.reject(&(&1 == action))
        |> Enum.any?(fn other -> Map.fetch!(bits, stem_atom(stem, other)) end)
    end
  end

  defp term({:not, pred}, ctx), do: "(#{ctx.notb} #{paren(term(pred, ctx))})"

  defp term({:and, left, right}, ctx),
    do: "(#{ctx.andb} #{paren(term(left, ctx))} #{paren(term(right, ctx))})"

  defp term({:or, left, right}, ctx),
    do: "(#{ctx.orb} #{paren(term(left, ctx))} #{paren(term(right, ctx))})"

  defp term({:feat, name}, ctx), do: atom_term(feat_atom(name, ctx.actions), ctx)
  defp term({:self, stem, action, _}, ctx), do: atom_term(stem_atom(stem, action), ctx)

  defp term({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> Enum.map(&atom_term(stem_atom(stem, &1), ctx))
    |> or_term(ctx.orb)
  end

  defp or_term([], _orb), do: "false"
  defp or_term([one], _orb), do: one
  defp or_term([one | rest], orb), do: "(#{orb} #{paren(one)} #{paren(or_term(rest, orb))})"

  defp atom_term({:reach, action}, ctx),
    do: "(#{ctx.one} #{Names.current("s")} #{action} horizon)"

  defp atom_term({:pos, action}, ctx),
    do: "(#{ctx.pos} (snd (step #{Names.current("s")} #{action})))"

  defp prove({:not, pred}, ctx) do
    {bit, proof} = prove(pred, ctx)
    lemma = if bit, do: ctx.lnf, else: ctx.lnt
    {not bit, call(lemma, [term(pred, ctx), proof])}
  end

  defp prove({:and, left, right}, ctx) do
    {lb, lp} = prove(left, ctx)

    if lb do
      {rb, rp} = prove(right, ctx)
      {rb, call(ctx.lat, [term(left, ctx), term(right, ctx), bool_word(rb), lp, rp])}
    else
      {false, call(ctx.laf, [term(left, ctx), term(right, ctx), lp])}
    end
  end

  defp prove({:or, left, right}, ctx) do
    {lb, lp} = prove(left, ctx)

    if lb do
      {true, call(ctx.lor, [term(left, ctx), term(right, ctx), lp])}
    else
      {rb, rp} = prove(right, ctx)
      {rb, call(ctx.lof, [term(left, ctx), term(right, ctx), bool_word(rb), lp, rp])}
    end
  end

  defp prove({:feat, name}, ctx) do
    atom = feat_atom(name, ctx.actions)
    {Map.fetch!(ctx.bits, atom), Map.fetch!(ctx.hyps, atom)}
  end

  defp prove({:self, stem, action, _}, ctx) do
    atom = stem_atom(stem, action)
    {Map.fetch!(ctx.bits, atom), Map.fetch!(ctx.hyps, atom)}
  end

  defp prove({:other, stem, action, _}, ctx) do
    ctx.actions
    |> Enum.reject(&(&1 == action))
    |> prove_others(stem, ctx)
  end

  # A true disjunct does not read the bits after it. Those rows are one case.
  # One remaining action is that action, the same term `or_term` prints.
  # Wrapping it as `orb atom false` does not convert with the formula.
  defp prove_others([], _stem, _ctx), do: {false, "refl"}

  defp prove_others([action], stem, ctx) do
    atom = stem_atom(stem, action)
    {Map.fetch!(ctx.bits, atom), Map.fetch!(ctx.hyps, atom)}
  end

  defp prove_others([action | rest], stem, ctx) do
    atom = stem_atom(stem, action)
    bit = Map.fetch!(ctx.bits, atom)
    proof = Map.fetch!(ctx.hyps, atom)
    t = atom_term(atom, ctx)
    rt = or_term(Enum.map(rest, &atom_term(stem_atom(stem, &1), ctx)), ctx.orb)

    if bit do
      {true, call(ctx.lor, [t, rt, proof])}
    else
      {rb, rp} = prove_others(rest, stem, ctx)
      {rb, call(ctx.lof, [t, rt, bool_word(rb), proof, rp])}
    end
  end

  defp call(fun, args), do: Enum.join([fun | Enum.map(args, &paren/1)], " ")

  defp paren(term) do
    cond do
      term in ["true", "false", "refl", "horizon"] -> term
      String.match?(term, ~r/^[A-Za-z_][A-Za-z0-9_\-]*$/) -> term
      String.starts_with?(term, "(") -> term
      true -> "(#{term})"
    end
  end

  defp bool_word(true), do: "true"
  defp bool_word(false), do: "false"
end
