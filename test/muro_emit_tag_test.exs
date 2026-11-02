defmodule Muro.EmitTagTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Emit, Parser, Prelude, Session}

  # Constructor names are unique in one book, so the two collisions are
  # two books. `both` puts `is-on` and `muro__iszdon` on one declaration.
  # `cross` puts `is-on` on one declaration and `muro__iszdon` on another
  # of the same arity. A nested split reads every constructor of both.

  test "a declaration that has both spellings keeps them apart" do
    for repr? <- [false, true] do
      book = both_book(repr?) |> checked!()
      assert_both(book, repr?)
    end
  end

  test "a nested split resolves each declaration on its own constructors" do
    for repr? <- [false, true] do
      book = cross_book(repr?) |> checked!()
      assert_cross(book, repr?)
    end
  end

  defp assert_both(book, repr?) do
    parent = fsm!(book)
    otp = otp!(book)

    for {value, repr_value, n, branch} <- both_rows() do
      assert Session.eval_run("count-choice", [value], book) == n
      assert Session.eval_run("count-pack", [{:held, value}], book) == n
      assert fsm_branch(parent, "choice", input(value, repr_value, repr?)) == shown(branch, repr?)

      assert fsm_branch(parent, "mark_choice", input(value, repr_value, repr?)) ==
               shown(branch, repr?)

      assert fsm_branch(parent, "mark_pack", pack_input(value, repr_value, repr?)) ==
               shown(branch, repr?)

      assert otp_reply(otp, "reply", {:held, value}, preface(n)) == n
    end

    for {value, repr_value, n, branch} <- both_box_rows() do
      assert Session.eval_run("count-box", [box(value)], book) == n
      assert Session.eval_run("count-pack-box", [{:boxed, box(value)}], book) == n

      assert fsm_branch(parent, "choice_box", box_input(value, repr_value, repr?)) ==
               shown(branch, repr?)

      assert fsm_branch(parent, "mark_box", box_input(value, repr_value, repr?)) ==
               shown(branch, repr?)

      assert otp_reply(otp, "reply_box", {:boxed, box(value)}, preface(n)) == n
    end
  end

  defp assert_cross(book, repr?) do
    parent = fsm!(book)
    otp = otp!(book)

    for row <- cross_rows() do
      %{wire: value, repr: repr_value, n: n, which: which, branch: branch} = row
      run = if which in [:on, :off], do: "count-choice", else: "count-wrap"
      packed = if which in [:on, :off], do: {:held, value}, else: {:wrapped, value}
      session = if which in [:on, :off], do: "choice", else: "wrap"

      assert Session.eval_run(run, [value], book) == n
      assert Session.eval_run("count-pack", [packed], book) == n
      assert fsm_branch(parent, session, input(value, repr_value, repr?)) == shown(branch, repr?)

      assert fsm_branch(parent, "mark_pack", pack_input_cross(packed, repr_value, which, repr?)) ==
               shown(branch, repr?)

      assert otp_reply(otp, "reply", packed, preface(n)) == n
    end

    for row <- cross_box_rows() do
      %{wire: value, repr: repr_value, n: n, which: which, branch: branch} = row
      run = if which in [:on, :off], do: "count-choice-box", else: "count-wrap-box"
      packed = if which in [:on, :off], do: {:boxed, box(value)}, else: {:enclosed, box(value)}
      session = if which in [:on, :off], do: "choice_box", else: "wrap_box"

      assert Session.eval_run(run, [box(value)], book) == n
      assert Session.eval_run("count-pack-box", [packed], book) == n

      assert fsm_branch(parent, session, box_input(value, repr_value, repr?)) ==
               shown(branch, repr?)

      assert fsm_branch(parent, "mark_pack_box", pack_box_input(packed, repr_value, which, repr?)) ==
               shown(branch, repr?)

      assert otp_reply(otp, "reply_box", packed, preface(n)) == n
    end
  end

  defp both_rows do
    on = host("is-on")
    spelled = wire("is-on")
    other = host("muro__iszdon")

    [
      {on, :on, 1, nat_send()},
      {spelled, :on, 1, nat_send()},
      {other, :alias, 2, nat_recv()}
    ]
  end

  defp both_box_rows do
    hold = host("hold-it")
    spelled = wire("hold-it")
    other = host("muro__holdzdit")

    [
      {hold, :hold, 1, nat_send()},
      {spelled, :hold, 1, nat_send()},
      {other, :alias, 2, nat_recv()}
    ]
  end

  defp cross_rows do
    [
      %{wire: host("is-on"), repr: :on, n: 1, which: :on, branch: :done},
      %{wire: wire("is-on"), repr: :on, n: 1, which: :on, branch: :done},
      %{wire: host("is-off"), repr: :off, n: 2, which: :off, branch: nat_send()},
      %{wire: wire("is-off"), repr: :off, n: 2, which: :off, branch: nat_send()},
      %{wire: wire("muro__iszdon"), repr: :wrap, n: 3, which: :wrap, branch: nat_recv()},
      %{wire: host("muro__iszdon"), repr: :wrap, n: 3, which: :wrap, branch: nat_recv()},
      %{wire: host("other"), repr: :other, n: 4, which: :other, branch: unit_send()}
    ]
  end

  defp cross_box_rows do
    [
      %{wire: host("hold-it"), repr: :hold, n: 1, which: :on, branch: :done},
      %{wire: wire("hold-it"), repr: :hold, n: 1, which: :on, branch: :done},
      %{wire: host("drop-it"), repr: :drop, n: 2, which: :off, branch: nat_send()},
      %{wire: wire("drop-it"), repr: :drop, n: 2, which: :off, branch: nat_send()},
      %{wire: wire("muro__holdzdit"), repr: :wrap, n: 3, which: :wrap, branch: nat_recv()},
      %{wire: host("muro__holdzdit"), repr: :wrap, n: 3, which: :wrap, branch: nat_recv()},
      %{wire: host("extra"), repr: :extra, n: 4, which: :other, branch: unit_send()}
    ]
  end

  defp box(tag) when is_atom(tag), do: {tag, 0}
  defp input(wire, _repr, false), do: wire
  defp input(_wire, repr, true), do: repr
  defp box_input(tag, _repr, false) when is_atom(tag), do: {tag, 0}
  defp box_input(_tag, repr, true), do: %{"k" => Atom.to_string(repr), "n" => 0}

  defp pack_input(inner, _repr, false), do: {:held, inner}
  defp pack_input(_inner, repr, true), do: %{"tag" => "held", "v" => repr}

  defp pack_input_cross(packed, _repr_value, _which, false), do: packed

  defp pack_input_cross(_packed, repr_value, which, true) do
    tag = if which in [:on, :off], do: "held", else: "wrapped"
    %{"tag" => tag, "v" => repr_value}
  end

  defp pack_box_input(packed, _repr_value, _which, false), do: packed

  defp pack_box_input(_packed, repr_value, which, true) do
    tag = if which in [:on, :off], do: "boxed", else: "enclosed"
    %{"tag" => tag, "v" => %{"k" => Atom.to_string(repr_value), "n" => 0}}
  end

  defp nat_send, do: {:send, :nat}
  defp nat_recv, do: {:recv, :nat}
  defp unit_send, do: {:send, :unit}

  defp shown({:send, :nat}, true), do: {:send, {:repr, :nat, "Nat"}}
  defp shown({:recv, :nat}, true), do: {:recv, {:repr, :nat, "Nat"}}
  defp shown(branch, _repr?), do: branch

  defp fsm_branch(parent, session, value) do
    mod = Module.concat(parent, Emit.elixir_alias(session))
    assert {:ok, st} = mod.recv(mod.init(), value)
    if mod.done?(st), do: :done, else: mod.expected(st)
  end

  # Sibling constructors select different protocols, so the split stays
  # on this declaration. Each arm then sends the branch number. The
  # preface is what that arm receives before the number.
  defp preface(1), do: []
  defp preface(2), do: [:tt]
  defp preface(3), do: [:tt, :tt]
  defp preface(4), do: [0]

  defp otp_reply(parent, conform, value, preface) do
    child = Module.concat(parent, Emit.elixir_alias(conform))
    assert {:ok, pid, ref} = apply(child, :start, [self()])
    send(pid, {:muro, self(), value})

    for extra <- preface do
      send(pid, {:muro, self(), extra})
    end

    assert_receive {:muro, ^pid, n}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
    n
  end

  defp fsm!(book) do
    parent = Module.concat(["TagFsm#{System.unique_integer([:positive])}"])
    assert {:ok, src} = Emit.Fsm.render(book, "tags.muro", parent, book: "tags.muro")
    compile!(src)
    parent
  end

  defp otp!(book) do
    stem = "tag#{System.unique_integer([:positive])}"
    assert {:ok, src} = Emit.Otp.render(book, stem)
    compile!(src)
    Module.concat([Macro.camelize(String.replace(stem, "-", "_")) <> "Otp"])
  end

  defp host(name), do: String.to_atom(Emit.elixir_atom_name(name))
  defp wire(name), do: String.to_atom(name)

  defp both_book(repr?) do
    """
    data Choice : Type where
      is-on : Choice
      muro__iszdon : Choice

    data ChoiceBox : Type where
      hold-it : Nat → ChoiceBox
      muro__holdzdit : Nat → ChoiceBox

    data Pack : Type where
      held : Choice → Pack

    data PackBox : Type where
      boxed : ChoiceBox → PackBox

    data Mark : Type where
      saw-on : Mark
      saw-alias : Mark

    #{if repr?, do: both_repr(), else: ""}

    def count-choice : run Π (c : Choice) → Nat :=
      λ (c : Choice) →
        match c motive (λ _ → Nat)
          | is-on => suc 0
          | muro__iszdon => suc (suc 0)

    def one : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc 0

    def two : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc (suc 0)

    def count-box : run Π (c : ChoiceBox) → Nat :=
      λ (c : ChoiceBox) →
        match c motive (λ _ → Nat)
          | hold-it n => one n
          | muro__holdzdit n => two n

    def count-pack : run Π (p : Pack) → Nat :=
      λ (p : Pack) →
        match p motive (λ _ → Nat)
          | held c => count-choice c

    def count-pack-box : run Π (p : PackBox) → Nat :=
      λ (p : PackBox) →
        match p motive (λ _ → Nat)
          | boxed c => count-box c

    def mark-choice : run Π (c : Choice) → Mark :=
      λ (c : Choice) →
        match c motive (λ _ → Mark)
          | is-on => saw-on
          | muro__iszdon => saw-alias

    def mark-pack : run Π (p : Pack) → Mark :=
      λ (p : Pack) →
        match p motive (λ _ → Mark)
          | held c => mark-choice c

    def hold-mark : run Π (n : Nat) → Mark :=
      λ (n : Nat) →
        match n motive (λ _ → Mark)
          | 0 => saw-on
          | suc p => saw-on

    def alias-mark : run Π (n : Nat) → Mark :=
      λ (n : Nat) →
        match n motive (λ _ → Mark)
          | 0 => saw-alias
          | suc p => saw-alias

    def mark-box : run Π (c : ChoiceBox) → Mark :=
      λ (c : ChoiceBox) →
        match c motive (λ _ → Mark)
          | hold-it n => hold-mark n
          | muro__holdzdit n => alias-mark n

    def mark-pack-box : run Π (p : PackBox) → Mark :=
      λ (p : PackBox) →
        match p motive (λ _ → Mark)
          | boxed c => mark-box c

    session choice :=
      recv (c : Choice) (case c
        | is-on => send Nat end
        | muro__iszdon => recv Nat end)

    session choice_box :=
      recv (c : ChoiceBox) (case c
        | hold-it => send Nat end
        | muro__holdzdit => recv Nat end)

    session mark_box :=
      recv (c : ChoiceBox) (case (mark-box c)
        | saw-on => send Nat end
        | saw-alias => recv Nat end)

    session mark_choice :=
      recv (c : Choice) (case (mark-choice c)
        | saw-on => send Nat end
        | saw-alias => recv Nat end)

    session mark_pack :=
      recv (p : Pack) (case (mark-pack p)
        | saw-on => send Nat end
        | saw-alias => recv Nat end)

    session ask :=
      recv (p : Pack) (case (mark-pack p)
        | saw-on => send Nat end
        | saw-alias => recv Unit (send Nat end))

    conform reply : ask :=
      get (p : Pack) (match p
        | held c => match c
            | is-on => put 1 done
            | muro__iszdon => get Unit (put 2 done))

    session ask_box :=
      recv (p : PackBox) (case (mark-pack-box p)
        | saw-on => send Nat end
        | saw-alias => recv Unit (send Nat end))

    conform reply_box : ask_box :=
      get (p : PackBox) (match p
        | boxed c => match c
            | hold-it n => put (one n) done
            | muro__holdzdit n => get Unit (put (two n) done))
    """
  end

  defp both_repr do
    """
    repr Nat := integer
    repr Choice := is-on => :on | muro__iszdon => :alias
    repr ChoiceBox := hold-it => map { "k" => "hold", "n" => integer }
                    | muro__holdzdit => map { "k" => "alias", "n" => integer }
    repr Pack := held => map { "tag" => "held", "v" => Choice }
    repr PackBox := boxed => map { "tag" => "boxed", "v" => ChoiceBox }
    """
  end

  defp cross_book(repr?) do
    """
    data Choice : Type where
      is-on : Choice
      is-off : Choice

    data Wrap : Type where
      muro__iszdon : Wrap
      other : Wrap

    data ChoiceBox : Type where
      hold-it : Nat → ChoiceBox
      drop-it : Nat → ChoiceBox

    data WrapBox : Type where
      muro__holdzdit : Nat → WrapBox
      extra : Nat → WrapBox

    data Pack : Type where
      held : Choice → Pack
      wrapped : Wrap → Pack

    data PackBox : Type where
      boxed : ChoiceBox → PackBox
      enclosed : WrapBox → PackBox

    data Mark : Type where
      saw-on : Mark
      saw-off : Mark
      saw-wrap : Mark
      saw-other : Mark

    #{if repr?, do: cross_repr(), else: ""}

    def count-choice : run Π (c : Choice) → Nat :=
      λ (c : Choice) →
        match c motive (λ _ → Nat)
          | is-on => suc 0
          | is-off => suc (suc 0)

    def count-wrap : run Π (w : Wrap) → Nat :=
      λ (w : Wrap) →
        match w motive (λ _ → Nat)
          | muro__iszdon => suc (suc (suc 0))
          | other => suc (suc (suc (suc 0)))

    def one : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc 0

    def two : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc (suc 0)

    def three : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc (suc (suc 0))

    def four : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc (suc (suc (suc 0)))

    def count-choice-box : run Π (c : ChoiceBox) → Nat :=
      λ (c : ChoiceBox) →
        match c motive (λ _ → Nat)
          | hold-it n => one n
          | drop-it n => two n

    def count-wrap-box : run Π (w : WrapBox) → Nat :=
      λ (w : WrapBox) →
        match w motive (λ _ → Nat)
          | muro__holdzdit n => three n
          | extra n => four n

    def count-pack : run Π (p : Pack) → Nat :=
      λ (p : Pack) →
        match p motive (λ _ → Nat)
          | held c => count-choice c
          | wrapped w => count-wrap w

    def count-pack-box : run Π (p : PackBox) → Nat :=
      λ (p : PackBox) →
        match p motive (λ _ → Nat)
          | boxed c => count-choice-box c
          | enclosed w => count-wrap-box w

    def mark-choice : run Π (c : Choice) → Mark :=
      λ (c : Choice) →
        match c motive (λ _ → Mark)
          | is-on => saw-on
          | is-off => saw-off

    def mark-wrap : run Π (w : Wrap) → Mark :=
      λ (w : Wrap) →
        match w motive (λ _ → Mark)
          | muro__iszdon => saw-wrap
          | other => saw-other

    def mark-pack : run Π (p : Pack) → Mark :=
      λ (p : Pack) →
        match p motive (λ _ → Mark)
          | held c => mark-choice c
          | wrapped w => mark-wrap w

    def hold-mark : run Π (n : Nat) → Mark :=
      λ (n : Nat) →
        match n motive (λ _ → Mark)
          | 0 => saw-on
          | suc p => saw-on

    def drop-mark : run Π (n : Nat) → Mark :=
      λ (n : Nat) →
        match n motive (λ _ → Mark)
          | 0 => saw-off
          | suc p => saw-off

    def wrap-mark : run Π (n : Nat) → Mark :=
      λ (n : Nat) →
        match n motive (λ _ → Mark)
          | 0 => saw-wrap
          | suc p => saw-wrap

    def extra-mark : run Π (n : Nat) → Mark :=
      λ (n : Nat) →
        match n motive (λ _ → Mark)
          | 0 => saw-other
          | suc p => saw-other

    def mark-choice-box : run Π (c : ChoiceBox) → Mark :=
      λ (c : ChoiceBox) →
        match c motive (λ _ → Mark)
          | hold-it n => hold-mark n
          | drop-it n => drop-mark n

    def mark-wrap-box : run Π (w : WrapBox) → Mark :=
      λ (w : WrapBox) →
        match w motive (λ _ → Mark)
          | muro__holdzdit n => wrap-mark n
          | extra n => extra-mark n

    def mark-pack-box : run Π (p : PackBox) → Mark :=
      λ (p : PackBox) →
        match p motive (λ _ → Mark)
          | boxed c => mark-choice-box c
          | enclosed w => mark-wrap-box w

    session choice :=
      recv (c : Choice) (case c
        | is-on => end
        | is-off => send Nat end)

    session wrap :=
      recv (w : Wrap) (case w
        | muro__iszdon => recv Nat end
        | other => send Unit end)

    session choice_box :=
      recv (c : ChoiceBox) (case c
        | hold-it => end
        | drop-it => send Nat end)

    session wrap_box :=
      recv (w : WrapBox) (case w
        | muro__holdzdit => recv Nat end
        | extra => send Unit end)

    session mark_pack :=
      recv (p : Pack) (case (mark-pack p)
        | saw-on => end
        | saw-off => send Nat end
        | saw-wrap => recv Nat end
        | saw-other => send Unit end)

    session mark_pack_box :=
      recv (p : PackBox) (case (mark-pack-box p)
        | saw-on => end
        | saw-off => send Nat end
        | saw-wrap => recv Nat end
        | saw-other => send Unit end)

    session ask :=
      recv (p : Pack) (case (mark-pack p)
        | saw-on => send Nat end
        | saw-off => recv Unit (send Nat end)
        | saw-wrap => recv Unit (recv Unit (send Nat end))
        | saw-other => recv Nat (send Nat end))

    conform reply : ask :=
      get (p : Pack) (match p
        | held c => (match c
            | is-on => put 1 done
            | is-off => get Unit (put 2 done))
        | wrapped w => (match w
            | muro__iszdon => get Unit (get Unit (put 3 done))
            | other => get Nat (put 4 done)))

    session ask_box :=
      recv (p : PackBox) (case (mark-pack-box p)
        | saw-on => send Nat end
        | saw-off => recv Unit (send Nat end)
        | saw-wrap => recv Unit (recv Unit (send Nat end))
        | saw-other => recv Nat (send Nat end))

    conform reply_box : ask_box :=
      get (p : PackBox) (match p
        | boxed c => (match c
            | hold-it n => put (one n) done
            | drop-it n => get Unit (put (two n) done))
        | enclosed w => (match w
            | muro__holdzdit n => get Unit (get Unit (put (three n) done))
            | extra n => get Nat (put (four n) done)))
    """
  end

  defp cross_repr do
    """
    repr Nat := integer
    repr Choice := is-on => :on | is-off => :off
    repr Wrap := muro__iszdon => :wrap | other => :other
    repr ChoiceBox := hold-it => map { "k" => "hold", "n" => integer }
                    | drop-it => map { "k" => "drop", "n" => integer }
    repr WrapBox := muro__holdzdit => map { "k" => "wrap", "n" => integer }
                  | extra => map { "k" => "extra", "n" => integer }
    repr Pack := held => map { "tag" => "held", "v" => Choice }
               | wrapped => map { "tag" => "wrapped", "v" => Wrap }
    repr PackBox := boxed => map { "tag" => "boxed", "v" => ChoiceBox }
                  | enclosed => map { "tag" => "enclosed", "v" => WrapBox }
    """
  end

  defp checked!(src) do
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    Prelude.for_emit(book)
  end

  defp compile!(src) do
    mods = Code.compile_string(src)

    on_exit(fn ->
      for {mod, _} <- mods do
        :code.purge(mod)
        :code.delete(mod)
      end
    end)

    mods
  end
end
