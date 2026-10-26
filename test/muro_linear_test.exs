defmodule Muro.LinearTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Meet, Parser}

  test "a linear endpoint, its dual, and a matching meeting check" do
    path = "examples/linear.muro"
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, LinearRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "forward"
    refute out =~ "echo"
    refute out =~ "pass"
    refute out =~ "flags-pass"
    refute out =~ "⊸"
  end

  test "lam1 and -o are the same binders" do
    assert check("""
           session ping := recv Nat (send Nat end)
           session back := dual ping
           def forward : (s : ping) -o ping := lam1 (s : ping) -> s
           def backed : (s : ping) -o back := lam1 (s : ping) -> dual s
           def wire : (s : ping) -o (t : back) -o done :=
             lam1 (s : ping) -> lam1 (t : back) -> meet s t
           """) == :ok
  end

  test "an unused linear endpoint is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             def drop : (s : ping) ⊸ (t : ping) ⊸ ping :=
               λ¹ (s : ping) → λ¹ (t : ping) → t
             """)

    assert msg =~ "linear variable unused"
  end

  test "a linear endpoint used twice is the affine refusal" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             def twice : (s : ping) ⊸ done :=
               λ¹ (s : ping) → meet s (dual s)
             """)

    assert msg =~ "affine variable used twice"
  end

  test "the arrow and the binder carry the same multiplicity" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             def bad : (s : ping) → ping := λ¹ (s : ping) → s
             """)

    assert msg =~ "λ/arrow multiplicity mismatch"

    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             def bad : (s : ping) ⊸ ping := λ (s : ping) → s
             """)

    assert msg =~ "λ/arrow multiplicity mismatch"
  end

  test "a meeting refuses endpoints of different multiplicity" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             session back := dual ping
             def bad : (s : ping) ⊸ (t : back) → done :=
               λ¹ (s : ping) → λ (t : back) → meet s t
             """)

    assert msg =~ "multiplicity mismatch"
  end

  test "an affine endpoint may be dropped, and a second use is refused" do
    assert check("""
           session ping := recv Nat (send Nat end)
           def forget : (s : ping) → (t : ping) → ping :=
             λ (s : ping) → λ (t : ping) → t
           """) == :ok

    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             def twice : (s : ping) → done :=
               λ (s : ping) → meet s (dual s)
             """)

    assert msg =~ "affine variable used twice"
  end

  test "reusable data stays reusable beside a linear endpoint" do
    assert check("""
           session ping := recv Nat (send Nat end)
           def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
             λ (n : Nat) → λ (m : Nat) → n
           def twin : run Π (+ n : Nat) → Nat :=
             λ (+ n : Nat) → plus n n
           def forward : (s : ping) ⊸ ping := λ¹ (s : ping) → s
           """) == :ok
  end

  test "a %1 session and a %1 binder stay beside a linear endpoint" do
    assert check("""
           session %1 done-s := end
           conform finished : done-s := done
           session ping := recv Nat (send Nat end)
           def keep : run Π (%1 n : Nat) → Nat := λ (%1 n : Nat) → n
           def forward : (s : ping) ⊸ ping := λ¹ (s : ping) → s
           """) == :ok
  end

  test "a linear binder on Nat is an unknown session" do
    assert {:error, msg} =
             check("""
             def bad : (n : Nat) ⊸ Nat := λ¹ (n : Nat) → n
             """)

    assert msg =~ "unknown session Nat"
  end

  test "a quantity mark on an endpoint binder is refused" do
    assert {:error, msg} =
             Parser.parse("""
             session ping := recv Nat (send Nat end)
             def bad : (+ s : ping) ⊸ ping := λ¹ (s : ping) → s
             """)

    assert msg =~ "a session endpoint is affine or linear"
  end

  test "a linear endpoint of a recursive session and of a declared data payload checks" do
    assert check("""
           session loop := rec X. recv Nat (send Nat X)
           session loop-back := dual loop
           def echo : (s : loop) ⊸ loop := λ¹ (s : loop) → s
           def echo-back : (s : loop) ⊸ loop-back := λ¹ (s : loop) → dual s
           def loop-wire : (s : loop) ⊸ (t : loop-back) ⊸ done :=
             λ¹ (s : loop) → λ¹ (t : loop-back) → meet s t
           data Bool : Type where
             true : Bool
             false : Bool
           session flag := send Bool end
           session flag-back := dual flag
           def pass : (s : flag) ⊸ flag := λ¹ (s : flag) → s
           def pass-back : (s : flag) ⊸ flag-back := λ¹ (s : flag) → dual s
           def flag-wire : (s : flag) ⊸ (t : flag-back) ⊸ done :=
             λ¹ (s : flag) → λ¹ (t : flag-back) → meet s t
           session flags := rec X. send Bool X
           session flags-back := dual flags
           def flags-pass : (s : flags) ⊸ flags := λ¹ (s : flags) → s
           def flags-backed : (s : flags) ⊸ flags-back := λ¹ (s : flags) → dual s
           """) == :ok

    assert {:error, msg} =
             check("""
             session loop := rec X. recv Nat (send Nat X)
             session flags := rec X. send Bool X
             def drop : (s : loop) ⊸ (t : flags) ⊸ flags :=
               λ¹ (s : loop) → λ¹ (t : flags) → t
             """)

    assert msg =~ "linear variable unused"
  end

  test "a jump does not consume a linear endpoint, and rec done does" do
    assert {:ok, book} =
             Parser.parse("""
             session closed := rec X. end
             conform finished : closed := rec X. done
             conform other : closed := rec Y. done
             session loop := rec X. recv Nat (send Nat X)
             session back := dual loop
             conform server : loop := rec X. get (n : Nat) (put n X)
             conform client : back := rec Y. put 1 (get (m : Nat) Y)
             """)

    assert Check.check_sig(book) == :ok
    finished = Enum.find(book, &(&1.name == "finished")).proc
    other = Enum.find(book, &(&1.name == "other")).proc
    server = Enum.find(book, &(&1.name == "server")).proc
    client = Enum.find(book, &(&1.name == "client")).proc
    assert Meet.meet_mult(:lin, finished, other) == :ok
    assert {:error, msg} = Meet.meet_mult(:lin, server, client)
    assert msg =~ "linear endpoint not consumed"
  end

  test "a linear meeting consumes each end once" do
    pong = {:get, :nat, :_, {:put, :nat, {:nat, 1}, :done}}
    peer = {:put, :nat, {:nat, 0}, {:get, :nat, :_, :done}}
    assert Meet.meets(pong, peer) == :ok
    assert Meet.meet_mult(:lin, pong, peer) == :ok
    assert Meet.meet_mult(:aff, :stop, :stop) == :ok
    assert Meet.meets(:stop, :stop) == :ok

    assert {:error, msg} = Meet.meet_mult(:lin, :stop, :stop)
    assert msg =~ "linear endpoint not consumed: left"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end
