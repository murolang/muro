defmodule Muro.AxiomTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @either """
  data Either (A : Type) (B : Type) : Type where
    left  : A → Either A B
    right : B → Either A B
  """

  test "Classical.muro checks and names LEM under dne" do
    assert Muro.check_file("lib/Classical.muro") == :ok
    assert Muro.Check.axiom_lines() == ["dne: depends on Classical.LEM"]
  end

  test "mix muro.check prints the dependency and is silent without one" do
    version = Mix.Tasks.Muro.version()

    assert check_out("lib/Classical.muro") ==
             """
             Muro v#{version}
             dne: depends on Classical.LEM
             All terms check. Evidence never becomes a run.
             """

    quiet = write!("quiet.muro", "def n : run Nat := 0\n")
    assert Muro.check_file(quiet) == :ok
    assert Muro.Check.axiom_lines() == []

    assert check_out(quiet) ==
             """
             Muro v#{version}
             All terms check. Evidence never becomes a run.
             """
  end

  test "a hole is an unsolved goal beside an axiom" do
    path =
      write!("hole.muro", """
      axiom LEM : evidence Nat
      def gap : evidence Nat := ?
      """)

    assert {:error, msg} = Muro.check_file(path)
    assert msg =~ "unsolved hole"
    refute msg =~ "All terms check"

    typed =
      write!("hole-type.muro", """
      axiom LEM : evidence ?
      """)

    assert {:error, msg} = Muro.check_file(typed)
    assert msg =~ "unsolved hole"
  end

  test "an axiom must be evidence" do
    path =
      write!("modes.muro", """
      axiom A : run Nat
      axiom B : spec Nat
      axiom C : run internal Nat
      """)

    assert {:error, msg} = Muro.check_file(path)
    assert msg =~ "A: an axiom is evidence"
    assert msg =~ "B: an axiom is evidence"
    assert msg =~ "C: an axiom is evidence"
  end

  test "the name axiom is a definition when it is not the declaration" do
    path = write!("named.muro", "def axiom : run Nat := 0\n")
    assert Muro.check_file(path) == :ok
    assert Muro.Check.axiom_lines() == []
  end

  test "a run that reaches an axiom is refused and not emitted" do
    path =
      write!("Classical.muro", """
      #{@either}
      axiom LEM : evidence Π (P : Type) → (P ⊎ (P → Empty))

      def via : evidence Π (P : Type) → (P ⊎ (P → Empty)) :=
        λ (P : Type) → LEM P

      def ignore : run Π (- _ : Either Nat (Nat → Empty)) → Nat :=
        λ (- _ : Either Nat (Nat → Empty)) → 0

      def bad : run Nat := ignore (via Nat)

      def plain : run Nat := 0
      """)

    assert {:error, msg} = Muro.check_file(path)
    assert msg =~ "bad: a run depends on Classical.LEM"
    assert {:error, emit} = Muro.emit_file(path, Bad)
    assert emit =~ "bad: a run depends on Classical.LEM"

    direct =
      write!("direct.muro", """
      #{@either}
      axiom LEM : evidence Π (P : Type) → (P ⊎ (P → Empty))

      def bad : run Nat :=
        match LEM Nat motive (λ _ → Nat)
          | left n => n
          | right _ => 0
      """)

    assert {:error, msg} = Muro.check_file(direct)
    assert msg =~ "bad: a run depends on direct.LEM"
  end

  test "a run that does not reach the axiom is emitted" do
    path =
      write!("beside.muro", """
      axiom LEM : evidence Nat
      def n : run Nat := 0
      """)

    assert Muro.check_file(path) == :ok
    assert Muro.Check.axiom_lines() == []
    assert {:ok, src} = Muro.emit_file(path, Beside)
    assert src =~ "def n"
    refute src =~ "LEM"
  end

  test "an imported axiom is reported under the declaring file" do
    dir = tmp()
    classical = Path.join(dir, "Classical.muro")
    File.write!(classical, File.read!("lib/Classical.muro"))
    use = Path.join(dir, "use.muro")

    File.write!(use, """
    import "Classical.muro"
    def again : evidence Π (P : Type) → (P ⊎ (P → Empty)) :=
      λ (P : Type) → LEM P
    """)

    assert Muro.check_file(use) == :ok

    assert Muro.Check.axiom_lines() == [
             "again: depends on Classical.LEM",
             "dne: depends on Classical.LEM"
           ]
  end

  defp check_out(path) do
    capture_io(fn ->
      assert Mix.Tasks.Muro.Check.run([path]) == :ok
    end)
  end

  defp write!(name, src) do
    path = Path.join(tmp(), name)
    File.write!(path, src)
    path
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro-axiom-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    dir
  end
end
