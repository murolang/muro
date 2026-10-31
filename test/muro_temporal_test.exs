defmodule Muro.TemporalTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.{Check, Parser}

  @echo """
  session echo := rec X. send Nat (recv Nat X)
  session echo-back := rec Y. recv Nat (send Nat Y)
  conform echo-a : echo := rec X. put 0 (get (m : Nat) X)
  conform echo-b : echo-back := rec Y. get (n : Nat) (put n Y)
  meet echo-wire : echo-a with echo-b buffer 1
  temporal echo-returns-zero : echo-wire :=
    always (echo-b at first put implies echo-b has n = 0)
  temporal echo-answers : echo-wire := eventually (echo-a has m = 0)
  temporal echo-answered : echo-wire :=
    (inbox echo-b head 0) leads_to (inbox echo-a head 0)
  """

  @spin """
  data Frame : Type where
    bytes : Frame
    trailers : Frame
    headers : Frame

  session spin := rec X. send Frame X
  session hear :=
    rec Y. recv (f : Frame) (case f
      | bytes => Y
      | trailers => end
      | headers => end)
  conform spin-client : spin := rec X. put bytes X
  conform hear-server : hear := rec Y. get (f : Frame) (match f Y done done)
  meet spin-wire : spin-client with hear-server buffer 1
  temporal drained : spin-wire := always (inbox hear-server is empty)
  temporal ends : spin-wire := eventually (hear-server done)
  """

  test "echo declarations hold in 8 reachable states" do
    assert check(@echo) == :ok

    assert Check.temporal_lines() == [
             "temporal echo-returns-zero: holds in 8 reachable states",
             "temporal echo-answers: holds in 8 reachable states",
             "temporal echo-answered: holds in 8 reachable states"
           ]
  end

  test "the leads_to sugar is the same verdict" do
    src = """
    session echo := rec X. send Nat (recv Nat X)
    session echo-back := rec Y. recv Nat (send Nat Y)
    conform echo-a : echo := rec X. put 0 (get (m : Nat) X)
    conform echo-b : echo-back := rec Y. get (n : Nat) (put n Y)
    meet echo-wire : echo-a with echo-b buffer 1
    temporal echo-answered : echo-wire :=
      always ((inbox echo-b head 0) implies eventually (inbox echo-a head 0))
    """

    assert check(src) == :ok
    assert Check.temporal_lines() == ["temporal echo-answered: holds in 8 reachable states"]
  end

  test "spin refusals name the trace" do
    assert {:error, msg} = check(@spin)

    assert msg =~
             "drained: always (inbox hear-server is empty) fails in spin-wire (spin-client : spin, hear-server : hear) after spin-client put bytes: spin-client: put bytes; hear-server: get (f : Frame); l2r: [bytes]; r2l: []"

    assert msg =~
             "ends: eventually (hear-server done) fails in spin-wire (spin-client : spin, hear-server : hear) after spin-client put bytes, hear-server arm bytes; then forever: spin-client put bytes, hear-server arm bytes"
  end

  test "spin reaches 4 states" do
    src = """
    data Frame : Type where
      bytes : Frame
      trailers : Frame
      headers : Frame
    session spin := rec X. send Frame X
    session hear :=
      rec Y. recv (f : Frame) (case f
        | bytes => Y
        | trailers => end
        | headers => end)
    conform spin-client : spin := rec X. put bytes X
    conform hear-server : hear := rec Y. get (f : Frame) (match f Y done done)
    meet spin-wire : spin-client with hear-server buffer 1
    temporal counted : spin-wire := always true
    """

    assert check(src) == :ok
    assert Check.temporal_lines() == ["temporal counted: holds in 4 reachable states"]
  end

  test "inflight constructor case holds" do
    src =
      File.read!("examples/async-meetings.muro") <>
        """
        temporal ctl-seen : inflight :=
          always (client done implies client has c is rst)
        """

    assert check(src) == :ok
    assert Check.temporal_lines() == ["temporal ctl-seen: holds in 9 reachable states"]
  end

  test "fuel does not change a temporal verdict" do
    assert check(@echo, fuel: 1) == :ok
    low = Check.temporal_lines()
    assert check(@echo, fuel: 50) == :ok
    assert Check.temporal_lines() == low
  end

  test "a book with no temporal declaration leaves the success lines empty" do
    assert check("def z : run Nat := 0\n") == :ok
    assert Check.temporal_lines() == []
  end

  test "contextual keywords stay names outside an entry" do
    assert check("""
           def always : run Nat := 0
           def eventually : run Nat := 0
           data Box : Type where
             temporal : Box
             leads_to : Box
             inbox : Box
           """) == :ok
  end

  test "a rendezvous meeting is out of scope" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             session back := dual ping
             conform pong : ping := get (k : Nat) (put 1 done)
             conform peer : back := put 1 (get (m : Nat) done)
             meet wire : pong with peer
             temporal late : wire := always true
             """)

    assert msg =~ "late: temporal needs a buffered meeting"
  end

  test "a meeting that does not check is skipped" do
    assert {:error, msg} =
             check("""
             session ping := send Nat end
             conform a : ping := put 0 done
             conform b : ping := put 0 done
             meet bad : a with b
             temporal t : bad := always true
             """)

    assert msg =~ "skipped because bad does not check"
    refute msg =~ "temporal needs a buffered meeting"
  end

  test "a vector payload is outside the fragment" do
    assert {:error, msg} =
             check("""
             session out (k : Nat) := send (Vec Nat k) (recv (Vec Nat k) end)
             session out1 := out 1
             conform vec-a : out1 := put (rep 1 0) (get (v : Vec Nat 1) done)
             conform vec-b : out1 := put (rep 1 0) (get (v : Vec Nat 1) done)
             meet vec-wire : vec-a with vec-b buffer 1
             temporal t : vec-wire := always true
             """)

    assert msg =~ "t: payload outside the temporal fragment"
  end

  test "an echo of a repeated binder is refused" do
    assert {:error, msg} =
             check("""
             session dup := rec X. recv Nat (recv Nat (send Nat X))
             session back := rec Y. send Nat (send Nat (recv Nat Y))
             conform dup-a : dup := rec X. get (n : Nat) (get (n : Nat) (put n X))
             conform dup-b : back := rec Y. put 0 (put 1 (get (m : Nat) Y))
             meet dup-wire : dup-a with dup-b buffer 1
             temporal t : dup-wire := always true
             """)

    assert msg =~ "t: echo of a repeated binder"
  end

  test "a mu of a repeated binder is refused" do
    assert {:error, msg} =
             check("""
             session nest := rec X. send Nat (rec X. send Nat X)
             session nest-back := rec Y. recv Nat (rec Z. recv Nat Y)
             conform nest-a : nest := rec X. put 0 (rec X. put 1 X)
             conform nest-b : nest-back := rec Y. get (n : Nat) (rec Z. get (m : Nat) Y)
             meet nest-wire : nest-a with nest-b buffer 1
             temporal t : nest-wire := always true
             """)

    assert msg =~ "t: mu of a repeated binder"
  end

  test "refusals name the offending formula" do
    assert {:error, msg} = Parser.parse("temporal t : wire := always (always true)\n")
    assert msg =~ "nested temporal operator"

    assert {:error, msg} = Parser.parse("temporal t : wire := under fair always true\n")
    assert msg =~ "expected done, stopped, at, or has"

    src = """
    session echo := rec X. send Nat (recv Nat X)
    session echo-back := rec Y. recv Nat (send Nat Y)
    conform echo-a : echo := rec X. put 0 (get (m : Nat) X)
    conform echo-b : echo-back := rec Y. get (n : Nat) (put n Y)
    meet echo-wire : echo-a with echo-b buffer 1
    def steps : run Nat := 0
    temporal open : echo-wire := forall (n : Nat). always true
    temporal role : echo-wire := always (steps done)
    temporal missing : echo-wire := always (echo-a has z = 0)
    temporal step : echo-wire := always (echo-a at 9th put)
    """

    assert {:error, msg} = check(src)
    assert msg =~ "forall over Nat ranges over an open type"
    assert msg =~ "temporal formulas do not mention run definitions"
    assert msg =~ "unknown binder z in echo-a"
    assert msg =~ "unknown step"
  end

  test "refusals name the role, the binder, the literal, and the meeting" do
    assert {:error, msg} =
             check("""
             session echo := rec X. send Nat (recv Nat X)
             session echo-back := rec Y. recv Nat (send Nat Y)
             conform echo-a : echo := rec X. put 0 (get (m : Nat) X)
             conform echo-b : echo-back := rec Y. get (n : Nat) (put n Y)
             meet echo-wire : echo-a with echo-b buffer 1
             data Box : Type where
               wrap : Nat -> Box
             data Note : Type where
               none : Note
             temporal gone : missing := always true
             temporal who : echo-wire := always (nobody done)
             temporal bit : echo-wire := always (echo-a has m = b0)
             temporal ctor : echo-wire := always (echo-a has m is nope)
             temporal openbox : echo-wire := forall (x : Box). always true
             temporal pairs : echo-wire := forall (x : Nat * Nat). always true
             temporal rows : echo-wire := forall (x : { n : Nat }). always true
             temporal vecs : echo-wire := forall (x : Vec Nat 1). always true
             temporal bits : echo-wire := forall (b : Bit). always (inbox echo-a head nope)
             temporal tagged : echo-wire := forall (c : Note). always true
             """)

    assert msg =~ ~r/\d+:\d+: gone: unknown meeting missing/
    assert msg =~ ~r/\d+:\d+: who: unknown role nobody/
    assert msg =~ ~r/\d+:\d+: bit: ill-typed literal/
    assert msg =~ ~r/\d+:\d+: ctor: ill-typed literal/
    assert msg =~ ~r/\d+:\d+: openbox: forall over Box ranges over an open type/
    assert msg =~ ~r/\d+:\d+: pairs: forall over a pair ranges over an open type/
    assert msg =~ ~r/\d+:\d+: rows: forall over a record ranges over an open type/
    assert msg =~ ~r/\d+:\d+: vecs: forall over Vec ranges over an open type/
    assert msg =~ ~r/\d+:\d+: bits: unknown constructor nope/
    refute msg =~ "tagged:"
  end

  test "a repeated binder is ambiguous and a foreign constructor is ill-typed" do
    src =
      File.read!("examples/async-meetings.muro") <>
        """
        temporal amb : inflight := always (server has g)
        temporal foreign : inflight := always (client has c is bytes)
        temporal missing-ctor : inflight := always (client has c is nope)
        """

    assert {:error, msg} = check(src)
    assert msg =~ ~r/\d+:\d+: amb: ambiguous binder g in server/
    assert msg =~ ~r/\d+:\d+: foreign: ill-typed literal/
    assert msg =~ ~r/\d+:\d+: missing-ctor: unknown constructor nope/
  end

  test "a closed quantifier is one check per constructor" do
    src = """
    data Note : Type where
      none : Note
      some : Note
    session echo := rec X. send Nat (recv Nat X)
    session echo-back := rec Y. recv Nat (send Nat Y)
    conform echo-a : echo := rec X. put 0 (get (m : Nat) X)
    conform echo-b : echo-back := rec Y. get (n : Nat) (put n Y)
    meet echo-wire : echo-a with echo-b buffer 1
    temporal tagged : echo-wire := forall (c : Note). always true
    """

    assert check(src) == :ok
    assert Check.temporal_lines() == ["temporal tagged: holds in 8 reachable states"]
  end

  test "emit is unchanged when a temporal declaration is appended" do
    books =
      "examples/**/*.muro"
      |> Path.wildcard()
      |> Enum.filter(fn path -> File.read!(path) =~ ~r/\bbuffer\s+\d+/ end)
      |> Enum.sort()

    assert "examples/async-meetings.muro" in books
    assert "examples/field-choice.muro" in books
    assert "examples/pair-bindings.muro" in books

    for path <- books do
      src = File.read!(path)
      [_, name] = Regex.run(~r/^meet\s+(\S+)\s*:.*\bbuffer\s+\d+/m, src)

      dir =
        System.tmp_dir!()
        |> Path.join("muro-temporal-emit-#{System.unique_integer([:positive])}")

      File.mkdir_p!(dir)
      dest = Path.join(dir, Path.basename(path))
      extra = "\ntemporal hold : #{name} := always true\n"
      File.write!(dest, src)
      assert Muro.check_file(dest) == :ok
      File.write!(dest, src <> extra)

      case Muro.check_file(dest) do
        :ok ->
          File.write!(dest, src)
          before = emit_all(dest)
          File.write!(dest, src <> extra)
          assert comparable(before) == comparable(emit_all(dest))

        {:error, msg} ->
          assert msg =~ "payload outside the temporal fragment"
          assert {:error, emitted} = Muro.emit_file(dest, :Hold)
          assert emitted =~ "payload outside the temporal fragment"
      end
    end
  end

  test "a book with no temporal declaration prints the two success lines" do
    dir = System.tmp_dir!() |> Path.join("muro-temporal-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "plain.muro")
    File.write!(path, "def z : run Nat := 0\n")
    version = Mix.Tasks.Muro.version()
    out = capture_io(fn -> assert Mix.Tasks.Muro.Check.run([path]) == :ok end)

    assert out ==
             """
             Muro v#{version}
             All terms check. Evidence never becomes a run.
             """
  end

  test "mix muro.check prints a temporal line before the success sentence" do
    dir = System.tmp_dir!() |> Path.join("muro-temporal-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "echo.muro")
    File.write!(path, @echo)

    version = Mix.Tasks.Muro.version()

    out = capture_io(fn -> assert Mix.Tasks.Muro.Check.run([path]) == :ok end)

    assert out ==
             """
             Muro v#{version}
             temporal echo-returns-zero: holds in 8 reachable states
             temporal echo-answers: holds in 8 reachable states
             temporal echo-answered: holds in 8 reachable states
             All terms check. Evidence never becomes a run.
             """
  end

  defp check(src, opts \\ []) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book, opts)
  end

  defp emit_all(path) do
    assert {:ok, elixir} = Muro.emit_file(path, :Book)
    assert {:ok, %{source: suite}} = Muro.emit_exunit(path, :BookTest)
    assert {:ok, fsm} = Muro.emit_fsm(path, :BookFsm)
    assert {:ok, c_paths} = Muro.emit_c(path)
    assert {:ok, rust_paths} = Muro.emit_rust(path)
    assert {:ok, asm_paths} = Muro.emit_asm(path)

    %{
      elixir: elixir,
      exunit: suite,
      fsm: fsm,
      c: bodies(c_paths),
      rust: bodies(rust_paths),
      asm: bodies(asm_paths)
    }
  end

  defp bodies(paths) do
    Map.new(paths, fn path -> {Path.basename(path), File.read!(path)} end)
  end

  # The ExUnit header records the book hash. The module body does not.
  defp comparable(%{exunit: source} = emitted) do
    %{emitted | exunit: String.replace(source, ~r/@muro_book ".*"/, ~s(@muro_book "HASH"))}
  end
end
