defmodule Muro.FamilyTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.{Check, Parser}

  @slots """
  data Event : Type where
    init : Event
    signal : Event

  data Report : Type where
    ok : Report

  session task-work := send Report end
  session server-wait := recv Report end

  conform task : task-work := put ok done

  conform server : server-wait :=
    get (r : Report) done
    fail
      done

  meet slot : server with task may fail buffer 1
  family slots : slot per key of Event
    init never held
    signal held while earlier unresolved
  """

  @mayfail "c:mayfail\nmay fail is checked and not emitted"

  test "the keyed book checks and names the family" do
    assert check(@slots) == :ok

    assert Check.temporal_lines() == [
             "family slots: slot per key of Event"
           ]
  end

  test "mix muro.check prints the family line" do
    dir = System.tmp_dir!() |> Path.join("muro-family-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "keyed-slots.muro")
    File.write!(path, @slots)
    version = Mix.Tasks.Muro.version()

    assert check_out(path) ==
             """
             Muro v#{version}
             family slots: slot per key of Event
             All terms check. Evidence never becomes a run.
             """

    assert Muro.check_file("examples/keyed-slots.muro") == :ok

    assert Check.temporal_lines() == [
             "family slots: slot per key of Event",
             "temporal no-overtake: holds in 171649 reachable states, 729184 transitions",
             "temporal no-starve: holds in 171649 reachable states, 729184 transitions"
           ]
  end

  test "a family line keeps its place among temporal lines" do
    src = """
    data Event : Type where
      init : Event
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    family slots : wire per key of Event
      init never held
    temporal answered : wire := always true
    """

    assert check(src) == :ok
    assert ["family slots: wire per key of Event", temporal] = Check.temporal_lines()
    assert temporal =~ "temporal answered: holds in "
  end

  test "an unknown meeting is refused" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
             family slots : missing per key of Event
               init never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: unknown meeting missing/
  end

  test "a rendezvous meeting is refused" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b
             family slots : wire per key of Event
               init never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: family needs a buffered meeting/
  end

  test "a meeting that does not check is skipped" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
             session ping := send Nat end
             conform a : ping := put 0 done
             conform b : ping := put 1 done
             meet slot : a with b buffer 1
             family slots : slot per key of Event
               init never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: skipped because slot does not check/
  end

  test "a temporal over a family that does not check is skipped" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
             session ping := send Nat end
             conform a : ping := put 0 done
             conform b : ping := put 1 done
             meet slot : a with b buffer 1
             family slots : slot per key of Event
               init never held
             temporal later : slots := always (opened z signal)
             """)

    assert msg =~ ~r/\d+:\d+: slots: skipped because slot does not check/
    assert msg =~ ~r/\d+:\d+: later: skipped because slots does not check/
    refute msg =~ "not yet decided"
    refute msg =~ "unbound key"
  end

  test "a temporal over a family that is not a closed kind is skipped" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               wrap : Nat -> Event
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Event
               wrap never held
             temporal named : slots :=
               forall (k : key). always ((opened k wrap) implies (resolved k wrap))
             """)

    assert msg =~ ~r/\d+:\d+: slots: family over Event is not a closed kind/
    assert msg =~ ~r/\d+:\d+: named: skipped because slots does not check/
    refute msg =~ "not yet decided"
  end

  test "an empty kind is not closed" do
    assert {:error, msg} =
             check("""
             data Event : Type where
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Event
             """)

    assert msg =~ ~r/\d+:\d+: slots: family over Event is not a closed kind/
  end

  test "Bit is not a kind" do
    assert {:error, msg} =
             check("""
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Bit
             """)

    assert msg =~ ~r/\d+:\d+: slots: unknown data type Bit/
  end

  test "forall over key stays the key sort when a data type is named key" do
    assert check("""
           data key : Type where
             wrap : Nat -> key
           data Event : Type where
             init : Event
             signal : Event
           session ping := send Nat end
           session pong := recv Nat end
           conform a : ping := put 0 done
           conform b : pong := get (n : Nat) done
           meet wire : a with b buffer 1
           family slots : wire per key of Event
             init never held
             signal held while earlier unresolved
           temporal named : slots :=
             forall (k : key). always ((opened k signal) implies (resolved k init))
           """) == :ok

    assert ["family slots: wire per key of Event", line] = Check.temporal_lines()
    assert line =~ ~r/^temporal named: holds in \d+ reachable states, \d+ transitions$/
    refute line =~ "ranges over an open type"
    refute line =~ "expects a key"
  end

  test "a constructor with no rule is refused" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
               signal : Event
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Event
               init never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: no rule for signal/
  end

  test "a constructor with a field is not a closed kind" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               wrap : Nat -> Event
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Event
               wrap never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: family over Event is not a closed kind/
  end

  test "an unknown kind is refused" do
    assert {:error, msg} =
             check("""
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Missing
               init never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: unknown data type Missing/
  end

  test "a duplicate rule is refused" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
               signal : Event
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Event
               init never held
               init held while earlier unresolved
               signal never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: duplicate rule for init/
  end

  test "a rule names a constructor of the kind" do
    assert {:error, msg} =
             check("""
             data Event : Type where
               init : Event
               signal : Event
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Event
               init never held
               nope never held
             """)

    assert msg =~ ~r/\d+:\d+: slots: nope is not a constructor of Event/
  end

  test "a bad rule is a parse error" do
    assert {:error, msg} =
             Parser.parse("""
             family slots : wire per key of Event
               init held forever
             """)

    assert msg =~ "expected never held or held while earlier unresolved"
  end

  # `resolved k init` is every counting init, and there may be none.
  # The holds line is only stored when the book is accepted.
  test "no-overtake holds on its own" do
    src =
      @slots <>
        """
        temporal no-overtake : slots :=
          forall (k : key). always ((opened k signal) implies (resolved k init))
        """

    assert check(src) == :ok

    assert Check.temporal_lines() == [
             "family slots: slot per key of Event",
             "temporal no-overtake: holds in 171649 reachable states, 729184 transitions"
           ]
  end

  # The hold line is the count. The same search as no-overtake.
  test "no-starve holds when the failure arm is done" do
    src =
      @slots <>
        """
        temporal no-starve : slots :=
          forall (k : key). (held k signal) leads_to (opened k signal)
        """

    assert check(src) == :ok

    assert Check.temporal_lines() == [
             "family slots: slot per key of Event",
             "temporal no-starve: holds in 171649 reachable states, 729184 transitions"
           ]
  end

  # Golden lasso. The task dies, the server takes fail stop, both signals
  # of key a stay held, and key b runs to resolves while a is blocked.
  # The cycle is the family stutter. The state after it shows `a signal` held.
  test "no-starve is refused when the failure arm is stop" do
    src =
      String.replace(@slots, "fail\n    done", "fail\n    stop") <>
        """
        temporal no-starve : slots :=
          forall (k : key). (held k signal) leads_to (opened k signal)
        """

    assert {:error, msg} = check(src)
    assert msg =~ ~r/\d+:\d+: no-starve: #{Regex.escape(Muro.FamilyLasso.text())}/
    assert msg =~ "task died"
    assert msg =~ "fail stop"
    assert msg =~ "a signal 1 held"
    assert msg =~ "a signal 2 held"
    [path, forever] = String.split(msg, "; then forever: ")
    assert forever =~ "the family has finished:"
    assert forever =~ "a signal 1: held"
    assert forever =~ "a signal 2: held"
    assert path =~ "b init 0 opens"
    assert path =~ "b init 0 resolves"
    refute forever =~ "opens"
    refute msg =~ "not yet decided"
    refute msg =~ "holds in"
  end

  test "a constructor the kind does not have is not the decision" do
    src =
      @slots <>
        """
        temporal bad : slots := forall (k : key). always (opened k nope)
        """

    assert {:error, msg} = check(src)
    assert msg =~ ~r/\d+:\d+: bad: nope is not a constructor of Event/
    refute msg =~ "not yet decided"
  end

  test "an unbound key is refused" do
    src =
      @slots <>
        """
        temporal loose : slots := always (opened z signal)
        """

    assert {:error, msg} = check(src)
    assert msg =~ ~r/\d+:\d+: loose: unbound key z/
  end

  test "a quantifier that is not a key is refused" do
    # An unused `Bit` binder used to be peeled and ignored, so
    # `always true` held. `Event` is the kind. `Nat` is open.
    # None of them is a key.
    for ty <- ["Bit", "Event", "Nat"] do
      src =
        @slots <>
          """
          temporal valued : slots := forall (c : #{ty}). always true
          """

      assert {:error, msg} = check(src)
      assert msg =~ ~r/\d+:\d+: valued: forall over #{ty} is not a key/, ty
      refute msg =~ "holds in", ty
      refute msg =~ "not yet decided", ty
    end
  end

  test "an ill-formed always does not build the family graph" do
    src =
      @slots <>
        """
        temporal loose : slots := always (opened z signal)
        temporal wide : slots := forall (c : Bit). always true
        temporal live : slots := (held z signal) leads_to (opened z signal)
        """

    events =
      explorations(fn ->
        assert {:error, msg} = check(src)
        assert msg =~ ~r/\d+:\d+: loose: unbound key z/
        assert msg =~ ~r/\d+:\d+: wide: forall over Bit is not a key/
        assert msg =~ ~r/\d+:\d+: live: unbound key z/
        refute msg =~ "holds in"
        refute msg =~ "not yet decided"
      end)

    refute Enum.any?(events, &match?({:family, _}, &1))
  end

  test "an instance atom on a meeting names a family" do
    src = """
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    temporal inst : wire := always (opened k signal)
    """

    assert {:error, msg} = check(src)
    assert msg =~ ~r/\d+:\d+: inst: opened names an instance of a family/
  end

  test "forall over key on a meeting stays an open type" do
    src = """
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    temporal open : wire := forall (k : key). always true
    """

    assert {:error, msg} = check(src)
    assert msg =~ ~r/\d+:\d+: open: forall over key ranges over an open type/
  end

  test "opened done stays a role atom" do
    src = """
    session ping := send Nat end
    session pong := recv Nat end
    conform server : ping := put 0 done
    conform task : pong := get (n : Nat) done
    meet wire : server with task buffer 1
    temporal finished : wire := eventually (server done)
    """

    assert check(src) == :ok
    assert [line] = Check.temporal_lines()
    assert line =~ "temporal finished: holds in "
  end

  test "family words stay names outside the declaration" do
    assert check("""
           def family : run Nat := 0
           def per : run Nat := 0
           def key : run Nat := 0
           def held : run Nat := 0
           def opened : run Nat := 0
           def resolved : run Nat := 0
           """) == :ok

    assert check("""
           session opened := end
           data Box : Type where
             family : Box
             resolved : Box
           """) == :ok
  end

  test "emit skips the family except the state-machine dispatcher" do
    plain = """
    def z : run Nat := 0
    data Event : Type where
      init : Event
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    """

    fam =
      plain <>
        """
        family slots : wire per key of Event
          init never held
        """

    dir = System.tmp_dir!() |> Path.join("muro-family-emit-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, plain)
    before = image(path)
    File.write!(path, fam)
    after_image = image(path)
    assert Map.delete(before, :fsm) == Map.delete(after_image, :fsm)
    refute before.fsm =~ "defmodule Slots do"
    assert after_image.fsm =~ "defmodule Slots do"
    assert after_image.fsm =~ "def arrive(state, key, kind, index)"
    assert after_image.fsm =~ "def resolved(state, id)"
    assert after_image.fsm =~ "def check_trace(trace)"
    assert after_image.fsm =~ "defmodule Ping do"
    assert after_image.fsm =~ "defmodule Pong do"
  end

  test "keyed-slots emit keeps every backend but the state-machine dispatcher" do
    src = File.read!("examples/keyed-slots.muro")
    bare_src = String.replace(src, ~r/\nfamily slots :[\s\S]*\z/, "\n")
    refute bare_src =~ "family slots"

    dir = System.tmp_dir!() |> Path.join("muro-family-slot-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "keyed-slots.muro")
    File.write!(path, bare_src)
    {fsm_before, otp_before} = slot_image(path)
    File.write!(path, src)
    {fsm_after, otp_after} = slot_image(path)
    assert otp_before == otp_after
    refute fsm_before =~ "defmodule Slots do"
    assert fsm_after =~ "defmodule Slots do"
    assert fsm_after =~ "def arrive(state, key, kind, index)"
    assert fsm_after =~ "defmodule ServerWait do"
    assert fsm_before =~ "defmodule ServerWait do"
  end

  defp slot_image(path) do
    assert Muro.emit_file(path, :Book) == {:error, @mayfail}
    assert {:ok, fsm} = Muro.emit_fsm(path, :BookFsm)
    assert {:ok, otp} = Muro.emit_otp(path)
    assert Muro.emit_c(path) == {:error, @mayfail}
    assert Muro.emit_rust(path) == {:error, @mayfail}
    assert Muro.emit_zig(path) == {:error, @mayfail}
    assert Muro.emit_asm(path) == {:error, @mayfail}
    assert Muro.emit_js(path) == {:error, @mayfail}
    assert Muro.emit_exunit(path, :BookTest) == {:error, @mayfail}
    {fsm, bodies(otp)}
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp explorations(fun) do
    Muro.Explore.listen(self())

    try do
      fun.()
      collect_explores([])
    after
      Muro.Explore.silence()
    end
  end

  defp collect_explores(acc) do
    receive do
      {:muro_explore, kind, name} -> collect_explores([{kind, name} | acc])
    after
      0 -> Enum.reverse(acc)
    end
  end

  defp check_out(path) do
    fn -> assert Mix.Tasks.Muro.Check.run([path]) == :ok end
    |> capture_io()
    |> String.replace(~r/^==> \S+\n/m, "")
  end

  defp image(path) do
    assert {:ok, elixir} = Muro.emit_file(path, :Book)
    assert {:ok, %{source: suite}} = Muro.emit_exunit(path, :BookTest)
    assert {:ok, fsm} = Muro.emit_fsm(path, :BookFsm)
    assert {:ok, c_paths} = Muro.emit_c(path)
    assert {:ok, rust_paths} = Muro.emit_rust(path)
    assert {:ok, zig_paths} = Muro.emit_zig(path)
    assert {:ok, asm_paths} = Muro.emit_asm(path)
    assert {:ok, js_paths} = Muro.emit_js(path)
    assert {:ok, otp_paths} = Muro.emit_otp(path)

    %{
      elixir: elixir,
      exunit: String.replace(suite, ~r/@muro_book ".*"/, ~s(@muro_book "HASH")),
      fsm: fsm,
      c: bodies(c_paths),
      rust: bodies(rust_paths),
      zig: bodies(zig_paths),
      asm: bodies(asm_paths),
      js: bodies(js_paths),
      otp: bodies(otp_paths)
    }
  end

  defp bodies(paths) do
    Map.new(paths, fn path -> {Path.basename(path), File.read!(path)} end)
  end
end
