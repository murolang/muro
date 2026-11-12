defmodule Muro.SynthLoopTest do
  use ExUnit.Case, async: false

  @two "examples/cshrl/envs/two_state.muro"
  @bin "examples/cshrl/envs/binary_sacrifice.muro"
  @lam "test/fixtures/synth_lam.muro"
  @neg "test/fixtures/synth_neg.muro"
  @stay "test/fixtures/synth_false.muro"
  @chain "test/fixtures/synth_chain.muro"
  @retry "test/fixtures/synth_retry.muro"

  test "two state trace rediscovers prefer go as the survivor" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@two, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.program == true
    assert result.book =~ "def survivor : run PredProg := truep"
    assert result.book =~ "| true => go"
    assert result.book =~ "| false => stay"
    refute result.book =~ "| start =>"
    refute result.book =~ "CoindHomo"
    refute result.book =~ "CoinductiveHomomorphism"

    text = joined(result)
    assert text =~ "muro synth: policy checked"
    assert text =~ "program: truep"
    assert text =~ "at start the program prefers go"
    assert text =~ "carrier start bit true"
    assert text =~ "homomorphism certificate is later"
    assert hd(result.versions) > List.last(result.versions)
  end

  test "hiding go does not rediscover a preference for go" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@two, depth: 0, max_depth: 0, blind: ["go"])
    assert result.status == :policy
    assert result.program == false
    assert result.book =~ "def survivor : run PredProg := falsep"
    assert result.book =~ "| false => stay"

    text = joined(result)
    assert text =~ "at start the program prefers stay"
    assert text =~ "carrier start bit false"
    refute text =~ "prefers go"
  end

  test "a high score on an inconsistent program does not win the loop" do
    score = fn
      false -> 100
      _pred -> 0
    end

    assert {:ok, result} =
             Muro.Synth.cegis_loop(@two, depth: 0, max_depth: 0, score: score)

    assert result.program == true
  end

  test "coind-homo cannot label the binary sacrifice pair" do
    assert {:ok, result} =
             Muro.Synth.cegis_loop(@bin, oracle: "coind-homo", depth: 0, max_depth: 0)

    assert result.status == :silent
    assert result.program == nil
    assert result.book == nil

    text = joined(result)
    assert text =~ "muro synth: oracle cannot label"
    assert text =~ "action-value streams are incomparable"
    assert text =~ "carrier start"
    assert text =~ "pair go-paradise go-trap"
    refute text =~ "CoindHomo"
    refute text =~ "CoinductiveHomomorphism"
    refute text =~ "policy checked"
  end

  test "successor on binary sacrifice prefers go-paradise and does not claim a homomorphism" do
    assert {:ok, result} =
             Muro.Synth.cegis_loop(@bin, oracle: "successor", depth: 0, max_depth: 0)

    assert result.status == :policy
    assert result.program == true
    assert result.book =~ "def survivor : run PredProg := truep"
    refute result.book =~ "CoindHomo"
    refute result.book =~ "CoinductiveHomomorphism"

    text = joined(result)
    assert text =~ "at start the program prefers go-paradise"
    assert text =~ "homomorphism certificate is later"
    refute text =~ "CoinductiveHomomorphism"
  end

  test "the lam graph cannot separate len from copy" do
    src = File.read!(@lam)
    assert src =~ "uses-gt1"
    assert src =~ "arg-apps-ne0"
    refute src =~ ~r/copy\s*:\s*Feature/

    assert {:ok, result} = Muro.Synth.cegis_loop(@lam, depth: 1, max_depth: 3)
    assert result.status == :insufficient
    assert result.program == nil
    assert result.book == nil
    assert length(result.versions) == 2
    assert hd(result.versions) > 4
    assert List.last(result.versions) == 0

    text = joined(result)
    assert text =~ "muro synth: features insufficient"
    assert text =~ "len agrees with copy on every feature"
    assert text =~ "carrier len"
    assert text =~ "predicted true"
    assert text =~ "oracle false"
    assert text =~ "fed back 1"
    assert text =~ "version space #{hd(result.versions)}"
    assert text =~ "version space 0"
    refute text =~ "policy checked"
    refute text =~ "sufficient-cegis"
  end

  test "depth 0 on the negation fixture is an empty space, not insufficient features" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@neg, depth: 0, max_depth: 0)
    assert result.status == :empty
    assert result.book == nil
    text = joined(result)
    assert text =~ "muro synth: empty version space"
    assert text =~ "depth 0"
    refute text =~ "features insufficient"
  end

  test "one deepening finds the negation, and eval of that program checks" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@neg, depth: 0)
    assert result.status == :policy
    assert result.program == {:not, {:feat, "on-p"}}
    assert result.book =~ "def survivor : run PredProg := (notp (feat on-p))"
    refute result.book =~ "| on =>"
    refute result.book =~ "CoindHomo"

    text = joined(result)
    assert text =~ "at on the program prefers stay"
    assert text =~ "at off the program prefers go"
    assert text =~ "homomorphism certificate is later"
    assert 0 in result.versions
  end

  test "a failed policy check is fed back and then reported" do
    checker = fn _path, _fuel ->
      {:error, "out.muro:1:1: hold-start body: cannot convert false ≁ true"}
    end

    assert {:ok, result} =
             Muro.Synth.cegis_loop(@two,
               depth: 0,
               max_depth: 0,
               checker: checker,
               max_rounds: 2
             )

    assert result.status == :residual
    assert result.book == nil
    [cex] = result.cex
    assert cex.carrier == "start"
    assert cex.predicted == false
    assert cex.oracle == true
    assert cex.fed >= 1

    text = joined(result)
    assert text =~ "muro synth: residual counterexample"
    assert text =~ "carrier start"
    assert text =~ "predicted false"
    assert text =~ "oracle true"
    assert text =~ "fed back #{cex.fed}"
  end

  test "the command refuses an unchecked book and a book that is not an environment" do
    dir = tmp()

    bad = Path.join(dir, "bad.muro")
    File.write!(bad, "def one : run Nat := true\n")
    assert {:error, :book, _msg} = Muro.Synth.cegis_loop(bad)
    assert {:exit, 2, "", lines} = Muro.CLI.Synth.run([bad])
    assert Enum.join(lines, "\n") =~ "refusing to synthesize from a book that does not check"

    bare = Path.join(dir, "book.muro")
    File.write!(bare, "def one : run Nat := 0\n")
    assert {:exit, 2, "", lines} = Muro.CLI.Synth.run([bare])
    assert Enum.join(lines, "\n") =~ "does not define State"
  end

  test "unknown oracle, a negative depth, and an existing --out are refusals" do
    assert {:exit, 2, "", ["unknown oracle nope"]} =
             Muro.CLI.Synth.run([@two, "--oracle", "nope"])

    assert {:raise, "", depth} = Muro.CLI.Synth.run([@two, "--depth", "-1"])
    assert depth =~ "--depth"

    assert {:raise, "", fuel} = Muro.CLI.Synth.run([@two, "--fuel", "0"])
    assert fuel =~ "--fuel"

    out = Path.join(tmp(), "out.muro")
    File.write!(out, "already\n")
    assert {:exit, 2, "", [message]} = Muro.CLI.Synth.run([@two, "--out", out])
    assert message == "#{out} already exists"
    assert File.read!(out) == "already\n"
  end

  test "without --out the book is the command result and --out writes only a checked policy" do
    assert {:exit, 1, book, report} = Muro.CLI.Synth.run([@two, "--depth", "0"])
    assert book =~ "def survivor : run PredProg := truep"
    assert Enum.join(report, "\n") =~ "homomorphism certificate is later"
    refute book =~ "CoindHomo"

    out = Path.join(tmp(), "policy.muro")
    assert {:exit, 1, "", written} = Muro.CLI.Synth.run([@two, "--depth", "0", "--out", out])
    assert File.read!(out) =~ "def survivor : run PredProg := truep"
    assert Enum.join(written, "\n") =~ "policy checked"

    silent = Path.join(tmp(), "silent.muro")

    assert {:exit, 1, "", lines} =
             Muro.CLI.Synth.run([@bin, "--oracle", "coind-homo", "--out", silent])

    assert Enum.join(lines, "\n") =~ "oracle cannot label"
    refute File.exists?(silent)
  end

  test "a false program is falsep in the json log outside the checkout" do
    parent = Path.join(System.tmp_dir!(), "muro_synth_cwd_#{System.unique_integer([:positive])}")
    File.mkdir_p!(parent)
    book_path = Path.expand(@stay)

    assert {:exit, 1, book, [json]} =
             File.cd!(parent, fn ->
               Muro.CLI.Synth.run([book_path, "--json", "--depth", "0"])
             end)

    assert book =~ "def survivor : run PredProg := falsep"
    assert book =~ "data PredProg"
    refute book =~ "examples/cshrl"
    refute book =~ "import \"std:bool.muro\""
    decoded = JSON.decode!(json)
    assert decoded["status"] == "policy"
    assert decoded["program"] == "falsep"
    assert decoded["note"] == "homomorphism certificate is later"
  end

  test "a chain reports the action the arms select" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@chain, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.program == [false, true, false]
    assert result.book =~ "| true => b"
    assert result.book =~ "| false => c"

    programs = Enum.filter(result.lines, &String.starts_with?(&1, "program: "))
    assert programs == ["program: falsep", "program: truep", "program: falsep"]
    assert "at s the program prefers b" in result.lines
    refute Enum.any?(result.lines, &String.contains?(&1, "prefers a"))
    refute Enum.any?(result.lines, &String.contains?(&1, "prefers c"))

    assert {:exit, 1, _book, [json]} =
             Muro.CLI.Synth.run([@chain, "--json", "--depth", "0"])

    assert JSON.decode!(json)["program"] == ["falsep", "truep", "falsep"]
  end

  test "a refused candidate is dropped and the next survivor is checked" do
    calls = :counters.new(1, [:atomics])

    checker = fn path, _fuel ->
      :counters.add(calls, 1, 1)
      src = File.read!(path)

      if String.contains?(src, "def survivor : run PredProg := truep") do
        {:error, "#{path}:1:1: hold-s body: cannot convert false ≁ true"}
      else
        :ok
      end
    end

    assert {:ok, result} =
             Muro.Synth.cegis_loop(@retry,
               depth: 0,
               max_depth: 0,
               checker: checker,
               max_rounds: 2
             )

    assert :counters.get(calls, 1) == 2
    assert result.status == :policy
    assert result.program == {:feat, "hot"}
  end

  test "a check that produces no bit reports unknown and does not retry" do
    calls = :counters.new(1, [:atomics])

    checker = fn path, _fuel ->
      :counters.add(calls, 1, 1)

      {:error,
       "#{path}:1:1: hold-start body: out of fuel (the checker gave up reducing; raise the fuel)"}
    end

    assert {:ok, result} =
             Muro.Synth.cegis_loop(@two,
               depth: 0,
               max_depth: 0,
               checker: checker,
               max_rounds: 4
             )

    assert :counters.get(calls, 1) == 1
    assert result.status == :residual
    [cex] = result.cex
    assert cex.predicted == nil
    assert cex.oracle == true
    text = joined(result)
    assert text =~ "predicted unknown"
    assert text =~ "oracle true"
    refute text =~ "predicted false"
  end

  test "a declaration with the wrong type is an environment refusal" do
    dir = tmp()

    nat = Path.join(dir, "nat-actions.muro")

    File.write!(nat, """
    import "std:bool.muro"

    data State : Type where
      s : State

    data Action : Type where
      a : Action
      b : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (_ : Action) → (s, 0)

    def all-actions : run Nat := 0
    def horizon : run Nat := 0

    def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
      λ (_ : Nat) → λ (_ : Nat) → true
    """)

    assert {:error, :usage, msg} = Muro.Synth.Host.open(nat)
    assert msg =~ "all-actions must be run List Action"
    assert {:exit, 2, "", lines} = Muro.CLI.Synth.run([nat])
    assert Enum.join(lines, "\n") =~ "all-actions must be run List Action"

    step = Path.join(dir, "bad-step.muro")

    File.write!(step, """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      s : State

    data Action : Type where
      a : Action
      b : Action

    def step : run Nat := 0
    def all-actions : run List Action := cons a (cons b nil)
    def horizon : run Nat := 0

    def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
      λ (_ : Nat) → λ (_ : Nat) → true
    """)

    assert {:error, :usage, step_msg} = Muro.Synth.Host.open(step)
    assert step_msg =~ "step must be run"
  end

  test "--json is a log of the version space, not a certificate" do
    assert {:exit, 1, book, [json]} = Muro.CLI.Synth.run([@neg, "--json", "--depth", "0"])
    assert book =~ "(notp (feat on-p))"
    decoded = JSON.decode!(json)
    assert decoded["status"] == "policy"
    assert decoded["program"] == "(notp (feat on-p))"
    assert decoded["note"] == "homomorphism certificate is later"
    assert is_list(decoded["versions"])
    assert decoded["cex"] == []
  end

  defp joined(result), do: Enum.join(result.lines, "\n")

  defp tmp do
    path = Path.join(System.tmp_dir!(), "muro_synth_loop_#{System.unique_integer([:positive])}")
    File.mkdir_p!(path)
    path
  end
end
