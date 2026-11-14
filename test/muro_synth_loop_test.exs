defmodule Muro.SynthLoopTest do
  use ExUnit.Case, async: false

  @two "examples/cshrl/envs/two_state.muro"
  @bin "examples/cshrl/envs/binary_sacrifice.muro"
  @maze "examples/cshrl/envs/maze_auto.muro"
  @maze3 "examples/cshrl/envs/maze_auto_e2e.muro"
  @place "examples/cshrl/envs/placement.muro"
  @nest "examples/cshrl/envs/nested_bit.muro"
  @cover "examples/cshrl/envs/list_cover.muro"
  @tree "examples/cshrl/envs/tree_cover.muro"
  @neg "test/fixtures/synth_neg.muro"
  @gap "test/fixtures/synth_gap.muro"
  @stay "test/fixtures/synth_false.muro"
  @chain "test/fixtures/synth_chain.muro"
  @retry "test/fixtures/synth_retry.muro"

  test "two state trace certifies prefer go" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@two, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == true
    assert result.book =~ "def survivor : run PredProg := truep"
    assert result.book =~ "| true => go"
    assert result.book =~ "| false => stay"
    assert result.book =~ "def rank "
    assert result.book =~ "match eval survivor"
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "CoinductiveHomomorphism"
    [policy, _cert] = String.split(result.book, "def rank", parts: 2)
    refute policy =~ "| start =>"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: truep"
    assert text =~ "at start the program prefers go"
    assert text =~ "carrier start bit true"
    assert text =~ "certificate CoindHomo"
    assert hd(result.versions) > List.last(result.versions)
  end

  test "hiding go does not certify a preference for go" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@two, depth: 0, max_depth: 0, blind: ["go"])
    refute result.status == :certified
    assert result.book == nil

    text = joined(result)
    assert text =~ "muro synth: homomorphism is not derivable"
    assert text =~ "carrier start"
    assert text =~ "predicted false"
    assert text =~ "oracle false"
    assert text =~ "pair go stay"
    assert text =~ "fed back 1"
    refute text =~ "prefers go"
    refute text =~ "certificate CoindHomo"
  end

  test "a failed certificate drops the candidate and the next survivor is checked" do
    calls = :counters.new(1, [:atomics])

    checker = fn path, _fuel ->
      :counters.add(calls, 1, 1)
      src = File.read!(path)

      if String.contains?(src, "def survivor : run PredProg := truep") do
        {:error, "#{path}:1:1: cert-below-action-start-stay-go body: cannot convert tt ≁ Empty"}
      else
        :ok
      end
    end

    assert {:ok, result} =
             Muro.Synth.cegis_loop(@two,
               depth: 0,
               max_depth: 1,
               checker: checker,
               max_rounds: 4
             )

    assert :counters.get(calls, 1) == 2
    assert result.status == :certified
    assert result.program != true
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "def survivor : run PredProg := truep"
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

  # is-self-loop of go-paradise is false at start and true at the sinks,
  # which is the trace label. CoindHomo cannot rank go-trap above
  # go-paradise at start, so the check fails and the space is empty.
  test "trace on binary sacrifice separates start and cannot rank it" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@bin, oracle: "trace", depth: 0, max_depth: 0)
    assert result.status == :residual
    assert result.program == nil
    assert result.book == nil
    assert result.versions == [5, 1]

    text = joined(result)
    assert text =~ "muro synth: homomorphism is not derivable"
    assert text =~ "carrier start"
    assert text =~ "predicted false"
    assert text =~ "oracle false"
    assert text =~ "pair go-paradise go-trap"
    refute text =~ "homomorphism checked"
    refute text =~ "features insufficient"
    refute text =~ "CoinductiveHomomorphism"
  end

  test "successor on binary sacrifice certifies a preference for go-paradise" do
    assert {:ok, result} =
             Muro.Synth.cegis_loop(@bin, oracle: "successor", depth: 0, max_depth: 0)

    assert result.status == :certified
    assert result.certificate == "CoinductiveHomomorphism"
    assert result.program == true
    assert result.book =~ "def survivor : run PredProg := truep"
    assert result.book =~ "match eval survivor"
    assert result.book =~ "evidence CoinductiveHomomorphism rank"
    refute result.book =~ "CoindHomo"
    [policy, _cert] = String.split(result.book, "def rank", parts: 2)
    refute policy =~ "| start =>"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "at start the program prefers go-paradise"
    assert text =~ "certificate CoinductiveHomomorphism"
    refute text =~ "CoindHomo"
  end

  @tag timeout: 180_000
  test "a corridor with no declared feature certifies the reward of go" do
    src = File.read!(@maze)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, result} = Muro.Synth.cegis_loop(@maze, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "has-pos-reward-go"}
    assert result.book =~ "def survivor : run PredProg := (feat has-pos-reward-go)"
    assert result.book =~ "has-pos-reward-go : Feature"
    assert result.book =~ "def dyn-pos "
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "cert-cover-miss"
    refute result.book =~ "data DynFeature"
    [policy, _cert] = String.split(result.book, "def rank", parts: 2)
    refute policy =~ "| west =>"
    refute policy =~ "| east =>"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat has-pos-reward-go)"
    assert text =~ "at west the program prefers stay"
    assert text =~ "at east the program prefers go"
    assert text =~ "certificate CoindHomo"
    refute text =~ "CoinductiveHomomorphism"
  end

  @tag timeout: 180_000
  test "the three-cell maze certifies forward everywhere" do
    src = File.read!(@maze3)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, result} = Muro.Synth.cegis_loop(@maze3, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == true
    assert result.book =~ "def survivor : run PredProg := truep"
    assert result.book =~ "evidence CoindHomo rank"
    assert result.book =~ "def cert-solve-P0-0 : evidence {solve P0 0 ≡ 0 : Nat}"

    assert result.book =~
             "def cert-solve-P0 : evidence Π (n : Nat) → {solve P0 (suc n) ≡ suc 0 : Nat}"

    assert result.book =~ "def cert-solve-P1 : evidence Π (n : Nat) → {solve P1 n ≡ suc 0 : Nat}"
    assert result.book =~ "def cert-solve-P2 : evidence Π (n : Nat) → {solve P2 n ≡ suc 0 : Nat}"
    refute result.book =~ "cert-cover-miss"
    refute result.book =~ "CoinductiveHomomorphism"
    [policy, _cert] = String.split(result.book, "def rank", parts: 2)
    refute policy =~ "| P0 =>"
    refute policy =~ "| P1 =>"
    refute policy =~ "| P2 =>"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: truep"
    assert text =~ "at P0 the program prefers Fwd"
    assert text =~ "at P1 the program prefers Fwd"
    assert text =~ "at P2 the program prefers Fwd"
    assert text =~ "certificate CoindHomo"
    refute text =~ "CoinductiveHomomorphism"
  end

  @tag timeout: 180_000
  test "two rows certify the comparison of the fields" do
    src = File.read!(@place)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, bare} = Muro.Synth.Host.open(@place, structural: false)
    assert bare.features == []

    assert {:ok, missed} =
             Muro.Synth.cegis_loop(@place, structural: false, depth: 0, max_depth: 0)

    assert missed.status == :insufficient
    assert missed.book == nil
    missed_text = joined(missed)
    assert missed_text =~ "muro synth: features insufficient"
    assert missed_text =~ "agrees with"
    refute missed_text =~ "homomorphism checked"

    assert {:ok, result} = Muro.Synth.cegis_loop(@place, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "pair-any-0-1"}
    assert result.book =~ "def survivor : run PredProg := (feat pair-any-0-1)"
    assert result.book =~ "pair-any-0-1 : Feature"
    assert result.book =~ "nat-of-Row"
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "cert-cover-miss"

    assert result.book =~
             "def cert-solve-board-r0-r0 : evidence Π (n : Nat) → {solve (board r0 r0) n ≡ suc (suc 0) : Nat}"

    refute result.book =~ "vals-eq"
    refute result.book =~ "spread-eq"
    refute result.book =~ "has-pos-reward"
    refute result.book =~ "is-self-loop"
    refute result.book =~ "leads-terminal"
    refute result.book =~ "CoinductiveHomomorphism"

    [_, policy_and_rest] = String.split(result.book, "def policy : run", parts: 2)
    [policy, _cert] = String.split(policy_and_rest, "def rank", parts: 2)
    refute policy =~ "| board"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat pair-any-0-1)"
    assert text =~ "at (board r0 r0) the program prefers move"
    assert text =~ "at (board r0 r2) the program prefers stay"
    assert text =~ "at (board r1 r1) the program prefers move"
    assert text =~ "at (board r2 r0) the program prefers stay"
    assert text =~ "at (board r2 r2) the program prefers move"
    assert text =~ "certificate CoindHomo"
  end

  @tag timeout: 180_000
  test "a list cover certifies the reward of go" do
    src = File.read!(@cover)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, result} = Muro.Synth.cegis_loop(@cover, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "has-pos-reward-go"}
    assert result.book =~ "def survivor : run PredProg := (feat has-pos-reward-go)"
    assert result.book =~ "evidence CoindHomo rank"
    assert result.book =~ "cert-cover-miss"

    assert result.book =~
             "def cert-solve-cell-nil : evidence Π (n : Nat) → {solve (cell nil) n ≡ suc 0 : Nat}"

    assert result.book =~
             "def cert-solve-cell-cons-n0 : evidence Π (n : Nat) → {solve (cell (cons 0 nil)) n ≡ suc 0 : Nat}"

    refute result.book =~ "CoinductiveHomomorphism"
    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat has-pos-reward-go)"
    assert text =~ "at (cell nil) the program prefers stay"
    assert text =~ "at (cell (cons 0 nil)) the program prefers go"
    assert text =~ "certificate CoindHomo"
  end

  test "a recursive all-states cover decodes as states" do
    assert {:ok, host} = Muro.Synth.Host.open(@tree)
    assert host.structured
    assert host.inhabitants == nil
    assert Enum.map(host.all_states, & &1.spell) == ["(tip 0)", "(bin (tip 0) (tip 0))"]
    assert Muro.Synth.Term.equatable?(host.schema)
    refute match?({:open, _}, host.schema)
  end

  @tag timeout: 180_000
  test "a tree cover certifies the reward of go" do
    src = File.read!(@tree)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, result} = Muro.Synth.cegis_loop(@tree, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "has-pos-reward-go"}
    assert result.book =~ "def survivor : run PredProg := (feat has-pos-reward-go)"
    assert result.book =~ "evidence CoindHomo rank"
    assert result.book =~ "cert-cover-miss"

    assert result.book =~
             "def cert-solve-tip-n0 : evidence Π (n : Nat) → {solve (tip 0) n ≡ suc 0 : Nat}"

    assert result.book =~
             "def cert-solve-bin-tip-n0-tip-n0 : evidence Π (n : Nat) → {solve (bin (tip 0) (tip 0)) n ≡ suc 0 : Nat}"

    refute result.book =~ "CoinductiveHomomorphism"
    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat has-pos-reward-go)"
    assert text =~ "at (tip 0) the program prefers stay"
    assert text =~ "at (bin (tip 0) (tip 0)) the program prefers go"
    assert text =~ "certificate CoindHomo"
  end

  @tag timeout: 180_000
  test "a bit under two constructors is invented and certified" do
    src = File.read!(@nest)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, missed} = Muro.Synth.cegis_loop(@nest, structural: false, depth: 0, max_depth: 0)
    assert missed.status == :insufficient
    assert missed.book == nil
    assert joined(missed) =~ "muro synth: features insufficient"

    assert {:ok, result} = Muro.Synth.cegis_loop(@nest, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "ctor-is-p0-0-on"}
    assert result.book =~ "def survivor : run PredProg := (feat ctor-is-p0-0-on)"
    assert result.book =~ "ctor-is-p0-0-on : Feature"
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "cert-cover-miss"
    refute result.book =~ "has-pos-reward"
    refute result.book =~ "CoinductiveHomomorphism"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat ctor-is-p0-0-on)"
    assert text =~ "at (wrap (inn off)) the program prefers stay"
    assert text =~ "at (wrap (inn on)) the program prefers move"
    assert text =~ "certificate CoindHomo"
  end

  test "depth 0 on a reward gap is an empty space, not insufficient features" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@gap, depth: 0, max_depth: 0)
    assert result.status == :empty
    assert result.book == nil
    text = joined(result)
    assert text =~ "muro synth: empty version space"
    assert text =~ "depth 0"
    refute text =~ "features insufficient"
  end

  test "one deepening finds the negation of a discovered reward" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@gap, depth: 0)
    assert result.status == :policy
    assert result.program == {:not, {:feat, "has-pos-reward-go"}}
    assert result.book =~ "def survivor : run PredProg := (notp (feat has-pos-reward-go))"
    assert result.book =~ "data Feature : Type where"
    assert result.book =~ "has-pos-reward-go : Feature"
    assert result.book =~ "def dyn-pos "
    refute result.book =~ "data DynFeature"
    refute result.book =~ "| a =>"
    refute result.book =~ "CoindHomo"
    refute result.book =~ "def rank "

    text = joined(result)
    assert text =~ "at a the program prefers stay"
    assert text =~ "at b the program prefers go"
    assert text =~ "homomorphism is not derivable"
    assert text =~ "does not define CoindHomo"
    assert 0 in result.versions
  end

  test "a declared hint yields to the reward that matches" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@neg, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.program == {:feat, "has-pos-reward-go"}
    assert result.book =~ "def survivor : run PredProg := (feat has-pos-reward-go)"
    assert result.book =~ "data DynFeature : Type where"
    assert result.book =~ "def eval-dyn "
    assert result.book =~ "def dyn-pos "
    refute result.book =~ "(notp (feat on-p))"
    refute result.book =~ "| on =>"
    refute result.book =~ "CoindHomo"
    refute result.book =~ "def rank "

    text = joined(result)
    assert text =~ "at on the program prefers stay"
    assert text =~ "at off the program prefers go"
    assert text =~ "homomorphism is not derivable"
    assert text =~ "does not define CoindHomo"
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

  @tag timeout: 180_000
  test "without --out the book is the command result and --out writes a checked homomorphism" do
    assert {:exit, 0, book, report} = Muro.CLI.Synth.run([@two, "--depth", "0"])
    assert book =~ "def survivor : run PredProg := truep"
    assert book =~ "evidence CoindHomo rank"
    assert Enum.join(report, "\n") =~ "homomorphism checked"
    [policy, _cert] = String.split(book, "def rank", parts: 2)
    refute policy =~ "| start =>"

    out = Path.join(tmp(), "policy.muro")
    assert {:exit, 0, "", written} = Muro.CLI.Synth.run([@two, "--depth", "0", "--out", out])
    assert File.read!(out) =~ "def survivor : run PredProg := truep"
    assert File.read!(out) =~ "evidence CoindHomo rank"
    assert Enum.join(written, "\n") =~ "homomorphism checked"

    silent = Path.join(tmp(), "silent.muro")

    assert {:exit, 1, "", lines} =
             Muro.CLI.Synth.run([@bin, "--oracle", "coind-homo", "--out", silent])

    assert Enum.join(lines, "\n") =~ "oracle cannot label"
    refute File.exists?(silent)

    successor = Path.join(tmp(), "successor.muro")

    assert {:exit, 0, "", successor_report} =
             Muro.CLI.Synth.run([
               @bin,
               "--oracle",
               "successor",
               "--depth",
               "0",
               "--out",
               successor
             ])

    successor_book = File.read!(successor)
    assert successor_book =~ "evidence CoinductiveHomomorphism rank"
    refute successor_book =~ "CoindHomo"
    assert Enum.join(successor_report, "\n") =~ "homomorphism checked"

    assert {:exit, 0, _json_book, [json]} = Muro.CLI.Synth.run([@two, "--json", "--depth", "0"])
    decoded = JSON.decode!(json)
    assert decoded["status"] == "certified"
    assert decoded["note"] == "homomorphism checked"
    assert decoded["certificate"] == "CoindHomo"
    assert decoded["cex"] == []
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
    assert decoded["note"] == "homomorphism is not derivable"
    assert decoded["certificate"] == nil
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

    assert :counters.get(calls, 1) == 1
    assert result.status == :residual
    assert result.program == nil
    assert result.book == nil
    assert joined(result) =~ "muro synth: residual counterexample"
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

  test "a certificate check that produces no bit reports unknown and does not retry" do
    calls = :counters.new(1, [:atomics])

    checker = fn path, _fuel ->
      :counters.add(calls, 1, 1)

      {:error,
       "#{path}:1:1: cert-below-action-start-stay-go body: out of fuel (the checker gave up reducing; raise the fuel)"}
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
    assert cex.kind == :certificate
    text = joined(result)
    assert text =~ "predicted unknown"
    refute text =~ "predicted false"
    refute text =~ "predicted true"
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
    assert book =~ "(feat has-pos-reward-go)"
    decoded = JSON.decode!(json)
    assert decoded["status"] == "policy"
    assert decoded["program"] == "(feat has-pos-reward-go)"
    assert decoded["note"] == "homomorphism is not derivable"
    assert decoded["certificate"] == nil
    assert is_list(decoded["versions"])
    assert decoded["cex"] == []
  end

  test "three actions stay silent when the losers are incomparable" do
    dir = tmp()
    path = Path.join(dir, "dom.muro")

    File.write!(path, """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      s : State

    data Reward : Type where
      rt : Reward
      rp : Reward
      rq : Reward

    data Action : Type where
      top : Action
      p : Action
      q : Action

    def step : run Π (s : State) → Π (a : Action) → State × Reward :=
      λ (s : State) → λ (a : Action) →
        match a motive (λ _ → State × Reward)
          | top => (s, rt)
          | p => (s, rp)
          | q => (s, rq)

    def all-actions : run List Action := cons top (cons p (cons q nil))
    def default-action : run Action := q
    def horizon : run Nat := 0
    def all-states : run List State := cons s nil

    def leb : run Π (m : Reward) → Π (n : Reward) → Bool :=
      λ (m : Reward) → λ (n : Reward) →
        match m motive (λ _ → Bool)
          | rt =>
              (match n motive (λ _ → Bool) | rt => true | rp => false | rq => false)
          | rp =>
              (match n motive (λ _ → Bool) | rt => true | rp => true | rq => false)
          | rq =>
              (match n motive (λ _ → Bool) | rt => true | rp => false | rq => true)
    """)

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :silent
    assert result.program == nil
    assert result.book == nil
    text = joined(result)
    assert text =~ "oracle cannot label"
    assert text =~ "pair p q"
  end

  test "a reward that is not a closed Nat leaves the policy without a ranking" do
    dir = tmp()
    path = Path.join(dir, "tokens.muro")

    File.write!(path, """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      s : State

    data Action : Type where
      go : Action
      stay : Action

    data Token : Type where
      tok : Token
      other : Token

    def Reward : spec Type := Token
    def origin : run Token := tok
    def maxN : run Π (r : Token) → Π (q : Token) → Token :=
      λ (r : Token) → λ (_ : Token) → r
    def max : run Π (r : Reward) → Π (q : Reward) → Reward := maxN
    def bottom : run Reward := origin

    def step : run Π (s : State) → Π (a : Action) → State × Reward :=
      λ (s : State) → λ (a : Action) →
        match a motive (λ _ → State × Reward)
          | go => (s, tok)
          | stay => (s, other)

    def all-actions : run List Action := cons go (cons stay nil)
    def default-action : run Action := stay
    def horizon : run Nat := 0
    def all-states : run List State := cons s nil

    def leb : run Π (m : Reward) → Π (n : Reward) → Bool :=
      λ (m : Reward) → λ (n : Reward) →
        match m motive (λ _ → Bool)
          | tok => true
          | other =>
              (match n motive (λ _ → Bool) | tok => false | other => true)

    def CoindHomo : spec Type := Unit
    def action-value : run Nat := 0
    def action-at : run Nat := 0
    def value : run Nat := 0
    def solve : run Nat := 0
    def dom-refl : evidence {0 ≡ 0 : Nat} := refl
    def tabulate-dom : evidence {0 ≡ 0 : Nat} := refl
    def le-refl : evidence {0 ≡ 0 : Nat} := refl
    """)

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.book =~ "def survivor"
    refute result.book =~ "def rank "
    text = joined(result)
    assert text =~ "homomorphism is not derivable"
    assert text =~ "reward is not a closed Nat"

    assert {:exit, 1, book, report} = Muro.CLI.Synth.run([path, "--depth", "0"])
    assert book =~ "def survivor"
    assert Enum.join(report, "\n") =~ "reward is not a closed Nat"
  end

  test "an output path created after the existence check is refused" do
    dir = tmp()
    out = Path.join(dir, "out.muro")
    refute File.exists?(out)

    assert {:exit, 2, "", [message]} =
             Muro.CLI.Synth.run([prefer_go(dir), "--depth", "0", "--out", out],
               before_write: fn path -> File.write!(path, "raced\n") end
             )

    assert message == "#{out} already exists"
    assert File.read!(out) == "raced\n"
  end

  test "an environment that already declares the evaluator synthesizes" do
    dir = tmp()
    path = Path.join(dir, "env.muro")

    File.write!(
      path,
      prefer_src() <> "\n" <> feature_src() <> "\n" <> Muro.Synth.Book.evaluator()
    )

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.program == true
    refute result.book =~ "data PredProg"
    refute result.book =~ "def andb "
    refute result.book =~ "def eval :"
  end

  test "a generated policy book can be synthesized again" do
    dir = tmp()
    env = Path.join(dir, "env.muro")
    File.write!(env, prefer_src())

    assert {:ok, first} = Muro.Synth.cegis_loop(env, depth: 0, max_depth: 0)
    assert first.status == :policy
    policy = Path.join(dir, "policy.muro")
    File.write!(policy, first.book)

    assert {:ok, second} = Muro.Synth.cegis_loop(policy, depth: 0, max_depth: 0)
    assert second.status == :policy
    assert second.book =~ "def survivor-2 "
    assert second.book =~ "def policy-2 "
    assert second.book =~ "def hold-s-2 "
    refute second.book =~ "data PredProg"
  end

  test "a later obligation's bit does not drop the candidate" do
    calls = :counters.new(1, [:atomics])

    checker = fn path, _fuel ->
      :counters.add(calls, 1, 1)

      if :counters.get(calls, 1) == 1 do
        {:error,
         """
         #{path}:1:1: hold-s body: out of fuel (the checker gave up reducing; raise the fuel)

         #{path}:2:1: hold-t body: cannot convert false ≁ true
         """}
      else
        :ok
      end
    end

    assert {:ok, result} =
             Muro.Synth.cegis_loop(two_hot(tmp()),
               depth: 0,
               max_depth: 0,
               checker: checker,
               max_rounds: 4
             )

    assert :counters.get(calls, 1) == 1
    assert result.status == :residual
    [cex] = result.cex
    assert cex.carrier == "s"
    assert cex.predicted == nil
    assert cex.oracle == true
  end

  test "the next depth is fitted after the last survivor is refused" do
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
             Muro.Synth.cegis_loop(prefer_go(tmp()),
               depth: 0,
               max_depth: 1,
               checker: checker,
               max_rounds: 2
             )

    assert :counters.get(calls, 1) == 2
    assert result.status == :policy
    assert result.program == {:not, false}
    assert result.book =~ "def survivor : run PredProg := (notp falsep)"
    refute result.book =~ "def survivor : run PredProg := truep"
  end

  test "an internal or erased callback is an environment refusal" do
    dir = tmp()

    internal =
      host_book(dir, "internal.muro", """
      def step : run internal Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, msg} = Muro.Synth.Host.open(internal)
    assert msg =~ "step is run internal"
    assert {:exit, 2, "", lines} = Muro.CLI.Synth.run([internal])
    assert Enum.join(lines, "\n") =~ "step is run internal"

    erased =
      host_book(dir, "erased.muro", """
      def step : run Π (- s : State) → Π (a : Action) → State × Nat :=
        λ (- _ : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, erased_msg} = Muro.Synth.Host.open(erased)
    assert erased_msg =~ "erased argument"
    assert {:exit, 2, "", erased_lines} = Muro.CLI.Synth.run([erased])
    assert Enum.join(erased_lines, "\n") =~ "erased argument"

    actions =
      host_book(dir, "actions.muro", """
      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run internal List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, actions_msg} = Muro.Synth.Host.open(actions)
    assert actions_msg =~ "all-actions is run internal"

    leb =
      host_book(dir, "leb.muro", """
      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (- m : Nat) → Π (n : Nat) → Bool :=
        λ (- _ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, leb_msg} = Muro.Synth.Host.open(leb)
    assert leb_msg =~ "leb takes an erased argument"

    hidden =
      host_book(dir, "default.muro", """
      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def default-action : run internal Action := a
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, hidden_msg} = Muro.Synth.Host.open(hidden)
    assert hidden_msg =~ "default-action is run internal"

    feat =
      host_book(dir, "feat.muro", """
      def Carrier : spec Type := State
      data Feature : Type where
        hot : Feature
      def eval-feature : run internal Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
        λ (+ _ : Feature) → λ (+ _ : Carrier) → true
      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, feat_msg} = Muro.Synth.Host.open(feat)
    assert feat_msg =~ "eval-feature is run internal"
  end

  test "a Carrier that does not convert to State is refused" do
    dir = tmp()

    plain =
      host_book(dir, "carrier.muro", """
      def Carrier : spec Type := Nat
      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, msg} = Muro.Synth.Host.open(plain)
    assert msg =~ "Carrier must convert to State"
    assert {:exit, 2, "", lines} = Muro.CLI.Synth.run([plain])
    assert Enum.join(lines, "\n") =~ "Carrier must convert to State"

    featured =
      host_book(dir, "carrier-feat.muro", """
      def Carrier : spec Type := Nat
      data Feature : Type where
        hot : Feature
      def eval-feature : run Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
        λ (+ _ : Feature) → λ (+ c : Carrier) →
          match c motive (λ _ → Bool)
            | 0 => true
            | suc _ => false
      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, feat_msg} = Muro.Synth.Host.open(featured)
    assert feat_msg =~ "Carrier must convert to State"
  end

  test "stdout import resolves when the book is saved in the current directory" do
    parent =
      Path.join(System.tmp_dir!(), "muro_synth_stdout_#{System.unique_integer([:positive])}")

    nested = Path.join(parent, "nested")
    File.mkdir_p!(nested)
    env = Path.join(nested, "env.muro")
    File.write!(env, prefer_src())

    assert {:exit, 1, book, _report} =
             File.cd!(parent, fn ->
               Muro.CLI.Synth.run([env, "--depth", "0"])
             end)

    refute book =~ "import \"env.muro\""
    saved = Path.join(parent, "policy.muro")
    File.write!(saved, book)
    assert :ok = Muro.check_file(saved)
  end

  test "a temporary book that cannot be stored exits 2" do
    dir = tmp()
    env = prefer_go(dir)
    blocker = Path.join(dir, "blocker")
    File.write!(blocker, "not a directory\n")
    out = Path.join(blocker, "policy.muro")

    assert {:exit, 2, "", [message]} = Muro.CLI.Synth.run([env, "--depth", "0", "--out", out])
    assert message =~ "temporary book"
    assert message =~ ":enotdir" or message =~ ":eexist"
    refute message =~ "unknown"
    refute message =~ "residual"
    refute message =~ "counterexample"
    refute File.exists?(out)

    assert {:error, :storage, diagnostic} =
             Muro.Synth.cegis_loop(env,
               depth: 0,
               max_depth: 0,
               anchor: Path.join(blocker, "books")
             )

    assert diagnostic =~ ":enotdir" or diagnostic =~ ":eexist"
    refute diagnostic =~ "unknown"
  end

  test "a failed write of --out removes the partial file" do
    dir = tmp()
    env = prefer_go(dir)
    out = Path.join(dir, "policy.muro")

    assert {:exit, 2, "", [message]} =
             Muro.CLI.Synth.run([env, "--depth", "0", "--out", out],
               binwrite: fn io, data ->
                 IO.binwrite(io, binary_part(data, 0, min(8, byte_size(data))))
                 {:error, :eio}
               end
             )

    assert message =~ ":eio"
    refute File.exists?(out)

    closed = Path.join(dir, "closed.muro")

    assert {:exit, 2, "", [close_message]} =
             Muro.CLI.Synth.run([env, "--depth", "0", "--out", closed],
               close: fn io ->
                 File.close(io)
                 {:error, :eio}
               end
             )

    assert close_message =~ ":eio"
    refute File.exists?(closed)

    assert {:exit, 1, "", _} = Muro.CLI.Synth.run([env, "--depth", "0", "--out", out])
    assert File.read!(out) =~ "def survivor"
  end

  test "a fresh policy name does not reuse an Elixir spelling" do
    dir = tmp()

    path =
      write_book(dir, "spell.muro", """
      #{prefer_src()}
      def policy : run Nat := 0
      def policy_2 : run Nat := 0
      """)

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.book =~ "def policy-3 "
    refute result.book =~ "def policy-2 "
  end

  test "a state named none still synthesizes a constant policy" do
    dir = tmp()

    path =
      write_book(dir, "none-state.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        none : State

      data Action : Type where
        go : Action
        stay : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (a : Action) →
          match a motive (λ _ → State × Nat)
            | go => (s, suc 0)
            | stay => (s, 0)

      def all-actions : run List Action := cons go (cons stay nil)
      def default-action : run Action := stay
      def horizon : run Nat := 0
      def all-states : run List State := cons none nil
      #{leb_src()}
      """)

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.book =~ "none-2 : Feature"
    assert result.book =~ "| none-2 => false"
    refute result.book =~ ~r/^[ \t]*none : Feature/m

    action =
      write_book(dir, "none-action.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        s : State

      data Action : Type where
        none : Action
        stay : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (a : Action) →
          match a motive (λ _ → State × Nat)
            | none => (s, suc 0)
            | stay => (s, 0)

      def all-actions : run List Action := cons none (cons stay nil)
      def default-action : run Action := stay
      def horizon : run Nat := 0
      def all-states : run List State := cons s nil
      #{leb_src()}
      """)

    assert {:ok, action_result} = Muro.Synth.cegis_loop(action, depth: 0, max_depth: 0)
    assert action_result.status == :policy
    assert action_result.book =~ "none-2 : Feature"
    refute action_result.book =~ ~r/^[ \t]*none : Feature/m
  end

  test "a repeated action is one arm and the default stays the last element" do
    dir = tmp()

    path =
      write_book(dir, "dup-action.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        s : State

      data Action : Type where
        a : Action
        b : Action

      def step : run Π (s : State) → Π (x : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons a (cons b (cons a nil))
      def horizon : run Nat := 0
      def all-states : run List State := cons s nil
      #{leb_src()}
      """)

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert host.actions == ["a", "b"]
    assert host.default == "a"

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert length(Regex.scan(~r/^def survivor :/m, result.book)) == 1
    refute result.book =~ "def survivor-a "
  end

  test "a repeated state is one obligation" do
    dir = tmp()

    path =
      write_book(dir, "dup-state.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        t : State
        s : State

      data Action : Type where
        go : Action
        stay : Action

      def step : run Π (x : State) → Π (a : Action) → State × Nat :=
        λ (x : State) → λ (a : Action) →
          match a motive (λ _ → State × Nat)
            | go => (x, suc 0)
            | stay => (x, 0)

      def all-actions : run List Action := cons go (cons stay nil)
      def default-action : run Action := stay
      def horizon : run Nat := 0
      def all-states : run List State := cons t (cons s (cons t nil))
      #{leb_src()}
      """)

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert host.all_states == ["t", "s"]

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert length(Regex.scan(~r/^def hold-t :/m, result.book)) == 1
    assert length(Regex.scan(~r/^def hold-s :/m, result.book)) == 1
  end

  test "eval-feature without Feature is a usage error" do
    dir = tmp()

    path =
      host_book(dir, "bare-eval.muro", """
      def eval-feature : run Nat := 0
      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)
      def all-actions : run List Action := cons a (cons b nil)
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, msg} = Muro.Synth.Host.open(path)
    assert msg =~ "eval-feature"
    assert msg =~ "Feature"
    assert {:exit, 2, "", lines} = Muro.CLI.Synth.run([path])
    text = Enum.join(lines, "\n")
    assert text =~ "does not define Feature"
    refute text =~ "residual"
  end

  test "an incomparable state does not emit an empty match" do
    host = %{
      book: [],
      defined_feature: false,
      structured: true,
      inhabitants: nil,
      schema: {:data, "State", [%{name: "box", fields: [{:open, "function"}]}]},
      actions: ["go"],
      feature_specs: [%{name: "is-self-loop-go", kind: :is_self_loop, action: "go"}]
    }

    arm = %{
      name: "survivor",
      pred: {:feat, "is-self-loop-go"},
      action: "go",
      else: "stay",
      observations: []
    }

    assert {:error, "state equality is not a run"} =
             Muro.Synth.Book.render(host, [arm], ".", "trace")
  end

  test "a policy book that names no obligation tries the next survivor" do
    dir = tmp()
    calls = :counters.new(1, [:atomics])

    checker = fn book, fuel ->
      :counters.add(calls, 1, 1)

      if :counters.get(calls, 1) == 1 do
        {:error, "scratch body: the policy book does not check"}
      else
        Muro.check_file(book, fuel: fuel)
      end
    end

    assert {:ok, result} =
             Muro.Synth.cegis_loop(prefer_go(dir),
               depth: 0,
               max_depth: 1,
               checker: checker,
               max_rounds: 4
             )

    assert :counters.get(calls, 1) >= 2
    assert result.status == :policy
    assert result.program == {:not, false}
  end

  test "a parameterized State is refused" do
    dir = tmp()

    path =
      write_book(dir, "params.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State (A : Type) : Type where
        box : Π (x : A) → State A

      data Action : Type where
        go : Action

      def step : run Π (s : State Nat) → Π (a : Action) → (State Nat) × Nat :=
        λ (s : State Nat) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "State has parameters"} = Muro.Synth.Host.open(path)
  end

  test "an indexed State is refused" do
    dir = tmp()

    path =
      write_book(dir, "indexed.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Nat → Type where
        here : Π (n : Nat) → State n

      data Action : Type where
        go : Action

      def step : run Π (n : Nat) → Π (s : State n) → Π (a : Action) → (State n) × Nat :=
        λ (n : Nat) → λ (s : State n) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "State has indices"} = Muro.Synth.Host.open(path)
  end

  test "an open constructor without all-states is refused" do
    dir = tmp()

    path =
      write_book(dir, "open-list.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        cell : Π (xs : List Nat) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "State constructors take arguments; declare all-states"} =
             Muro.Synth.Host.open(path)
  end

  test "a recursive State without all-states is refused" do
    dir = tmp()

    path =
      write_book(dir, "tree.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        tip : Π (n : Nat) → State
        bin : Π (l : State) → Π (r : State) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "State constructors take arguments; declare all-states"} =
             Muro.Synth.Host.open(path)
  end

  test "a mutually inductive State is refused" do
    dir = tmp()

    path =
      write_book(dir, "mutual.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data Even : Type where
        ez : Even
        es : Π (o : Odd) → Even

      data Odd : Type where
        oz : Odd
        os : Π (e : Even) → Odd

      data State : Type where
        ev : Π (e : Even) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def all-states : run List State := cons (ev ez) nil
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "State is mutually inductive"} = Muro.Synth.Host.open(path)
  end

  test "more than 32 inhabitants without all-states is refused" do
    dir = tmp()

    path = write_book(dir, "wide.muro", wide_src(false))

    message = "State has more than #{Muro.Synth.Term.cap()} inhabitants; declare all-states"
    assert {:error, :usage, ^message} = Muro.Synth.Host.open(path)
  end

  test "more than 32 inhabitants with all-states compares by schema" do
    dir = tmp()
    path = write_book(dir, "wide-cover.muro", wide_src(true))

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert host.structured
    assert host.inhabitants == nil
    assert length(host.all_states) == 2

    book = stub_ranking(path)
    assert book =~ "dyn-same"
    assert book =~ "| b0 =>"
    assert book =~ "| b1 =>"
    assert book =~ "| row "
    assert byte_size(book) < 80_000
  end

  test "an open list cover compares the two cells" do
    dir = tmp()
    path = write_book(dir, "cells.muro", list_cover_src())

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert host.structured
    assert host.inhabitants == nil
    assert length(host.all_states) == 2

    book = stub_ranking(path)
    assert book =~ "dyn-same"
    assert book =~ "| nil =>"
    assert book =~ "| cons "
    assert book =~ "| cell "
    refute book =~ "predicted unknown"
  end

  test "a cover split returns the named lists and misses the rest" do
    dir = tmp()
    path = write_book(dir, "cells.muro", list_cover_src())
    assert {:ok, host} = Muro.Synth.Host.open(path)
    [empty, zero] = host.all_states

    bodies = %{empty.spell => "0", zero.spell => "suc 0"}

    assert {:ok, pick} =
             Muro.Synth.Term.cover_match(
               host.schema,
               "s",
               host.all_states,
               fn _src -> "Nat" end,
               fn spell -> Map.fetch!(bodies, spell) end,
               fn _src -> "suc (suc 0)" end
             )

    assert {:ok, back} =
             Muro.Synth.Term.cover_match(
               host.schema,
               "s",
               host.all_states,
               fn _src -> "State" end,
               fn spell -> spell end,
               fn src -> src end
             )

    book =
      write_book(dir, "pick.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        cell : Π (xs : List Nat) → State

      def pick : run Π (s : State) → Nat :=
        λ (s : State) →
          #{pick}
      def at-nil : evidence {pick (cell nil) ≡ 0 : Nat} := refl
      def at-zero : evidence {pick (cell (cons 0 nil)) ≡ suc 0 : Nat} := refl
      def at-one : evidence {pick (cell (cons (suc 0) nil)) ≡ suc (suc 0) : Nat} := refl
      def at-longer : evidence {pick (cell (cons 0 (cons 0 nil))) ≡ suc (suc 0) : Nat} := refl
      def back : run Π (s : State) → State :=
        λ (s : State) →
          #{back}
      def back-nil : evidence {back (cell nil) ≡ (cell nil) : State} := refl
      def back-zero : evidence {back (cell (cons 0 nil)) ≡ (cell (cons 0 nil)) : State} := refl
      def back-one : evidence {back (cell (cons (suc 0) nil)) ≡ (cell (cons (suc 0) nil)) : State} := refl
      def back-longer : evidence {back (cell (cons 0 (cons 0 nil))) ≡ (cell (cons 0 (cons 0 nil))) : State} := refl
      """)

    assert Muro.check_file(book) == :ok
  end

  test "a cover step leaves is not ranked" do
    dir = tmp()
    path = write_book(dir, "open.muro", unclosed_src())

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.program == {:feat, "is-self-loop-go"}
    assert result.reason == "all-states is not closed under step"
    refute result.book =~ "evidence CoindHomo"
    refute result.book =~ "def rank"
    refute result.book =~ "State is not a finite enumeration"
  end

  test "an empty all-states is not ranked" do
    dir = tmp()
    path = write_book(dir, "empty.muro", empty_cover_src())

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.program == true
    assert result.reason == "all-states is empty"
    refute result.book =~ "evidence CoindHomo"
    refute result.book =~ "State is not a finite enumeration"
  end

  test "schema equality decides two constructors" do
    schema =
      {:data, "State", [%{name: "none", fields: []}, %{name: "some", fields: [:nat]}]}

    assert {:ok, text, _taken} = Muro.Synth.Term.eq_source("dyn-same", schema, MapSet.new())
    dir = tmp()

    path =
      write_book(dir, "eq.muro", """
      import "std:bool.muro"

      data State : Type where
        none : State
        some : Π (n : Nat) → State

      #{text}
      def same-none : evidence {dyn-same none none ≡ true : Bool} := refl
      def diff-arm : evidence {dyn-same none (some 0) ≡ false : Bool} := refl
      def same-some : evidence {dyn-same (some 0) (some 0) ≡ true : Bool} := refl
      def diff-suc : evidence {dyn-same (some 0) (some (suc 0)) ≡ false : Bool} := refl
      """)

    assert Muro.check_file(path) == :ok
  end

  test "schema equality recurses on a tree" do
    assert {:ok, book} =
             Muro.Parser.parse("""
             data State : Type where
               tip : Π (n : Nat) → State
               bin : Π (+ l : State) → Π (r : State) → State
             """)

    schema = Muro.Synth.Term.schema(book, "State")
    assert {:ok, text, _taken} = Muro.Synth.Term.eq_source("dyn-same", schema, MapSet.new())
    dir = tmp()

    path =
      write_book(dir, "tree-eq.muro", """
      import "std:bool.muro"

      data State : Type where
        tip : Π (n : Nat) → State
        bin : Π (+ l : State) → Π (r : State) → State

      #{text}
      def same-tip : evidence {dyn-same (tip 0) (tip 0) ≡ true : Bool} := refl
      def diff-nat : evidence {dyn-same (tip 0) (tip (suc 0)) ≡ false : Bool} := refl
      def same-bin : evidence {dyn-same (bin (tip 0) (tip 0)) (bin (tip 0) (tip 0)) ≡ true : Bool} := refl
      def diff-arm : evidence {dyn-same (tip 0) (bin (tip 0) (tip 0)) ≡ false : Bool} := refl
      def diff-child : evidence {dyn-same (bin (tip 0) (tip 0)) (bin (tip (suc 0)) (tip 0)) ≡ false : Bool} := refl
      def nest : evidence {dyn-same (bin (bin (tip 0) (tip (suc 0))) (tip 0)) (bin (bin (tip 0) (tip (suc 0))) (tip 0)) ≡ true : Bool} := refl
      """)

    assert Muro.check_file(path) == :ok
  end

  # The stub names `CoindHomo` as `Nat`, so a real certificate cannot
  # check. The rendered book is the evidence that the cover was ranked.
  # It is not a homomorphism.
  defp stub_ranking(path) do
    parent = self()
    _ = ranked_books()

    checker = fn book, fuel ->
      send(parent, {:ranked, File.read!(book)})
      Muro.check_file(book, fuel: fuel)
    end

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0, checker: checker)
    assert result.status == :residual
    assert result.book == nil
    refute result.status == :certified

    books = ranked_books()
    assert books != []
    book = Enum.join(books, "\n")
    assert book =~ "def survivor : run PredProg := (feat is-self-loop-go)"
    assert book =~ "cert-solve"
    assert book =~ "evidence CoindHomo"
    assert book =~ "Empty"
    assert book =~ "cert-cover-miss"
    refute book =~ "State is not a finite enumeration"
    book
  end

  defp ranked_books do
    receive do
      {:ranked, src} -> [src | ranked_books()]
    after
      0 -> []
    end
  end

  defp unclosed_src do
    String.replace(
      list_cover_src(),
      "(cell (cons 0 nil), suc 0)",
      "(cell (cons (suc 0) nil), suc 0)"
    )
  end

  defp empty_cover_src do
    String.replace(
      list_cover_src(),
      "cons (cell nil) (cons (cell (cons 0 nil)) nil)",
      "nil"
    )
  end

  defp ranking_names do
    """
    def CoindHomo : spec Type := Nat
    def action-value : spec Type := Nat
    def action-at : spec Type := Nat
    def value : spec Type := Nat
    def solve : spec Type := Nat
    def dom-refl : spec Type := Nat
    def tabulate-dom : spec Type := Nat
    def le-refl : spec Type := Nat
    def maxN : run Π (m : Nat) → Π (n : Nat) → Nat :=
      λ (m : Nat) → λ (_ : Nat) → m
    def max : run Π (m : Nat) → Π (n : Nat) → Nat := maxN
    def bottom : run Nat := 0
    def Reward : spec Type := Nat
    """
  end

  defp list_cover_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      cell : Π (xs : List Nat) → State

    data Action : Type where
      go : Action
      stay : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match s motive (λ _ → State × Nat)
          | cell xs =>
              (match a motive (λ _ → State × Nat)
                | go =>
                    (match xs motive (λ _ → State × Nat)
                      | nil => (cell (cons 0 nil), suc 0)
                      | cons h t => (cell (cons h t), 0))
                | stay =>
                    (match xs motive (λ _ → State × Nat)
                      | nil => (cell nil, suc (suc 0))
                      | cons _ _ => (cell nil, 0)))

    def all-actions : run List Action := cons go (cons stay nil)
    def horizon : run Nat := 0
    def all-states : run List State :=
      cons (cell nil) (cons (cell (cons 0 nil)) nil)
    #{leb_src()}
    #{ranking_names()}
    """
  end

  defp wide_src(cover?) do
    cover =
      if cover? do
        """
        def all-states : run List State :=
          cons (row b0 b0 b0 b0 b0 b0) (cons (row b1 b1 b1 b1 b1 b1) nil)
        """
      else
        ""
      end

    """
    import "std:bool.muro"
    import "std:list.muro"

    data Bit : Type where
      b0 : Bit
      b1 : Bit

    data State : Type where
      row : Π (a : Bit) → Π (b : Bit) → Π (c : Bit) → Π (d : Bit) → Π (e : Bit) → Π (f : Bit) → State

    data Action : Type where
      go : Action
      stay : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match s motive (λ _ → State × Nat)
          | row x _ _ _ _ _ =>
              (match a motive (λ _ → State × Nat)
                | go =>
                    (match x motive (λ _ → State × Nat)
                      | b0 => (row b1 b1 b1 b1 b1 b1, suc 0)
                      | b1 => (row b1 b1 b1 b1 b1 b1, 0))
                | stay =>
                    (match x motive (λ _ → State × Nat)
                      | b0 => (row b0 b0 b0 b0 b0 b0, suc (suc 0))
                      | b1 => (row b0 b0 b0 b0 b0 b0, 0)))

    def all-actions : run List Action := cons go (cons stay nil)
    def horizon : run Nat := 0
    #{cover}
    #{leb_src()}
    #{ranking_names()}
    """
  end

  defp joined(result), do: Enum.join(result.lines, "\n")

  defp prefer_go(dir), do: write_book(dir, "prefer.muro", prefer_src())

  defp two_hot(dir), do: write_book(dir, "hot.muro", two_hot_src())

  defp write_book(dir, name, src) do
    path = Path.join(dir, name)
    File.write!(path, src)
    path
  end

  defp host_book(dir, name, body) do
    write_book(dir, name, """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      s : State

    data Action : Type where
      a : Action
      b : Action

    #{body}
    """)
  end

  defp prefer_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      s : State

    data Action : Type where
      go : Action
      stay : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match a motive (λ _ → State × Nat)
          | go => (s, suc 0)
          | stay => (s, 0)

    def all-actions : run List Action := cons go (cons stay nil)
    def default-action : run Action := stay
    def horizon : run Nat := 0
    def all-states : run List State := cons s nil
    #{leb_src()}
    """
  end

  defp feature_src do
    """
    def Carrier : spec Type := State

    data Feature : Type where
      hot : Feature

    def eval-feature : run Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
      λ (+ _ : Feature) → λ (+ _ : Carrier) → true
    """
  end

  defp two_hot_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      s : State
      t : State

    data Action : Type where
      go : Action
      stay : Action

    def Carrier : spec Type := State

    data Feature : Type where
      hot : Feature

    def eval-feature : run Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
      λ (+ _ : Feature) → λ (+ _ : Carrier) → true

    def step : run Π (x : State) → Π (a : Action) → State × Nat :=
      λ (x : State) → λ (a : Action) →
        match a motive (λ _ → State × Nat)
          | go => (x, suc 0)
          | stay => (x, 0)

    def all-actions : run List Action := cons go (cons stay nil)
    def default-action : run Action := stay
    def horizon : run Nat := 0
    def all-states : run List State := cons s (cons t nil)
    #{leb_src()}
    """
  end

  defp leb_src do
    """
    def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
      λ (m : Nat) → λ (n : Nat) →
        match m motive (λ _ → Bool)
          | 0 => true
          | suc p =>
              (match n motive (λ _ → Bool)
                | 0 => false
                | suc q => leb p q)
    """
  end

  defp tmp do
    path =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_loop_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    path
  end
end
