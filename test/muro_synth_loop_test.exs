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
    assert message =~ ":enotdir"
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

    assert diagnostic =~ ":enotdir"
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
    path = Path.join(System.tmp_dir!(), "muro_synth_loop_#{System.unique_integer([:positive])}")
    File.mkdir_p!(path)
    path
  end
end
