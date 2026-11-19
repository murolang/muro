defmodule Muro.SynthLoopTest do
  use ExUnit.Case, async: false

  @two "examples/cshrl/envs/two_state.muro"
  @bin "examples/cshrl/envs/binary_sacrifice.muro"
  @maze "examples/cshrl/envs/maze_auto.muro"
  @maze3 "examples/cshrl/envs/maze_auto_e2e.muro"
  @place "examples/cshrl/envs/placement.muro"
  @queens4 "examples/cshrl/envs/queens4.muro"
  @nest "examples/cshrl/envs/nested_bit.muro"
  @cover "examples/cshrl/envs/list_cover.muro"
  @tree "examples/cshrl/envs/tree_cover.muro"
  @tip "examples/cshrl/envs/tip_suc.muro"
  @deep "examples/cshrl/envs/nested_bin.muro"
  @reach "examples/cshrl/envs/reachable_bin.muro"
  @fork "examples/cshrl/envs/reachable_fork.muro"
  @neg "test/fixtures/synth_neg.muro"
  @gap "test/fixtures/synth_gap.muro"
  @horizon "test/fixtures/synth_horizon.muro"
  @later "test/fixtures/synth_later.muro"
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
    assert missed_text =~ "the feature language cannot separate"
    assert missed_text =~ "agrees with"
    assert missed_text =~ "templates "
    assert missed_text =~ "path depth "
    assert is_list(missed.features)
    assert is_list(missed.kinds)
    assert is_integer(missed.path_depth)
    assert missed.path_bound == Muro.Synth.Term.path_bound()
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

  test "4-queens list templates enumerate 23, keep 18, and reduce to 6" do
    assert {:ok, host} = Muro.Synth.Host.open(@queens4)
    cover = Muro.Synth.Oracle.cover(host)
    assert length(cover) == 18

    lists = fn tag ->
      Enum.flat_map(cover, fn state ->
        case state.value do
          {^tag, xs} -> [xs]
          _ -> []
        end
      end)
    end

    open = lists.(:ongoing)
    solved = lists.(:solved)
    alive = open ++ solved
    assert length(open) == 15
    assert length(solved) == 2

    {templates, _} = Muro.Synth.Term.templates({:list, :nat}, alive, MapSet.new(), 0)
    assert length(templates) == 23
    assert Enum.count(templates, &(&1.kind in [:vals_eq, :spread_eq, :pair_any])) == 18
    assert Enum.count(templates, &(&1.kind == :len_is)) == 5

    bit? = fn spec, config -> Muro.Synth.Term.eval_spec({:list, :nat}, spec, config) end
    kept = Enum.filter(templates, fn spec -> not Enum.any?(alive, &bit?.(spec, &1)) end)
    reduced = Muro.Synth.Feature.eliminate_redundant(kept)

    goals =
      Enum.filter(templates, fn spec ->
        Enum.all?(solved, &bit?.(spec, &1)) and Enum.all?(open, &(not bit?.(spec, &1)))
      end)

    assert length(kept) == 18

    assert Enum.map(reduced, & &1.name) == [
             "pair-any-0-1",
             "pair-any-0-2",
             "pair-any-1-2",
             "pair-any-0-3",
             "pair-any-1-3",
             "pair-any-2-3"
           ]

    assert Enum.map(goals, & &1.name) == ["len-is-4"]
  end

  # The certificate is the placement class lemma. The 18-state table stays.
  # Locally that check took 9860 ms.
  # The survivor is size 4. Enumeration of that size took under a second.
  # Default `mix test` excludes `:slow`. CI runs this with `mix test --only slow`.
  @tag timeout: 720_000
  @tag :slow
  test "4-queens certifies positive-reward reachability" do
    src = File.read!(@queens4)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    pred = %{
      "c0" => "(orp (feat has-pos-reward-c0) (notp (otherp reaches-pos c0)))",
      "c1" => "(orp (feat reaches-pos-c1) (notp (otherp reaches-pos c1)))",
      "c2" => "(orp (feat reaches-pos-c2) (notp (otherp reaches-pos c2)))",
      "c3" => "(orp (feat has-pos-reward-c0) (notp (otherp reaches-pos c3)))"
    }

    assert {:ok, result} = Muro.Synth.cegis_loop(@queens4)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"

    assert result.versions == [
             16,
             0,
             1056,
             0,
             26,
             0,
             46,
             0,
             171,
             0,
             454,
             1,
             454,
             1,
             454,
             1,
             454,
             1
           ]

    assert result.sizes == [
             [1, 26],
             [2, 20],
             [3, 125],
             [4, 283]
           ]

    assert result.considered == 8_138
    assert result.distinct == 454
    assert result.enum_ms < 120_000
    assert Enum.map(result.program, &Muro.Synth.render/1) == Enum.map(~w(c0 c1 c2 c3), &pred[&1])

    assert result.book =~ "def survivor-c0 : run PredProg := #{pred["c0"]}"
    assert result.book =~ "def survivor-c3 : run PredProg := #{pred["c3"]}"
    assert result.book =~ "def policy : run Π (+ s : State) → Action :="
    assert result.book =~ "match eval survivor-c0 s"
    assert result.book =~ "match eval survivor-c1 s"
    assert result.book =~ "match eval survivor-c2 s"
    assert result.book =~ "match eval survivor-c3 s"
    assert result.book =~ "| reaches-pos-c0 => dyn-one c c0 horizon"
    assert result.book =~ "| reaches-pos-c3 => dyn-one c c3 horizon"
    assert result.book =~ "data Stem : Type where"
    assert result.book =~ "reaches-pos : Stem"
    assert result.book =~ "def stem-at "
    assert result.book =~ "def other-at "
    assert result.book =~ "(orb (stem-at "
    assert result.book =~ "def dyn-best-pos "
    assert result.book =~ "def dyn-one "
    assert result.book =~ "def dyn-any "
    assert result.book =~ "def dyn-known "
    assert result.book =~ "def dyn-best-rec "
    assert result.book =~ "def dyn-one-rec "
    assert result.book =~ "def dyn-any-rec "
    assert result.book =~ "| suc j => dyn-any-rec s j"
    assert result.book =~ "def dyn-reach-holds-dead-0"
    assert result.book =~ "dyn-best-pos dead 0 ≡ false : Bool"
    assert result.book =~ "def dyn-reach-holds-dead-1"
    assert result.book =~ "dyn-best-pos dead 1 ≡ dyn-any dead 0 : Bool"
    refute result.book =~ "dyn-reach-agrees"
    assert result.book =~ "evidence CoindHomo rank"
    assert result.book =~ "import \"../lib/placement.muro\""
    assert result.book =~ "rec-is-hit"
    assert result.cert_ms < 180_000
    refute result.book =~ "cert-cover-miss"
    refute result.book =~ "find-policy"
    refute result.book =~ "find-ranking"
    refute result.book =~ "placed-find-policy"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "certificate CoindHomo"
    assert text =~ "program: #{pred["c0"]}"
    assert text =~ "enumeration"
    assert text =~ "considered 8138"
    assert text =~ "distinct 454"
    assert text =~ "predicate size bound 18"
    assert text =~ "book open"
    assert text =~ "reach table"
    assert text =~ "cover 18"
    assert text =~ "policy render"
    assert text =~ "certificate check"
    assert text =~ "at (ongoing nil) the program prefers c1"
    assert text =~ "at (ongoing (cons (suc 0) nil)) the program prefers c3"
    assert text =~ "at (ongoing (cons (suc (suc 0)) nil)) the program prefers c0"
    assert text =~ "at dead the program prefers c0"
    assert text =~ "version space 16"
    assert text =~ "version space 1056"
    assert text =~ "version space 454"
    refute text =~ "empty version space"
    refute text =~ "features insufficient"
    refute text =~ "homomorphism is not derivable"
    refute text =~ "placed-find-policy"
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

  test "tip (suc 0) takes the suc arm of step" do
    assert {:ok, host} = Muro.Synth.Host.open(@tip)
    suc = Enum.find(host.all_states, &(&1.spell == "(tip (suc 0))"))
    zero = Enum.find(host.all_states, &(&1.spell == "(tip 0)"))
    assert zero.value == {:tip, 0}
    assert suc.value == {:tip, 1}

    assert {%{value: {:tip, 0}}, 0} = host.step.(zero, "go")
    assert {%{value: {:tip, 1}, spell: "(tip (suc 0))"}, 1} = host.step.(suc, "go")
    assert {%{value: {:tip, 1}}, 0} = host.step.(suc, "stay")
  end

  test "a decoded Nat greater than 0 takes the suc arm" do
    dir = tmp()
    path = write_book(dir, "tip-suc-host.muro", tip_suc_host_src())

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert host.structured

    zero = Enum.find(host.all_states, &(&1.spell == "(tip 0)"))
    suc = Enum.find(host.all_states, &(&1.spell == "(tip (suc 0))"))
    assert zero.value == {:tip, 0}
    assert suc.value == {:tip, 1}

    assert {%{value: {:tip, 0}}, 0} = host.step.(zero, "go")
    assert {%{value: {:tip, 1}, spell: "(tip (suc 0))"}, 1} = host.step.(suc, "go")
    assert {%{value: {:tip, 1}}, 0} = host.step.(suc, "stay")

    refute host.hint_eval.("big", zero)
    assert host.hint_eval.("big", suc)
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
  test "a tip of suc 0 certifies the reward of go" do
    src = File.read!(@tip)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, result} = Muro.Synth.cegis_loop(@tip, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "has-pos-reward-go"}
    assert result.book =~ "def survivor : run PredProg := (feat has-pos-reward-go)"
    assert result.book =~ "evidence CoindHomo rank"
    assert result.book =~ "cert-cover-miss"

    assert result.book =~
             "def cert-solve-tip-n0 : evidence Π (n : Nat) → {solve (tip 0) n ≡ suc 0 : Nat}"

    assert result.book =~
             "def cert-solve-tip-n1 : evidence Π (n : Nat) → {solve (tip (suc 0)) n ≡ suc 0 : Nat}"

    refute result.book =~ "CoinductiveHomomorphism"
    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat has-pos-reward-go)"
    assert text =~ "at (tip 0) the program prefers stay"
    assert text =~ "at (tip (suc 0)) the program prefers go"
    assert text =~ "certificate CoindHomo"
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
  test "a constructor under a recursive child is enumerated and certified" do
    src = File.read!(@deep)
    refute src =~ "data Feature"
    refute src =~ "eval-feature"

    assert {:ok, missed} = Muro.Synth.cegis_loop(@deep, structural: false, depth: 0, max_depth: 0)
    assert missed.status == :insufficient
    assert missed.book == nil
    assert joined(missed) =~ "muro synth: features insufficient"

    assert {:ok, result} = Muro.Synth.cegis_loop(@deep, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "ctor-is-p0-0-bin-bin-bin"}
    assert result.book =~ "def survivor : run PredProg := (feat ctor-is-p0-0-bin-bin-bin)"
    assert result.book =~ "ctor-is-p0-0-bin-bin-bin : Feature"
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "has-pos-reward"
    refute result.book =~ "CoinductiveHomomorphism"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat ctor-is-p0-0-bin-bin-bin)"
    assert text =~ "at (bin (bin (tip 0) (tip 0)) (tip 0)) the program prefers stay"
    assert text =~ "at (bin (bin (bin (tip 0) (tip 0)) (tip 0)) (tip 0)) the program prefers move"
    assert text =~ "certificate CoindHomo"
  end

  @tag timeout: 180_000
  test "a reachable cover of a recursive State is certified" do
    src = File.read!(@reach)
    refute src =~ "data Feature"
    refute src =~ "def all-states"
    refute src =~ "eval-feature"

    assert {:ok, host} = Muro.Synth.Host.open(@reach)
    assert length(host.all_states) == 2

    assert Enum.map(host.all_states, & &1.spell) == [
             "(bin (bin (tip 0) (tip 0)) (tip 0))",
             "(bin (bin (bin (tip 0) (tip 0)) (tip 0)) (tip 0))"
           ]

    assert {:ok, missed} =
             Muro.Synth.cegis_loop(@reach, structural: false, depth: 0, max_depth: 0)

    assert missed.status == :insufficient
    assert missed.book == nil

    assert {:ok, result} = Muro.Synth.cegis_loop(@reach, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "ctor-is-p0-0-bin-bin-bin"}
    assert result.book =~ "def survivor : run PredProg := (feat ctor-is-p0-0-bin-bin-bin)"
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "has-pos-reward"
    refute result.book =~ "CoinductiveHomomorphism"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat ctor-is-p0-0-bin-bin-bin)"
    assert text =~ "at (bin (bin (tip 0) (tip 0)) (tip 0)) the program prefers stay"
    assert text =~ "at (bin (bin (bin (tip 0) (tip 0)) (tip 0)) (tip 0)) the program prefers move"
    assert text =~ "certificate CoindHomo"
  end

  @tag timeout: 180_000
  test "actions that diverge are both in the reachable cover" do
    src = File.read!(@fork)
    refute src =~ "data Feature"
    refute src =~ "def all-states"
    refute src =~ "eval-feature"
    refute src =~ "find-policy"
    refute src =~ "find-ranking"

    assert {:ok, host} = Muro.Synth.Host.open(@fork)
    assert host.actions == ["move", "stay"]
    assert length(host.all_states) == 3

    assert Enum.map(host.all_states, & &1.spell) == [
             "(bin (tip 0) (tip 0))",
             "(bin (bin (tip 0) (tip 0)) (tip 0))",
             "(bin (tip 0) (bin (tip 0) (tip 0)))"
           ]

    [seed | _] = host.all_states

    assert {:ok, by_move} =
             Muro.Synth.Oracle.close_under_step(%{host | actions: ["move"]}, [seed])

    assert length(by_move) == 2
    refute Enum.any?(by_move, &(&1.spell == "(bin (tip 0) (bin (tip 0) (tip 0)))"))

    assert {:ok, by_stay} =
             Muro.Synth.Oracle.close_under_step(%{host | actions: ["stay"]}, [seed])

    assert length(by_stay) == 2
    refute Enum.any?(by_stay, &(&1.spell == "(bin (bin (tip 0) (tip 0)) (tip 0))"))

    assert {:ok, result} = Muro.Synth.cegis_loop(@fork, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.program == {:feat, "ctor-is-p0-bin-bin"}
    assert result.book =~ "def survivor : run PredProg := (feat ctor-is-p0-bin-bin)"
    assert result.book =~ "match eval survivor"
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "find-policy"
    refute result.book =~ "find-ranking"
    refute result.book =~ "has-pos-reward"
    refute result.book =~ "CoinductiveHomomorphism"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "program: (feat ctor-is-p0-bin-bin)"
    assert text =~ "at (bin (tip 0) (tip 0)) the program prefers stay"
    assert text =~ "at (bin (bin (tip 0) (tip 0)) (tip 0)) the program prefers move"
    assert text =~ "at (bin (tip 0) (bin (tip 0) (tip 0))) the program prefers stay"
    assert text =~ "certificate CoindHomo"
  end

  # `left` is private to the search. A deepen that separates the pair
  # calls search again with the same invent budget. Only a successful
  # invention spends a round.
  test "a deepen does not spend an invent round" do
    dir = tmp()
    low = "nest (tip off)"
    high = "nest (tip on)"
    path = write_book(dir, "budget.muro", swap_src(low, high))

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert length(host.all_states) == 2
    [earlier, later] = host.all_states
    assert {:ok, _specs, 2} = Muro.Synth.Feature.deepen(host, earlier, later)

    {result, calls} =
      with_budget_trace(fn ->
        Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0, checker: fn _book, _fuel -> :ok end)
      end)

    assert {:ok, result} = result
    assert result.program == {:feat, "ctor-is-p0-0-nest-tip-on"}
    refute result.status == :insufficient

    limits = %{
      considered_budget: Muro.Synth.considered_budget(),
      memory_budget: Muro.Synth.memory_budget()
    }

    search = for {:search, left, got} <- calls, do: {left, got}
    invent = for {:invent, left, _got} <- calls, do: left
    assert search == [{2, limits}, {2, limits}]
    assert invent == []
  end

  test "a field past the path bound is invented after the walk stops" do
    dir = tmp()
    low = "nest (nest (nest (tip off)))"
    high = "nest (nest (nest (tip on)))"
    path = write_book(dir, "past.muro", swap_src(low, high))
    assert_invented_after_bound(path, [0, 0, 0, 0], "ctor-is-p0-0-0-0-on")
  end

  test "a list element is invented after the walk stops" do
    dir = tmp()

    path =
      write_book(dir, "elem.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data Bit : Type where
        off : Bit
        on : Bit

      data State : Type where
        cell : Π (xs : List Bit) → State

      data Action : Type where
        go : Action
        stay : Action

      def marked : run Π (s : State) → Bool :=
        λ (s : State) →
          match s motive (λ _ → Bool)
            | cell xs =>
                (match xs motive (λ _ → Bool)
                  | nil => false
                  | cons h _ =>
                      (match h motive (λ _ → Bool)
                        | off => false
                        | on => true))

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (a : Action) →
          match a motive (λ _ → State × Nat)
            | go =>
                (match marked s motive (λ _ → State × Nat)
                  | true => (cell (cons off nil), suc (suc 0))
                  | false => (cell (cons on nil), suc 0))
            | stay =>
                (match marked s motive (λ _ → State × Nat)
                  | true => (cell (cons off nil), suc 0)
                  | false => (cell (cons on nil), suc (suc 0)))

      def all-actions : run List Action := cons go (cons stay nil)
      def horizon : run Nat := 0
      def all-states : run List State :=
        cons (cell (cons off nil)) (cons (cell (cons on nil)) nil)
      #{leb_src()}
      """)

    assert_invented_after_bound(path, [0, 0], "ctor-is-p0-0-on")
  end

  test "product recursion opens and the certificate is refused" do
    dir = tmp()
    path = write_book(dir, "prod-rec.muro", product_rec_src())

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert host.structured
    assert Enum.map(host.all_states, & &1.spell) == ["(tip 0)", "(fork ((tip 0), (tip 0)))"]
    refute Muro.Synth.Term.equatable?(host.schema)

    assert Muro.Synth.Term.cert_refusal(host.schema) ==
             "State recursion under List/product cannot be certified"

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.reason == "State recursion under List/product cannot be certified"
    refute result.book =~ "evidence CoindHomo"
    refute result.book =~ "def rank"
  end

  test "product recursion without all-states is refused at open" do
    dir = tmp()

    src =
      product_rec_src()
      |> String.replace(
        """
        def all-states : run List State :=
          cons (tip 0) (cons (fork (tip 0, tip 0)) nil)
        """,
        ""
      )

    path = write_book(dir, "prod-open.muro", src)

    assert {:error, :usage, "State constructors take arguments; declare all-states"} =
             Muro.Synth.Host.open(path)

    assert {:error, :usage, "State constructors take arguments; declare all-states"} =
             Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
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

  test "a depth-1 survivor does not install reaches-pos" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@horizon)
    assert result.status == :policy

    assert result.program ==
             {:and, {:feat, "is-self-loop-stay"}, {:not, {:feat, "has-pos-reward-go"}}}

    assert result.versions == [4, 0, 72, 1]

    assert result.book =~
             "def survivor : run PredProg := (andp (feat is-self-loop-stay) (notp (feat has-pos-reward-go)))"

    refute result.book =~ "reaches-pos"

    text = joined(result)
    assert text =~ "at a the program prefers stay"
    assert text =~ "at b the program prefers go"
    assert text =~ "at late the program prefers stay"
    refute text =~ "reaches-pos"
    refute text =~ "predicate size"
  end

  test "max depth 0 does not install reaches-pos when depth 1 was not searched" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@horizon, depth: 0, max_depth: 0)
    assert result.status == :empty
    assert result.book == nil
    assert result.versions == [4, 0]
    assert result.features == ["has-pos-reward-go", "is-self-loop-stay"]
    refute "reaches-pos" in result.kinds

    text = joined(result)
    assert text =~ "predicate depth 0 exhausted"
    assert text =~ "muro synth: empty version space"
    refute text =~ "reaches-pos"
    refute text =~ "predicate size"
  end

  @tag timeout: 180_000
  test "a sooner reward of 1 is not certified over a later 100" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@later)
    assert result.status == :residual
    assert result.program == nil
    assert result.book == nil
    assert result.versions == [5, 1, 110, 28, 27, 26]
    assert Map.get(result, :certificate) == nil

    text = joined(result)
    assert text =~ "homomorphism is not derivable"
    assert text =~ "carrier start"
    assert text =~ "pair later now"
    refute text =~ "homomorphism checked"
    refute text =~ "reaches-pos"
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
    parent =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_cwd_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

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
      Path.join(
        System.tmp_dir!(),
        "muro_synth_stdout_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

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

    assert {:error, :usage, "a recursive State declares no initial state"} =
             Muro.Synth.Host.open(path)
  end

  test "an open constructor with init is still refused" do
    dir = tmp()

    path =
      write_book(dir, "open-init.muro", """
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
      def init : run State := cell nil
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "State constructors take arguments; declare all-states"} =
             Muro.Synth.Host.open(path)
  end

  test "init of the wrong type is refused" do
    dir = tmp()

    path =
      write_book(dir, "init-nat.muro", """
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
      def init : run Nat := 0
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "init must be run State or run List State"} =
             Muro.Synth.Host.open(path)
  end

  test "a declared all-states is not replaced by init" do
    dir = tmp()

    path =
      write_book(dir, "declared.muro", """
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
      def all-states : run List State := cons (tip 0) nil
      def init : run State := bin (tip 0) (tip 0)
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert Enum.map(host.all_states, & &1.spell) == ["(tip 0)"]
  end

  test "init lists the states the reachable cover starts from" do
    dir = tmp()

    path =
      write_book(dir, "seeds.muro", """
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
      def init : run List State :=
        cons (tip 0) (cons (bin (tip 0) (tip 0)) nil)
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:ok, host} = Muro.Synth.Host.open(path)

    assert Enum.map(host.all_states, & &1.spell) == [
             "(tip 0)",
             "(bin (tip 0) (tip 0))"
           ]
  end

  test "a reachable set that does not close within the bound is refused" do
    dir = tmp()

    path =
      write_book(dir, "tick.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        stop : State
        more : Π (+ s : State) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) →
          match s motive (λ _ → State × Nat)
            | stop => (more stop, 0)
            | more s => (more (more s), 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def init : run State := stop
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    message = Muro.Synth.Oracle.reachable_bound_message()
    assert {:error, :usage, ^message} = Muro.Synth.Host.open(path)
    assert {:error, :usage, ^message} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert message =~ "not finite within #{Muro.Synth.Oracle.reachable_cap()}"
  end

  test "an empty init list declares no initial state" do
    dir = tmp()

    path =
      write_book(dir, "empty-init.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        stop : State
        more : Π (+ s : State) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def init : run List State := nil
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "a recursive State declares no initial state"} =
             Muro.Synth.Host.open(path)
  end

  test "init that does not decode as a State is refused" do
    dir = tmp()

    path =
      write_book(dir, "init-word.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        stop : State
        more : Π (s : State) → Π (n : U8) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) →
          match s motive (λ _ → State × Nat)
            | stop => (stop, 0)
            | more s _ => (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def init : run State := more stop (toU8 0)
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "init has a value that is not a State"} = Muro.Synth.Host.open(path)
  end

  test "a successor that is not a State is refused before the cover is closed" do
    dir = tmp()

    path =
      write_book(dir, "not-state.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        stop : State
        more : Π (s : State) → Π (n : U8) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) →
          match s motive (λ _ → State × Nat)
            | stop => (more stop (toU8 0), 0)
            | more s _ => (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def init : run State := stop
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    message = Muro.Synth.Oracle.step_not_state_message()
    assert {:error, :usage, ^message} = Muro.Synth.Host.open(path)
    assert {:error, :usage, ^message} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    refute message == Muro.Synth.Oracle.step_left_message()
  end

  test "a successor outside the closed set is not a non-state step" do
    key = {:left_probe, make_ref()}

    step = fn state, action ->
      seen = Process.get(key, %{})
      n = Map.get(seen, {state, action}, 0)
      Process.put(key, Map.put(seen, {state, action}, n + 1))

      if n == 0 do
        {state, 0}
      else
        {{:escaped, state}, 0}
      end
    end

    host = %{actions: ["go"], step: step}
    assert {:error, :left} = Muro.Synth.Oracle.close_under_step(host, [:here])

    other = %{
      actions: ["go"],
      step: fn _state, _action -> raise ArgumentError, "left the module" end
    }

    assert {:error, :left} = Muro.Synth.Oracle.close_under_step(other, [:here])

    decode = %{
      actions: ["go"],
      step: fn _state, _action ->
        raise ArgumentError, "not a value of this state: 0"
      end
    }

    assert {:error, :not_state} = Muro.Synth.Oracle.close_under_step(decode, [:here])
    refute Muro.Synth.Oracle.step_not_state_message() == Muro.Synth.Oracle.step_left_message()
  end

  test "a cover of 256 states is accepted and 257 is refused" do
    assert {:ok, cover} = Muro.Synth.Oracle.close_under_step(chain_host(256), [0])
    assert length(cover) == 256

    assert {:error, :bound} = Muro.Synth.Oracle.close_under_step(chain_host(257), [0])

    stay = %{
      actions: ["go"],
      step: fn state, _action -> {state, 0} end
    }

    assert {:ok, held} = Muro.Synth.Oracle.close_under_step(stay, Enum.to_list(0..255))
    assert length(held) == 256
    assert {:error, :bound} = Muro.Synth.Oracle.close_under_step(stay, Enum.to_list(0..256))
  end

  test "the unbounded closure walk is nullary constructors only" do
    finite = %{
      all_states: nil,
      structured: true,
      states: [:a, :b],
      actions: ["go"],
      step: fn _state, _action -> raise "step is not the finite cover" end
    }

    assert Muro.Synth.Oracle.cover(finite) == [:a, :b]

    nullary = %{
      all_states: nil,
      structured: false,
      states: [:a],
      actions: ["go"],
      step: fn state, _action -> {state, 0} end
    }

    assert Muro.Synth.Oracle.cover(nullary) == [:a]
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

  test "wrapper recursion is mutually inductive" do
    dir = tmp()

    path =
      write_book(dir, "wrap.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data Box : Type where
        box : Π (s : State) → Box

      data State : Type where
        wrap : Π (b : Box) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def all-states : run List State := nil
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :usage, "State is mutually inductive"} = Muro.Synth.Host.open(path)
  end

  test "List State is not strictly positive" do
    dir = tmp()

    path =
      write_book(dir, "list-rec.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        tip : Π (n : Nat) → State
        kids : Π (xs : List State) → State

      data Action : Type where
        go : Action

      def step : run Π (s : State) → Π (a : Action) → State × Nat :=
        λ (s : State) → λ (_ : Action) → (s, 0)

      def all-actions : run List Action := cons go nil
      def horizon : run Nat := 0
      def all-states : run List State := cons (tip 0) nil
      def leb : run Π (m : Nat) → Π (n : Nat) → Bool :=
        λ (_ : Nat) → λ (_ : Nat) → true
      """)

    assert {:error, :book, msg} = Muro.Synth.Host.open(path)
    assert msg =~ "constructor is not strictly positive"
  end

  test "a linear field opens and the certificate is refused" do
    dir = tmp()
    path = write_book(dir, "linear.muro", linear_cover_src())

    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert host.structured
    assert Muro.Synth.Term.cert_refusal(host.schema) == "State has a linear field"

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :policy
    assert result.reason == "State has a linear field"
    refute result.book =~ "evidence CoindHomo"
    refute result.book =~ "def rank"
  end

  test "an erased constructor argument is refused" do
    dir = tmp()
    path = write_book(dir, "erased.muro", erased_cover_src())

    assert {:error, :usage, "State has an erased constructor argument"} =
             Muro.Synth.Host.open(path)

    assert {:error, :usage, "State has an erased constructor argument"} =
             Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
  end

  test "a function field is refused" do
    dir = tmp()
    path = write_book(dir, "fun.muro", function_cover_src())

    assert {:error, :usage, "State has a function field"} = Muro.Synth.Host.open(path)

    assert {:error, :usage, "State has a function field"} =
             Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
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

  test "schema equality of a product uses let" do
    schema = {:data, "State", [%{name: "cell", fields: [{:prod, :nat, :nat}]}]}
    assert {:ok, text, _taken} = Muro.Synth.Term.eq_source("dyn-same", schema, MapSet.new())
    assert text =~ "let ("
    refute text =~ "| (a, b) =>"
    dir = tmp()

    path =
      write_book(dir, "pair-eq.muro", """
      import "std:bool.muro"

      data State : Type where
        cell : Π (p : Nat × Nat) → State

      #{text}
      def same-zero : evidence {dyn-same (cell (0, 0)) (cell (0, 0)) ≡ true : Bool} := refl
      def diff-fst : evidence {dyn-same (cell (0, 0)) (cell (suc 0, 0)) ≡ false : Bool} := refl
      def diff-snd : evidence {dyn-same (cell (0, 0)) (cell (0, suc 0)) ≡ false : Bool} := refl
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

  defp chain_host(n) do
    %{
      actions: ["go"],
      step: fn state, _action ->
        next = if state + 1 < n, do: state + 1, else: state
        {next, 0}
      end
    }
  end

  defp product_rec_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      tip : Π (n : Nat) → State
      fork : Π (p : State × State) → State

    data Action : Type where
      go : Action
      stay : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match s motive (λ _ → State × Nat)
          | tip n =>
              (match a motive (λ _ → State × Nat)
                | go => (tip n, 0)
                | stay => (tip n, suc 0))
          | fork p =>
              (match a motive (λ _ → State × Nat)
                | go => (fork p, suc 0)
                | stay => (fork p, 0))

    def all-actions : run List Action := cons go (cons stay nil)
    def horizon : run Nat := 0
    def all-states : run List State :=
      cons (tip 0) (cons (fork (tip 0, tip 0)) nil)
    #{leb_src()}
    #{ranking_names()}
    """
  end

  defp linear_cover_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      tip : Π (%1 n : Nat) → State
      bin : Π (%1 n : Nat) → State

    data Action : Type where
      go : Action
      stay : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match s motive (λ _ → State × Nat)
          | tip n =>
              (match a motive (λ _ → State × Nat)
                | go => (tip n, 0)
                | stay => (tip n, suc 0))
          | bin n =>
              (match a motive (λ _ → State × Nat)
                | go => (bin n, suc 0)
                | stay => (bin n, 0))

    def all-actions : run List Action := cons go (cons stay nil)
    def horizon : run Nat := 0
    def all-states : run List State := cons (tip 0) (cons (bin 0) nil)
    #{leb_src()}
    #{ranking_names()}
    """
  end

  defp erased_cover_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      box : Π (- x : Nat) → Π (y : Nat) → State

    data Action : Type where
      go : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (_ : Action) →
        match s motive (λ _ → State × Nat)
          | box x y => (box 0 y, 0)

    def all-actions : run List Action := cons go nil
    def horizon : run Nat := 0
    def all-states : run List State := cons (box 0 0) nil
    #{leb_src()}
    """
  end

  defp function_cover_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    def idN : run Π (n : Nat) → Nat := λ (n : Nat) → n

    data State : Type where
      cell : Π (n : Nat) → Π (f : Π (k : Nat) → Nat) → State

    data Action : Type where
      go : Action

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (_ : Action) →
        match s motive (λ _ → State × Nat)
          | cell n f => (cell n f, 0)

    def all-actions : run List Action := cons go nil
    def horizon : run Nat := 0
    def all-states : run List State := cons (cell 0 idN) nil
    #{leb_src()}
    """
  end

  defp assert_invented_after_bound(path, path_at, name) do
    assert {:ok, host} = Muro.Synth.Host.open(path)
    [earlier, later] = host.all_states
    assert {:stop, specs, 3} = Muro.Synth.Feature.deepen(host, earlier, later)
    assert specs != nil
    assert Enum.all?(specs, &(length(Map.get(&1, :path, [])) <= Muro.Synth.Term.path_bound()))

    refute Enum.any?(specs, fn spec ->
             Muro.Synth.Term.eval_spec(host.schema, spec, earlier) !=
               Muro.Synth.Term.eval_spec(host.schema, spec, later)
           end)

    {added, _} =
      Muro.Synth.Term.invent(host.schema, earlier, later, host.feature_specs, MapSet.new())

    assert Enum.any?(added, &(&1.path == path_at and &1.name == name))

    assert {:ok, result} =
             Muro.Synth.cegis_loop(path,
               depth: 0,
               max_depth: 0,
               checker: fn _book, _fuel -> :ok end
             )

    assert result.program == {:feat, name}
    refute result.status == :insufficient
    refute joined(result) =~ "features insufficient"
  end

  defp swap_src(low, high) do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data Bit : Type where
      off : Bit
      on : Bit

    data State : Type where
      tip : Π (b : Bit) → State
      nest : Π (c : State) → State

    data Action : Type where
      go : Action
      stay : Action

    def buried : run Π (s : State) → Bool :=
      λ (s : State) →
        match s motive (λ _ → Bool)
          | tip b =>
              (match b motive (λ _ → Bool)
                | off => false
                | on => true)
          | nest c => buried c

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match a motive (λ _ → State × Nat)
          | go =>
              (match buried s motive (λ _ → State × Nat)
                | true => (#{low}, suc (suc 0))
                | false => (#{high}, suc 0))
          | stay =>
              (match buried s motive (λ _ → State × Nat)
                | true => (#{low}, suc 0)
                | false => (#{high}, suc (suc 0)))

    def all-actions : run List Action := cons go (cons stay nil)
    def horizon : run Nat := 0
    def all-states : run List State :=
      cons (#{low}) (cons (#{high}) nil)
    #{leb_src()}
    """
  end

  # The invent budget is an argument of the private search, and the
  # search limits follow it. The trace records both. A deepen that
  # returns a separator does not change either.
  defp with_budget_trace(fun) do
    parent = self()

    tracer =
      spawn(fn ->
        send(parent, :budget_ready)
        budget_trace([])
      end)

    receive do
      :budget_ready -> :ok
    end

    # A trace pattern matches only a module the code server has loaded.
    Code.ensure_loaded!(Muro.Synth.Loop)
    :erlang.trace(self(), true, [:call, {:tracer, tracer}])
    :erlang.trace_pattern({Muro.Synth.Loop, :search, 11}, true, [:local])
    :erlang.trace_pattern({Muro.Synth.Loop, :invent_at, 16}, true, [:local])

    try do
      result = fun.()
      {result, stop_budget_trace(tracer)}
    after
      :erlang.trace_pattern({Muro.Synth.Loop, :search, 11}, false, [:local])
      :erlang.trace_pattern({Muro.Synth.Loop, :invent_at, 16}, false, [:local])
      :erlang.trace(self(), false, [:call])

      if Process.alive?(tracer) do
        send(tracer, {:done, self()})
      end
    end
  end

  defp stop_budget_trace(tracer) do
    send(tracer, {:done, self()})

    receive do
      {:budget, calls} -> calls
    after
      5_000 -> flunk("the budget trace did not return")
    end
  end

  defp budget_trace(acc) do
    receive do
      {:trace, _pid, :call, {Muro.Synth.Loop, :search, args}} ->
        budget_trace([{:search, Enum.at(args, 9), List.last(args)} | acc])

      {:trace, _pid, :call, {Muro.Synth.Loop, :invent_at, args}} ->
        budget_trace([{:invent, Enum.at(args, 9), List.last(args)} | acc])

      {:done, from} ->
        send(from, {:budget, Enum.reverse(acc)})
    end
  end

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

  defp tip_suc_host_src do
    """
    import "std:bool.muro"
    import "std:list.muro"

    data State : Type where
      tip : Π (n : Nat) → State

    data Action : Type where
      go : Action
      stay : Action

    def Carrier : spec Type := State

    data Feature : Type where
      big : Feature

    def eval-feature : run Π (+ f : Feature) → Π (+ c : Carrier) → Bool :=
      λ (+ f : Feature) → λ (+ c : Carrier) →
        match f motive (λ _ → Bool)
          | big =>
              (match c motive (λ _ → Bool)
                | tip n =>
                    (match n motive (λ _ → Bool)
                      | 0 => false
                      | suc _ => true))

    def step : run Π (s : State) → Π (a : Action) → State × Nat :=
      λ (s : State) → λ (a : Action) →
        match s motive (λ _ → State × Nat)
          | tip n =>
              (match n motive (λ _ → State × Nat)
                | 0 =>
                    (match a motive (λ _ → State × Nat)
                      | go => (tip 0, 0)
                      | stay => (tip 0, suc 0))
                | suc k =>
                    (match a motive (λ _ → State × Nat)
                      | go => (tip (suc k), suc 0)
                      | stay => (tip (suc k), 0)))

    def all-actions : run List Action := cons go (cons stay nil)
    def default-action : run Action := stay
    def horizon : run Nat := 0
    def all-states : run List State := cons (tip 0) (cons (tip (suc 0)) nil)
    #{leb_src()}
    """
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
