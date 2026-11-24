defmodule Muro.SynthTest do
  use ExUnit.Case, async: true

  alias Muro.Synth

  # The bit is the only feature. true fires, false is the default.
  defp bit(_feature, state), do: state

  defp oracle(_pred, state), do: state

  defp traj(_pred), do: [true, false]

  defp feats(_states), do: [:bit]

  defp score({:feat, _}), do: 1
  defp score(_), do: 0

  test "a chain fires one action" do
    chain = [{{:feat, :bit}, :go}]
    assert Synth.eval_chain(chain, :stay, &bit/2, true) == :go
    assert Synth.eval_chain(chain, :stay, &bit/2, false) == :stay
  end

  test "depth 0 returns the feature test that matches the oracle" do
    assert {:survivors, preds} =
             Synth.run(&score/1, &oracle/2, &traj/1, &feats/1, &bit/2, 0)

    assert Synth.pick(preds, &score/1) == {:feat, :bit}
  end

  test "a high score does not keep a program that misses an observation" do
    # true scores 100 and is wrong at false. The feature test scores 0
    # and matches both states. The score does not put true back.
    score = fn
      true -> 100
      _pred -> 0
    end

    assert {:survivors, preds} =
             Synth.solve([true, {:feat, :bit}], score, &oracle/2, &traj/1, &bit/2)

    refute true in preds
    assert Synth.pick(preds, score) == {:feat, :bit}
  end

  test "a smaller program wins over a higher score" do
    score = fn
      {:not, false} -> 100
      _pred -> 0
    end

    assert Synth.pick([{:not, false}, true], score) == true
    assert Synth.size(true) == 1
    assert Synth.size({:not, {:feat, :bit}}) == 2
  end

  test "a predicate that matches an observation stays, and the space shrinks" do
    vs = Synth.enumerate([:bit], 0)
    kept = Synth.refine(vs, {true, true}, &bit/2)
    assert {:feat, :bit} in kept
    assert false not in kept
    assert length(kept) < length(vs)

    both = Synth.refine_all(vs, [{true, true}, {false, false}], &bit/2)
    assert {:feat, :bit} in both
    assert true not in both
  end

  test "states that agree on the features a predicate reads agree on its value" do
    pred = {:and, {:feat, :bit}, {:not, {:feat, :other}}}

    feat = fn
      :bit, state -> state.bit
      :other, state -> state.other
    end

    left = %{bit: true, other: false, tag: 1}
    right = %{bit: true, other: false, tag: 2}
    assert Synth.reads(pred) == [:bit, :other]
    assert Synth.eval(pred, feat, left) == Synth.eval(pred, feat, right)
  end

  test "fewer steps is the better action, and a stop ties them" do
    step = fn
      :far, :short -> :done
      :far, :long -> :mid
      :mid, _ -> :done
      other, _ -> other
    end

    stop? = fn state -> state == :done end
    pi = fn _ -> :short end

    assert Synth.fewer?(:far, :short, :long, step, stop?, pi, 4)
    refute Synth.fewer?(:far, :long, :short, step, stop?, pi, 4)
    assert Synth.rollout(:done, :short, step, stop?, pi, 4) == 0
    assert Synth.rollout(:done, :long, step, stop?, pi, 4) == 0
  end

  test "the synthesized policy checks and runs" do
    assert {:survivors, preds} =
             Synth.run(&score/1, &oracle/2, &traj/1, &feats/1, &bit/2, 0)

    pred = Synth.pick(preds, &score/1)

    spell = fn :bit -> "s" end
    src = Synth.policy([{pred, :go}], :stay, spell)

    path =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_policy_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}.muro"
      )

    File.write!(path, src)

    assert Muro.check_file(path) == :ok
    assert {:ok, out} = Muro.emit_file(path, Muro.SynthBitPolicy)
    Code.eval_string(out)
    assert apply(Muro.SynthBitPolicy, :policy, [true]) == :go
    assert apply(Muro.SynthBitPolicy, :policy, [false]) == :stay

    assert {:survivors, neg_preds} =
             Synth.deepen(0, 0, &neg_score/1, &neg_oracle/2, &traj/1, &feats/1, &bit/2)

    negated = Synth.pick(neg_preds, &neg_score/1)

    neg = Synth.policy([{negated, :go}], :stay, spell)

    neg_path =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_neg_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}.muro"
      )

    File.write!(neg_path, neg)
    assert Muro.check_file(neg_path) == :ok
    assert {:ok, neg_out} = Muro.emit_file(neg_path, Muro.SynthNegPolicy)
    Code.eval_string(neg_out)
    assert apply(Muro.SynthNegPolicy, :policy, [true]) == :stay
    assert apply(Muro.SynthNegPolicy, :policy, [false]) == :go
  end

  defp neg_score({:not, {:feat, _}}), do: 1
  defp neg_score(_), do: 0

  defp neg_oracle(_pred, state), do: not state

  test "a miss at depth 0 deepens once and finds the negation" do
    # The oracle wants the bit off. Depth 0 has the positive test, not
    # its negation. One deepening builds {:not, {:feat, :bit}}.
    score = fn
      {:not, {:feat, _}} -> 1
      _ -> 0
    end

    oracle = fn _pred, state -> not state end

    assert {:survivors, preds} =
             Synth.deepen(0, 0, score, oracle, &traj/1, &feats/1, &bit/2)

    assert Synth.pick(preds, score) == {:not, {:feat, :bit}}
  end

  test "a tag reading separates carriers that agree on the other features" do
    # hot and wide hold on both carriers. The tag does not. The
    # conjunction is consistent with the first carrier and dropped by
    # the second. The smallest remaining program is the negation of
    # the tag. The carriers are not a state of any environment.
    feat = fn
      "erased", :blue -> true
      "erased", :red -> false
      _feature, _state -> true
    end

    phase = {:and, {:feat, "hot"}, {:feat, "wide"}}
    vs = Synth.enumerate(["hot", "wide", "erased"], 1)
    assert phase in vs
    assert phase in Synth.refine(vs, {:red, true}, feat)
    kept = Synth.refine_all(vs, [{:red, true}, {:blue, false}], feat)
    refute phase in kept
    assert Synth.pick(kept, fn _ -> 0 end) == {:not, {:feat, "erased"}}
  end

  test "an observation of len drops the copy formula" do
    # uses > 1 and arg_apps ≠ 0. Both features hold at len, so the
    # formula predicts true. The observation says false.
    pred = {:and, {:feat, "uses-gt1"}, {:feat, "arg-apps-ne0"}}

    feat = fn
      _feature, state when state in [:len, :copy] -> true
      _feature, _state -> false
    end

    vs = [pred | Synth.enumerate(["uses-gt1", "arg-apps-ne0"], 0)]
    kept = Synth.refine(vs, {:len, false}, feat)
    refute pred in kept
    assert length(kept) < length(vs)
  end

  test "a failed refl names the obligation" do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_cex_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.mkdir_p!(dir)
    path = Path.join(dir, "bad.muro")

    File.write!(path, """
    data Bool : Type where
      true : Bool
      false : Bool

    def hold-len : evidence {false ≡ true : Bool} := refl
    """)

    assert {:error, text} = Muro.check_file(path)
    cex = Muro.Synth.Book.cex_from(text, [%{name: "hold-len", carrier: "len", oracle: true}])
    assert cex.carrier == "len"
    assert cex.predicted == false
    assert cex.oracle == true
  end

  test "sized enumeration keeps the smallest program of a signature" do
    features = ["a", "b", "c", "d"]
    states = [:s0, :s1, :s2, :s3, :s4, :s5]

    # s0 is only a, s1 only b, s2 only c, s3 only d, s4 none, s5 is a and b.
    # a ∨ ¬(b ∨ c ∨ d) holds at s0, s4, and s5. ¬(b ∨ c ∨ d) misses s5.
    feat = fn
      "a", state when state in [:s0, :s5] -> true
      "b", state when state in [:s1, :s5] -> true
      "c", :s2 -> true
      "d", :s3 -> true
      _feature, _state -> false
    end

    {:ok, index, meta} =
      Synth.enumerate_sized(
        features,
        Synth.pred_size_bound(),
        &Synth.signature(&1, states, feat),
        6
      )

    assert meta.truncated == false
    assert meta.considered > meta.distinct
    assert meta.enum_ms >= 0

    any = {:or, {:or, {:feat, "b"}, {:feat, "c"}}, {:feat, "d"}}
    target = {:or, {:feat, "a"}, {:not, any}}
    sig = Synth.signature(target, states, feat)
    assert Synth.pack_bits([true, false, false, false, true, true]) == sig

    assert {prog, 8, _ord} = Map.fetch!(index, sig)
    assert prog == target

    assert Synth.render(prog) ==
             "(orp (feat a) (notp (orp (orp (feat b) (feat c)) (feat d))))"

    assert Synth.signature(prog, states, feat) == sig

    smaller = {:not, any}
    assert {^smaller, 6, _ord} = Map.fetch!(index, Synth.signature(smaller, states, feat))
    assert {true, 1, _ord} = Map.fetch!(index, Synth.signature(true, states, feat))
  end

  test "self reads one column and other reads the rest" do
    feat = fn
      "fa", :s -> true
      "fb", :s -> false
      _, _ -> false
    end

    assert Synth.eval({:self, "reaches-pos", "a", "fa"}, feat, :s)
    refute Synth.eval({:self, "reaches-pos", "a", nil}, feat, :s)
    assert Synth.eval({:other, "reaches-pos", "a", ["fb", "fa"]}, feat, :s)
    refute Synth.eval({:other, "reaches-pos", "a", ["fb"]}, feat, :s)
    assert Synth.size({:self, "reaches-pos", "a", "fa"}) == 1
    assert Synth.size({:other, "reaches-pos", "a", ["fb", "fa"]}) == 1
    assert Synth.size({:or, {:feat, "fa"}, {:not, {:other, "reaches-pos", "a", ["fb"]}}}) == 4

    assert Synth.render({:self, "reaches-pos", "a", "fa"}) == "(selfp reaches-pos a)"

    assert Synth.render({:or, {:feat, "fa"}, {:not, {:other, "reaches-pos", "a", ["fb"]}}}) ==
             "(orp (feat fa) (notp (otherp reaches-pos a)))"
  end

  test "an action family groups the columns that survived" do
    specs = [
      %{name: "reaches-pos-a", kind: :reaches_pos, action: "a"},
      %{name: "reaches-pos-b", kind: :reaches_pos, action: "b"},
      %{name: "has-pos-reward-a", kind: :has_pos_reward, action: "a"},
      %{name: "len-is-0", kind: :len_is, action: nil}
    ]

    [reward, reach] = Muro.Synth.Feature.families(specs, ["b", "a"])
    assert reward.stem == "has-pos-reward"
    assert reward.actions == ["a"]
    assert reach.stem == "reaches-pos"
    assert reach.actions == ["b", "a"]
    assert reach.by_action["b"] == "reaches-pos-b"
  end

  test "sized enumeration finds the action quantifier by size 4" do
    features = ["reaches-pos-a", "reaches-pos-b", "reaches-pos-c", "reaches-pos-d"]
    states = [:none, :only_b, :only_a, :a_and_b, :only_c]

    feat = fn
      "reaches-pos-a", state when state in [:only_a, :a_and_b] -> true
      "reaches-pos-b", state when state in [:only_b, :a_and_b] -> true
      "reaches-pos-c", :only_c -> true
      _, _ -> false
    end

    family = %{
      stem: "reaches-pos",
      kind: :reaches_pos,
      actions: ["a", "b", "c", "d"],
      by_action: %{
        "a" => "reaches-pos-a",
        "b" => "reaches-pos-b",
        "c" => "reaches-pos-c",
        "d" => "reaches-pos-d"
      }
    }

    target =
      {:or, {:feat, "reaches-pos-a"},
       {:not, {:other, "reaches-pos", "a", ["reaches-pos-b", "reaches-pos-c", "reaches-pos-d"]}}}

    sig = Synth.signature(target, states, feat)
    assert Synth.pack_bits([true, false, true, true, false]) == sig
    assert Synth.size(target) == 4

    {:ok, plain, _} =
      Synth.enumerate_sized(features, 4, &Synth.signature(&1, states, feat), 5)

    refute Map.has_key?(plain, sig)

    {:ok, index, meta} =
      Synth.enumerate_sized(
        features,
        4,
        &Synth.signature(&1, states, feat),
        5,
        MapSet.new([sig]),
        families: [family]
      )

    assert {prog, 4, _ord} = Map.fetch!(index, sig)
    assert prog == target
    assert Synth.eval(prog, feat, :none)
    refute Synth.eval(prog, feat, :only_b)
    assert Synth.eval(prog, feat, :only_a)
    assert Synth.eval(prog, feat, :a_and_b)
    refute Synth.eval(prog, feat, :only_c)
    assert [[1, _], [2, _], [3, _], [4, _]] = meta.sizes
  end

  test "the checker reduces self and other" do
    assert Muro.check_file("test/fixtures/synth_quant.muro") == :ok
  end

  test "a family column that is not a feat atom still gets a signature" do
    family = %{
      stem: "reaches-pos",
      kind: :reaches_pos,
      actions: ["a", "b"],
      by_action: %{"a" => "reaches-pos-a", "b" => "reaches-pos-b"}
    }

    feat = fn _, state -> state == :on end
    states = [:on, :off]

    # `reaches-pos-b` is not a search atom, but the family still reads
    # it, so the walk signs the column instead of refusing or dropping it.
    {:ok, index, _meta} =
      Synth.enumerate_sized(
        ["reaches-pos-a"],
        2,
        &Synth.signature(&1, states, feat),
        2,
        nil,
        families: [family]
      )

    other_b = {:other, "reaches-pos", "b", ["reaches-pos-a"]}
    assert {kept, 1, _} = Map.fetch!(index, Synth.signature(other_b, states, feat))
    assert Synth.signature(kept, states, feat) == Synth.signature(other_b, states, feat)

    listed = %{family | by_action: %{"a" => "reaches-pos-a"}}

    assert_raise ArgumentError, ~r/reaches-pos lists b with no column/, fn ->
      Synth.enumerate_sized(
        ["reaches-pos-a", "reaches-pos-b"],
        2,
        &Synth.signature(&1, [:on, :off], feat),
        2,
        nil,
        families: [listed]
      )
    end
  end

  test "the policy term for other tests the columns in order" do
    pred = {:other, "reaches-pos", "a", ["fb", "fc"]}
    text = Synth.policy([{pred, :go}], :stay, & &1)
    assert :binary.match(text, "fb") < :binary.match(text, "fc")
  end

  test "one action: other has no column and is false" do
    path = "test/fixtures/synth_quant_one.muro"
    assert {:ok, host} = Muro.Synth.Host.open(path)
    assert [family] = Muro.Synth.Feature.families(host.feature_specs, host.actions)
    assert family.actions == ["go"]
    column = Map.fetch!(family.by_action, "go")
    feat = fn feature, state -> host.eval_feature.(feature, state) end
    states = host.all_states

    self = {:self, family.stem, "go", column}
    other = {:other, family.stem, "go", []}
    preds = [self, other, {:not, other}, {:or, self, other}, {:and, self, {:not, other}}]

    assert Synth.size(other) == 1
    assert Synth.render(other) == "(otherp #{family.stem} go)"
    for state <- states, do: refute(Synth.eval(other, feat, state))
    assert Enum.any?(states, &Synth.eval(self, feat, &1))
    assert Enum.any?(states, &(not Synth.eval(self, feat, &1)))

    {:ok, index, _meta} =
      Synth.enumerate_sized(
        host.features,
        2,
        &Synth.signature(&1, states, feat),
        length(states),
        nil,
        families: [family]
      )

    assert {false, 1, _} = Map.fetch!(index, Synth.signature(other, states, feat))

    {_dir, text} = book = quant_book(host, [self])
    assert text =~ "| go => false"
    assert_book_agrees(book, host, family_list(host), preds, feat)
  end

  test "the generated book agrees with Synth.eval on stem-at, other-at, and eval" do
    path = "test/fixtures/synth_quant_env.muro"
    assert {:ok, host} = Muro.Synth.Host.open(path)
    [family] = families = family_list(host)
    assert family.actions == ["up", "left", "right"]
    feat = fn feature, state -> host.eval_feature.(feature, state) end
    col = family.by_action
    self = fn a -> {:self, family.stem, a, col[a]} end
    other = fn a -> {:other, family.stem, a, for(x <- family.actions, x != a, do: col[x])} end

    preds =
      Enum.flat_map(family.actions, fn a ->
        [self.(a), other.(a), {:or, self.(a), {:not, other.(a)}}, {:and, other.(a), self.(a)}]
      end)

    # The survivor names only `up`. `stem-at` still reads `left` and
    # `right` from their columns, not as missing columns.
    {_dir, text} = book = quant_book(host, [self.("up")])
    assert text =~ "| left => eval-feature #{col["left"]} car"
    assert text =~ "| right => eval-feature #{col["right"]} car"
    assert_book_agrees(book, host, families, preds, feat)
  end

  test "a duplicate stem column stays in the family and otherp reads it" do
    path = "test/fixtures/synth_quant_dup.muro"
    assert {:ok, host} = Muro.Synth.Host.open(path)
    families = family_list(host)
    family = Enum.find(families, &(&1.stem == "has-pos-reward"))
    assert family
    assert family.actions == ["up", "left", "right"]
    col = family.by_action
    feat = fn feature, state -> host.eval_feature.(feature, state) end
    states = host.all_states

    up_bits = Enum.map(states, &feat.(col["up"], &1))
    left_bits = Enum.map(states, &feat.(col["left"], &1))
    right_bits = Enum.map(states, &feat.(col["right"], &1))
    assert up_bits == left_bits
    assert up_bits != right_bits
    assert "has-pos-reward-up" in host.features
    refute "has-pos-reward-left" in host.features

    self_left = {:self, family.stem, "left", col["left"]}
    self_up = {:self, family.stem, "up", col["up"]}
    other_up = {:other, family.stem, "up", for(x <- family.actions, x != "up", do: col[x])}
    other_left = {:other, family.stem, "left", for(x <- family.actions, x != "left", do: col[x])}

    other_right =
      {:other, family.stem, "right", for(x <- family.actions, x != "right", do: col[x])}

    assert Enum.map(states, &Synth.eval(self_left, feat, &1)) == left_bits
    assert Enum.map(states, &Synth.eval(self_up, feat, &1)) == up_bits

    # `otherp` at `up` includes `left`. The two columns agree, so that
    # reading is true wherever `up` itself is true, and also wherever
    # `right` is true.
    other_up_bits = Enum.map(states, &Synth.eval(other_up, feat, &1))
    other_left_bits = Enum.map(states, &Synth.eval(other_left, feat, &1))
    expected_other_up = Enum.zip(left_bits, right_bits) |> Enum.map(fn {l, r} -> l or r end)
    expected_other_left = Enum.zip(up_bits, right_bits) |> Enum.map(fn {u, r} -> u or r end)
    assert other_up_bits == expected_other_up
    assert other_left_bits == expected_other_left
    assert Enum.any?(states, &Synth.eval(other_up, feat, &1))

    assert Enum.map(states, &Synth.eval(other_right, feat, &1)) ==
             Enum.zip(up_bits, left_bits) |> Enum.map(fn {u, l} -> u or l end)

    {:ok, index, _meta} =
      Synth.enumerate_sized(
        host.features,
        2,
        &Synth.signature(&1, states, feat),
        length(states),
        nil,
        families: [family]
      )

    # `selfp left` has the same signature as the earlier `feat` atom.
    # `otherp up` is the first size-1 program that is the disjunction of
    # `left` and `right`.
    self_sig = Synth.signature(self_left, states, feat)
    assert self_sig == Synth.signature({:feat, col["up"]}, states, feat)
    assert {kept_self, 1, _} = Map.fetch!(index, self_sig)
    assert Synth.signature(kept_self, states, feat) == self_sig

    other_sig = Synth.signature(other_up, states, feat)
    assert {kept_other, 1, _} = Map.fetch!(index, other_sig)
    assert kept_other == other_up

    preds = [self_up, self_left, other_up, other_left, other_right]
    {_dir, text} = book = quant_book(host, [self_left, other_up])
    assert text =~ "| left => eval-feature #{col["left"]} car"
    assert text =~ "| up => eval-feature #{col["up"]} car"
    refute text =~ "| left => false"
    assert_book_agrees(book, host, families, preds, feat)
  end

  test "a duplicate-column environment certifies the deployed PredProg" do
    path = "test/fixtures/synth_dup_cert.muro"
    assert {:ok, host} = Muro.Synth.Host.open(path)
    family = Enum.find(family_list(host), &(&1.stem == "has-pos-reward"))
    assert family
    assert "go" in family.actions
    assert "copy" in family.actions
    feat = fn feature, state -> host.eval_feature.(feature, state) end
    states = host.all_states
    col = family.by_action

    assert Enum.map(states, &feat.(col["go"], &1)) ==
             Enum.map(states, &feat.(col["copy"], &1))

    refute "has-pos-reward-copy" in host.features

    self_copy = {:self, family.stem, "copy", col["copy"]}
    other_go = {:other, family.stem, "go", for(x <- family.actions, x != "go", do: col[x])}
    {_dir, text} = book = quant_book(host, [self_copy, other_go])
    assert text =~ "| copy => eval-feature #{col["copy"]} car"
    refute text =~ "| copy => false"
    assert_book_agrees(book, host, [family], [self_copy, other_go], feat)

    assert {:ok, result} = Muro.Synth.cegis_loop(path, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.book =~ "def survivor"
    assert result.book =~ "run PredProg"
    assert result.book =~ "def policy "
    assert result.book =~ "match eval survivor"
    refute result.book =~ "find-policy"
    refute result.book =~ "find-ranking"
    refute result.book =~ "placed-find-policy"
  end

  defp family_list(host), do: Muro.Synth.Feature.families(host.feature_specs, host.actions)

  # The policy book up to `policy`, as `Muro.Synth.Book.render/4` wrote
  # it. The certificate after it ranks these arms and is not the subject.
  defp quant_book(host, preds) do
    arms =
      preds
      |> Enum.with_index()
      |> Enum.map(fn {pred, i} ->
        %{
          name: "survivor-#{i}",
          pred: pred,
          action: hd(host.actions),
          else: hd(host.actions),
          observations: []
        }
      end)

    dir = tmp_quant_dir()
    assert {:ok, src, _meta} = Muro.Synth.Book.render(host, arms, dir, "trace")
    [head, _rest] = String.split(src, "\ndef policy ", parts: 2)
    assert head =~ "def stem-at "
    assert head =~ "def other-at "
    assert head =~ "data Stem : Type where"
    {dir, head}
  end

  defp assert_book_agrees({dir, head}, host, families, preds, feat) do
    stems =
      for family <- families, action <- host.actions, state <- host.all_states do
        expected = action in family.actions and feat.(family.by_action[action], state)
        others = for a <- family.actions, a != action, do: family.by_action[a]
        other_expected = Enum.any?(others, &feat.(&1, state))

        [
          "{stem-at #{family.stem} #{action} #{state} ≡ #{expected} : Bool}",
          "{other-at #{family.stem} #{action} #{state} ≡ #{other_expected} : Bool}"
        ]
      end

    evals =
      for pred <- preds, state <- host.all_states do
        "{eval #{Synth.render(pred)} #{state} ≡ #{Synth.eval(pred, feat, state)} : Bool}"
      end

    claims =
      (List.flatten(stems) ++ evals)
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {claim, i} -> "def agree-#{i} : evidence #{claim} := refl" end)

    path = Path.join(dir, "agree.muro")
    File.write!(path, head <> "\n" <> claims <> "\n")
    assert Muro.check_file(path) == :ok
  end

  defp tmp_quant_dir do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_quant_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.rm_rf!(dir)
    File.mkdir_p!(dir)
    dir
  end

  test "the subset budget covers a nine-feature subset of thirty-six features" do
    # Size 18 asks for a subset of nine. C(36, 9) is 94143280.
    # C(40, 8) is 76904685. Both are built. C(40, 9) stays above the budget.
    assert Synth.pred_size_bound() == 18
    assert Synth.subset_budget() >= 94_143_280
    assert Synth.subset_budget() >= 76_904_685
  end

  test "the predicate evaluator is part of the compiler and does not import Bool" do
    src = Muro.Synth.Book.evaluator()
    assert src =~ "data PredProg"
    assert src =~ "def eval "
    refute src =~ "import"
    refute src =~ "def leb"
  end

  test "an obligation name is matched whole, and a missing bit stays unknown" do
    obs = [
      %{name: "hold-copy", carrier: "copy", oracle: true, pair: {"arg", "spine"}},
      %{name: "hold-copy4", carrier: "copy4", oracle: false, pair: {"arg", "spine"}}
    ]

    named =
      Muro.Synth.Book.cex_from("book.muro:1:1: hold-copy4 body: cannot convert true ≁ false", obs)

    assert named.carrier == "copy4"
    assert named.name == "hold-copy4"
    assert named.predicted == true
    assert named.oracle == false

    fuel =
      Muro.Synth.Book.cex_from(
        "book.muro:4:1: hold-len body: out of fuel (the checker gave up reducing; raise the fuel)",
        [%{name: "hold-len", carrier: "len", oracle: true}]
      )

    assert fuel.carrier == "len"
    assert fuel.oracle == true
    assert fuel.predicted == nil
  end

  test "an unordered reward pair is not a trace ranking" do
    step = fn
      "s", "a" -> {"s", :p}
      "s", "b" -> {"s", :q}
    end

    silent = observe(step, fn left, right -> left == right end)
    assert {:silent, cex} = silent
    assert cex.carrier == "s"
    assert cex.pair == {"a", "b"}
    assert cex.reason =~ "incomparable"

    ordered =
      observe(step, fn
        :q, :p -> true
        :p, :q -> false
        left, right -> left == right
      end)

    assert {:ok, %{tasks: [%{observations: [{"s", true}]}]}} = ordered
  end

  test "incomparable losers are not labelled after a dominance loss" do
    step = fn
      "s", "top" -> {"s", :top}
      "s", "p" -> {"s", :p}
      "s", "q" -> {"s", :q}
    end

    leb = fn
      left, right when left == right -> true
      :p, :top -> true
      :q, :top -> true
      _, _ -> false
    end

    assert {:silent, cex} = observe3(step, leb)
    assert cex.carrier == "s"
    assert cex.pair == {"p", "q"}
    assert cex.reason =~ "incomparable"
  end

  test "a total order still labels an action that loses" do
    step = fn
      "s", "top" -> {"s", 3}
      "s", "p" -> {"s", 2}
      "s", "q" -> {"s", 1}
    end

    assert {:ok, %{tasks: tasks}} = observe3(step, fn left, right -> left <= right end)
    bits = Map.new(tasks, &{&1.action, &1.observations})
    assert bits["top"] == [{"s", true}]
    assert bits["p"] == [{"s", false}]
    assert bits["q"] == [{"s", false}]
  end

  test "an out-of-fuel obligation does not take another obligation's bit" do
    obs = [
      %{name: "hold-start", carrier: "start", oracle: true, pair: {"go", "stay"}},
      %{name: "hold-goal", carrier: "goal", oracle: false, pair: {"go", "stay"}}
    ]

    fuel_first = """
    book.muro:1:1: hold-start body: out of fuel (the checker gave up reducing; raise the fuel)

    book.muro:2:1: hold-goal body: cannot convert false ≁ true
    """

    first = Muro.Synth.Book.cex_from(fuel_first, obs)
    assert first.carrier == "start"
    assert first.name == "hold-start"
    assert first.oracle == true
    assert first.predicted == nil

    convert_first = """
    book.muro:2:1: hold-goal body: cannot convert false ≁ true

    book.muro:1:1: hold-start body: out of fuel (the checker gave up reducing; raise the fuel)
    """

    goal = Muro.Synth.Book.cex_from(convert_first, obs)
    assert goal.carrier == "goal"
    assert goal.name == "hold-goal"
    assert goal.predicted == false
    assert goal.oracle == false
  end

  test "concurrent checks in one anchor keep distinct books" do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_conc_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.mkdir_p!(dir)
    parent = self()

    run = fn source ->
      Task.async(fn ->
        Muro.Synth.Book.check(source, dir, fn path ->
          send(parent, {:path, path, File.read!(path)})
          Process.sleep(200)
          :ok
        end)
      end)
    end

    left = run.("alpha\n")
    right = run.("beta\n")

    seen =
      for _ <- 1..2 do
        assert_receive {:path, path, body}, 5_000
        {path, body}
      end

    assert :ok = Task.await(left)
    assert :ok = Task.await(right)
    paths = Enum.map(seen, &elem(&1, 0))
    assert length(Enum.uniq(paths)) == 2
    assert Enum.sort(Enum.map(seen, &elem(&1, 1))) == ["alpha\n", "beta\n"]
    assert Enum.all?(paths, &String.contains?(&1, System.pid()))
    refute Enum.any?(paths, &File.exists?/1)
  end

  test "a temporary name that already exists is not overwritten" do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_claim_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.mkdir_p!(dir)
    taken = Path.join(dir, "taken.muro")
    File.write!(taken, "keep\n")
    attempts = :counters.new(1, [:atomics])

    namer = fn _anchor ->
      :counters.add(attempts, 1, 1)

      if :counters.get(attempts, 1) == 1 do
        "taken.muro"
      else
        "free.muro"
      end
    end

    assert :ok =
             Muro.Synth.Book.check(
               "source\n",
               dir,
               fn path ->
                 assert Path.basename(path) == "free.muro"
                 assert File.read!(path) == "source\n"
                 :ok
               end,
               namer
             )

    assert File.read!(taken) == "keep\n"
    refute File.exists?(Path.join(dir, "free.muro"))
    assert :counters.get(attempts, 1) >= 2

    assert {:error, :storage, msg} =
             Muro.Synth.Book.check(
               "new\n",
               dir,
               fn _path -> flunk("checker ran") end,
               fn _anchor ->
                 "taken.muro"
               end
             )

    assert msg =~ "temporary"
    assert msg =~ ":eexist"
    assert File.read!(taken) == "keep\n"
  end

  test "a failed write of a temporary book is not checked and leaves no file" do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_write_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.mkdir_p!(dir)

    partial = fn io, data ->
      IO.binwrite(io, binary_part(data, 0, min(4, byte_size(data))))
      {:error, :eio}
    end

    assert {:error, :storage, msg} =
             Muro.Synth.Book.check(
               "source\n",
               dir,
               fn _path -> flunk("checker ran") end,
               fn _anchor -> "partial.muro" end,
               binwrite: partial
             )

    assert msg =~ ":eio"
    refute File.exists?(Path.join(dir, "partial.muro"))

    assert {:error, :storage, close_msg} =
             Muro.Synth.Book.check(
               "source\n",
               dir,
               fn _path -> flunk("checker ran") end,
               fn _anchor -> "partial.muro" end,
               close: fn io ->
                 File.close(io)
                 {:error, :eio}
               end
             )

    assert close_msg =~ ":eio"
    refute File.exists?(Path.join(dir, "partial.muro"))

    assert :ok =
             Muro.Synth.Book.check(
               "source\n",
               dir,
               fn path ->
                 assert File.read!(path) == "source\n"
                 :ok
               end,
               fn _anchor -> "partial.muro" end
             )

    refute File.exists?(Path.join(dir, "partial.muro"))
  end

  test "a reward that dominates the set is the maximum in either order" do
    leb = fn
      left, right when left == right -> true
      :p, :top -> true
      :q, :top -> true
      _, _ -> false
    end

    assert Muro.Synth.Oracle.maximum_reward(leb, [:p, :q, :top]) == :top
    assert Muro.Synth.Oracle.maximum_reward(leb, [:top, :p, :q]) == :top
    assert Muro.Synth.Oracle.maximum_reward(leb, [:q, :top, :p]) == :top

    none = fn left, right -> left == right end
    assert Muro.Synth.Oracle.maximum_reward(none, [:p, :q, :top]) == :unordered
    assert Muro.Synth.Oracle.maximum_reward(none, [:top, :p, :q]) == :unordered
    assert Muro.Synth.Oracle.maximum_reward(none, [:q, :p]) == :unordered
    assert Muro.Synth.Oracle.maximum_reward(none, [:p, :q]) == :unordered

    assert {:silent, left} = observe_values(["p", "q", "top"], none)
    assert {:silent, right} = observe_values(["top", "q", "p"], none)
    assert left.reason =~ "incomparable"
    assert right.reason =~ "incomparable"
    assert left.carrier == "s"
    assert right.carrier == "s"
  end

  test "successor does not rank a state whose rewards have no maximum" do
    step = fn
      "s", "a" -> {"both", :z}
      "s", "b" -> {"only", :z}
      "both", "a" -> {"both", :p}
      "both", "b" -> {"both", :q}
      "only", "a" -> {"only", :q}
      "only", "b" -> {"only", :q}
    end

    host = %{
      actions: ["a", "b"],
      default: "b",
      states: ["s", "both", "only"],
      all_states: ["s"],
      horizon: 1,
      step: step,
      leb: fn left, right -> left == right end
    }

    assert {:silent, successor} = Muro.Synth.Oracle.observe(host, "successor")
    assert successor.carrier == "s"
    assert successor.pair == {"a", "b"}
    assert successor.reason =~ "incomparable"

    assert {:silent, coind} = Muro.Synth.Oracle.observe(host, "coind-homo")
    assert coind.carrier == "s"
    assert coind.pair == {"a", "b"}
    assert coind.reason =~ "incomparable"
  end

  test "sibling actions reuse the solved memo" do
    count = :counters.new(1, [:atomics])

    host = %{
      actions: ["a", "b"],
      default: "b",
      states: ["s"],
      all_states: ["s"],
      horizon: 12,
      step: fn state, _action ->
        :counters.add(count, 1, 1)
        {state, 0}
      end,
      leb: fn left, right -> left <= right end
    }

    assert {:ok, _} = Muro.Synth.Oracle.observe(host, "successor")
    assert :counters.get(count, 1) < 500
  end

  defp observe_values(actions, leb) do
    host = %{
      actions: actions,
      default: List.last(actions),
      states: ["s"],
      all_states: ["s"],
      horizon: 0,
      step: fn state, action -> {state, String.to_atom(action)} end,
      leb: leb
    }

    Muro.Synth.Oracle.observe(host, "successor")
  end

  defp observe3(step, leb) do
    host = %{
      actions: ["top", "p", "q"],
      default: "q",
      states: ["s"],
      all_states: ["s"],
      horizon: 0,
      step: step,
      leb: leb
    }

    Muro.Synth.Oracle.observe(host, "trace")
  end

  defp observe(step, leb) do
    host = %{
      actions: ["a", "b"],
      default: "b",
      states: ["s"],
      all_states: ["s"],
      horizon: 0,
      step: step,
      leb: leb
    }

    Muro.Synth.Oracle.observe(host, "trace")
  end
end
