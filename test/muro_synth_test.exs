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
      Path.join(System.tmp_dir!(), "muro_synth_policy_#{System.unique_integer([:positive])}.muro")

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
      Path.join(System.tmp_dir!(), "muro_synth_neg_#{System.unique_integer([:positive])}.muro")

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
    dir = Path.join(System.tmp_dir!(), "muro_synth_cex_#{System.unique_integer([:positive])}")
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
    dir = Path.join(System.tmp_dir!(), "muro_synth_conc_#{System.unique_integer([:positive])}")
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
    dir = Path.join(System.tmp_dir!(), "muro_synth_claim_#{System.unique_integer([:positive])}")
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
    dir = Path.join(System.tmp_dir!(), "muro_synth_write_#{System.unique_integer([:positive])}")
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
