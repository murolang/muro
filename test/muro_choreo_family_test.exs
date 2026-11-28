defmodule Muro.ChoreoFamilyTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Parser}

  @moduletag timeout: 120_000

  @choreo """
  choreography plan
    roles registry shared, release shared, front, worker
    release -> registry : publish
    registry -> release : published
    release -> front : deploy
    front -> release : deployed
    release -> worker : deploy
    worker -> release : deployed
    release chooses
      keep: release -> front : keep
      undo: release -> front : undo
            release -> worker : undo
  """

  @rollout @choreo <>
             """

             family rollout : plan per key

             def kept : run Nat := 0
             """

  # No shared role: every key starts at once.
  @plain """
  choreography plan
    roles release, front, worker
    release -> front : deploy
    front -> release : deployed
    release -> worker : deploy
    worker -> release : deployed

  family rollout : plan per key

  def kept : run Nat := 0
  """

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
  """

  setup do
    on_exit(fn ->
      for {mod, _} <- :code.all_loaded(),
          String.starts_with?(Atom.to_string(mod), "Elixir.ChoreoFamT") do
        :code.purge(mod)
        :code.delete(mod)
      end
    end)

    :ok
  end

  describe "parsing" do
    test "shared marks a role, and a family of a choreography has no kind" do
      assert {:ok, book} = Parser.parse(@rollout)
      chor = Enum.find(book, &(&1[:kind] == :choreography))
      assert chor.roles == ["registry", "release", "front", "worker"]
      assert chor.shared == ["registry", "release"]

      fam = Enum.find(book, &(&1[:kind] == :family))
      assert %{name: "rollout", meeting: "plan", key: nil, rules: []} = fam
    end

    test "a choreography with no mark has no shared role" do
      assert {:ok, book} = Parser.parse(@plain)
      chor = Enum.find(book, &(&1[:kind] == :choreography))
      assert chor.shared == []
    end

    test "shared before an interaction is a role named shared" do
      src = """
      choreography p
        roles a, shared
        shared -> a : x
      """

      assert {:ok, [chor]} = Parser.parse(src)
      assert chor.roles == ["a", "shared"]
      assert chor.shared == []
      assert chor.body == {:comm, "shared", "a", "x", :unit, :end}
      assert check(src) == :ok
    end

    test "the last role may be shared, and the body follows" do
      src = """
      choreography p
        roles a, b shared
        a -> b : x
      """

      assert {:ok, [chor]} = Parser.parse(src)
      assert chor.shared == ["b"]
      assert chor.body == {:comm, "a", "b", "x", :unit, :end}
    end

    test "done k (interaction) is an atom, and done done stays a role atom" do
      src =
        @rollout <>
          """

          temporal t : rollout :=
            forall (k : key). always ((done k (release -> front : deploy Nat)) implies (done k (release chooses keep)))
          """

      assert {:ok, book} = Parser.parse(src)
      t = Enum.find(book, &(&1[:kind] == :temporal))

      assert t.formula ==
               {:forall, "k", {:dat, "key", []},
                {:always,
                 {:imp, {:did, "k", {:msg, "release", "front", "deploy", :nat}},
                  {:did, "k", {:pick, "release", "keep"}}}}}

      assert {:ok, [d]} = Parser.parse("temporal t : m := always (done done)\n")
      assert d.formula == {:always, {:done, "done"}}
    end
  end

  describe "checking" do
    test "the family checks and prints its line" do
      assert check(@rollout) == :ok
      assert "family rollout: plan per key" in Check.temporal_lines()
    end

    test "a choreography family with no shared role checks" do
      assert check(@plain) == :ok
      assert Check.temporal_lines() == ["family rollout: plan per key"]
    end

    test "per key of a kind over a choreography is refused" do
      src = """
      data Tenant : Type where
        t : Tenant

      choreography plan
        roles release, front, worker
        release -> front : deploy
        front -> release : deployed

      family rollout : plan per key of Tenant
        t never held
      """

      assert {:error, msg} = check(src)

      assert msg =~
               "rollout: plan is a choreography: a family of a choreography is per key, with no kind and no hold rules"

      refute msg =~ "unknown meeting"
    end

    test "an unknown choreography is refused" do
      assert {:error, msg} = check("family rollout : nope per key\n")
      assert msg =~ "rollout: unknown choreography nope"
    end

    test "a meeting with no kind is refused" do
      assert {:error, msg} = check(@slots <> "\nfamily slots : slot per key\n")

      assert msg =~
               "slots: slot is a meeting: a family of a meeting names its kind, per key of <Kind>"
    end

    test "a family of a meeting still checks" do
      src =
        @slots <>
          """

          family slots : slot per key of Event
            init never held
            signal held while earlier unresolved
          """

      assert check(src) == :ok
      assert Check.temporal_lines() == ["family slots: slot per key of Event"]
    end

    test "hold rules, may redeliver, and may revert are refused on a choreography family" do
      assert {:error, msg} = check(@choreo <> "\nfamily rollout : plan per key\n  t never held\n")
      assert msg =~ "rollout: a family of a choreography has no hold rules"

      assert {:error, msg} = check(@choreo <> "\nfamily rollout : plan per key may redeliver\n")
      assert msg =~ "rollout: may redeliver is a mark on a family of a meeting"

      assert {:error, msg} = check(@choreo <> "\nfamily rollout : plan per key may revert\n")
      assert msg =~ "rollout: may revert is a mark on a family of a meeting"
    end

    test "a choreography that does not check skips the family, with the #308 refusals" do
      src = """
      choreography plan
        roles front-end, front_end
        front-end -> front_end : go

      family rollout : plan per key
      """

      assert {:error, msg} = check(src)
      assert msg =~ "plan: roles front-end and front_end spell one Elixir atom"
      assert msg =~ "rollout: skipped because plan does not check"

      src = """
      choreography plan
        roles a, b
        a -> c : go

      family rollout : plan per key
      """

      assert {:error, msg} = check(src)
      assert msg =~ "plan: unknown role c"
      assert msg =~ "rollout: skipped because plan does not check"
    end

    test "a family whose every role is shared is refused" do
      src = """
      choreography plan
        roles a shared, b shared
        a -> b : go

      family rollout : plan per key
      """

      assert {:error, msg} = check(src)
      assert msg =~ "rollout: every role of plan is shared, so no step runs per key"
    end

    test "a message between shared roles after a per-key step is refused" do
      src = """
      choreography plan
        roles registry shared, release shared, front
        release -> front : deploy
        release -> registry : publish
      """

      assert {:error, msg} = check(src)

      assert msg =~
               "plan: release -> registry : publish is between shared roles after a per-key step; a message between shared roles belongs in the shared preamble"
    end

    test "a refused message in one branch is reported" do
      src = """
      choreography plan
        roles registry shared, release shared, front
        release chooses
          go: release -> front : deploy
              registry -> release : late
          stop: release -> registry : publish
      """

      # `release` is shared, so the choice is in the preamble. `stop` stays
      # in it. `go` steps a key first.
      assert {:error, msg} = check(src)
      assert msg =~ "registry -> release : late is between shared roles after a per-key step"
      refute msg =~ "publish is between"
    end

    test "a choice by a shared role after a per-key step is that key's choice" do
      assert check(@rollout) == :ok
    end

    test "a plain choreography marks a shared role and keeps its #308 checks and lines" do
      marked = """
      choreography plan
        roles release shared, front, worker
        release -> front : deploy
      """

      plain = String.replace(marked, "release shared,", "release,")

      assert check(plain) == :ok
      lines = Check.choreo_lines()
      assert check(marked) == :ok
      assert Check.choreo_lines() == lines
      assert "choreography plan: release with front = send Unit end" in lines
    end

    test "a contract does not name a choreography family" do
      src = @rollout <> "\ncontract rollout : in order\n"
      assert {:error, msg} = check(src)
      assert msg =~ "rollout ranges over a choreography: a contract names a family of a meeting"
    end
  end

  describe "temporal formulas" do
    test "a property that holds, on one key and the preamble" do
      src =
        @rollout <>
          """

          temporal front-first : rollout :=
            forall (k : key). always ((done k (release -> worker : deploy)) implies (done k (front -> release : deployed)))
          temporal published : rollout :=
            forall (k : key). always ((done k (release -> front : deploy)) implies (done k (registry -> release : published)))
          temporal decided : rollout :=
            forall (k : key). (done k (worker -> release : deployed)) leads_to ((done k (release chooses keep)) or (done k (release chooses undo)))
          temporal ends : rollout :=
            forall (k : key). eventually (done k (release -> front : keep)) or (done k (release -> front : undo))
          """

      assert check(src) == :ok
      lines = Check.temporal_lines()

      for name <- ~w(front-first published decided ends) do
        assert "temporal #{name}: holds in 12 reachable states, 13 transitions" in lines
      end
    end

    test "an always that fails names the path and the next interaction" do
      src =
        @rollout <>
          """

          temporal never-undo : rollout :=
            forall (k : key). always (not (done k (release chooses undo)))
          """

      assert {:error, msg} = check(src)

      assert msg =~
               "never-undo: always (not done k (release chooses undo)) fails in rollout after " <>
                 "release -> registry : publish (shared), registry -> release : published (shared), " <>
                 "release -> front : deploy, front -> release : deployed, release -> worker : deploy, " <>
                 "worker -> release : deployed, release chooses undo: next release -> front : undo"
    end

    test "the worker before the front is a counterexample" do
      src =
        @rollout <>
          """

          temporal worker-first : rollout :=
            forall (k : key). always ((done k (release -> front : deploy)) implies (done k (worker -> release : deployed)))
          """

      assert {:error, msg} = check(src)

      assert msg =~
               "worker-first: always ((done k (release -> front : deploy)) implies (done k (worker -> release : deployed))) " <>
                 "fails in rollout after release -> registry : publish (shared), registry -> release : published (shared), " <>
                 "release -> front : deploy: next front -> release : deployed"
    end

    test "eventually and leads_to fail on a run to an end" do
      src =
        @rollout <>
          """

          temporal always-undo : rollout :=
            forall (k : key). eventually (done k (release chooses undo))
          temporal undo-after : rollout :=
            forall (k : key). (done k (front -> release : deployed)) leads_to (done k (release -> worker : undo))
          """

      assert {:error, msg} = check(src)

      keep =
        "release -> registry : publish (shared), registry -> release : published (shared), " <>
          "release -> front : deploy, front -> release : deployed, release -> worker : deploy, " <>
          "worker -> release : deployed, release chooses keep, release -> front : keep"

      assert msg =~
               "always-undo: eventually (done k (release chooses undo)) fails in rollout after #{keep}; then forever: the key has finished: end"

      assert msg =~
               "undo-after: (done k (front -> release : deployed)) leads_to (done k (release -> worker : undo)) fails in rollout after #{keep}; then forever: the key has finished: end"
    end

    test "an always false fails at the start" do
      src = @plain <> "\ntemporal f : rollout :=\n  forall (k : key). always false\n"
      assert {:error, msg} = check(src)
      assert msg =~ "f: always (false) fails in rollout: next release -> front : deploy"
    end

    test "atoms and binders are checked" do
      cases = [
        {"forall (k : key). always (done k (release -> worker : publish))",
         "plan has no interaction release -> worker : publish"},
        {"forall (k : key). always (done k (release -> front : deploy Nat))",
         "plan has no interaction release -> front : deploy Nat"},
        {"forall (k : key). always (done k (front chooses keep))",
         "plan has no choice front chooses keep"},
        {"forall (k : key). always (done j (release -> front : deploy))", "unbound key j"},
        {"always (done k (release -> front : deploy))", "unbound key k"},
        {"forall (k : key). forall (j : key). always (done k (release -> front : deploy))",
         "a formula over a choreography family binds one key"},
        {"forall (c : Bit). always true", "forall over Bit is not a key"},
        {"forall (k : key). always (opened k init)",
         "a formula over a choreography family names done <key> (<interaction>)"},
        {"forall (k : key). always (release done)",
         "a formula over a choreography family names done <key> (<interaction>)"}
      ]

      for {formula, want} <- cases do
        src = @rollout <> "\ntemporal t : rollout :=\n  #{formula}\n"
        assert {:error, msg} = check(src), formula
        assert msg =~ "t: #{want}", formula
      end
    end

    test "done names an interaction, not a meeting step" do
      src =
        @slots <>
          """

          family slots : slot per key of Event
            init never held
            signal held while earlier unresolved

          temporal t : slots :=
            forall (k : key). always (done k (a -> b : x))
          temporal u : slot :=
            always (done k (a -> b : x))
          """

      assert {:error, msg} = check(src)

      assert msg =~
               "t: a family formula names opened, held, resolved, earlier_resolved, or some_resolved"

      assert msg =~ "u: done names an interaction of a choreography family"
    end

    test "a formula over a family that does not check is skipped" do
      src = """
      choreography plan
        roles a shared, b shared
        a -> b : go

      family rollout : plan per key

      temporal t : rollout :=
        forall (k : key). always true
      """

      assert {:error, msg} = check(src)
      assert msg =~ "t: skipped because rollout does not check"
    end

    test "the example book checks" do
      assert Muro.check_file("examples/release-rollout.muro") == :ok
    end
  end

  describe "the state machine" do
    test "the preamble is a barrier, then keys step independently" do
      {parent, _src} = emit_text!("rollout.muro", @rollout)
      r = Module.concat(parent, Rollout)

      s0 = r.init()
      refute r.shared_done?(s0)
      assert r.keys(s0) == []
      assert r.expected_shared(s0) == {:message, :release, :registry, :publish, :unit}
      assert r.expected(s0, "eu") == {:shared, {:message, :release, :registry, :publish, :unit}}
      refute r.done?(s0, "eu")

      assert r.step(s0, "eu", :release, :front, :deploy) ==
               {:error,
                {:key, "eu",
                 {:preamble,
                  "rollout.muro:1 choreography plan: first release -> registry : publish",
                  {:message, :release, :registry, :publish, :unit}, {:release, :front, :deploy}}}}

      assert r.step_shared(s0, :registry, :release, :published) ==
               {:error,
                {:unexpected,
                 "rollout.muro:1 choreography plan: first release -> registry : publish",
                 {:message, :release, :registry, :publish, :unit},
                 {:registry, :release, :published}}}

      assert {:ok, s1} = r.step_shared(s0, :release, :registry, :publish)
      assert {:ok, s2} = r.step_shared(s1, :registry, :release, :published, :tt)
      assert r.shared_done?(s2)
      assert r.expected_shared(s2) == :done

      assert r.step_shared(s2, :release, :registry, :publish) ==
               {:error,
                {:unexpected, "rollout.muro:1 choreography plan: third release -> front : deploy",
                 :done, {:release, :registry, :publish}}}

      # Every key starts where the preamble ended.
      assert r.expected(s2, "eu") == {:message, :release, :front, :deploy, :unit}
      assert r.expected(s2, "us") == {:message, :release, :front, :deploy, :unit}

      assert {:ok, s3} = r.step(s2, "eu", :release, :front, :deploy)
      assert {:ok, s3} = r.step(s3, "eu", :front, :release, :deployed)

      # `eu` is further along; `us` is still at its start.
      assert r.step(s3, "us", :release, :worker, :deploy) ==
               {:error,
                {:key, "us",
                 {:unexpected,
                  "rollout.muro:1 choreography plan: third release -> front : deploy",
                  {:message, :release, :front, :deploy, :unit}, {:release, :worker, :deploy}}}}

      assert {:ok, s4} = r.step(s3, "us", :release, :front, :deploy)
      assert r.keys(s4) == ["eu", "us"]
      assert r.expected(s4, "eu") == {:message, :release, :worker, :deploy, :unit}
      assert r.expected(s4, "us") == {:message, :front, :release, :deployed, :unit}

      assert {:ok, s5} = r.step(s4, "eu", :release, :worker, :deploy)
      assert {:ok, s5} = r.step(s5, "eu", :worker, :release, :deployed)
      assert r.expected(s5, "eu") == {:choose, :release, [:keep, :undo]}

      assert r.choose(s5, "eu", :release, :maybe) ==
               {:error,
                {:key, "eu",
                 {:unexpected, "rollout.muro:1 choreography plan: first release chooses",
                  {:choose, :release, [:keep, :undo]}, {:release, :maybe}}}}

      assert {:ok, s6} = r.choose(s5, "eu", :release, :undo)
      assert {:ok, s6} = r.step(s6, "eu", :release, :front, :undo)
      assert {:ok, s6} = r.step(s6, "eu", :release, :worker, :undo)
      assert r.done?(s6, "eu")
      refute r.done?(s6, "us")
      assert r.expected(s6, "eu") == :done

      assert r.step(s6, "eu", :release, :front, :deploy) ==
               {:error,
                {:key, "eu",
                 {:unexpected, "rollout.muro:1 choreography plan: end", :done,
                  {:release, :front, :deploy}}}}

      # The same events give the same state, in any order across keys.
      assert {:ok, a} = r.step(s2, "eu", :release, :front, :deploy)
      assert {:ok, a} = r.step(a, "us", :release, :front, :deploy)
      assert {:ok, b} = r.step(s2, "us", :release, :front, :deploy)
      assert {:ok, b} = r.step(b, "eu", :release, :front, :deploy)
      assert a == b
    end

    test "check_trace replays the preamble and several keys" do
      {parent, _src} = emit_text!("rollout.muro", @rollout)
      r = Module.concat(parent, Rollout)

      pre = [
        {:shared, {:release, :registry, :publish}},
        {:shared, {:registry, :release, :published}}
      ]

      site = fn key, arm ->
        [
          {:key, key, {:release, :front, :deploy}},
          {:key, key, {:front, :release, :deployed}},
          {:key, key, {:release, :worker, :deploy}},
          {:key, key, {:worker, :release, :deployed}},
          {:key, key, {:release, arm}}
        ] ++
          if arm == :keep,
            do: [{:key, key, {:release, :front, :keep}}],
            else: [
              {:key, key, {:release, :front, :undo}},
              {:key, key, {:release, :worker, :undo}}
            ]
      end

      eu = site.(:eu, :keep)
      us = site.(:us, :undo)
      mixed = Enum.zip(eu, us) |> Enum.flat_map(fn {a, b} -> [a, b] end)
      mixed = mixed ++ Enum.drop(us, length(eu))

      assert r.check_trace([]) == :ok

      assert r.check_trace([], complete: true) ==
               {:error,
                {0,
                 {:incomplete, :shared,
                  "rollout.muro:1 choreography plan: first release -> registry : publish",
                  {:message, :release, :registry, :publish, :unit}}}}

      assert r.check_trace(pre, complete: true) == :ok
      assert r.check_trace(pre ++ eu ++ us, complete: true) == :ok
      assert r.check_trace(pre ++ mixed, complete: true) == :ok

      assert r.check_trace(pre ++ Enum.take(eu, 2) ++ us, complete: true) ==
               {:error,
                {2 + 2 + length(us),
                 {:incomplete, {:key, :eu},
                  "rollout.muro:1 choreography plan: 5th release -> worker : deploy",
                  {:message, :release, :worker, :deploy, :unit}}}}

      first = "rollout.muro:1 choreography plan: first release -> registry : publish"
      publish = {:message, :release, :registry, :publish, :unit}

      assert r.check_trace(eu) ==
               {:error,
                {0, {:key, :eu, {:preamble, first, publish, {:release, :front, :deploy}}}}}

      assert {:error, {3, {:key, :eu, {:unexpected, _, _, {:release, :worker, :deploy}}}}} =
               r.check_trace(pre ++ [hd(eu), {:key, :eu, {:release, :worker, :deploy}}])

      assert r.check_trace(:nope) == {:error, {:trace, :nope}}
      assert r.check_trace(:nope, complete: true) == {:error, {:trace, :nope}}
      assert r.check_trace([:bogus]) == {:error, {0, {:event, :bogus}}}
      assert r.check_trace([{:shared, :bogus}]) |> elem(0) == :error
      assert r.check_trace([{:key, :eu}]) == {:error, {0, {:event, {:key, :eu}}}}
    end

    test "a bad state never raises" do
      {parent, _src} = emit_text!("rollout.muro", @rollout)
      r = Module.concat(parent, Rollout)

      end_step = "rollout.muro:1 choreography plan: end"
      good = r.init()

      for bad <- [
            nil,
            :junk,
            %{},
            Map.put(good, :x, 1),
            %{good | s: :nope},
            %{good | k: []},
            %{good | f: "other"}
          ] do
        assert r.step_shared(bad, :release, :registry, :publish) ==
                 {:error, {:unexpected, end_step, :done, {:release, :registry, :publish}}}

        assert r.step(bad, :eu, :release, :front, :deploy) ==
                 {:error,
                  {:key, :eu, {:unexpected, end_step, :done, {:release, :front, :deploy}}}}

        assert {:error, {:key, :eu, _}} = r.choose(bad, :eu, :release, :keep)
        assert r.expected_shared(bad) == :done
        assert r.expected(bad, :eu) == :done
        refute r.done?(bad, :eu)
        assert r.keys(bad) == []
      end

      # A key whose position is not a node is a bad state for that key.
      {:ok, s} = r.step_shared(good, :release, :registry, :publish)
      {:ok, s} = r.step_shared(s, :registry, :release, :published)
      broken = %{s | k: %{eu: :nope}}

      assert {:error, {:key, :eu, {:unexpected, ^end_step, :done, _}}} =
               r.step(broken, :eu, :release, :front, :deploy)

      assert r.expected(broken, :eu) == :done
      assert r.expected(broken, :us) == {:message, :release, :front, :deploy, :unit}
    end

    test "with no shared role the preamble is already done" do
      {parent, src} = emit_text!("plain.muro", @plain)
      r = Module.concat(parent, Rollout)
      plan = Module.concat(parent, Plan)

      s = r.init()
      assert r.shared_done?(s)
      assert r.expected_shared(s) == :done
      assert {:ok, s} = r.step(s, 1, :release, :front, :deploy)
      assert {:ok, s} = r.step(s, 2, :release, :front, :deploy, :tt)
      assert r.keys(s) == [1, 2]

      assert r.step_shared(s, :release, :front, :deploy) ==
               {:error,
                {:unexpected, "plain.muro:1 choreography plan: first release -> front : deploy",
                 :done, {:release, :front, :deploy}}}

      # The #308 monitor of the choreography is still there.
      assert src =~ "defmodule Plan do"
      assert {:ok, _} = plan.step(plan.init(), :release, :front, :deploy)
    end

    test "a preamble that chooses keeps each arm's own start" do
      src = """
      choreography plan
        roles registry shared, release shared, site
        release chooses
          fresh: release -> registry : publish
                 release -> site : deploy
          cached: release -> site : deploy

      family rollout : plan per key

      def kept : run Nat := 0
      """

      {parent, _src} = emit_text!("arms.muro", src)
      r = Module.concat(parent, Rollout)

      s = r.init()
      assert r.expected_shared(s) == {:choose, :release, [:fresh, :cached]}
      assert {:error, {:key, :a, {:preamble, _, _, _}}} = r.step(s, :a, :release, :site, :deploy)

      assert {:ok, cached} = r.choose_shared(s, :release, :cached)
      assert r.shared_done?(cached)
      assert {:ok, _} = r.step(cached, :a, :release, :site, :deploy)

      assert {:ok, fresh} = r.choose_shared(s, :release, :fresh)
      refute r.shared_done?(fresh)
      assert {:ok, fresh} = r.step_shared(fresh, :release, :registry, :publish)
      assert r.shared_done?(fresh)
      assert {:ok, fresh} = r.step(fresh, :a, :release, :site, :deploy)
      assert r.done?(fresh, :a)
    end

    test "a payload is checked per key" do
      src = """
      choreography plan
        roles hub shared, site
        hub -> site : config Nat
        site -> hub : ack

      family rollout : plan per key

      def kept : run Nat := 0
      """

      {parent, _src} = emit_text!("pay.muro", src)
      r = Module.concat(parent, Rollout)

      s = r.init()
      assert r.expected(s, :a) == {:message, :hub, :site, :config, :nat}

      assert {:error, {:key, :a, {:unexpected, _, _, {:hub, :site, :config}}}} =
               r.step(s, :a, :hub, :site, :config)

      assert {:error, {:key, :a, {:unexpected, _, _, {:hub, :site, :config, -1}}}} =
               r.step(s, :a, :hub, :site, :config, -1)

      assert {:ok, s} = r.step(s, :a, :hub, :site, :config, 3)
      assert {:ok, s} = r.step(s, :a, :site, :hub, :ack)
      assert r.done?(s, :a)
    end

    test "the example book emits its dispatcher" do
      assert {:ok, src} = Muro.emit_fsm("examples/release-rollout.muro", ChoreoFamTExample)
      assert src =~ "defmodule Rollout do"
      assert src =~ "defmodule Plan do"
      compile!(src)
      r = Module.concat(ChoreoFamTExample, Rollout)
      state = r.init()
      assert r.expected_shared(state) == {:message, :release, :registry, :publish, :unit}

      # The example in manual/fsm.md.
      assert r.step(state, "eu", :release, :front, :deploy) ==
               {:error,
                {:key, "eu",
                 {:preamble,
                  "examples/release-rollout.muro:13 choreography plan: first release -> registry : publish",
                  {:message, :release, :registry, :publish, :unit}, {:release, :front, :deploy}}}}

      assert {:ok, state} = r.step_shared(state, :release, :registry, :publish)
      assert {:ok, state} = r.step_shared(state, :registry, :release, :published)
      assert r.shared_done?(state)
      assert {:ok, state} = r.step(state, "eu", :release, :front, :deploy)
      assert {:ok, state} = r.step(state, "us", :release, :front, :deploy)
      assert r.keys(state) == ["eu", "us"]
    end

    test "the outline names the dispatcher" do
      {:ok, book} = Muro.Load.file("examples/release-rollout.muro")
      assert {:ok, outline} = Muro.Emit.outline(:fsm, book, "examples/release-rollout.muro")
      clauses = outline.clauses
      assert "defmodule Rollout do" in clauses
      assert "def step(state, key, from, to, label)" in clauses
      assert "def step_shared(state, from, to, label)" in clauses
      assert "def choose(state, key, role, label)" in clauses
    end

    test "shared marks do not move the #308 monitor, and a book with no choreography family emits no dispatcher" do
      marked = """
      choreography plan
        roles release shared, front, worker
        release -> front : deploy
        front -> release : deployed

      def kept : run Nat := 0
      """

      plain = String.replace(marked, "release shared,", "release,")

      {:ok, a} = Muro.emit_fsm(write_text("plan.muro", marked), ChoreoFamTSame, book: "plan.muro")
      {:ok, b} = Muro.emit_fsm(write_text("plan.muro", plain), ChoreoFamTSame, book: "plan.muro")
      assert a == b
      refute a =~ "muro_fsm_cf_"
      refute a =~ "step_shared"

      {:ok, rp} = Muro.emit_fsm("examples/release-plan.muro", ChoreoFamTRp)
      refute rp =~ "muro_fsm_cf_"
    end
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp emit_text!(name, text) do
    path = write_text(name, text)
    assert Muro.check_file(path) == :ok
    parent = Module.concat(["ChoreoFamT#{System.unique_integer([:positive])}"])
    {:ok, src} = Muro.emit_fsm(path, parent, book: name)
    compile!(src)
    {parent, src}
  end

  defp write_text(name, text) do
    dir = Path.join(System.tmp_dir!(), "muro_choreo_family_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    path = Path.join(dir, name)
    File.write!(path, text)
    path
  end

  defp compile!(src) do
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(src) end)
    warnings = Enum.filter(diags, &(&1.severity == :warning))
    assert warnings == [], inspect(warnings, limit: 30)
    mods
  end
end
