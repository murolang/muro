defmodule Muro.FamilyNamedTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Parser}
  alias Muro.Family.{Graph, Step}

  @moduletag timeout: 180_000

  @release "examples/keyed-release.muro"

  @dag %{
    front: :never,
    schema: :never,
    worker: {:named, %{while: [], until: [:front, :schema]}},
    cleanup: {:named, %{while: [], until: [:worker]}}
  }

  @meet """
  data Report : Type where
    ok : Report
  session task-work := send Report end
  session server-wait := recv Report end
  conform task : task-work := put ok done
  conform server : server-wait :=
    get (r : Report) done
  meet slot : server with task buffer 1
  """

  test "keyed-release proves the release order, and front can be open with schema" do
    assert Muro.check_file(@release) == :ok

    assert Check.temporal_lines() == [
             "family rollout: slot per key of Step",
             "temporal front-before-worker: holds in 8906 reachable states, 26423 transitions",
             "temporal schema-before-worker: holds in 8906 reachable states, 26423 transitions",
             "temporal worker-before-cleanup: holds in 8906 reachable states, 26423 transitions"
           ]

    assert {:ok, book} = Parser.parse(File.read!(@release))
    family = Enum.find(book, &(&1.kind == :family))
    assert {:ok, search} = Graph.prepare(book, family)
    assert length(search.states) == 8906
    assert search.transitions == 26423

    # `some_resolved` does not double the script: one of each kind on `a`,
    # and one `front` on `b`.
    assert length(search.g.instances) == 5
    front = Enum.find_index(search.g.instances, &(&1.key == "a" and &1.kind == "front"))
    schema = Enum.find_index(search.g.instances, &(&1.key == "a" and &1.kind == "schema"))

    assert Enum.any?(search.states, fn state ->
             match?({:run, _, _, _}, elem(state, front)) and
               match?({:run, _, _, _}, elem(state, schema))
           end)
  end

  test "held while front unresolved does not prove some_resolved" do
    src =
      kinds(~w(front worker)) <>
        @meet <>
        """
        family rollout : slot per key of Step
          front never held
          worker held while front unresolved
        temporal bad : rollout :=
          forall (k : key). always ((opened k worker) implies (some_resolved k front))
        """

    assert {:error, msg} = check(src)
    assert msg =~ "bad:"
    assert msg =~ "fails"
    assert msg =~ "some_resolved a front"
    assert msg =~ "a front 0: absent"
    refute msg =~ "holds in"
  end

  test "unknown kinds and hold cycles are refused at the kind token" do
    assert {:error, msg} = check(rollout("  front held while nope unresolved\n"))
    assert msg =~ ~r/\d+:\d+: rollout: nope is not a constructor of Step/
    refute msg =~ "no rule for"

    assert {:error, msg} =
             check(
               rollout("""
                 front held while front unresolved
                 schema never held
                 worker never held
                 cleanup never held
               """)
             )

    assert msg =~ ~r/\d+:\d+: rollout: hold cycle front, front/

    assert {:error, msg} =
             check(
               rollout("""
                 front held until front resolved
                 schema never held
                 worker never held
                 cleanup never held
               """)
             )

    assert msg =~ ~r/\d+:\d+: rollout: hold cycle front, front/

    two = """
      front held while worker unresolved
      schema never held
      worker held until front resolved
      cleanup never held
    """

    assert {:error, msg} = check(rollout(two))
    assert msg =~ ~r/\d+:\d+: rollout: hold cycle front, worker, front/

    three = """
      front held until schema resolved
      schema held while worker unresolved
      worker held until front resolved
      cleanup never held
    """

    assert {:error, msg} = check(rollout(three))
    assert msg =~ ~r/\d+:\d+: rollout: hold cycle front, schema, worker, front/

    mixed = """
      schema held until worker resolved
      worker held while schema unresolved
      front never held
      cleanup never held
    """

    assert {:error, msg} = check(rollout(mixed))
    assert msg =~ ~r/\d+:\d+: rollout: hold cycle schema, worker, schema/
  end

  test "named lists parse, and while earlier stays the old rule" do
    assert {:ok, book} =
             Parser.parse(
               rollout("  worker held until front resolved, held while front unresolved\n")
             )

    family = Enum.find(book, &(&1.kind == :family))
    worker = Enum.find(family.rules, &(&1.ctor == "worker"))
    assert worker.hold == {:named, %{while: ["front"], until: ["front"]}}

    assert {:ok, book} =
             Parser.parse(rollout("  worker held while front unresolved, schema unresolved\n"))

    family = Enum.find(book, &(&1.kind == :family))
    worker = Enum.find(family.rules, &(&1.ctor == "worker"))
    assert worker.hold == {:named, %{while: ["front", "schema"], until: []}}

    assert {:error, msg} =
             Parser.parse(
               "family rollout : slot per key of Step\n  front held while front resolved\n"
             )

    assert msg =~ "expected unresolved"

    assert {:error, msg} =
             Parser.parse(
               "family rollout : slot per key of Step\n  front held until front unresolved\n"
             )

    assert msg =~ "expected resolved"

    earlier = """
    data Step : Type where
      earlier : Step
    family rollout : slot per key of Step
      earlier held while earlier unresolved
    """

    assert {:ok, book} = Parser.parse(earlier)
    family = Enum.find(book, &(&1.kind == :family))
    assert [%{ctor: "earlier", hold: :earlier}] = family.rules

    named = """
    data Step : Type where
      until : Step
      while : Step
      other : Step
    family rollout : slot per key of Step
      until never held
      while never held
      other held while until unresolved, held until while resolved
    """

    assert {:ok, book} = Parser.parse(named)
    family = Enum.find(book, &(&1.kind == :family))
    other = Enum.find(family.rules, &(&1.ctor == "other"))
    assert other.hold == {:named, %{while: ["until"], until: ["while"]}}
  end

  test "until waits for one resolution, while opens when none have arrived" do
    wonly = %{front: :never, worker: {:named, %{while: [:front], until: []}}}
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :worker, 0, wonly)
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :front, 1, wonly)
    assert Step.view(st) == [{"a", 0, 0, :worker, :open}, {"a", 1, 1, :front, :open}]

    uonly = %{front: :never, worker: {:named, %{while: [], until: [:front]}}}
    st = Step.empty()
    assert {:ok, :held, 0, st} = Step.arrive(st, "a", :worker, 0, uonly)
    assert Step.waiting_on(st, 0, uonly) == {:ok, %{kinds: [:front], ids: []}}

    # One resolved front releases the worker. A second open front does not.
    some = %{front: :never, worker: {:named, %{while: [], until: [:front]}}}
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, some)
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :front, 1, some)
    assert {:ok, :held, 2, st} = Step.arrive(st, "a", :worker, 2, some)
    assert Step.waiting_on(st, 2, some) == {:ok, %{kinds: [:front], ids: [0, 1]}}
    assert {:ok, [{2, "a", :worker}], st} = Step.resolve(st, 0, some)
    assert {:error, {:opened, 2}} = Step.waiting_on(st, 2, some)
    assert {:ok, :open, 3, _st} = Step.arrive(st, "a", :worker, 3, some)

    # Both clauses: one resolved front is not enough while another is open.
    mix = %{front: :never, worker: {:named, %{while: [:front], until: [:front]}}}
    st = Step.empty()
    assert {:ok, :held, 0, st} = Step.arrive(st, "a", :worker, 0, mix)
    assert Step.waiting_on(st, 0, mix) == {:ok, %{kinds: [:front], ids: []}}
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :front, 1, mix)
    assert {:ok, :open, 2, st} = Step.arrive(st, "a", :front, 2, mix)
    assert {:ok, [], st} = Step.resolve(st, 1, mix)
    assert Step.waiting_on(st, 0, mix) == {:ok, %{kinds: [:front], ids: [2]}}
    assert {:ok, [{0, "a", :worker}], st} = Step.resolve(st, 2, mix)
    assert {:error, {:opened, 0}} = Step.waiting_on(st, 0, mix)
  end

  test "withdraw does not record a kind, and drop_key forgets a resolved one" do
    rules = %{
      schema: :never,
      front: {:named, %{while: [], until: [:schema]}},
      worker: {:named, %{while: [], until: [:front]}}
    }

    st = Step.empty()
    assert {:ok, :held, 0, st} = Step.arrive(st, "a", :worker, 0, rules)
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :front, 1, rules)
    assert {:ok, [], st} = Step.withdraw(st, 1, rules)
    assert Step.waiting_on(st, 0, rules) == {:ok, %{kinds: [:front], ids: []}}
    assert Map.get(st, :kinds, %{}) == %{}
    assert {:ok, :open, 2, st} = Step.arrive(st, "a", :schema, 2, rules)
    assert {:ok, [], st} = Step.resolve(st, 2, rules)
    assert Step.waiting_on(st, 0, rules) == {:ok, %{kinds: [:front], ids: []}}
    assert {:ok, :open, 3, st} = Step.arrive(st, "a", :front, 3, rules)
    assert {:ok, [{0, "a", :worker}], _st} = Step.resolve(st, 3, rules)

    uonly = %{front: :never, worker: {:named, %{while: [], until: [:front]}}}
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, uonly)
    assert {:ok, [], st} = Step.resolve(st, 0, uonly)
    assert {:ok, st} = Step.skip(st, "a", 9)
    assert Map.get(st, :kinds) == %{"a" => %{front: true}}
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :worker, 1, uonly)
    assert {:ok, [], st} = Step.resolve(st, 1, uonly)
    assert {:ok, st} = Step.skip_below(st, 0)
    assert Map.get(st, :kinds) == %{"a" => %{front: true}}
    assert {:ok, st} = Step.drop_key(st, "a")
    assert Map.get(st, :kinds) == %{}
    assert {:ok, :held, 2, st} = Step.arrive(st, "a", :worker, 2, uonly)
    assert Step.waiting_on(st, 2, uonly) == {:ok, %{kinds: [:front], ids: []}}

    assert {:ok, bare} = Step.drop_key(Step.empty(), "z")
    refute Map.has_key?(bare, :kinds)
  end

  test "waiting_on names held, open, unknown, and departed rows" do
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @dag)
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :schema, 1, @dag)
    assert {:ok, :held, 2, st} = Step.arrive(st, "a", :worker, 2, @dag)
    assert {:ok, :held, 3, st} = Step.arrive(st, "a", :cleanup, 3, @dag)
    assert Step.waiting_on(st, 2, @dag) == {:ok, %{kinds: [:front, :schema], ids: [0, 1]}}
    assert Step.waiting_on(st, 3, @dag) == {:ok, %{kinds: [:worker], ids: [2]}}
    assert {:ok, [], st} = Step.resolve(st, 0, @dag)
    assert Step.waiting_on(st, 2, @dag) == {:ok, %{kinds: [:schema], ids: [1]}}
    assert {:ok, [{2, "a", :worker}], st} = Step.resolve(st, 1, @dag)
    assert {:error, {:opened, 2}} = Step.waiting_on(st, 2, @dag)
    assert Step.waiting_on(st, 3, @dag) == {:ok, %{kinds: [:worker], ids: [2]}}
    assert {:ok, [{3, "a", :cleanup}], st} = Step.resolve(st, 2, @dag)
    assert {:error, {:opened, 3}} = Step.waiting_on(st, 3, @dag)
    assert {:error, {:unknown, 0}} = Step.waiting_on(st, 0, @dag)
    assert {:error, {:unknown, 99}} = Step.waiting_on(st, 99, @dag)
    assert {:error, {:state, :nope}} = Step.waiting_on(:nope, 0, @dag)

    ear = %{command: :earlier}
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :command, 0, ear)
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :command, 1, ear)
    assert Step.waiting_on(st, 1, ear) == {:ok, %{kinds: [:command], ids: [0]}}
    assert {:error, {:opened, 0}} = Step.waiting_on(st, 0, ear)

    any = %{command: :any}
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :command, 0, any)
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :command, 1, any)
    assert Step.waiting_on(st, 1, any) == {:ok, %{kinds: [:command], ids: [0]}}
  end

  test "the emitted dispatcher agrees with Step, including finish and contracts" do
    {disp, parent, src} = compile!(release_book(), Rollout)
    assert src =~ "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1, kinds: %{}}\n"
    assert src =~ "def waiting_on(state, id)"

    # `cleanup` still says `until` in the release book. A while-only
    # family is one with no `until` clause, so the state has no `kinds`.
    {_while, _wp, wsrc} =
      compile!(
        release_book()
        |> String.replace(
          "worker held until front resolved, schema resolved",
          "worker held while front unresolved"
        )
        |> String.replace("cleanup held until worker resolved", "cleanup never held"),
        Rollout
      )

    assert wsrc =~ "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1}\n"
    refute wsrc =~ "floor: -1, kinds:"

    {commands, _cp, csrc} = compile!(File.read!("examples/keyed-commands.muro"), Commands)
    assert csrc =~ "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1}\n"
    refute csrc =~ "kinds: %{}"
    assert csrc =~ "def waiting_on(state, id)"

    cst = commands.new()
    assert {:open, 0, cst} = commands.arrive(cst, "a", :command, 0)
    assert {:held, 1, cst} = commands.arrive(cst, "a", :command, 1)
    assert commands.waiting_on(cst, 1) == {:ok, %{kinds: [:command], ids: [0]}}
    assert commands.waiting_on(cst, 0) == {:error, {:opened, 0}}
    assert commands.waiting_on(cst, 9) == {:error, {:unknown, 9}}
    assert commands.waiting_on(:nope, 0) == {:error, {:state, :nope}}

    trace = [
      {:arrive, "a", :front, 0},
      {:arrive, "a", :schema, 1},
      {:arrive, "a", :worker, 2},
      {:arrive, "a", :cleanup, 3},
      {:resolved, 0},
      {:resolved, 1},
      {:withdraw, 3},
      {:resolved, 2},
      {:skip, "a", 9},
      {:drop, "a"},
      {:arrive, "a", :worker, 4},
      {:skip_below, 4}
    ]

    drive(disp, @dag, trace)
    assert disp.check_trace(trace) == :ok
    assert {:ok, _} = Step.replay(@dag, trace)

    server = Module.concat(parent, ServerWait)
    st = Step.empty()
    dst = disp.new()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @dag)
    assert {:open, 0, dst} = disp.arrive(dst, "a", :front, 0)
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :worker, 1, @dag)
    assert {:held, 1, dst} = disp.arrive(dst, "a", :worker, 1)
    assert {:ok, done} = server.recv(server.init(), :ok)
    assert {:ok, [], dst} = disp.finish(dst, 0, done, :rerun)
    assert Map.get(dst, :kinds) == %{}
    assert dst.by["a"][0] == {0, :front, :open}
    assert {:ok, done} = server.recv(server.init(), :ok)
    assert {:ok, rel, dst} = disp.finish(dst, 0, done)
    assert {:ok, ^rel, st} = Step.resolve(st, 0, @dag)
    assert Step.view(st) == Step.view_disp(dst)
    assert Map.get(st, :kinds) == Map.get(dst, :kinds)
    assert rel == []

    :rand.seed(:exsss, {309, 22, 41})

    for _ <- 1..25 do
      trace = for _ <- 1..8, do: random_act()
      drive(disp, @dag, trace)

      replayed = Step.replay(@dag, trace)

      case replayed do
        {:ok, _} -> assert disp.check_trace(trace) == :ok
        {:error, reason} -> assert disp.check_trace(trace) == {:error, reason}
      end
    end

    {cd, _parent, csrc} = compile!(contract_book(), Rollout)
    assert csrc =~ "{:contract, :idempotent_init, key, index}"
    assert csrc =~ "{:contract, :in_order, key, index}"
    assert csrc =~ "{:contract, :dense, key, index}"

    crules = %{
      init: :never,
      front: :never,
      worker: {:named, %{while: [], until: [:front]}}
    }

    legal = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :front, 1},
      {:arrive, "a", :worker, 2},
      {:resolved, 1}
    ]

    drive(cd, crules, legal)
    assert cd.check_trace(legal) == :ok

    assert {:error, {:contract, :dense, "a", 2}} = cd.arrive(cd.new(), "a", :front, 2)

    assert {:error, {0, {:contract, :dense, "a", 2}}} =
             cd.check_trace([{:arrive, "a", :front, 2}])

    assert {:ok, :open, _, _} = Step.arrive(Step.empty(), "a", :front, 2, crules)

    dst = cd.new()
    assert {:open, 0, dst} = cd.arrive(dst, "a", :init, 0)
    assert {:open, 1, dst} = cd.arrive(dst, "a", :front, 1)
    assert {:ok, _, dst} = cd.resolved(dst, 1)
    assert {:error, {:contract, :in_order, "a", 1}} = cd.arrive(dst, "a", :front, 1)

    assert {:error, {3, {:contract, :in_order, "a", 1}}} =
             cd.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :front, 1},
               {:resolved, 1},
               {:arrive, "a", :front, 1}
             ])

    assert {:ok, left} =
             Step.replay(crules, [
               {:arrive, "a", :init, 0},
               {:arrive, "a", :front, 1},
               {:resolved, 1}
             ])

    assert {:error, {:departed, "a", 1}} = Step.arrive(left, "a", :front, 1, crules)

    assert {:ok, _, dst} = cd.resolved(dst, 0)
    assert {:error, {:contract, :idempotent_init, "a", 0}} = cd.arrive(dst, "a", :init, 0)

    assert {:error, {4, {:contract, :idempotent_init, "a", 0}}} =
             cd.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :front, 1},
               {:resolved, 1},
               {:resolved, 0},
               {:arrive, "a", :init, 0}
             ])
  end

  test "held until earlier resolved names those constructors" do
    src = """
    data Step : Type where
      earlier : Step
      any : Step
      worker : Step
    #{@meet}
    family rollout : slot per key of Step
      earlier held while earlier unresolved
      any never held
      worker held until earlier resolved, any resolved
    """

    assert {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    assert [%{hold: :earlier}, %{hold: :never}, %{hold: hold}] = family.rules
    assert hold == {:named, %{while: [], until: ["earlier", "any"]}}
    assert check(src) == :ok

    assert {:error, msg} =
             Parser.parse(
               "family rollout : slot per key of Step\n  worker held while front unresolved, earlier unresolved\n"
             )

    assert msg =~ "expected never held"

    assert {:error, msg} =
             Parser.parse(
               "family rollout : slot per key of Step\n  worker held until earlier unresolved\n"
             )

    assert msg =~ "expected resolved"

    assert {:error, msg} =
             Parser.parse(
               "family rollout : slot per key of Step\n  worker held until any unresolved\n"
             )

    assert msg =~ "expected resolved"
  end

  test "Graph.withdraw does not witness until or some_resolved" do
    g = %{
      instances: [
        %{id: 0, key: "a", kind: "schema", index: 0},
        %{id: 1, key: "a", kind: "front", index: 1},
        %{id: 2, key: "a", kind: "worker", index: 2}
      ],
      rules: %{
        "schema" => :never,
        "front" => {:named, %{while: [], until: ["schema"]}},
        "worker" => {:named, %{while: [], until: ["front"]}}
      }
    }

    # `front` is the held prerequisite. Withdrawing it leaves `worker` held.
    held = {:absent, :held, :held}
    assert Graph.openable(g, held) == []
    assert {:ok, dropped} = Graph.withdraw(g, held, 1)
    assert Graph.phase(dropped, 1) == :withdrawn
    assert Graph.phase(dropped, 2) == :held
    assert Graph.openable(g, dropped) == []
    refute Graph.holds?(g, {:some_resolved, "a", "front"}, dropped)
    refute Graph.holds?(g, {:resolved, "a", "front"}, dropped)
    refute Graph.holds?(g, {:some_resolved, "a", "schema"}, dropped)
    assert {:error, {:resolved, 1}} = Graph.withdraw(g, dropped, 1)

    gave = {:gave_up, :held, :held}
    assert Graph.holds?(g, {:some_resolved, "a", "schema"}, gave)
    assert Graph.openable(g, gave) == [1]

    resolved = {:resolved, :held, :held}
    assert Graph.holds?(g, {:some_resolved, "a", "schema"}, resolved)
    assert Graph.openable(g, resolved) == [1]

    # A withdrawn `while` witness stops blocking and is not a fact.
    waiting = %{
      g
      | rules: %{
          "schema" => :never,
          "front" => {:named, %{while: [], until: ["schema"]}},
          "worker" => {:named, %{while: ["front"], until: []}}
        }
    }

    assert {:ok, opened} = Graph.withdraw(waiting, held, 1)
    assert Graph.phase(opened, 1) == :withdrawn
    assert Graph.phase(opened, 2) == :held
    assert Graph.openable(waiting, opened) == [2]
    refute Graph.holds?(waiting, {:some_resolved, "a", "front"}, opened)
  end

  test "lock_walk agrees with Graph.withdraw on an until family" do
    instances = [
      %{id: 0, key: "a", kind: "schema", index: 0},
      %{id: 1, key: "a", kind: "front", index: 1},
      %{id: 2, key: "a", kind: "worker", index: 2}
    ]

    src =
      kinds(~w(schema front worker)) <>
        @meet <>
        """
        family chain : slot per key of Step
          schema never held
          front held until schema resolved
          worker held until front resolved
        """

    {disp, _parent, _emitted} = compile!(src, Chain)
    assert {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    assert {:ok, search} = Graph.prepare(book, family, instances: instances)
    assert chain_walk(disp, search, disp.new(), search.g.start, instances, %{}, []) == 90
  end

  test "waiting_on refuses a malformed row the way the dispatcher does" do
    ear = %{command: :earlier}
    any = %{command: :any}
    {commands, _parent, _} = compile!(File.read!("examples/keyed-commands.muro"), Commands)

    {anys, _parent, _} =
      compile!(
        command_src("held while any unresolved"),
        Commands
      )

    until = %{front: :never, worker: {:named, %{while: [], until: [:front]}}}

    {roll, _parent, _} =
      compile!(
        kinds(~w(front worker)) <>
          @meet <>
          """
          family rollout : slot per key of Step
            front never held
            worker held until front resolved
          """,
        Rollout
      )

    while_only = %{front: :never, worker: {:named, %{while: [:front], until: []}}}

    {whiles, _parent, _} =
      compile!(
        kinds(~w(front worker)) <>
          @meet <>
          """
          family rollout : slot per key of Step
            front never held
            worker held while front unresolved
          """,
        Rollout
      )

    mixed = %{
      front: :never,
      worker: {:named, %{while: [:front], until: []}},
      cleanup: {:named, %{while: [], until: [:worker]}}
    }

    {mixd, _parent, _} =
      compile!(
        kinds(~w(front worker cleanup)) <>
          @meet <>
          """
          family rollout : slot per key of Step
            front never held
            worker held while front unresolved
            cleanup held until worker resolved
          """,
        Rollout
      )

    refuse_classic(Step, ear, commands, "a", 0, 1)
    refuse_classic(Step, any, anys, "a", 0, 1)

    {st, dst} = pair_until(Step, until, roll)
    assert Step.waiting_on(st, 1, until) == {:ok, %{kinds: [:front], ids: [0]}}
    assert roll.waiting_on(dst, 1) == {:ok, %{kinds: [:front], ids: [0]}}
    refute Map.has_key?(st, :kinds)
    refuse_rows(st, until, dst, roll, "a", 0, 1)

    st_kinds = Map.put(st, :kinds, %{"a" => :nope})
    dst_kinds = put_in(dst.kinds["a"], :nope)
    assert_state(st_kinds, until, 1, dst_kinds, roll)

    st_map = Map.put(st, :kinds, :nope)
    dst_map = %{dst | kinds: :nope}
    assert_state(st_map, until, 1, dst_map, roll)

    {wst, wdst} = pair_until(Step, while_only, whiles)
    assert Step.waiting_on(wst, 1, while_only) == {:ok, %{kinds: [:front], ids: [0]}}
    assert whiles.waiting_on(wdst, 1) == {:ok, %{kinds: [:front], ids: [0]}}
    wst = Map.put(wst, :kinds, :nope)
    wdst = Map.put(wdst, :kinds, :nope)
    assert Step.waiting_on(wst, 1, while_only) == {:ok, %{kinds: [:front], ids: [0]}}
    assert whiles.waiting_on(wdst, 1) == {:ok, %{kinds: [:front], ids: [0]}}

    {mst, mdst} = pair_until(Step, mixed, mixd)
    assert Step.waiting_on(mst, 1, mixed) == {:ok, %{kinds: [:front], ids: [0]}}
    assert mixd.waiting_on(mdst, 1) == {:ok, %{kinds: [:front], ids: [0]}}
    assert_state(Map.put(mst, :kinds, :nope), mixed, 1, %{mdst | kinds: :nope}, mixd)
  end

  defp refuse_classic(step, rules, disp, key, open_id, held_id) do
    st = Step.empty()
    assert {:ok, :open, ^open_id, st} = step.arrive(st, key, :command, 0, rules)
    assert {:ok, :held, ^held_id, st} = step.arrive(st, key, :command, 1, rules)
    dst = disp.new()
    assert {:open, ^open_id, dst} = disp.arrive(dst, key, :command, 0)
    assert {:held, ^held_id, dst} = disp.arrive(dst, key, :command, 1)
    assert step.waiting_on(st, held_id, rules) == {:ok, %{kinds: [:command], ids: [open_id]}}
    assert disp.waiting_on(dst, held_id) == {:ok, %{kinds: [:command], ids: [open_id]}}

    # A bad kinds field is not read on `earlier` or `any`.
    assert step.waiting_on(Map.put(st, :kinds, :nope), held_id, rules) ==
             {:ok, %{kinds: [:command], ids: [open_id]}}

    refuse_rows(st, rules, dst, disp, key, open_id, held_id)

    assert {:ok, :open, 2, st} = step.arrive(st, "b", :command, 0, rules)
    assert {:open, 2, dst} = disp.arrive(dst, "b", :command, 0)
    other = poison_step(st, 2, &%{&1 | index: -1})
    other_d = move_disp_index(dst, "b", 0, -1)

    assert step.waiting_on(other, held_id, rules) ==
             {:ok, %{kinds: [:command], ids: [open_id]}}

    assert disp.waiting_on(other_d, held_id) == {:ok, %{kinds: [:command], ids: [open_id]}}

    broken = %{st | rows: [:nope | st.rows]}
    assert {:error, {:state, ^broken}} = step.waiting_on(broken, held_id, rules)
  end

  defp pair_until(step, rules, disp) do
    st = step.empty()
    assert {:ok, :open, 0, st} = step.arrive(st, "a", :front, 0, rules)
    assert {:ok, :held, 1, st} = step.arrive(st, "a", :worker, 1, rules)
    dst = disp.new()
    assert {:open, 0, dst} = disp.arrive(dst, "a", :front, 0)
    assert {:held, 1, dst} = disp.arrive(dst, "a", :worker, 1)
    {st, dst}
  end

  defp refuse_rows(st, rules, dst, disp, key, open_id, held_id) do
    for bad <- [-1, :bad, ~D[2020-01-01]] do
      assert_state(
        poison_step(st, open_id, &%{&1 | index: bad}),
        rules,
        held_id,
        move_disp_index(dst, key, 0, bad),
        disp
      )
    end

    assert_state(
      poison_step(st, open_id, &%{&1 | id: :nope}),
      rules,
      held_id,
      poison_disp_id(dst, key, 0, :nope),
      disp
    )

    assert_state(
      poison_step(st, held_id, &%{&1 | index: -1}),
      rules,
      held_id,
      move_disp_index(dst, key, 1, -1),
      disp
    )
  end

  defp assert_state(st, rules, id, dst, disp) do
    assert {:error, {:state, ^st}} = Step.waiting_on(st, id, rules)
    assert {:error, {:state, ^dst}} = disp.waiting_on(dst, id)
  end

  defp poison_step(st, id, fun) do
    %{st | rows: Enum.map(st.rows, fn row -> if row.id == id, do: fun.(row), else: row end)}
  end

  defp move_disp_index(st, key, from, to) do
    rows = Map.fetch!(st.by, key)
    {row, rows} = Map.pop!(rows, from)
    {id, _kind, _phase} = row
    rows = Map.put(rows, to, row)
    %{st | by: Map.put(st.by, key, rows), id: Map.put(st.id, id, {key, to})}
  end

  defp poison_disp_id(st, key, index, id) do
    rows = Map.fetch!(st.by, key)
    {old, kind, phase} = Map.fetch!(rows, index)
    rows = Map.put(rows, index, {id, kind, phase})
    ids = st.id |> Map.delete(old) |> Map.put(id, {key, index})
    %{st | by: Map.put(st.by, key, rows), id: ids}
  end

  defp command_src(rule) do
    """
    data Command : Type where
      command : Command
    #{@meet}
    family commands : slot per key of Command
      command #{rule}
    """
  end

  defp kinds(names) do
    ctors = Enum.map_join(names, "\n", &"  #{&1} : Step")

    """
    data Step : Type where
    #{ctors}
    """
  end

  defp rollout(rules) do
    kinds(~w(front schema worker cleanup)) <>
      @meet <>
      """
      family rollout : slot per key of Step
      #{rules}
      """
  end

  defp release_book do
    kinds(~w(front schema worker cleanup)) <>
      @meet <>
      """
      family rollout : slot per key of Step
        front never held
        schema never held
        worker held until front resolved, schema resolved
        cleanup held until worker resolved
      """
  end

  defp contract_book do
    kinds(~w(init front worker)) <>
      @meet <>
      """
      family rollout : slot per key of Step
        init never held
        front never held
        worker held until front resolved
      contract rollout : idempotent init
      contract rollout : in order
      contract rollout : dense
      """
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp compile!(src, family) do
    dir = System.tmp_dir!() |> Path.join("muro-named-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    parent = Module.concat(["NamedFam#{System.unique_integer([:positive])}"])
    assert {:ok, emitted} = Muro.emit_fsm(path, parent)
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(emitted) end)

    warnings =
      Enum.filter(diags, &(match?(%{severity: :warning}, &1) or match?({:warning, _}, &1)))

    assert warnings == [], inspect(warnings, limit: 20)
    disp = Module.concat(parent, family)
    assert disp in Enum.map(mods, &elem(&1, 0))
    {disp, parent, emitted}
  end

  defp random_act do
    key = Enum.random(["a", "b"])
    kind = Enum.random([:front, :schema, :worker, :cleanup])
    index = :rand.uniform(4) - 1
    id = :rand.uniform(6) - 1

    Enum.random([
      {:arrive, key, kind, index},
      {:resolved, id},
      {:withdraw, id},
      {:skip, key, index},
      {:drop, key},
      {:skip_below, index}
    ])
  end

  defp drive(disp, rules, trace) do
    Enum.reduce_while(trace, {Step.empty(), disp.new()}, fn act, {st, dst} ->
      {st2, s} = step_act(st, act, rules)
      {dst2, d} = disp_act(disp, dst, act)
      assert s == d, "#{inspect(act)}\nstep #{inspect(s)}\ndisp #{inspect(d)}"

      case s do
        {:error, _} ->
          {:halt, :error}

        _ ->
          assert Step.view(st2) == Step.view_disp(dst2)
          assert Map.get(st2, :kinds, %{}) == Map.get(dst2, :kinds, %{})

          for id <- Enum.map(st2.rows, & &1.id) do
            assert Step.waiting_on(st2, id, rules) == disp.waiting_on(dst2, id)
          end

          {:cont, {st2, dst2}}
      end
    end)
  end

  defp step_act(st, {:arrive, key, kind, index}, rules) do
    case Step.arrive(st, key, kind, index, rules) do
      {:ok, phase, id, st} -> {st, {phase, id}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:resolved, id}, rules) do
    case Step.resolve(st, id, rules) do
      {:ok, rel, st} -> {st, {:ok, rel}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:withdraw, id}, rules) do
    case Step.withdraw(st, id, rules) do
      {:ok, rel, st} -> {st, {:ok, rel}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:skip, key, index}, _rules) do
    case Step.skip(st, key, index) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:drop, key}, _rules) do
    case Step.drop_key(st, key) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:skip_below, index}, _rules) do
    case Step.skip_below(st, index) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:arrive, key, kind, index}) do
    case disp.arrive(dst, key, kind, index) do
      {phase, id, dst} when phase in [:open, :held] -> {dst, {phase, id}}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:resolved, id}) do
    case disp.resolved(dst, id) do
      {:ok, rel, dst} -> {dst, {:ok, rel}}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:withdraw, id}) do
    case disp.withdraw(dst, id) do
      {:ok, rel, dst} -> {dst, {:ok, rel}}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:skip, key, index}) do
    case disp.skip(dst, key, index) do
      {:ok, dst} -> {dst, :ok}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:drop, key}) do
    case disp.drop_key(dst, key) do
      {:ok, dst} -> {dst, :ok}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:skip_below, index}) do
    case disp.skip_below(dst, index) do
      {:ok, dst} -> {dst, :ok}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  # One dispatcher step at a time, matched on the graph. A withdrawal is
  # Graph.withdraw. The phase is :withdrawn, so it does not witness
  # some_resolved and the dispatcher's kinds map is unchanged.
  defp chain_walk(disp, search, dst, gst, remaining, live, trace) do
    g = search.g

    arrived =
      Enum.reduce(remaining, 0, fn inst, acc ->
        kind = String.to_atom(inst.kind)
        assert {phase, id, dst2} = disp.arrive(dst, inst.key, kind, inst.index)
        tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}
        gst2 = chain_step!(search, gst, tag, trace)
        left = Enum.reject(remaining, &(&1.id == inst.id))
        step = {:arrive, inst.key, kind, inst.index, phase}
        acc + chain_walk(disp, search, dst2, gst2, left, Map.put(live, id, inst), [step | trace])
      end)

    finished =
      Enum.reduce(live, 0, fn {id, inst}, acc ->
        {op, dst2, released, gst1} =
          case Graph.phase(gst, inst.id) do
            :held ->
              before = Map.get(dst, :kinds, %{})
              assert {:error, {:held, ^id}} = disp.resolved(dst, id)
              assert {:ok, released, dst2} = disp.withdraw(dst, id)
              assert {:ok, gst1} = Graph.withdraw(g, gst, inst.id)
              assert Graph.phase(gst1, inst.id) == :withdrawn
              assert Map.get(dst2, :kinds, %{}) == before

              others =
                Enum.any?(g.instances, fn other ->
                  other.id != inst.id and other.key == inst.key and other.kind == inst.kind and
                    Graph.phase(gst1, other.id) in [:resolved, :gave_up]
                end)

              assert Graph.holds?(g, {:some_resolved, inst.key, inst.kind}, gst1) == others
              {:withdraw, dst2, released, gst1}

            {:run, _, _, _} ->
              assert {:error, {:opened, ^id}} = disp.withdraw(dst, id)
              assert {:error, {:opened, _}} = Graph.withdraw(g, gst, inst.id)
              assert {:ok, released, dst2} = disp.resolved(dst, id)
              {:resolved, dst2, released, chain_resolve!(search, gst, inst.id, trace)}
          end

        trace = [{op, id, released} | trace]
        gst2 = chain_release!(search, gst1, released, live, trace)
        assert {:error, {:resolved, ^id}} = disp.withdraw(dst2, id)
        assert {:error, {:resolved, _}} = Graph.withdraw(g, gst2, inst.id)
        acc + chain_walk(disp, search, dst2, gst2, remaining, Map.delete(live, id), trace)
      end)

    max(arrived + finished, 1)
  end

  defp chain_release!(search, gst, released, live, trace) do
    ids =
      Enum.map(released, fn {id, key, kind} ->
        inst = Map.fetch!(live, id)
        assert {inst.key, inst.kind} == {key, Atom.to_string(kind)}
        inst
      end)

    opened =
      ids
      |> Enum.sort_by(& &1.index)
      |> Enum.reduce(gst, fn inst, st ->
        assert inst.id in Graph.openable(search.g, st),
               "dispatcher opened #{inspect(inst)} the graph holds after #{inspect(Enum.reverse(trace))}"

        chain_step!(search, st, {:open, inst.id}, trace)
      end)

    assert Graph.openable(search.g, opened) == [],
           "graph can still open #{inspect(Graph.openable(search.g, opened))} after #{inspect(Enum.reverse(trace))}"

    opened
  end

  defp chain_resolve!(search, gst, gid, trace) do
    chain_resolve_bfs(search, gid, MapSet.new(), [gst]) ||
      flunk("resolve of #{gid} is not a graph run after #{inspect(Enum.reverse(trace))}")
  end

  defp chain_resolve_bfs(_search, _gid, _seen, []), do: nil

  defp chain_resolve_bfs(search, gid, seen, [state | rest]) do
    if MapSet.member?(seen, state) do
      chain_resolve_bfs(search, gid, seen, rest)
    else
      steps = chain_steps(search, state)

      case Enum.find(steps, fn {tag, _} -> tag in [{:resolve, gid}, {:give_up, gid}] end) do
        {_tag, dest} ->
          dest

        nil ->
          more =
            for {tag, dest} <- steps,
                match?({:meet, ^gid, _}, tag) or tag == {:retry, gid},
                do: dest

          chain_resolve_bfs(search, gid, MapSet.put(seen, state), rest ++ more)
      end
    end
  end

  defp chain_step!(search, state, tag, trace) do
    steps = chain_steps(search, state)

    case Enum.find(steps, fn {t, _} -> t == tag end) do
      {_, dest} ->
        dest

      nil ->
        flunk(
          "graph has no #{inspect(tag)} after #{inspect(Enum.reverse(trace))}; edges #{inspect(Enum.map(steps, &elem(&1, 0)))}"
        )
    end
  end

  defp chain_steps(search, state) do
    case Map.fetch(search.edges, state) do
      {:ok, steps} -> steps
      :error -> Graph.edges(search.g, state)
    end
  end
end
