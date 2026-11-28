defmodule Muro.EmitGoLiveTest do
  use ExUnit.Case, async: false

  @moduletag timeout: 180_000

  # Resolved when this file is compiled. The live tests are skipped when
  # `go version` does not exit 0 with a version line, or when the probe
  # does not finish, including in CI. GNU `timeout` is used when it is
  # on PATH so a hung probe is reaped. Adding Go to a CI runner is a
  # workflow change; these tests skip cleanly until that lands.
  @go System.find_executable("go")

  @go_line (case @go do
              exe when is_binary(exe) ->
                try do
                  {cmd, args} =
                    case System.find_executable("timeout") do
                      bin when is_binary(bin) ->
                        case System.cmd(bin, ["--version"], stderr_to_stdout: true) do
                          {out, 0} ->
                            if String.contains?(out, "GNU coreutils") do
                              {bin, ["--kill-after=1", "5", exe, "version"]}
                            else
                              {exe, ["version"]}
                            end

                          _ ->
                            {exe, ["version"]}
                        end

                      _ ->
                        {exe, ["version"]}
                    end

                  task = Task.async(fn -> System.cmd(cmd, args, stderr_to_stdout: true) end)

                  case Task.yield(task, 5_000) || Task.shutdown(task, :brutal_kill) do
                    {:ok, {out, 0}} ->
                      if String.contains?(out, "go version"), do: out, else: ""

                    _ ->
                      ""
                  end
                rescue
                  _ -> ""
                end

              _ ->
                ""
            end)

  @have_go @go_line != ""
  @go_skip if(@have_go, do: false, else: "go is not available")

  @have_race System.find_executable("gcc") != nil or System.find_executable("cc") != nil

  @go_mod (case Regex.run(~r/go(\d+\.\d+)/, @go_line) do
             [_, ver] -> "go #{ver}"
             _ -> "go 1.22"
           end)

  @cache Path.join(System.tmp_dir!(), "muro-go-live-cache")
  @gopath Path.join(System.tmp_dir!(), "muro-go-live-gopath")

  @moduletag skip: @go_skip

  alias Muro.Family.Step

  test "sessions agree with the state machine, including an illegal step" do
    parent = fsm!("examples/ping.muro")

    ping =
      session_trace(parent, "ping", [
        {:send, 0},
        {:recv, 0},
        {:send, 1},
        {:recv, 2}
      ])

    pick =
      session_trace(parent, "pick", [
        {:recv, {:pick, :b0}},
        {:send, {:pick, :b0}},
        {:send, {:pick, :b1}}
      ])

    both =
      session_trace(parent, "both-arms", [
        {:send, {:pick, :b0}},
        {:recv, {:pick, :b1}},
        {:send, 0}
      ])

    go_run("examples/ping.muro", session_test("ping", [ping, pick, both]))
  end

  test "payloads, bounds, and a parameter agree with the state machine" do
    meet = fsm!("examples/meet.muro")

    box =
      session_trace(meet, "box", [
        {:recv, {:b0, %{"x" => 0, "y" => 1}}},
        {:send, {:b0, %{"x" => 0, "y" => 1}}},
        {:send, %{}}
      ])

    sized =
      session_trace(meet, "sized", [
        {:recv, 2},
        {:send, [0]},
        {:send, [0, 0]}
      ])

    window =
      session_trace(meet, "window", [
        {:recv, 8},
        {:send, 9},
        {:send, 8}
      ])

    # session-calls.muro jumps from one session to another. That book is
    # refused. The parameter itself is a session with one nat argument.
    dir = fresh!()
    nums_path = Path.join(dir, "nums.muro")
    File.write!(nums_path, "session nums (k : Nat) := send Nat end\n")
    calls = fsm!(nums_path)
    nums = param_trace(calls, "nums", [1], [{:send, 4}, {:recv, 4}])

    go_run("examples/meet.muro", session_test("meet", [box, sized, window]))
    go_run(nums_path, nums_only(nums))
  end

  test "a choreography monitor agrees with the state machine" do
    parent = fsm!("examples/release-plan.muro")
    mod = child(parent, "plan")
    st = mod.init()

    script = [
      {:step, :release, :front, :deploy},
      {:step, :front, :worker, :deployed},
      {:step, :front, :release, :deployed},
      {:step, :release, :worker, :deploy},
      {:step, :worker, :release, :deployed},
      {:step, :release, :front, :deploy}
    ]

    lines =
      Enum.map_reduce(script, st, fn
        {:step, a, b, l}, st ->
          case mod.step(st, a, b, l) do
            {:ok, st} ->
              {%{
                 ok: true,
                 expected: exp(mod.expected(st)),
                 done: mod.done?(st),
                 a: a,
                 b: b,
                 l: l
               }, st}

            {:error, _} ->
              {%{
                 ok: false,
                 expected: exp(mod.expected(st)),
                 done: mod.done?(st),
                 a: a,
                 b: b,
                 l: l
               }, st}
          end
      end)
      |> elem(0)

    go_run("examples/release-plan.muro", monitor_test("Plan", lines))
  end

  test "a choreography family agrees on the preamble and on one key" do
    parent = fsm!("examples/release-rollout.muro")
    mod = child(parent, "rollout")
    st = mod.init()

    early = exp(mod.expected(st, "site"))

    {:ok, st} = mod.step_shared(st, :release, :registry, :publish)
    {:ok, st} = mod.step_shared(st, :registry, :release, :published)
    assert mod.shared_done?(st)
    {:error, _} = mod.step_shared(st, :release, :registry, :publish)

    {:ok, st} = mod.step(st, "site", :release, :front, :deploy)
    keys = mod.keys(st)
    {:ok, st} = mod.step(st, "site", :front, :release, :deployed)
    {:ok, st} = mod.step(st, "site", :release, :worker, :deploy)
    {:ok, st} = mod.step(st, "site", :worker, :release, :deployed)
    choose = exp(mod.expected(st, "site"))
    {:ok, st} = mod.choose(st, "site", :release, :keep)
    {:ok, st} = mod.step(st, "site", :release, :front, :keep)
    {:ok, st} = mod.step(st, "site", :release, :worker, :keep)
    assert mod.done?(st, "site")

    go_run(
      "examples/release-rollout.muro",
      rollout_test(%{early: early, keys: keys, choose: choose})
    )
  end

  test "keyed families agree with Family.Step on every host rule" do
    go_run(
      "examples/keyed-slots.muro",
      family_test(book!("examples/keyed-slots.muro"), slots_script())
    )

    go_run(
      "examples/keyed-commands.muro",
      family_test(book!("examples/keyed-commands.muro"), commands_script())
    )

    go_run(
      "examples/keyed-release.muro",
      family_test(book!("examples/keyed-release.muro"), release_script())
    )

    go_run(
      "examples/keyed-rollback.muro",
      family_test(book!("examples/keyed-rollback.muro"), rollback_script())
    )

    go_run_text("any.muro", any_book(), family_test(parse!(any_book(), "any.muro"), any_script()))

    go_run_text(
      "while.muro",
      while_book(),
      family_test(parse!(while_book(), "while.muro"), while_script())
    )
  end

  test "a seeded trace matches Family.Step" do
    book = book!("examples/keyed-slots.muro")
    {_name, ctors, _rules} = rules_of(book)
    ops = fuzz_ops(ctors, 40, {316, 22, 52})
    go_run("examples/keyed-slots.muro", family_test(book, ops))
  end

  test "several goroutines each own a dispatcher, and one shared value is locked" do
    src = render!("examples/keyed-slots.muro")

    test = """
    package keyed_slots

    import (
    	"sync"
    	"testing"
    )

    func TestOwnDispatcher(t *testing.T) {
    	var wg sync.WaitGroup
    	for range 4 {
    		wg.Add(1)
    		go func() {
    			defer wg.Done()
    			s := NewSlots()
    			phase, id, err := s.Arrive("k", SlotsKindInit, 0)
    			if err != nil || phase != PhaseOpen || id != 0 {
    				t.Errorf("own: %v %v %d", err, phase, id)
    			}
    		}()
    	}
    	wg.Wait()
    }

    func TestSharedMutex(t *testing.T) {
    	s := NewSlots()
    	var mu sync.Mutex
    	var wg sync.WaitGroup
    	for i := range 4 {
    		wg.Add(1)
    		go func(i int) {
    			defer wg.Done()
    			mu.Lock()
    			defer mu.Unlock()
    			phase, _, err := s.Arrive("k", SlotsKindInit, i)
    			if err != nil || phase != PhaseOpen {
    				t.Errorf("shared %d: %v %v", i, err, phase)
    			}
    		}(i)
    	}
    	wg.Wait()
    	if len(s.View()) != 4 {
    		t.Fatalf("view %d", len(s.View()))
    	}
    }
    """

    go_check(src, test, true)
  end

  defp slots_script do
    [
      {:arrive, "k", "init", 0},
      {:arrive, "k", "signal", 1},
      {:arrive, "k", "init", 0},
      {:waiting, 1},
      {:resolve, 0},
      {:arrive, "k", "init", 0},
      {:skip, "k", 5},
      {:arrive, "k", "init", 5},
      {:below, 10},
      {:arrive, "m", "signal", 10},
      {:arrive, "m", "init", 11},
      {:revert, 0},
      {:drop, "gone"},
      {:arrive, "k", "init", -1},
      {:rerun, 99},
      {:finish, 0, false, :resolve}
    ]
  end

  defp commands_script do
    [
      {:arrive, "k", "command", 1},
      {:arrive, "k", "command", 0},
      {:waiting, 0},
      {:resolve, 1},
      {:resolve, 0}
    ]
  end

  defp release_script do
    [
      {:arrive, "k", "worker", 0},
      {:waiting, 0},
      {:arrive, "k", "front", 1},
      {:arrive, "k", "schema", 2},
      {:resolve, 1},
      {:waiting, 0},
      {:resolve, 2},
      {:resolve, 0},
      {:arrive, "k", "cleanup", 3},
      {:withdraw, 0}
    ]
  end

  defp rollback_script do
    [
      {:arrive, "k", "front", 0},
      {:resolve, 0},
      {:revert, 0},
      {:resolve, 0},
      {:arrive, "k", "worker", 1},
      {:revert, 0},
      {:withdraw, 1},
      {:revert, 0}
    ]
  end

  defp any_script do
    [
      {:arrive, "k", "item", 0},
      {:arrive, "k", "item", 1},
      {:waiting, 1},
      {:resolve, 0},
      {:resolve, 1}
    ]
  end

  defp while_script do
    [
      {:arrive, "k", "worker", 1},
      {:waiting, 0},
      {:arrive, "k", "front", 0},
      {:resolve, 1},
      {:waiting, 0}
    ]
  end

  defp any_book do
    """
    data Event : Type where
      item : Event
    data Report : Type where
      ok : Report
    session task-work := send Report end
    session server-wait := recv Report end
    conform task : task-work := put ok done
    conform server : server-wait := get (r : Report) done
    meet slot : server with task buffer 1
    family slots : slot per key of Event
      item held while any unresolved
    """
  end

  defp while_book do
    """
    data Step : Type where
      front : Step
      worker : Step
    data Report : Type where
      ok : Report
    session task-work := send Report end
    session server-wait := recv Report end
    conform task : task-work := put ok done
    conform server : server-wait := get (r : Report) done
    meet slot : server with task buffer 1
    family slots : slot per key of Step
      front never held
      worker held while front unresolved
    """
  end

  defp fuzz_ops(ctors, n, seed) do
    :rand.seed(:exsss, seed)

    Enum.map(1..n, fn i ->
      key = Enum.random(~w(a b))
      ctor = Enum.random(ctors)

      case :rand.uniform(6) do
        1 -> {:arrive, key, ctor, :rand.uniform(8) - 1}
        2 -> {:resolve, :rand.uniform(max(i, 1)) - 1}
        3 -> {:withdraw, :rand.uniform(max(i, 1)) - 1}
        4 -> {:skip, key, :rand.uniform(6)}
        5 -> {:below, :rand.uniform(4)}
        6 -> {:drop, key}
      end
    end)
  end

  defp family_test(book, ops) do
    {name, ctors, rules} = rules_of(book)
    go = GoName.camel(name)
    {steps, _st} = Enum.map_reduce(ops, Step.empty(), &fam_step(&1, &2, rules))

    body =
      Enum.map_join(Enum.with_index(steps), "\n", fn {step, i} -> go_step(go, ctors, step, i) end)

    """
    package placeholder

    import (
        "errors"
        "testing"
    )

    func TestFamily(t *testing.T) {
        s := New#{go}()
        var zero *#{go}
        if _, _, err := zero.Arrive("k", #{go}Kind#{Macro.camelize(hd(ctors))}, 0); !errors.Is(err, ErrBadState) {
            t.Fatal(err)
        }
    #{body}
    }

    #{family_helpers(go)}
    """
  end

  defp family_helpers(go) do
    """
    func departed(s *#{go}, key string, index int) bool {
        if s == nil {
            return false
        }
        if index <= s.Floor() {
            return true
        }
        prefix, gaps, ok := s.Departed(key)
        if !ok {
            return false
        }
        if index <= prefix {
            return true
        }
        for _, g := range gaps {
            if g == index {
                return true
            }
        }
        return false
    }

    func feAs(err error) *FamilyError {
        var fe *FamilyError
        if errors.As(err, &fe) {
            return fe
        }
        return nil
    }

    func feKey(err error) string {
        if fe := feAs(err); fe != nil {
            return fe.Key
        }
        return ""
    }

    func feIndex(err error) int {
        if fe := feAs(err); fe != nil {
            return fe.Index
        }
        return -1
    }

    func feID(err error) int {
        if fe := feAs(err); fe != nil {
            return fe.ID
        }
        return -1
    }

    func feKind(err error) string {
        if fe := feAs(err); fe != nil {
            return fe.Kind
        }
        return ""
    }

    func feIDs(err error) []int {
        if fe := feAs(err); fe != nil {
            return fe.IDs
        }
        return nil
    }
    """
  end

  defp fam_step(op, st, rules) do
    {st2, outcome} = fam_apply(st, rules, op)

    snap = %{
      op: op,
      outcome: outcome,
      view: Step.view(st2),
      floor: Map.get(st2, :floor, -1),
      departed: departed_snap(st2, op)
    }

    {snap, st2}
  end

  defp departed_snap(st, op) do
    keys =
      case op do
        {_, key, _, _} when is_binary(key) -> [key]
        {_, key} when is_binary(key) -> [key]
        _ -> []
      end

    Enum.map(keys, fn key ->
      flags = Enum.map(0..12, &Step.departed?(st, key, &1))
      {key, flags}
    end)
  end

  defp fam_apply(st, rules, {:arrive, key, kind, index}) do
    case Step.arrive(st, key, String.to_atom(kind), index, rules) do
      {:ok, phase, id, st} -> {st, {:arrive, phase, id}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, rules, {:resolve, id}) do
    case Step.resolve(st, id, rules) do
      {:ok, rel, st} -> {st, {:rel, rel}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, rules, {:withdraw, id}) do
    case Step.withdraw(st, id, rules) do
      {:ok, rel, st} -> {st, {:rel, rel}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, rules, {:waiting, id}) do
    case Step.waiting_on(st, id, rules) do
      {:ok, %{kinds: kinds, ids: ids}} -> {st, {:wait, kinds, ids}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, _rules, {:skip, key, index}) do
    case Step.skip(st, key, index) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, _rules, {:drop, key}) do
    case Step.drop_key(st, key) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, _rules, {:below, index}) do
    case Step.skip_below(st, index) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, rules, {:revert, id}) do
    case Step.revert(st, id, rules) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, _rules, {:rerun, id}) do
    case Step.rerun(st, id) do
      {:ok, _rel, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp fam_apply(st, rules, {:finish, id, false, _outcome}) do
    {st, {:unfinished, Step.view(st), id, rules}}
  end

  defp fam_apply(st, rules, {:finish, id, true, :resolve}) do
    fam_apply(st, rules, {:resolve, id})
  end

  defp fam_apply(st, rules, {:finish, id, true, :rerun}) do
    fam_apply(st, rules, {:rerun, id})
  end

  defp go_step(
         go,
         ctors,
         %{op: op, outcome: outcome, view: view, floor: floor, departed: deps},
         i
       ) do
    call = go_call(go, ctors, op)
    check = go_outcome(outcome, i)
    view_check = go_view(view, floor, deps, i)
    body = Enum.join([call, String.trim(check), String.trim(view_check), go_sinks(op)], "\n")
    "{\n" <> indent_go(body) <> "\n}"
  end

  defp indent_go(text) do
    text
    |> String.trim()
    |> String.split("\n")
    |> Enum.map_join("\n", fn line -> if line == "", do: "", else: "\t" <> line end)
  end

  defp go_sinks({:arrive, _, _, _}), do: "_ = phase\n_ = id\n_ = err"
  defp go_sinks({:resolve, _}), do: "_ = rel\n_ = err"
  defp go_sinks({:withdraw, _}), do: "_ = rel\n_ = err"
  defp go_sinks({:waiting, _}), do: "_ = kinds\n_ = ids\n_ = err"
  defp go_sinks({:finish, _, _, _}), do: "_ = rel\n_ = err"
  defp go_sinks(_), do: "_ = err"

  defp go_call(go, ctors, {:arrive, key, kind, index}) do
    "phase, id, err := s.Arrive(#{gq(key)}, #{kind_const(go, ctors, kind)}, #{index})"
  end

  defp go_call(_go, _ctors, {:resolve, id}), do: "rel, err := s.Resolved(#{id})"
  defp go_call(_go, _ctors, {:withdraw, id}), do: "rel, err := s.Withdraw(#{id})"
  defp go_call(_go, _ctors, {:waiting, id}), do: "kinds, ids, err := s.WaitingOn(#{id})"
  defp go_call(_go, _ctors, {:skip, key, index}), do: "err := s.Skip(#{gq(key)}, #{index})"
  defp go_call(_go, _ctors, {:drop, key}), do: "err := s.DropKey(#{gq(key)})"
  defp go_call(_go, _ctors, {:below, index}), do: "err := s.SkipBelow(#{index})"
  defp go_call(_go, _ctors, {:revert, id}), do: "err := s.Revert(#{id})"
  defp go_call(_go, _ctors, {:rerun, id}), do: "err := s.Rerun(#{id})"

  defp go_call(_go, _ctors, {:finish, id, false, _}) do
    "rel, err := s.Finish(#{id}, false, OutcomeResolve)"
  end

  defp go_call(_go, _ctors, {:finish, id, true, :resolve}) do
    "rel, err := s.Finish(#{id}, true, OutcomeResolve)"
  end

  defp go_call(_go, _ctors, {:finish, id, true, :rerun}) do
    "rel, err := s.Finish(#{id}, true, OutcomeRerun)"
  end

  defp kind_const(go, _ctors, kind), do: go <> "Kind" <> Macro.camelize(kind)

  defp go_outcome({:arrive, phase, id}, i) do
    """
    if err != nil || phase.String() != #{gq(Atom.to_string(phase))} || id != #{id} {
    	t.Fatalf("#{i} arrive %v %v %d", err, phase, id)
    }
    """
  end

  defp go_outcome({:rel, rel}, i) do
    want =
      rel
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {{id, key, kind}, j} ->
        "if rel[#{j}].ID != #{id} || rel[#{j}].Key != #{gq(key)} || rel[#{j}].Kind != #{gq(atom_name(kind))} { t.Fatalf(\"#{i} rel #{j} %v\", rel) }"
      end)

    """
    if err != nil || len(rel) != #{length(rel)} {
    	t.Fatalf("#{i} rel %v %v", err, rel)
    }
    #{want}
    """
  end

  defp go_outcome({:wait, kinds, ids}, i) do
    kind_bad = list_bad(kinds, "kinds", &gq(atom_name(&1)))
    id_bad = list_bad(ids, "ids", &to_string/1)

    """
    if err != nil || len(kinds) != #{length(kinds)} || len(ids) != #{length(ids)} || #{kind_bad} || #{id_bad} {
        t.Fatalf("#{i} wait %v %v %v", err, kinds, ids)
    }
    """
  end

  defp go_outcome(:ok, i) do
    """
    if err != nil {
    	t.Fatalf("#{i}: %v", err)
    }
    """
  end

  defp go_outcome({:unfinished, _view, _id, _rules}, i) do
    """
    if err == nil || !errors.Is(err, ErrUnfinished) || !errors.Is(err, ErrFamily) {
    	t.Fatalf("#{i} unfinished %v", err)
    }
    """
  end

  defp go_outcome({:error, reason}, i) do
    {sentinel, extra} = go_reason(reason)

    """
    if err == nil || !errors.Is(err, #{sentinel}) || !errors.Is(err, ErrFamily) {
    	t.Fatalf("#{i} error %v", err)
    }
    #{extra}
    """
  end

  defp list_bad([], _name, _show), do: "false"

  defp list_bad(items, name, show) do
    Enum.map_join(Enum.with_index(items), " || ", fn {item, j} ->
      "#{name}[#{j}] != #{show.(item)}"
    end)
  end

  defp go_reason({:duplicate, key, index}), do: {"ErrDuplicate", key_index(key, index)}
  defp go_reason({:departed, key, index}), do: {"ErrDeparted", key_index(key, index)}
  defp go_reason({:unknown, id}), do: {"ErrUnknown", id_check(id)}
  defp go_reason({:held, id}), do: {"ErrHeld", id_check(id)}
  defp go_reason({:opened, id}), do: {"ErrOpened", id_check(id)}
  defp go_reason({:resolved, id}), do: {"ErrResolved", id_check(id)}
  defp go_reason({:withdrawn, id}), do: {"ErrWithdrawn", id_check(id)}
  defp go_reason({:live, key}), do: {"ErrLive", "if feKey(err) != #{gq(key)} { t.Fatal(err) }"}

  defp go_reason({:index, index}),
    do: {"ErrIndex", "if feIndex(err) != #{index} { t.Fatal(err) }"}

  defp go_reason({:unmarked, :revert}), do: {"ErrUnmarked", ""}

  defp go_reason({:kind, kind}),
    do: {"ErrKind", "if feKind(err) != #{gq(atom_name(kind))} { t.Fatal(err) }"}

  defp go_reason({:held_by, ids}) do
    cmp = list_bad(ids, "feIDs(err)", &to_string/1)

    {"ErrHeldBy",
     "if len(feIDs(err)) != #{length(ids)} || #{cmp} { t.Fatalf(\"%v\", feIDs(err)) }"}
  end

  defp go_reason(other), do: {"ErrBadState", "t.Logf(\"reason #{inspect(other)}\")"}

  defp key_index(key, index) do
    "if feKey(err) != #{gq(key)} || feIndex(err) != #{index} { t.Fatal(err) }"
  end

  defp id_check(id), do: "if feID(err) != #{id} { t.Fatal(err) }"

  defp go_view(rows, floor, deps, i) do
    row_checks =
      rows
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {{key, index, id, kind, phase}, j} ->
        "if rows[#{j}].Key != #{gq(key)} || rows[#{j}].Index != #{index} || rows[#{j}].ID != #{id} || rows[#{j}].Kind != #{gq(atom_name(kind))} || rows[#{j}].Phase.String() != #{gq(Atom.to_string(phase))} { t.Fatalf(\"#{i} row #{j} %v\", rows[#{j}]) }"
      end)

    dep_checks =
      Enum.map_join(deps, "\n", fn {key, flags} ->
        wants =
          Enum.map_join(Enum.with_index(flags), " || ", fn {flag, j} ->
            "departed(s, #{gq(key)}, #{j}) != #{flag}"
          end)

        "if #{wants} { t.Fatalf(\"#{i} departed #{key}\") }"
      end)

    """
    if s.Floor() != #{floor} {
    	t.Fatalf("#{i} floor %d", s.Floor())
    }
    rows := s.View()
    if len(rows) != #{length(rows)} {
    	t.Fatalf("#{i} view %v", rows)
    }
    #{row_checks}
    #{dep_checks}
    """
  end

  defp rules_of(book) do
    fam = Enum.find(book, &(&1.kind == :family and &1.key != nil))
    data = Enum.find(book, &(&1.kind == :data and &1.name == fam.key))
    ctors = Enum.map(data.ctors, & &1.name)
    by = Map.new(fam.rules || [], &{&1.ctor, &1.hold})

    rules =
      Map.new(ctors, fn ctor ->
        {String.to_atom(ctor), hold_atom(Map.get(by, ctor))}
      end)

    rules = if fam.revert, do: Map.put(rules, {:mark, :revert}, true), else: rules
    {fam.name, ctors, rules}
  end

  defp hold_atom(nil), do: :never
  defp hold_atom(hold) when hold in [:never, :earlier, :any], do: hold

  defp hold_atom({:named, %{while: w, until: u}}) do
    {:named, %{while: Enum.map(w, &atom_of/1), until: Enum.map(u, &atom_of/1)}}
  end

  defp atom_of(a) when is_atom(a), do: a
  defp atom_of(s) when is_binary(s), do: String.to_atom(s)
  defp atom_name(a) when is_atom(a), do: Atom.to_string(a)
  defp atom_name(s) when is_binary(s), do: s

  defp session_trace(parent, name, events) do
    mod = child(parent, name)
    go = GoName.camel(name)
    st = mod.init()
    first = exp(mod.expected(st))

    {lines, _} =
      Enum.map_reduce(events, st, fn ev, st ->
        case step_fsm(mod, st, ev) do
          {:ok, st} ->
            {%{ok: true, expected: exp(mod.expected(st)), done: mod.done?(st), ev: ev}, st}

          {:error, _} ->
            {%{ok: false, expected: exp(mod.expected(st)), done: mod.done?(st), ev: ev}, st}
        end
      end)

    %{go: go, first: first, lines: lines, params: []}
  end

  defp param_trace(parent, name, args, events) do
    mod = child(parent, name)
    go = GoName.camel(name)
    st = apply(mod, :init, args)
    first = exp(mod.expected(st))

    {lines, _} =
      Enum.map_reduce(events, st, fn ev, st ->
        case step_fsm(mod, st, ev) do
          {:ok, st} ->
            {%{ok: true, expected: exp(mod.expected(st)), done: mod.done?(st), ev: ev}, st}

          {:error, _} ->
            {%{ok: false, expected: exp(mod.expected(st)), done: mod.done?(st), ev: ev}, st}
        end
      end)

    %{go: go, first: first, lines: lines, params: args}
  end

  defp step_fsm(mod, st, {:send, v}), do: mod.send(st, v)
  defp step_fsm(mod, st, {:recv, v}), do: mod.recv(st, v)

  defp session_test(_stem, traces) do
    body = Enum.map_join(traces, "\n", &session_fn/1)

    """
    package ping

    import (
    	"errors"
    	"testing"
    )

    #{body}
    """
  end

  defp session_fn(%{go: go, first: first, lines: lines, params: []}) do
    steps =
      Enum.map_join(Enum.with_index(lines), "\n", fn {line, i} -> sess_line(go, line, i) end)

    """
    func Test#{go}(t *testing.T) {
    	var zero #{go}
    	var ill *IllegalTransitionError
    	if err := zero.Step(Recv{Value: Nat(0)}); err == nil || !errors.Is(err, ErrIllegalTransition) || !errors.As(err, &ill) || ill.Expected != "start" {
    		t.Fatal(err)
    	}
    	m := New#{go}()
    	if m.Expected() != #{gq(first)} || m.Done() {
    		t.Fatalf("start %s %v", m.Expected(), m.Done())
    	}
    #{steps}
    }
    """
  end

  defp nums_only(%{go: go, first: first, lines: lines, params: [k]}) do
    steps =
      Enum.map_join(Enum.with_index(lines), "\n", fn {line, i} -> sess_line(go, line, i) end)

    """
    package session_calls

    import (
    	"errors"
    	"testing"
    )

    func Test#{go}(t *testing.T) {
    	if _, err := New#{go}(-1); err == nil || !errors.Is(err, ErrArgument) {
    		t.Fatal(err)
    	}
    	var ae *ArgumentError
    	if _, err := New#{go}(-1); !errors.As(err, &ae) {
    		t.Fatal(err)
    	}
    	m, err := New#{go}(#{k})
    	if err != nil {
    		t.Fatal(err)
    	}
    	var ill *IllegalTransitionError
    	if m.Expected() != #{gq(first)} {
    		t.Fatal(m.Expected())
    	}
    #{steps}
    }
    """
  end

  defp sess_line(_go, %{ok: true, expected: expected, done: done, ev: ev}, i) do
    """
    	if err := m.Step(#{go_event(ev)}); err != nil {
    		t.Fatalf("#{i}: %v", err)
    	}
    	if m.Expected() != #{gq(expected)} || m.Done() != #{done} {
    		t.Fatalf("#{i} %s %v", m.Expected(), m.Done())
    	}
    """
  end

  defp sess_line(_go, %{ok: false, expected: expected, done: done, ev: ev}, i) do
    """
    	if err := m.Step(#{go_event(ev)}); err == nil || !errors.Is(err, ErrIllegalTransition) {
    		t.Fatalf("#{i}: %v", err)
    	} else if !errors.As(err, &ill) || ill.Expected != #{gq(expected)} {
    		t.Fatalf("#{i} ill %v", err)
    	}
    	if m.Expected() != #{gq(expected)} || m.Done() != #{done} {
    		t.Fatalf("#{i} stay %s %v", m.Expected(), m.Done())
    	}
    """
  end

  defp monitor_test(go, lines) do
    steps =
      Enum.map_join(Enum.with_index(lines), "\n", fn {line, i} ->
        call = "m.Step(#{gq(line.a)}, #{gq(line.b)}, #{gq(line.l)}, Unit())"

        if line.ok do
          """
          	if err := #{call}; err != nil { t.Fatalf("#{i}: %v", err) }
          	if m.Expected() != #{gq(line.expected)} || m.Done() != #{line.done} { t.Fatalf("#{i} %s", m.Expected()) }
          """
        else
          """
          	if err := #{call}; err == nil || !errors.Is(err, ErrIllegalTransition) { t.Fatalf("#{i}: %v", err) }
          	if m.Expected() != #{gq(line.expected)} || m.Done() != #{line.done} { t.Fatalf("#{i} %s", m.Expected()) }
          """
        end
      end)

    """
    package release_plan

    import (
    	"errors"
    	"testing"
    )

    func TestPlan(t *testing.T) {
    	m := New#{go}()
    #{steps}
    }
    """
  end

  defp rollout_test(%{early: early, keys: keys, choose: choose}) do
    """
    package release_rollout

    import (
    	"errors"
    	"testing"
    )

    func TestRollout(t *testing.T) {
    	m := NewRollout()
    	if m.SharedDone() { t.Fatal("shared") }
    	err := m.Step("site", "release", "front", "deploy", Unit())
    	if err == nil || !errors.Is(err, ErrIllegalTransition) { t.Fatal(err) }
    	var ill *IllegalTransitionError
    	if !errors.As(err, &ill) || ill.Expected != #{gq(early)} { t.Fatalf("%v", err) }
    	if err := m.StepShared("release", "registry", "publish", Unit()); err != nil { t.Fatal(err) }
    	if err := m.StepShared("registry", "release", "published", Unit()); err != nil { t.Fatal(err) }
    	if !m.SharedDone() { t.Fatal("preamble") }
    	if err := m.StepShared("release", "registry", "publish", Unit()); err == nil { t.Fatal("again") }
    	if err := m.Step("site", "release", "front", "deploy", Unit()); err != nil { t.Fatal(err) }
    	if len(m.Keys()) != #{length(keys)} || #{if keys == [], do: "false", else: Enum.map_join(Enum.with_index(keys), " || ", fn {k, i} -> "m.Keys()[#{i}] != #{gq(k)}" end)} {
    		t.Fatalf("keys %v", m.Keys())
    	}
    	if err := m.Step("site", "front", "release", "deployed", Unit()); err != nil { t.Fatal(err) }
    	if err := m.Step("site", "release", "worker", "deploy", Unit()); err != nil { t.Fatal(err) }
    	if err := m.Step("site", "worker", "release", "deployed", Unit()); err != nil { t.Fatal(err) }
    	if err := m.Choose("other", "release", "keep"); err == nil { t.Fatal("other") }
    	if err := m.Choose("site", "release", "nope"); err == nil || !errors.As(err, &ill) || ill.Expected != #{gq(choose)} {
    		t.Fatalf("choose %v", err)
    	}
    	if err := m.Choose("site", "release", "keep"); err != nil { t.Fatal(err) }
    	if err := m.Step("site", "release", "front", "keep", Unit()); err != nil { t.Fatal(err) }
    	if err := m.Step("site", "release", "worker", "keep", Unit()); err != nil { t.Fatal(err) }
    	if !m.Done("site") { t.Fatal("done") }
    }
    """
  end

  defp go_event({:send, v}), do: "Send{Value: #{go_val(v)}}"
  defp go_event({:recv, v}), do: "Recv{Value: #{go_val(v)}}"

  defp go_val(n) when is_integer(n), do: "Nat(#{n})"
  defp go_val(:b0), do: "Bit0()"
  defp go_val(:b1), do: "Bit1()"
  defp go_val({:pick, :b0}), do: "Pick0()"
  defp go_val({:pick, :b1}), do: "Pick1()"
  defp go_val({:b0, fields}) when is_map(fields), do: "Pair(Bit0(), #{go_record(fields)})"
  defp go_val({:b1, fields}) when is_map(fields), do: "Pair(Bit1(), #{go_record(fields)})"
  defp go_val(fields) when is_map(fields), do: go_record(fields)
  defp go_val(list) when is_list(list), do: "Vec(#{Enum.map_join(list, ", ", &go_val/1)})"

  defp go_record(fields) do
    names = fields |> Map.keys() |> Enum.sort()
    ns = Enum.map_join(names, ", ", &gq/1)
    vs = Enum.map_join(names, ", ", &go_val(Map.fetch!(fields, &1)))
    "Record([]string{#{ns}}, []Value{#{vs}})"
  end

  defp exp(:done), do: "done"
  defp exp(:stop), do: "stop"
  defp exp({:send, ty}), do: "send " <> ty_name(ty)
  defp exp({:recv, ty}), do: "recv " <> ty_name(ty)
  defp exp({:send_pick, _}), do: "send pick"
  defp exp({:recv_pick, _}), do: "recv pick"
  defp exp({:message, a, b, l, _}), do: "message #{a} #{b} #{l}"
  defp exp({:shared, inner}), do: "shared " <> exp(inner)
  defp exp({:choose, role, labels}), do: "choose #{role} " <> Enum.join(labels, "|")

  defp ty_name(:nat), do: "nat"
  defp ty_name(:bit), do: "bit"
  defp ty_name(:unit), do: "unit"
  defp ty_name({:pair, _, _}), do: "pair"
  defp ty_name({:record, _}), do: "record"
  defp ty_name({:vec, _, _}), do: "vec"
  defp ty_name({:nat_at_most, _}), do: "nat"
  defp ty_name({:dat, name, _}), do: to_string(name)
  defp ty_name({:data, name, _}), do: to_string(name)
  defp ty_name({:repr, inner, _}), do: ty_name(inner)
  defp ty_name({:bnat, _}), do: "nat"
  defp ty_name(other), do: raise("unmapped type #{inspect(other)}")

  defp gq(a) when is_atom(a), do: gq(Atom.to_string(a))
  defp gq(s) when is_binary(s), do: inspect(s)

  defp child(parent, name), do: Module.concat(parent, Muro.Emit.elixir_alias(name))

  defp fsm!(path) do
    mod = Module.concat(GoLive, "M#{System.unique_integer([:positive])}")
    {:ok, src} = Muro.emit_fsm(path, mod)
    Code.compile_string(src)
    mod
  end

  defp book!(path) do
    {:ok, book} = Muro.Load.file(path)
    book
  end

  defp parse!(text, name) do
    dir = fresh!()
    path = Path.join(dir, name)
    File.write!(path, text)
    book!(path)
  end

  defp render!(path) do
    {:ok, book} = Muro.Load.file(path)
    book = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()
    {:ok, src} = Muro.Emit.Go.render(book, path, [])
    src
  end

  defp go_run(path, test), do: go_check(render!(path), test, false)

  defp go_run_text(name, text, test) do
    dir = fresh!()
    path = Path.join(dir, name)
    File.write!(path, text)
    go_check(render!(path), test, false)
  end

  defp go_check(src, test, _force_race) do
    File.mkdir_p!(@cache)
    File.mkdir_p!(@gopath)
    dir = fresh!()
    test = align_package(src, test)
    File.write!(Path.join(dir, "book.go"), src)
    test_path = Path.join(dir, "book_test.go")
    File.write!(test_path, test)
    File.write!(Path.join(dir, "go.mod"), "module muro_test\n\n#{@go_mod}\n")
    assert {_, 0} = go_cmd(["gofmt", "-w", test_path], cgo: false)
    {listed, 0} = go_cmd(["gofmt", "-l", Path.join(dir, "book.go"), test_path], cgo: false)
    assert String.trim(listed) == ""
    assert {_, 0} = go_cmd(["go", "vet", "./..."], dir: dir, cgo: false)
    assert {_, 0} = go_cmd(["go", "test", "-count=1", "./..."], dir: dir, cgo: false)

    if @have_race do
      assert {_, 0} = go_cmd(["go", "test", "-race", "-count=1", "./..."], dir: dir, cgo: true)
    end
  end

  defp align_package(src, test) do
    case Regex.run(~r/^package ([A-Za-z0-9_]+)/m, src) do
      [_, pkg] ->
        Regex.replace(~r/^package [A-Za-z0-9_]+/m, test, "package #{pkg}", global: false)

      _ ->
        raise "emitted Go has no package clause"
    end
  end

  defp go_cmd([bin | args], opts) do
    dir = Keyword.get(opts, :dir, File.cwd!())
    cgo = Keyword.get(opts, :cgo, false)

    env =
      System.get_env()
      |> Map.merge(%{
        "GOFLAGS" => "-mod=mod",
        "GOPROXY" => "off",
        "GOTOOLCHAIN" => "local",
        "GOCACHE" => @cache,
        "GOPATH" => @gopath,
        "GO111MODULE" => "on",
        "CGO_ENABLED" => if(cgo, do: "1", else: "0")
      })
      |> Enum.to_list()

    cmd_opts = [cd: dir, env: env, stderr_to_stdout: true]

    if timeout() do
      System.cmd(timeout(), ["--kill-after=1", "120", bin | args], cmd_opts)
    else
      System.cmd(bin, args, cmd_opts)
    end
  end

  defp timeout do
    case System.find_executable("timeout") do
      bin when is_binary(bin) ->
        case System.cmd(bin, ["--version"], stderr_to_stdout: true) do
          {out, 0} -> if String.contains?(out, "GNU coreutils"), do: bin, else: nil
          _ -> nil
        end

      _ ->
        nil
    end
  end

  defp fresh! do
    dir = Path.join(System.tmp_dir!(), "muro-go-live-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    dir
  end
end

defmodule GoName do
  def camel(source), do: Muro.Emit.Go.camel(source)
  def package_of(stem), do: Muro.Emit.Go.package_of(stem)
end
