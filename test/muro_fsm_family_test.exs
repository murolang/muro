defmodule Muro.FsmFamilyTest do
  use ExUnit.Case, async: false

  alias Muro.Family.Graph

  @moduletag timeout: 180_000

  @path "examples/keyed-slots.muro"

  setup_all do
    {disp, parent, src} = compile!(@path)
    on_exit(&purge_fam/0)
    [disp: disp, parent: parent, src: src]
  end

  test "the production trace holds, opens, and releases", %{disp: disp, parent: parent} do
    search = search!()
    assert length(search.states) == 171_649
    assert search.transitions == 729_184

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:open, 2, state} = disp.arrive(state, "b", :init, 0)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:ok, [], state} = disp.resolved(state, 1)
    assert {:ok, [], _state} = disp.resolved(state, 2)

    trace = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:resolved, 0},
      {:resolved, 1},
      {:resolved, 2}
    ]

    assert :ok = disp.check_trace(trace)

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :signal, 1, :held, 1},
      {:arrive, "b", :init, 0, :open, 2},
      {:resolved, 0, [{1, "a", :signal}]},
      {:resolved, 1, []},
      {:resolved, 2, []}
    ])

    server = Module.concat(parent, ServerWait)
    task = Module.concat(parent, TaskWork)
    assert function_exported?(server, :init, 0)
    assert function_exported?(server, :down, 1)
    assert function_exported?(task, :send, 2)
    refute function_exported?(disp, :send, 2)
    assert {:recv, {:data, "Report", []}} = server.expected(server.init())
  end

  test "resolved of an unknown id is an error and does not raise", %{disp: disp} do
    state = disp.new()

    assert {:error, {:unknown, 0}} = disp.resolved(state, 0)
    assert {:error, {:unknown, 99}} = disp.resolved(state, 99)
    assert {:error, {0, {:unknown, 4}}} = disp.check_trace([{:resolved, 4}])
    assert {:error, {:state, :nope}} = disp.resolved(:nope, 0)
    assert {:error, {:state, :nope}} = disp.arrive(:nope, "a", :init, 0)
    assert {:error, {:trace, :nope}} = disp.check_trace(:nope)

    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:error, {:held, 1}} = disp.resolved(state, 1)
    assert {:error, {:kind, :nope}} = disp.arrive(state, "a", :nope, 3)
    assert {:error, {:kind, "init"}} = disp.arrive(state, "a", "init", 3)
    assert {:error, {:index, -1}} = disp.arrive(state, "a", :signal, -1)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :signal, 0)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(state, 0)
    assert {:open, 2, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:duplicate, "a", 1}} = disp.arrive(state, "a", :signal, 1)

    assert {:error, {2, {:unknown, 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:resolved, 0},
               {:resolved, 0}
             ])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :signal, 5)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert {:open, 1, _state} = disp.arrive(state, "a", :signal, 3)
  end

  test "a later signal opens before its init arrives, and an earlier signal blocks the next",
       %{disp: disp} do
    search = search!()
    g = search.g

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :signal, 1)
    assert {:open, 1, _state} = disp.arrive(state, "a", :init, 0)

    {_assigned, gst} =
      lockstep!(search, [
        {:arrive, "a", :signal, 1, :open, 0},
        {:arrive, "a", :init, 0, :open, 1}
      ])

    signal = Enum.find(g.instances, &(&1.key == "a" and &1.kind == "signal" and &1.index == 1))
    init = Enum.find(g.instances, &(&1.key == "a" and &1.kind == "init"))
    assert match?({:run, _, _, _}, Graph.phase(gst, signal.id))
    assert match?({:run, _, _, _}, Graph.phase(gst, init.id))
    refute Graph.known_at_open?(gst, signal.id, init.id)

    assert Graph.holds?(
             g,
             {:imp, {:opened, "a", "signal"}, {:resolved, "a", "init"}},
             gst
           )

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :signal, 2)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:held, _} = hold_of(disp, state, 2)
    assert {:ok, [{2, "a", :signal}], _state} = disp.resolved(state, 1)

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :signal, 1, :held, 1},
      {:arrive, "a", :signal, 2, :held, 2},
      {:resolved, 0, [{1, "a", :signal}]},
      {:resolved, 1, [{2, "a", :signal}]}
    ])
  end

  test "a second init opens at once and the signal waits for both", %{disp: disp} do
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:open, 1, state} = disp.arrive(state, "a", :init, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :signal, 2)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert {:held, _} = hold_of(disp, state, 2)
    assert {:ok, [{2, "a", :signal}], _state} = disp.resolved(state, 1)

    search = search!(two_inits())

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :init, 1, :open, 1},
      {:arrive, "a", :signal, 2, :held, 2},
      {:resolved, 0, []},
      {:resolved, 1, [{2, "a", :signal}]}
    ])
  end

  test "every dispatcher-accepted sequence over the script is a run of the family graph",
       %{disp: disp} do
    search = search!()
    assert length(search.states) == 171_649
    assert search.transitions == 729_184

    n =
      walk(
        disp,
        search,
        disp.new(),
        search.g.start,
        search.g.instances,
        %{},
        MapSet.new(),
        []
      )

    assert n > 1
  end

  test "the state keeps only the live instances", %{disp: disp} do
    state = disp.new()
    assert {:open, _, state} = disp.arrive(state, "stay", :init, 0)
    live = %{by: state.by, id: state.id}
    n0 = state.n

    state =
      Enum.reduce(1..40, state, fn n, state ->
        assert {:open, id, state} = disp.arrive(state, "a", :init, n)
        assert {:held, sig, state} = disp.arrive(state, "a", :signal, n + 1_000)
        assert {:open, other, state} = disp.arrive(state, "b", :init, n)
        assert {:ok, [{^sig, "a", :signal}], state} = disp.resolved(state, id)
        assert {:ok, [], state} = disp.resolved(state, sig)
        assert {:ok, [], state} = disp.resolved(state, other)
        assert map_size(state.id) == 1
        assert map_size(state.by) == 1
        assert %{by: state.by, id: state.id} == live
        rows = state.by |> Map.values() |> Enum.map(&map_size/1) |> Enum.sum()
        assert map_size(state.id) == rows
        state
      end)

    assert state.n == n0 + 120
    assert state.by["stay"][0] == {0, :init, :open}
    refute inspect(state.by) =~ ":resolved"
    refute inspect(state.id) =~ ":resolved"
  end

  test "a call reads only the key it names", %{disp: disp} do
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "b", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "b", :signal, 1)

    poisoned =
      state
      |> Map.update!(:by, &Map.put(&1, "a", :poison))
      |> Map.update!(:id, &Map.put(&1, 99, :poison))

    assert {:open, 2, next} = disp.arrive(poisoned, "b", :init, 2)
    assert next.by["a"] == :poison
    assert next.id[99] == :poison
    assert next.by["b"][0] == {0, :init, :open}
    assert next.by["b"][2] == {2, :init, :open}

    assert {:ok, [{1, "b", :signal}], back} = disp.resolved(next, 0)
    assert back.by["a"] == :poison
    assert back.id[99] == :poison
    refute Map.has_key?(back.id, 0)
    assert back.by["b"][1] == {1, :signal, :open}
    assert back.by["b"][2] == {2, :init, :open}

    assert {:error, {:state, _}} = disp.arrive(poisoned, "a", :init, 0)
    assert {:error, {:state, _}} = disp.resolved(poisoned, 99)
    assert {:error, {:held, 1}} = disp.resolved(poisoned, 1)

    dirty = put_in(state, [:by, "b", 9], :poison)
    assert {:open, _, kept} = disp.arrive(dirty, "b", :init, 3)
    assert kept.by["b"][9] == :poison
    assert {:error, {:held, 1}} = disp.resolved(dirty, 1)
    assert {:error, {:state, _}} = disp.resolved(dirty, 0)
    assert {:error, {:state, _}} = disp.arrive(dirty, "b", :signal, 4)
  end

  test "finish resolves the instance on the session's end", %{
    disp: disp,
    parent: parent,
    src: src
  } do
    assert src =~ "def new, do: %{n: 0, by: %{}, id: %{}}"
    assert src =~ "def finish(session_state, family_state, id)"
    assert src =~ "def finish(session_state, step, family_state, id)"
    assert src =~ "defp party(:server)"
    refute src =~ "{:error, {:resolved"

    server = Module.concat(parent, ServerWait)
    task = Module.concat(parent, TaskWork)
    assert function_exported?(server, :finish, 3)
    assert function_exported?(server, :finish, 4)
    assert function_exported?(task, :finish, 3)
    assert function_exported?(task, :finish, 4)

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)

    assert {:ok, [{1, "a", :signal}], done} = server.finish(server.init(), :down, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(done, 0)
    assert {:ok, [], _} = disp.resolved(done, 1)

    assert {:ok, [{1, "a", :signal}], _} = server.finish(server.init(), {:recv, :ok}, state, 0)
    {:ok, reported} = server.recv(server.init(), :ok)
    assert server.done?(reported)
    assert {:ok, [{1, "a", :signal}], _} = server.finish(reported, state, 0)

    assert {:error, _} = server.finish(server.init(), {:send, :ok}, state, 0)
    assert {:error, _} = server.finish(server.init(), {:recv, :nope}, state, 0)
    assert {:error, {:step, :nope}} = server.finish(server.init(), :nope, state, 0)
    assert {:error, _} = server.finish(:nope, state, 0)
    assert {:error, _} = server.finish(:nope, :down, state, 0)
    assert {:error, {:held, 1}} = server.finish(server.init(), :down, state, 1)
    assert {:error, {:unknown, 9}} = server.finish(server.init(), :down, state, 9)
    assert {:ok, [{1, "a", :signal}], _} = disp.resolved(state, 0)

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:ok, [], freed} = task.finish(task.init(), {:send, :ok}, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(freed, 0)
    assert {:error, _} = task.finish(task.init(), :down, state, 0)
    assert {:ok, [], _} = disp.resolved(state, 0)
  end

  test "check_trace names an instance whose session finished without resolved", %{disp: disp} do
    trace = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:server, 0, :down},
      {:resolved, 0},
      {:task, 1, {:send, :ok}},
      {:resolved, 1},
      {:server, 2, {:recv, :ok}},
      {:resolved, 2}
    ]

    assert :ok = disp.check_trace(trace)

    leaked = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:server, 0, :down}
    ]

    assert {:error, {:unresolved, 0, "a", :init}} = disp.check_trace(leaked)

    assert {:error, {:unresolved, 0, "a", :init}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:task, 0, {:send, :ok}}
             ])

    assert {:error, {0, {:unknown, 4}}} = disp.check_trace([{:server, 4, :down}])

    assert {:error, {2, {:held, 1}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :signal, 1},
               {:server, 1, {:recv, :ok}}
             ])

    assert {:error, {1, {:party, :nope}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:nope, 0, :down}
             ])
  end

  test "down into stop is not a resolved instance" do
    {disp, parent, _src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session task-work := send Report end
      session server-wait := recv Report end

      conform task : task-work := put ok done

      conform server : server-wait :=
        get (r : Report) done
        fail
          stop

      meet hold : server with task may fail buffer 1

      family slots : hold per key of Event
        init never held
      """)

    server = Module.concat(parent, ServerWait)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:unfinished, :stop}} = server.finish(server.init(), :down, state, 0)
    assert {:ok, [], _} = disp.resolved(state, 0)

    assert {:error, {2, {:unfinished, 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:server, 0, :down},
               {:resolved, 0}
             ])

    assert :ok =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:server, 0, :down}
             ])
  end

  test "a send then a death resolves only when the trace says so" do
    {disp, parent, _src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session task-work := recv Nat (send Report end)
      session server-work := send Nat (recv Report end)

      conform task : task-work :=
        get (n : Nat) (put ok done)

      conform server : server-work :=
        put 0 (get (r : Report) done fail done)

      meet wire : server with task may fail buffer 1

      family slots : wire per key of Event
        init never held
      """)

    server = Module.concat(parent, ServerWork)
    opened = [{:arrive, "a", :init, 0}, {:server, 0, {:send, 0}}]

    assert {:error, {2, {:unfinished, 0}}} = disp.check_trace(opened ++ [{:resolved, 0}])

    assert {:error, {:unresolved, 0, "a", :init}} =
             disp.check_trace(opened ++ [{:server, 0, {:recv, :ok}}])

    assert :ok = disp.check_trace(opened ++ [{:server, 0, :down}, {:resolved, 0}])
    assert :ok = disp.check_trace(opened ++ [{:server, 0, {:recv, :ok}}, {:resolved, 0}])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:unfinished, _}} = server.finish(server.init(), {:send, 0}, state, 0)
    assert {:ok, [], _} = disp.resolved(state, 0)
    {:ok, mid} = server.send(server.init(), 0)
    assert {:ok, [], freed} = server.finish(mid, :down, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(freed, 0)
    assert {:ok, [], _} = server.finish(mid, {:recv, :ok}, state, 0)
  end

  test "a meeting still in progress is not unresolved" do
    {disp, _parent, _src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session task-work := recv Nat (send Report end)
      session server-work := send Nat (recv Report end)

      conform task : task-work :=
        get (n : Nat) (put ok done)

      conform server : server-work :=
        put 0 (get (r : Report) done fail done)

      meet wire : server with task may fail buffer 1

      family slots : wire per key of Event
        init never held
      """)

    # The server has reached done. The task has received and has not sent.
    open = [
      {:arrive, "a", :init, 0},
      {:server, 0, {:send, 0}},
      {:task, 0, {:recv, 0}},
      {:server, 0, {:recv, :ok}}
    ]

    assert :ok = disp.check_trace(open)
    assert {:error, {4, {:unfinished, 0}}} = disp.check_trace(open ++ [{:resolved, 0}])

    done = open ++ [{:task, 0, {:send, :ok}}]
    assert {:error, {:unresolved, 0, "a", :init}} = disp.check_trace(done)
    assert :ok = disp.check_trace(done ++ [{:resolved, 0}])
  end

  test "finish refuses an end two families share and does not resolve" do
    {disp, parent, src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session server-wait := recv Report end
      session task-work := send Report end
      session peer-work := send Report end

      conform server : server-wait :=
        get (r : Report) done
        fail
          done

      conform other : server-wait :=
        get (r : Report) done
        fail
          done

      conform task : task-work := put ok done

      conform peer : peer-work := put ok done

      meet slot : server with task may fail buffer 1

      meet side : other with peer may fail buffer 1

      family slots : slot per key of Event
        init never held

      family spare : side per key of Event
        init never held
      """)

    assert src =~ "{:error, {:family, [:Slots, :Spare]}}"

    server = Module.concat(parent, ServerWait)
    task = Module.concat(parent, TaskWork)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)

    assert {:error, {:family, [:Slots, :Spare]}} =
             server.finish(server.init(), {:recv, :ok}, state, 0)

    assert {:ok, [], _} = disp.resolved(state, 0)

    {:ok, done} = server.recv(server.init(), :ok)
    assert server.done?(done)
    assert {:error, {:family, [:Slots, :Spare]}} = server.finish(done, state, 0)
    assert {:ok, [], _} = disp.resolved(state, 0)

    assert {:ok, [], freed} = task.finish(task.init(), {:send, :ok}, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(freed, 0)
  end

  defp hold_of(disp, state, id) do
    case disp.resolved(state, id) do
      {:error, {:held, ^id}} -> {:held, id}
      other -> flunk("expected the instance to stay held, got #{inspect(other)}")
    end
  end

  defp walk(disp, search, dst, gst, remaining, assigned, resolved, trace) do
    assert {:error, {:unknown, _}} = disp.resolved(dst, -1)

    arrived =
      Enum.reduce(remaining, 0, fn inst, acc ->
        kind = String.to_atom(inst.kind)

        case disp.arrive(dst, inst.key, kind, inst.index) do
          {phase, id, dst2} when phase in [:open, :held] ->
            tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}

            case step_to(search, gst, tag) do
              {:ok, gst2} ->
                left = Enum.reject(remaining, &(&1.id == inst.id))
                step = {:arrive, inst.key, kind, inst.index, phase}

                acc +
                  walk(
                    disp,
                    search,
                    dst2,
                    gst2,
                    left,
                    Map.put(assigned, id, inst),
                    resolved,
                    [step | trace]
                  )

              {:error, tags} ->
                flunk(mismatch(trace, tag, tags))
            end

          other ->
            flunk("dispatcher refused #{inspect(inst)} after #{show(trace)}: #{inspect(other)}")
        end
      end)

    finished =
      Enum.reduce(assigned, 0, fn {id, inst}, acc ->
        if MapSet.member?(resolved, id) do
          acc
        else
          case disp.resolved(dst, id) do
            {:error, _} ->
              case Graph.phase(gst, inst.id) do
                :held ->
                  acc

                other ->
                  flunk(
                    "dispatcher refused a running #{who(inst)} after #{show(trace)}, graph phase #{inspect(other)}"
                  )
              end

            {:ok, released, dst2} ->
              case realize(search, gst, inst.id) do
                {:ok, gst2, opened} ->
                  got = MapSet.new(released, &graph_id(assigned, &1))

                  if got == MapSet.new(opened) do
                    step = {:resolved, id, released}

                    acc +
                      walk(
                        disp,
                        search,
                        dst2,
                        gst2,
                        remaining,
                        assigned,
                        MapSet.put(resolved, id),
                        [step | trace]
                      )
                  else
                    flunk(
                      "release mismatch after #{show(trace)}: dispatcher #{inspect(released)} graph #{inspect(opened)}"
                    )
                  end

                :error ->
                  flunk(
                    "accepted resolve of #{who(inst)} is not a graph run after #{show(trace)}"
                  )
              end
          end
        end
      end)

    if arrived + finished == 0, do: 1, else: arrived + finished
  end

  defp lockstep!(search, trace) do
    Enum.reduce(trace, {%{}, search.g.start}, fn step, {assigned, gst} ->
      case step do
        {:arrive, key, kind, index, phase, id} ->
          inst = find_inst!(search.g, key, kind, index)
          tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}

          case step_to(search, gst, tag) do
            {:ok, gst} -> {Map.put(assigned, id, inst), gst}
            {:error, tags} -> flunk(mismatch(trace, tag, tags))
          end

        {:resolved, id, released} ->
          inst = Map.fetch!(assigned, id)

          case realize(search, gst, inst.id) do
            {:ok, gst, opened} ->
              got = MapSet.new(released, &graph_id(assigned, &1))

              assert MapSet.new(opened) == got,
                     "release mismatch: dispatcher #{inspect(released)} graph #{inspect(opened)}"

              {assigned, gst}

            :error ->
              flunk("resolve of #{who(inst)} is not a graph run")
          end
      end
    end)
  end

  defp find_inst!(g, key, kind, index) do
    kind = Atom.to_string(kind)

    Enum.find(g.instances, &(&1.key == key and &1.kind == kind and &1.index == index)) ||
      flunk("script has no #{key} #{kind} #{index}")
  end

  defp graph_id(assigned, {id, key, kind}) do
    inst = Map.fetch!(assigned, id)
    assert inst.key == key
    assert inst.kind == Atom.to_string(kind)
    inst.id
  end

  defp realize(search, state, gid) do
    case bfs(search, gid, MapSet.new(), [state]) do
      nil ->
        :error

      resolved ->
        ids = held_opens(search, resolved)

        case apply_opens(search, resolved, Enum.sort(ids)) do
          {:ok, dest} -> {:ok, dest, ids}
          :error -> :error
        end
    end
  end

  defp bfs(_search, _gid, _seen, []), do: nil

  defp bfs(search, gid, seen, [state | rest]) do
    if MapSet.member?(seen, state) do
      bfs(search, gid, seen, rest)
    else
      steps = steps_of(search, state)

      case resolving(steps, gid) do
        {_tag, dest} ->
          dest

        nil ->
          more =
            for {tag, dest} <- steps,
                match?({:meet, ^gid, _}, tag) or tag == {:retry, gid},
                do: dest

          bfs(search, gid, MapSet.put(seen, state), rest ++ more)
      end
    end
  end

  defp resolving(steps, gid) do
    Enum.find(steps, fn {tag, _} -> tag == {:resolve, gid} end) ||
      Enum.find(steps, fn {tag, _} -> tag == {:give_up, gid} end)
  end

  defp held_opens(search, state) do
    steps = steps_of(search, state)

    for inst <- search.g.instances,
        Graph.phase(state, inst.id) == :held,
        Enum.any?(steps, fn {tag, _} -> tag == {:open, inst.id} end),
        do: inst.id
  end

  defp apply_opens(_search, state, []), do: {:ok, state}

  defp apply_opens(search, state, [id | rest]) do
    case step_to(search, state, {:open, id}) do
      {:ok, state} -> apply_opens(search, state, rest)
      {:error, _} -> :error
    end
  end

  defp step_to(search, state, tag) do
    case Enum.find(steps_of(search, state), fn {t, _} -> t == tag end) do
      {_, dest} -> {:ok, dest}
      nil -> {:error, steps_of(search, state) |> Enum.map(&elem(&1, 0))}
    end
  end

  defp steps_of(search, state) do
    case Map.fetch(search.edges, state) do
      {:ok, steps} -> steps
      :error -> Graph.edges(search.g, state)
    end
  end

  defp mismatch(trace, tag, tags) do
    "graph has no #{inspect(tag)} after #{show(trace)}; edges #{inspect(tags)}"
  end

  defp show(trace) when is_list(trace), do: inspect(Enum.reverse(trace))

  defp who(inst), do: "#{inst.key} #{inst.kind} #{inst.index}"

  defp two_inits do
    [
      %{id: 0, key: "a", kind: "init", index: 0},
      %{id: 1, key: "a", kind: "init", index: 1},
      %{id: 2, key: "a", kind: "signal", index: 2}
    ]
  end

  defp search!(instances \\ nil) do
    src = File.read!(@path)
    assert {:ok, book} = Muro.Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    opts = if instances, do: [instances: instances], else: []
    assert {:ok, search} = Graph.prepare(book, family, opts)
    search
  end

  defp compile!(path) do
    parent = Module.concat(["FsmFam#{System.unique_integer([:positive])}"])
    assert {:ok, src} = Muro.emit_fsm(path, parent)
    assert src =~ "defmodule Slots do"
    assert src =~ "def new"
    assert src =~ "def arrive"
    assert src =~ "def resolved"
    assert src =~ "def check_trace"
    refute src =~ "GenServer"
    refute src =~ "Muro."
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(src) end)

    warnings =
      Enum.filter(diags, &(match?(%{severity: :warning}, &1) or match?({:warning, _}, &1)))

    assert warnings == [], inspect(warnings, limit: 20)
    assert parent in Enum.map(mods, &elem(&1, 0))
    {Module.concat(parent, Slots), parent, src}
  end

  defp compile_src!(src) do
    dir = System.tmp_dir!() |> Path.join("muro-fsm-fam-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    compile!(path)
  end

  defp purge_fam do
    for {mod, _} <- :code.all_loaded(),
        name = Atom.to_string(mod),
        String.starts_with?(name, "Elixir.FsmFam") do
      :code.purge(mod)
      :code.delete(mod)
    end
  end
end
