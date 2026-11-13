defmodule Muro.MayFailTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Fail, Parser, Session}

  @refuse "c:mayfail\nmay fail is checked and not emitted"

  @missing "examples/may-fail-missing.muro:15:1: miss: server: get (r : Report) does not handle failure of task"

  @held "examples/may-fail-hold.muro:20:1: held: (server at first get) leads_to (server done) fails in hold (server : server-wait, task : task-work) after task put ok, task died, task dropped ok, server fail; then forever: the meeting has finished"

  test "may fail prints on the party it marks, and buffer stays last" do
    assert {:ok, book} =
             Parser.parse("""
             meet wire : server with task may fail buffer 1
             meet left : server may fail with task
             meet both : server may fail with task may fail buffer 2
             meet plain : server with task
             meet down : server with down
             def may : run Π (n : Nat) → Nat := λ (n : Nat) → n
             def fail : run Nat := 0
             def use : run Nat := may fail
             """)

    meets = for %{kind: :meet} = meet <- book, do: Fail.show_meet(meet)

    assert meets == [
             "meet wire : server with task may fail buffer 1",
             "meet left : server may fail with task",
             "meet both : server may fail with task may fail buffer 2",
             "meet plain : server with task",
             "meet down : server with down"
           ]

    by_name = Map.new(book, fn d -> {d.name, d} end)
    assert by_name["may"].mode == :run
    assert by_name["fail"].mode == :run
    assert by_name["use"].mode == :run
    assert {:app, {:var, "may"}, {:var, "fail"}} = by_name["use"].body
  end

  test "fail is an arm only after a receive, and a bare fail stays a call" do
    assert show("""
           session s := recv Nat end
           conform server : s := get Nat fail
           """) == "get Nat fail"

    assert show("""
           session s := recv Nat end
           conform server : s := get Nat done fail done
           """) == "get Nat done fail done"

    assert show("""
           session s := recv Nat end
           conform server : s := get (r : Nat) done fail (e : Reason) done
           """) == "get (r : Nat) done fail (e : Reason) done"

    assert show("""
           session s := recv Nat (recv Nat end)
           conform server : s := get Nat (get Nat done fail done) fail done
           """) == "get Nat (get Nat done fail done) fail done"

    assert show("""
           session s := recv Nat end
           conform server : s := get Nat done fail (done)
           """) == "get Nat done fail done"

    assert show("""
           session s := end
           conform down : s := done
           """) == "done"
  end

  test "may fail outside a two-party meet is refused" do
    only = Fail.only_message()

    for src <- [
          "may fail\n",
          "session s := may fail end\n",
          "session s := end\nconform p : s := may fail done\n",
          "talk ping := may fail over\n",
          "choreography c\n  roles a, b\n  may fail\n",
          "seat home : may fail pong at home in talk\n",
          "link go : may fail cross a with b in talk\n",
          "endpoint home := may fail ping at local\n",
          "meet wire : server may with task\n",
          "meet wire : server with task may\n",
          """
          session ping := end
          def f : (s : ping) ⊸ ping := may fail
          """
        ] do
      assert {:error, msg} = Parser.parse(src)
      assert msg =~ only
    end
  end

  test "a missing failure arm is refused at the receive" do
    assert {:error, @missing} = Muro.check_file("examples/may-fail-missing.muro")
  end

  test "a failure arm that does not release the slot fails leads_to" do
    assert {:error, @held} = Muro.check_file("examples/may-fail-hold.muro")
  end

  test "a failure arm that releases the slot holds" do
    assert Muro.check_file("examples/may-fail-free.muro") == :ok

    assert Check.temporal_lines() == [
             "temporal freed: holds in 7 reachable states, 11 transitions"
           ]
  end

  test "a meeting that does not mark a party keeps the report path" do
    assert Muro.check_file("examples/may-fail-control.muro") == :ok

    assert Check.temporal_lines() == [
             "temporal released: holds in 3 reachable states, 3 transitions"
           ]
  end

  test "a send needs no failure arm" do
    assert Muro.check_file("examples/may-fail-send.muro") == :ok

    assert Check.temporal_lines() == [
             "temporal freed: holds in 14 reachable states, 21 transitions"
           ]
  end

  test "a failure arm on a party that may not fail is refused" do
    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session task-work := send Report end
             session server-wait := recv Report end
             conform task : task-work := put ok done
             conform server : server-wait :=
               get (r : Report) done
               fail
                 done
             meet wire : server with task buffer 1
             """)

    assert msg =~ "wire: server: get (r : Report) has a failure arm, and task may not fail"
  end

  test "both parties may fail, and each receive needs an arm" do
    assert check("""
           data Report : Type where
             ok : Report
           session left-s := send Report (recv Report end)
           session right-s := recv Report (send Report end)
           conform left : left-s := put ok (get (r : Report) done fail done)
           conform right : right-s := get (r : Report) (put ok done) fail done
           meet both : left may fail with right may fail buffer 1
           """) == :ok

    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session left-s := send Report (recv Report end)
             session right-s := recv Report (send Report end)
             conform left : left-s := put ok (get (r : Report) done)
             conform right : right-s := get (r : Report) (put ok done) fail done
             meet both : left may fail with right may fail buffer 1
             """)

    assert msg =~ "left: get (r : Report) does not handle failure of right"
  end

  test "a reason is a payload the book names" do
    assert check("""
           data Report : Type where
             ok : Report
           session task-work := send Report end
           session server-wait := recv Report end
           conform task : task-work := put ok done
           conform server : server-wait :=
             get (r : Report) done
             fail (e : Report)
               done
           meet wire : server with task may fail buffer 1
           """) == :ok

    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session task-work := send Report end
             session server-wait := recv Report end
             conform task : task-work := put ok done
             conform server : server-wait :=
               get (r : Report) done
               fail (e : Missing)
                 done
             meet wire : server with task may fail buffer 1
             """)

    assert msg =~ "unknown payload Missing"
  end

  test "session %1 refuses a failure arm that stops" do
    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session %1 server-wait := recv Report end
             session task-work := send Report end
             conform server : server-wait :=
               get (r : Report) done
               fail
                 stop
             conform task : task-work := put ok done
             meet wire : server with task may fail buffer 1
             """)

    assert msg =~ "linear channel abandoned"

    assert check("""
           data Report : Type where
             ok : Report
           session %1 server-wait := recv Report end
           session task-work := send Report end
           conform server : server-wait :=
             get (r : Report) done
             fail
               done
           conform task : task-work := put ok done
           meet wire : server with task may fail buffer 1
           """) == :ok
  end

  test "a rendezvous meeting may mark a party" do
    assert check("""
           data Report : Type where
             ok : Report
           session task-work := send Report end
           session server-wait := dual task-work
           conform task : task-work := put ok done
           conform server : server-wait :=
             get (r : Report) done
             fail
               done
           meet wire : server with task may fail
           """) == :ok
  end

  test "every backend refuses may fail, and a meeting without the mark still emits" do
    assert {:ok, src} = Muro.emit_file("examples/may-fail-control.muro", MayFailControl)
    refute src =~ "c:mayfail"

    dir =
      System.tmp_dir!()
      |> Path.join("muro-mayfail-emit-#{System.unique_integer([:positive])}")

    File.mkdir_p!(dir)
    path = Path.join(dir, "free.muro")
    File.cp!("examples/may-fail-free.muro", path)
    on_exit(fn -> File.rm_rf(dir) end)

    assert {:error, @refuse} = Muro.emit_file(path, MayFail)
    assert {:error, @refuse} = Muro.emit_exunit(path, MayFailEmitTest)
    assert {:error, @refuse} = Muro.emit_fsm(path, MayFail)
    assert {:error, @refuse} = Muro.emit_c(path, nif: false)
    assert {:error, @refuse} = Muro.emit_rust(path)
    assert {:error, @refuse} = Muro.emit_zig(path)
    assert {:error, @refuse} = Muro.emit_js(path)
    assert {:error, @refuse} = Muro.emit_asm(path)
    assert {:error, @refuse} = Muro.emit_otp(path)
    assert {:error, @refuse} = Muro.emit_node(path, :a)

    assert File.ls!(dir) == ["free.muro"]
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book, [])
  end

  defp show(src) do
    assert {:ok, book} = Parser.parse(src)
    %{proc: proc} = Enum.find(book, &match?(%{kind: :conform}, &1))
    Session.show_proc(proc)
  end
end
