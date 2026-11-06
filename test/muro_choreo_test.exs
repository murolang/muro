defmodule Muro.ChoreoTest do
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO

  alias Muro.{Check, Choreo, IR, Parser, Session}

  test "a message is send for the sender and recv for the receiver" do
    ping = {:comm, "a", "b", "ping", :unit, :end}

    assert Choreo.project(ping, "a", "b") == {:ok, {:send, :unit, :end}}
    assert Choreo.project(ping, "b", "a") == {:ok, {:recv, :unit, :end}}
    assert Choreo.project(ping, "c", "a") == {:ok, :end}
    assert Choreo.project(ping, "a", "a") == {:error, "self-interaction a"}

    {:ok, there} = Choreo.project(ping, "b", "a")
    {:ok, here} = Choreo.project(ping, "a", "b")
    assert Session.dual(here) == there
  end

  test "a payload is the type written on the message" do
    ping = {:comm, "a", "b", "ping", :nat, :end}
    assert Choreo.project(ping, "a", "b") == {:ok, {:send, :nat, :end}}
    assert Choreo.project(ping, "b", "a") == {:ok, {:recv, :nat, :end}}
  end

  test "a declared payload stops before the next message, label, and declaration" do
    reply = """
    data Reply : Type where
      written : Reply
      invalid : Reply

    choreography ping
      roles a, b
      a -> b : x Reply

    session ab := seen a with b in ping

    def kept : run Nat := 0
    """

    assert check(reply) == :ok
    assert {:ok, book} = Parser.parse(reply)
    ping = Enum.find(book, &(&1.name == "ping"))
    assert ping.body == {:comm, "a", "b", "x", {:dat, "Reply", []}, :end}

    two = """
    data Reply : Type where
      written : Reply
      invalid : Reply

    choreography ping
      roles a, b
      a -> b : x Reply
      b -> a : y Nat

    session ab := seen a with b in ping
    """

    assert check(two) == :ok
    assert {:ok, book} = Parser.parse(two)
    ping = Enum.find(book, &(&1.name == "ping"))

    assert ping.body ==
             {:comm, "a", "b", "x", {:dat, "Reply", []}, {:comm, "b", "a", "y", :nat, :end}}

    paren = """
    data Reply : Type where
      written : Reply

    choreography ping
      roles a, b
      a -> b : x (Reply)

    session ab := seen a with b in ping
    """

    assert check(paren) == :ok
    assert {:ok, book} = Parser.parse(paren)
    ping = Enum.find(book, &(&1.name == "ping"))
    assert ping.body == {:comm, "a", "b", "x", {:dat, "Reply", []}, :end}

    labelled = """
    data Reply : Type where
      written : Reply

    choreography pick
      roles a, b
      a chooses
        go: a -> b : x Reply
        stop: b -> a : y Nat

    session ab := seen a with b in pick
    """

    assert check(labelled) == :ok
    assert {:ok, book} = Parser.parse(labelled)
    pick = Enum.find(book, &(&1.name == "pick"))

    assert pick.body ==
             {:choice, "a",
              [
                {"go", {:comm, "a", "b", "x", {:dat, "Reply", []}, :end}},
                {"stop", {:comm, "b", "a", "y", :nat, :end}}
              ]}
  end

  test "the chooser has a choice even when the arms agree" do
    same = {:comm, "b", "c", "go", :unit, :end}

    choice =
      {:choice, "a", [{"go", same}, {"stop", {:comm, "b", "c", "stop", :unit, :end}}]}

    assert Choreo.project(choice, "a", "b") == {:ok, {:choose, :end, :end}}
    assert Choreo.project(choice, "b", "a") == {:ok, {:branch, :end, :end}}
    assert Choreo.project(choice, "b", "c") == {:ok, {:send, :unit, :end}}
    assert Choreo.project(choice, "c", "b") == {:ok, {:recv, :unit, :end}}
    assert Session.dual(elem(Choreo.project(choice, "b", "c"), 1)) == {:recv, :unit, :end}
  end

  test "more than two branches nest to the right" do
    three =
      {:choice, "a",
       [
         {"l", :end},
         {"m", :end},
         {"r", {:comm, "a", "b", "z", :unit, :end}}
       ]}

    assert Choreo.project(three, "a", "b") ==
             {:ok, {:choose, :end, {:choose, :end, {:send, :unit, :end}}}}

    assert Choreo.project(three, "b", "a") ==
             {:ok, {:branch, :end, {:branch, :end, {:recv, :unit, :end}}}}
  end

  test "a role off the choice is refused when the arms differ" do
    untold =
      {:choice, "coordinator",
       [
         {"commit", {:comm, "alice", "bob", "go", :unit, :end}},
         {"abort", {:comm, "bob", "alice", "stop", :unit, :end}}
       ]}

    assert Choreo.project(untold, "alice", "bob") ==
             {:error, "alice: branches commit and abort disagree"}

    assert Choreo.project(untold, "bob", "alice") ==
             {:error, "bob: branches commit and abort disagree"}

    assert Choreo.project(untold, "coordinator", "alice") == {:ok, {:choose, :end, :end}}
  end

  test "an inner refusal is not reported as the outer choice" do
    inner =
      {:choice, "b",
       [
         {"left", {:comm, "c", "d", "go", :unit, :end}},
         {"right", {:comm, "d", "c", "stop", :unit, :end}}
       ]}

    outer = {:choice, "a", [{"go", inner}, {"stop", :end}]}

    assert Choreo.project(outer, "c", "d") ==
             {:error, "c: branches left and right disagree"}
  end

  test "a choice of one branch is refused, and so is a repeated label" do
    assert Choreo.project({:choice, "a", [{"only", :end}]}, "a", "b") ==
             {:error, "a choice has two branches"}

    assert Choreo.project(
             {:choice, "a", [{"go", :end}, {"go", :end}]},
             "a",
             "b"
           ) == {:ok, {:choose, :end, :end}}
  end

  test "two-phase commit projects, and each pair is dual" do
    path = "examples/two-phase-commit.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    ca = "send Unit (recv Unit (choose (send Unit end) (send Unit end)))"
    ac = "recv Unit (send Unit (branch (recv Unit end) (recv Unit end)))"

    assert Check.choreo_lines() == [
             "choreography two-phase-commit: coordinator with alice = #{ca}",
             "choreography two-phase-commit: coordinator with bob = #{ca}",
             "choreography two-phase-commit: alice with coordinator = #{ac}",
             "choreography two-phase-commit: alice with bob = end",
             "choreography two-phase-commit: bob with coordinator = #{ac}",
             "choreography two-phase-commit: bob with alice = end"
           ]

    assert {:ok, out} = Muro.emit_file(path, ChoreoRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "coordinator"
    refute out =~ "choreography"
    refute out =~ "GenServer"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["kept"]
  end

  test "mix muro.check prints one line per projected pair" do
    dir = System.tmp_dir!() |> Path.join("muro-choreo-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "ping.muro")

    File.write!(path, """
    choreography ping
      roles a, b
      a -> b : ping Nat
    def kept : run Nat := 0
    """)

    version = Mix.Tasks.Muro.version()
    out = capture_io(fn -> assert Mix.Tasks.Muro.Check.run([path]) == :ok end)

    assert out ==
             """
             Muro v#{version}
             choreography ping: a with b = send Nat end
             choreography ping: b with a = recv Nat end
             All terms check. Evidence never becomes a run.
             """
  end

  test "a seen session may be written before the choreography" do
    assert check("""
           session ca := seen coordinator with alice in tpc
           conform coord : ca := put tt done
           choreography tpc
             roles coordinator, alice
             coordinator -> alice : prepare
           """) == :ok
  end

  test "a role the choreography does not name is refused" do
    assert {:error, msg} =
             check("""
             choreography ping
               roles a, b
               a -> c : ping
             """)

    assert msg =~ "unknown role c"
  end

  test "a role does not interact with itself" do
    assert {:error, msg} =
             check("""
             choreography ping
               roles a, b
               a -> a : ping
             """)

    assert msg =~ "self-interaction a"
    refute msg =~ "self-interaction a;"
  end

  test "a role is named once" do
    assert {:error, msg} =
             check("""
             choreography ping
               roles a, b, a
               a -> b : ping
             """)

    assert msg =~ "duplicate role a"
  end

  test "a branch label is named once" do
    assert {:error, msg} =
             check("""
             choreography arm
               roles a, b
               a chooses
                 go: a -> b : x
                 go: a -> b : y
             """)

    assert msg =~ "duplicate branch go"
  end

  test "a choice has two branches" do
    assert {:error, msg} =
             check("""
             choreography arm
               roles a, b
               a chooses
                 only: a -> b : x
             """)

    assert msg =~ "a choice has two branches"
  end

  test "three branches nest, and a label-only difference merges" do
    assert check("""
           choreography three
             roles a, b
             a chooses
               l: end
               m: end
               r: a -> b : z
           session ab := seen a with b in three
           conform taker : ab := pick0 done
           """) == :ok

    assert check("""
           choreography labels
             roles a, b, c
             a chooses
               go: b -> c : go
               stop: b -> c : stop
           session bc := seen b with c in labels
           conform sender : bc := put tt done
           """) == :ok
  end

  test "untold disagreement names the role and the branches" do
    src = File.read!("test/fixtures/choreo_untold.muro")
    assert {:error, msg} = check(src)
    assert msg =~ "alice: branches commit and abort disagree"
    assert msg =~ "bob: branches commit and abort disagree"
    refute msg =~ "coordinator: branches"
  end

  test "an unknown choreography is an unknown talk" do
    assert {:error, msg} =
             check("""
             session ping := seen a with b in gone
             """)

    assert msg =~ "unknown talk gone"
  end

  test "choreography is a keyword only when a name follows" do
    assert check("""
           def choreography : run Nat := 0
           def roles : run Nat := 0
           def chooses : run Nat := 0
           """) == :ok

    assert check("""
           data Box : Type where
             choreography : Box

           def z : run Box := choreography
           """) == :ok
  end

  test "a nested choice closes before the next branch" do
    assert check("""
           choreography nest
             roles a, b
             a chooses
               go: b chooses
                 left: a -> b : x
                 right: b -> a : y
               end
               stop: a -> b : z
           session ab := seen a with b in nest
           conform taker : ab := pick0 (cover (put tt done) (get Unit done))
           """) == :ok
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end
