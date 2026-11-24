defmodule Muro.ContractTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.{Check, Contract, Parser}
  alias Muro.Family.Graph

  @moduletag timeout: 120_000

  setup do
    on_exit(&purge/0)
    :ok
  end

  test "a contract entry and the redelivery mark parse, and the words stay names" do
    assert {:ok, book} =
             Parser.parse("""
             family slots : wire per key of Event may redeliver
               init never held
             contract slots : idempotent init
             contract other : idempotent init skip
             temporal plain : slots := always true
             temporal waived : slots := always true relies idempotent init
             def contract : run Nat := 0
             def may : run Π (n : Nat) → Nat := λ (n : Nat) → n
             def redeliver : run Nat := 0
             def app : run Nat := may redeliver
             def idempotent : run Nat := 0
             def relies : run Nat := 0
             def skip : run Nat := 0
             def init : run Nat := 0
             def dense : run Nat := 0
             def dedupe : run Nat := 0
             data Box : Type where
               contract : Box
             """)

    [slots] = for %{kind: :family} = d <- book, do: d
    assert slots.redeliver == true

    contracts = for %{kind: :contract} = d <- book, do: d

    assert [
             %{family: "slots", entry: :idempotent_init, skip: false},
             %{family: "other", entry: :idempotent_init, skip: true}
           ] = contracts

    by_name = Map.new(for %{name: name} = d <- book, is_binary(name), do: {name, d})
    assert by_name["plain"].relies == nil
    assert by_name["waived"].relies == :idempotent_init
    assert {:app, {:var, "may"}, {:var, "redeliver"}} = by_name["app"].body
    assert by_name["contract"].mode == :run

    assert check("""
           def contract : run Nat := 0
           def may : run Π (n : Nat) → Nat := λ (n : Nat) → n
           def redeliver : run Nat := 0
           def app : run Nat := may redeliver
           def idempotent : run Nat := 0
           def relies : run Nat := 0
           def skip : run Nat := 0
           def init : run Nat := 0
           def dense : run Nat := 0
           def dedupe : run Nat := 0
           """) == :ok

    [box] = for %{kind: :data, name: "Box"} = d <- book, do: d
    assert Enum.any?(box.ctors, &(&1.name == "contract"))
    refute Enum.any?(book, &(&1[:kind] == :contract and &1[:family] == "Box"))
  end

  test "the closed list refuses a name that is not in this version" do
    assert parse_error("contract slots : in order\n") =~ "in order is not in this version"
    assert parse_error("contract slots : dense\n") =~ "dense is not in this version"
    assert parse_error("contract slots : dedupe\n") =~ "dedupe is not in this version"
    assert parse_error("contract slots : foo\n") =~ "unknown contract entry foo"
    assert parse_error("contract slots : idempotent\n") =~ "expected init"
    assert parse_error("contract slots : in sideways\n") =~ "unknown contract entry in"

    assert parse_error("contract slots : may redeliver\n") =~
             "may redeliver is a mark on a family, not a contract entry"

    assert parse_error("contract slots : may fail\n") =~
             "may fail is only a mark on a party of a meet"

    for {entry, msg} <- [
          {"in order", "in order is not in this version"},
          {"dense", "dense is not in this version"},
          {"dedupe", "dedupe is not in this version"},
          {"foo", "unknown contract entry foo"},
          {"idempotent", "expected init"}
        ] do
      assert parse_error("temporal t : slots := always true relies #{entry}\n") =~ msg
    end

    assert parse_error("temporal t : slots := always true relies may redeliver\n") =~
             "may redeliver is a mark, not a contract a formula relies on"

    assert parse_error("temporal t : slots := always true relies idempotent init skip\n") =~
             "skip is a mark on a contract entry"
  end

  test "may redeliver is only a mark on a family" do
    assert parse_error("may redeliver\n") =~ "may redeliver is only a mark on a family"

    assert parse_error("""
           session ping := send Nat end
           session pong := recv Nat end
           conform a : ping := put 0 done
           conform b : pong := get (n : Nat) done
           meet wire : a with b may redeliver buffer 1
           """) =~ "may redeliver is only a mark on a family"

    assert parse_error(once(" may fail")) =~ "may fail is only a mark on a party of a meet"

    assert parse_error("""
           #{once()}
             may redeliver
           """) =~ "may redeliver is only a mark on a family"
  end

  test "a reserved entry is refused by the checker with the same words" do
    for entry <- [:in_order, :dense, :dedupe] do
      decl = %{kind: :contract, family: "slots", entry: entry, skip: false, loc: {1, 1}}
      assert {:error, msg} = Contract.check([], decl)
      assert msg =~ "#{Contract.spell(entry)} is not in this version"
    end
  end

  test "a contract is not an axiom, and a run that reaches one is still refused" do
    assert {:error, msg} =
             check("""
             axiom lem : evidence Nat
             def bad : run internal Nat := lem
             #{slots(contract: :assert)}
             """)

    assert msg =~ "bad: a run depends on lem"
    refute msg =~ "depends on contract"
    assert Check.temporal_lines() == []
    assert Check.axiom_lines() == []
  end

  test "a book with no contract still prints an axiom line and stays silent on contracts" do
    assert check("""
           axiom lem : evidence Nat
           def use : evidence Nat := lem
           #{slots()}
           """) == :ok

    assert Check.axiom_lines() == ["use: depends on lem"]
    assert Check.temporal_lines() == ["family slots: wire per key of Event"]
    refute Enum.any?(Check.temporal_lines(), &String.contains?(&1, "depends on"))
    refute Enum.any?(Check.temporal_lines(), &String.contains?(&1, "redeliver"))
  end

  test "may redeliver is a family line and not a depends line" do
    assert check(slots(redeliver: true)) == :ok
    assert Check.temporal_lines() == ["family slots: wire per key of Event may redeliver"]
    assert Check.axiom_lines() == []
  end

  test "a formula relies on idempotent init only when it says so" do
    src = """
    #{slots(contract: :assert, redeliver: true)}
    temporal plain : slots := always true
    temporal waived : slots := always true relies idempotent init
    """

    assert check(src) == :ok
    assert [family, plain, waived, depends] = Check.temporal_lines()
    assert family == "family slots: wire per key of Event may redeliver"
    assert plain =~ ~r/^temporal plain: holds in (\d+) reachable states, (\d+) transitions$/
    assert waived =~ ~r/^temporal waived: holds in \d+ reachable states, \d+ transitions$/
    assert counts(plain) == counts(waived)
    assert depends == "waived: depends on contract idempotent init"
    refute plain =~ "depends on"
  end

  test "a formula cannot rely on a contract the family does not declare" do
    src = """
    #{slots()}
    temporal bad : slots := always true relies idempotent init
    """

    assert {:error, msg} = no_family_graph(fn -> check(src) end)
    assert msg =~ "bad: assumes contract idempotent init, which slots does not declare"
  end

  test "a formula over a meeting does not rely on a contract" do
    src = """
    #{once()}
    temporal bad : wire := always true relies idempotent init
    """

    assert {:error, msg} = check(src)
    assert msg =~ "bad: a formula over a meeting does not rely on a contract"
  end

  test "the contract has to name a family that can open init" do
    assert {:error, msg} = check("contract slots : idempotent init\n")
    assert msg =~ "unknown family slots"

    assert {:error, msg} =
             check("""
             data Event : Type where
               signal : Event
             session ping := send Nat end
             session pong := recv Nat end
             conform a : ping := put 0 done
             conform b : pong := get (n : Nat) done
             meet wire : a with b buffer 1
             family slots : wire per key of Event
               signal never held
             contract slots : idempotent init
             """)

    assert msg =~ "no constructor init"

    assert {:error, msg} =
             check("""
             #{slots(contract: :assert)}
             contract slots : idempotent init skip
             """)

    assert msg =~ "duplicate contract idempotent init"
    refute msg =~ "1:1: duplicate"
  end

  test "may redeliver widens the family graph and leaves the state count" do
    assert check("""
           #{once()}
           temporal safe : slots := always true
           temporal opens : slots := forall (k : key). eventually (opened k init)
           """) == :ok

    [family, safe, opens] = Check.temporal_lines()
    assert family == "family slots: wire per key of Event"
    assert opens =~ "temporal opens: holds in "
    {states, transitions} = counts(safe)

    assert check("""
           #{once(" may redeliver")}
           temporal safe : slots := always true
           """) == :ok

    [marked, marked_safe] = Check.temporal_lines()
    assert marked == "family slots: wire per key of Event may redeliver"
    assert {^states, marked_transitions} = counts(marked_safe)
    assert marked_transitions == transitions + states

    assert {:error, msg} =
             check("""
             #{once(" may redeliver")}
             temporal opens : slots := forall (k : key). eventually (opened k init)
             """)

    assert msg =~ "a message is redelivered"
    assert msg =~ "opens:"
  end

  test "the redelivery loop is one self-loop on every reachable state" do
    {:ok, plain} = prepare(once())
    {:ok, marked} = prepare(once(" may redeliver"))

    assert length(plain.states) == length(marked.states)
    assert marked.transitions == plain.transitions + length(marked.states)

    refute Enum.any?(plain.states, fn state ->
             Enum.any?(Graph.edges(plain.g, state), &match?({:redeliver, _}, &1))
           end)

    assert Enum.all?(marked.states, fn state ->
             tags = Graph.edges(marked.g, state)
             Enum.count(tags, &match?({:redeliver, ^state}, &1)) == 1
           end)
  end

  test "no contract emits the same dispatcher, including under may redeliver" do
    plain = emit!(slots())
    marked = emit!(slots(redeliver: true))
    assert plain == marked
    assert plain =~ "defp fresh(rows, key, index, st) do"
    refute plain =~ "defp fresh(rows, key, index, st, kind) do"
    refute plain =~ ":idempotent_init"
    refute plain =~ "{:contract,"

    {disp, _src} = compile!(slots())
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert {:ok, _, done} = disp.resolved(state, 0)
    assert {:error, {:departed, "a", 0}} = disp.arrive(done, "a", :init, 0)
    assert {:ok, floor} = disp.skip_below(disp.new(), 0)
    assert {:error, {:departed, "a", 0}} = disp.arrive(floor, "a", :init, 0)
    assert {:error, {:departed, "a", 0}} = disp.arrive(floor, "a", :signal, 0)

    assert {:error, {1, {:duplicate, "a", 0}}} =
             disp.check_trace([{:arrive, "a", :init, 0}, {:arrive, "a", :init, 0}])

    assert {:error, {2, {:departed, "a", 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:resolved, 0},
               {:arrive, "a", :init, 0}
             ])
  end

  test "an asserted idempotent init reports the contract error" do
    {disp, src} = compile!(slots(contract: :assert))
    assert src =~ "defp fresh(rows, key, index, st, kind) do"
    assert src =~ "{:contract, :idempotent_init, key, index}"
    assert src =~ ":already -> {:error, {:state, st}}"
    refute src =~ "defp fresh(rows, key, index, st) do"

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert map_size(state.by["a"]) == 1
    assert {:error, {:contract, :idempotent_init, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :signal, 0)

    assert {:held, 1, held} = disp.arrive(state, "a", :signal, 1)
    assert {:error, {:duplicate, "a", 1}} = disp.arrive(held, "a", :init, 1)
    assert {:error, {:duplicate, "a", 1}} = disp.arrive(held, "a", :signal, 1)

    assert {:ok, _, done} = disp.resolved(state, 0)
    assert {:error, {:contract, :idempotent_init, "a", 0}} = disp.arrive(done, "a", :init, 0)

    signal = disp.new()
    assert {:open, 0, signal} = disp.arrive(signal, "a", :signal, 5)
    assert {:ok, _, left} = disp.resolved(signal, 0)
    assert {:error, {:departed, "a", 5}} = disp.arrive(left, "a", :signal, 5)
    assert {:error, {:contract, :idempotent_init, "a", 5}} = disp.arrive(left, "a", :init, 5)

    assert {:ok, floor} = disp.skip_below(disp.new(), 0)
    assert {:error, {:contract, :idempotent_init, "a", 0}} = disp.arrive(floor, "a", :init, 0)
    assert {:error, {:departed, "a", 0}} = disp.arrive(floor, "a", :signal, 0)

    assert {:error, {1, {:contract, :idempotent_init, "a", 0}}} =
             disp.check_trace([{:arrive, "a", :init, 0}, {:arrive, "a", :init, 0}])

    assert {:error, {2, {:contract, :idempotent_init, "a", 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:resolved, 0},
               {:arrive, "a", :init, 0}
             ])
  end

  test "skip opens a new init where the floor or the departed record would refuse one" do
    {disp, src} = compile!(slots(contract: :skip))
    assert src =~ ":already -> {:ok, st.departed}"
    refute src =~ ":already -> {:error, {:state, st}}"

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert map_size(state.by["a"]) == 1

    assert {:ok, _, done} = disp.resolved(state, 0)
    assert {:open, 1, again} = disp.arrive(done, "a", :init, 0)
    assert map_size(again.by["a"]) == 1
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(again, "a", :init, 0)
    assert {:ok, _, done2} = disp.resolved(again, 1)
    assert {:open, 2, third} = disp.arrive(done2, "a", :init, 0)
    assert map_size(third.by["a"]) == 1

    signal = disp.new()
    assert {:open, 0, signal} = disp.arrive(signal, "a", :signal, 5)
    assert {:ok, _, left} = disp.resolved(signal, 0)
    assert {:error, {:departed, "a", 5}} = disp.arrive(left, "a", :signal, 5)
    assert {:open, 1, reopened} = disp.arrive(left, "a", :init, 5)
    assert map_size(reopened.by["a"]) == 1

    assert {:ok, floor} = disp.skip_below(disp.new(), 0)
    assert {:open, 0, opened} = disp.arrive(floor, "a", :init, 0)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(opened, "a", :init, 0)
    assert {:error, {:departed, "a", 0}} = disp.arrive(floor, "a", :signal, 0)

    assert {:error, {1, {:duplicate, "a", 0}}} =
             disp.check_trace([{:arrive, "a", :init, 0}, {:arrive, "a", :init, 0}])
  end

  test "mix muro.check prints the family, the formula, and the contract line" do
    path =
      write!(
        slots(contract: :assert) <>
          "temporal waived : slots := always true relies idempotent init\n"
      )

    version = Mix.Tasks.Muro.version()
    out = check_out(path)
    assert out =~ "Muro v#{version}\n"
    assert out =~ "family slots: wire per key of Event\n"
    assert out =~ "waived: depends on contract idempotent init\n"
    assert out =~ "All terms check. Evidence never becomes a run.\n"
    refute out =~ "may redeliver"
  end

  test "elixir and the other backends omit the contract" do
    path = write!(slots(contract: :assert, redeliver: true))
    assert {:ok, elixir} = Muro.emit_file(path, Book)
    refute elixir =~ "idempotent"
    refute elixir =~ "defmodule Slots"

    for emit <- [
          &Muro.emit_c/1,
          &Muro.emit_rust/1,
          &Muro.emit_zig/1,
          &Muro.emit_js/1,
          &Muro.emit_asm/1
        ] do
      assert {:ok, files} = emit.(path)

      for file <- files do
        text = File.read!(file)
        refute text =~ "idempotent", file
        refute text =~ "idempotent_init", file
      end
    end

    assert {:ok, %{source: suite}} = Muro.emit_exunit(path, BookTest)
    refute suite =~ "idempotent"
    refute suite =~ "idempotent_init"
  end

  defp once(mark \\ "") do
    """
    data Event : Type where
      init : Event
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    family slots : wire per key of Event#{mark}
      init never held
    """
  end

  defp slots(opts \\ []) do
    mark = if opts[:redeliver], do: " may redeliver", else: ""

    contract =
      case opts[:contract] do
        nil -> ""
        :assert -> "contract slots : idempotent init\n"
        :skip -> "contract slots : idempotent init skip\n"
      end

    """
    data Event : Type where
      init : Event
      signal : Event
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    family slots : wire per key of Event#{mark}
      init never held
      signal held while earlier unresolved
    #{contract}
    """
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp prepare(src) do
    assert {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    Graph.prepare(book, family)
  end

  defp parse_error(src) do
    assert {:error, msg} = Parser.parse(src)
    msg
  end

  defp counts(line) do
    [_, n, m] = Regex.run(~r/holds in (\d+) reachable states, (\d+) transitions/, line)
    {String.to_integer(n), String.to_integer(m)}
  end

  defp no_family_graph(fun) do
    Muro.Explore.listen(self())

    try do
      result = fun.()
      refute_received {:muro_explore, :family, _}
      result
    after
      Muro.Explore.silence()
      flush_explores()
    end
  end

  defp flush_explores do
    receive do
      {:muro_explore, _, _} -> flush_explores()
    after
      0 -> :ok
    end
  end

  defp emit!(src) do
    path = write!(src)
    assert {:ok, fsm} = Muro.emit_fsm(path, BookFsm)
    fsm
  end

  defp compile!(src) do
    path = write!(src)
    parent = Module.concat(["ContractFam#{System.unique_integer([:positive])}"])
    assert {:ok, fsm} = Muro.emit_fsm(path, parent)
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(fsm) end)

    warnings =
      Enum.filter(diags, &(match?(%{severity: :warning}, &1) or match?({:warning, _}, &1)))

    assert warnings == [], inspect(warnings, limit: 20)
    assert parent in Enum.map(mods, &elem(&1, 0))
    {Module.concat(parent, Slots), fsm}
  end

  defp write!(src) do
    dir = Path.join(System.tmp_dir!(), "muro-contract-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    path
  end

  defp check_out(path) do
    fn -> assert Mix.Tasks.Muro.Check.run([path]) == :ok end
    |> capture_io()
    |> String.replace(~r/^==> \S+\n/m, "")
  end

  defp purge do
    for {mod, _} <- :code.all_loaded(),
        name = Atom.to_string(mod),
        String.starts_with?(name, "Elixir.ContractFam") do
      :code.purge(mod)
      :code.delete(mod)
    end
  end
end
