defmodule Muro.MutateTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @half "examples/half_ok.muro"

  test "half_ok reports every mutant of half, byte for byte" do
    {:ok, report} = Muro.Mutate.report(@half, only: ["half"], concurrency: 1)
    version = Mix.Tasks.Muro.version()

    assert report.version == version
    assert report.book == @half

    assert report.summary == %{
             killed: 5,
             surviving: 1,
             equivalent: 0,
             out_of_fuel: 0,
             discarded: 11
           }

    assert report.defs == [
             %{name: "half", rechecked: 1, evidence: 5, evidence_names: ["half_ok"]}
           ]

    assert Enum.map(report.mutants, & &1.outcome) |> Enum.uniq() |> Enum.sort() ==
             ["discarded", "killed", "surviving"]

    for mutant <- report.mutants do
      assert mutant.def == "half"
      assert mutant.location =~ ~r/examples\/half_ok\.muro:\d+:\d+$/
      assert mutant.before != ""
      assert Map.fetch!(mutant, :after) != ""

      if mutant.outcome == "killed" do
        assert mutant.killed_by == [
                 %{name: "half_ok", location: "examples/half_ok.muro:37:1"}
               ]
      else
        assert mutant.killed_by == []
      end
    end

    survivor = Enum.find(report.mutants, &(&1.outcome == "surviving"))
    assert survivor.id == "half#12"
    assert survivor.operator == "replace_ctor"
    assert survivor.location == "examples/half_ok.muro:25:18"
    assert survivor.before == "0"
    assert Map.fetch!(survivor, :after) == "suc(0)"

    body = File.read!("test/fixtures/mutate/half_only.txt")
    assert Muro.Mutate.render(report) == "Muro v#{version}\n" <> body

    json = Muro.Mutate.render_json(report)
    assert json == second_json()
    assert json == schedulers_json()
    assert_json(json, version)
  end

  test "a weak theorem leaves the unconstrained arm surviving" do
    path = write!("weak.muro", weak_src())
    {:ok, report} = Muro.Mutate.report(path, only: ["not"])

    survivor = Enum.find(report.mutants, &(&1.outcome == "surviving"))
    assert survivor.operator == "replace_ctor"
    assert survivor.location =~ ~r/:9:18$/
    assert survivor.before == "true"
    assert Map.fetch!(survivor, :after) == "false"
    assert survivor.killed_by == []

    killed = Enum.find(report.mutants, &(&1.id == "not#4"))
    assert killed.outcome == "killed"
    assert killed.before == "false"
    assert hd(killed.killed_by).name == "not_true"
  end

  test "an arm swap that computes the same value is equivalent" do
    path = write!("same.muro", same_src())
    {:ok, report} = Muro.Mutate.report(path, only: ["same"])

    swap = Enum.find(report.mutants, &(&1.operator == "swap_arms"))
    assert swap.outcome == "equivalent"
    assert swap.killed_by == []
    assert swap.before =~ "true  => plus 0 0"
    assert Map.fetch!(swap, :after) =~ "true  => 0"
    assert Map.fetch!(swap, :after) =~ "false  => plus 0 0"
    assert report.summary.equivalent >= 1
  end

  test "a mutant the fuel cannot decide is out of fuel" do
    path = write!("fuel.muro", fuel_src(40))
    {:ok, report} = Muro.Mutate.report(path, only: ["use"], fuel: 30, concurrency: 1)

    dear =
      Enum.find(report.mutants, fn mutant ->
        mutant.operator == "replace_call" and Map.fetch!(mutant, :after) == "dear n n"
      end)

    assert dear.outcome == "out_of_fuel"
    assert dear.killed_by == []
    refute Enum.any?(report.mutants, &(&1.outcome == "killed" and &1.id == dear.id))
    assert report.summary.out_of_fuel >= 1
  end

  test "a theorem that does not mention the definition is not re-checked" do
    path = write!("deps.muro", deps_src())
    {:ok, report} = Muro.Mutate.report(path, only: ["a"])
    [info] = report.defs

    assert info.name == "a"
    assert info.evidence_names == ["a_ok"]
    assert info.rechecked == 1
    assert info.evidence > info.rechecked
    refute "b_ok" in info.evidence_names

    assert Muro.Mutate.render(report) =~
             "a: re-checked #{info.rechecked} of #{info.evidence} evidence definitions"
  end

  test "plus is re-checked only through definitions that mention it" do
    {:ok, report} = Muro.Mutate.report(@half, only: ["plus"], concurrency: 1)
    [info] = report.defs

    assert info.evidence_names == ["plus_suc", "half_ok"]
    assert info.rechecked == 2
    assert info.evidence == 5

    swap = Enum.find(report.mutants, &(&1.operator == "swap_args"))
    assert swap.outcome == "discarded"
    assert swap.discard == :termination
    assert swap.location == "examples/half_ok.muro:8:23"
    assert Map.fetch!(swap, :after) == "plus m np"
  end

  test "the same book run twice is byte-identical JSON under two schedulers" do
    opts = [only: ["not"]]
    path = write!("det.muro", weak_src())

    {:ok, once} = Muro.Mutate.report(path, opts ++ [concurrency: 1])
    {:ok, twice} = Muro.Mutate.report(path, opts ++ [concurrency: 1])
    {:ok, wide} = Muro.Mutate.report(path, opts ++ [concurrency: System.schedulers_online()])

    assert Muro.Mutate.render_json(once) == Muro.Mutate.render_json(twice)
    assert Muro.Mutate.render_json(once) == Muro.Mutate.render_json(wide)
    assert Muro.Mutate.render(once) == Muro.Mutate.render(wide)
  end

  test "--only keeps the named run and --max-mutants-per-def stops the enumeration" do
    {:ok, capped} = Muro.Mutate.report(@half, only: ["half"], max_mutants_per_def: 1)
    assert Enum.map(capped.mutants, & &1.id) == ["half#1"]
    assert hd(capped.defs).name == "half"

    {:ok, none} = Muro.Mutate.report(@half, only: ["half"], max_mutants_per_def: 0)
    assert none.mutants == []
    assert hd(none.defs).rechecked == 1
    assert Muro.Mutate.render(none) =~ "half: re-checked 1 of 5 evidence definitions"
    refute Muro.Mutate.render(none) =~ "half#1"

    assert {:error, :only, msg} = Muro.Mutate.report(@half, only: ["half_ok"])
    assert msg =~ "half_ok"
    assert {:error, :only, _} = Muro.Mutate.report(@half, only: ["missing"])
  end

  test "mix muro.mutate prints the report and the JSON object" do
    version = Mix.Tasks.Muro.version()
    {out, err, code} = run_task(["--only", "half", "--max-mutants-per-def", "0", @half])
    assert code == :ok
    assert err == ""
    assert out =~ "Muro v#{version}\n"
    assert out =~ "half: re-checked 1 of 5 evidence definitions\n"
    refute out =~ "plus: re-checked"
    refute out =~ "half#1"

    {json_out, json_err, json_code} =
      run_task(["--only", "half", "--max-mutants-per-def", "0", "--json", @half])

    assert json_code == :ok
    assert json_err == ""
    decoded = JSON.decode!(json_out)
    assert decoded["summary"]["killed"] == 0
    assert decoded["mutants"] == []
    assert MapSet.new(Map.keys(decoded)) == MapSet.new(["book", "version", "summary", "mutants"])
    refute Map.has_key?(decoded, "defs")

    assert String.starts_with?(
             json_out,
             ~s({"book":"#{@half}","version":"#{version}","summary":{"killed":0,"surviving":0,"equivalent":0,"out_of_fuel":0,"discarded":0},"mutants":[]}\n)
           )
  end

  test "--max-survivors exits 1 after the report, and a clean cap exits 0" do
    path = write!("cap.muro", weak_src())
    {out, err, code} = run_task(["--max-survivors", "0", path])
    assert code == {:shutdown, 1}
    assert out =~ "surviving: 1\n"
    assert err =~ "1 survivors exceed --max-survivors 0\n"

    quiet = write!("quiet.muro", deps_src())
    {quiet_out, quiet_err, quiet_code} = run_task(["--only", "a", "--max-survivors", "0", quiet])
    assert quiet_code == :ok
    assert quiet_err =~ "a#1 replace_ctor killed\n"
    refute quiet_err =~ "survivors exceed"
    assert quiet_out =~ "surviving: 0\n"
  end

  test "replacing a passed-along key with a different constructor is killed" do
    path = write!("find.muro", find_true_src())
    {:ok, report} = Muro.Mutate.report(path, only: ["g"], concurrency: 1)

    mutant =
      Enum.find(report.mutants, fn mutant ->
        mutant.operator == "replace_var" and mutant.before == "k" and mutant.after == "wild"
      end)

    assert mutant.outcome == "killed"
    assert Enum.any?(mutant.killed_by, &(&1.name == "g-is-find"))
  end

  test "a book that does not check exits 2 and is not mutated" do
    version = Mix.Tasks.Muro.version()
    path = write!("bad.muro", "def z : run Nat := true\n")
    {out, err, code} = run_task(["--json", path])

    assert code == {:shutdown, 2}
    assert out == "Muro v#{version}\n"
    assert err =~ "refusing to mutate a book that does not check\n"
    refute out =~ "{"
    refute err =~ "{"
  end

  test "the task rejects a bad flag and a name that is not a run definition" do
    assert_raise Mix.Error, ~r/unknown option/, fn ->
      Mix.Tasks.Muro.Mutate.run(["--nope", @half])
    end

    assert_raise Mix.Error, ~r/expected one path/, fn ->
      Mix.Tasks.Muro.Mutate.run([])
    end

    assert_raise Mix.Error, ~r/--fuel must be a positive integer/, fn ->
      Mix.Tasks.Muro.Mutate.run(["--fuel", "0", @half])
    end

    assert_raise Mix.Error, ~r/half_ok is not a run definition/, fn ->
      Mix.Tasks.Muro.Mutate.run(["--only", "half_ok", @half])
    end
  end

  defp second_json do
    {:ok, report} = Muro.Mutate.report(@half, only: ["half"], concurrency: 1)
    Muro.Mutate.render_json(report)
  end

  defp schedulers_json do
    {:ok, report} =
      Muro.Mutate.report(@half, only: ["half"], concurrency: System.schedulers_online())

    Muro.Mutate.render_json(report)
  end

  defp assert_json(json, version) do
    assert String.ends_with?(json, "\n")

    assert String.starts_with?(
             json,
             ~s({"book":"#{@half}","version":"#{version}","summary":{"killed":5,"surviving":1,"equivalent":0,"out_of_fuel":0,"discarded":11},"mutants":[)
           )

    decoded = JSON.decode!(json)
    assert decoded["version"] == version
    assert decoded["summary"]["surviving"] == 1
    assert decoded["summary"]["killed"] == 5

    assert String.contains?(
             json,
             ~s|{"id":"half#12","def":"half","operator":"replace_ctor","location":"examples/half_ok.muro:25:18","before":"0","after":"suc(0)","outcome":"surviving","killed_by":[]}|
           )

    assert String.contains?(
             json,
             ~s|"outcome":"killed","killed_by":[{"name":"half_ok","location":"examples/half_ok.muro:37:1"}]|
           )
  end

  defp run_task(args) do
    parent = self()

    stdout =
      capture_io(fn ->
        stderr =
          capture_io(:stderr, fn ->
            send(parent, {:result, task_result(args)})
          end)

        send(parent, {:stderr, stderr})
      end)

    assert_received {:stderr, stderr}
    assert_received {:result, code}
    {stdout, stderr, code}
  end

  defp task_result(args) do
    try do
      Mix.Tasks.Muro.Mutate.run(args)
      :ok
    catch
      :exit, reason -> reason
    end
  end

  defp write!(name, src) do
    dir = Path.join(System.tmp_dir!(), "muro_mutate_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, name)
    File.write!(path, src)
    path
  end

  defp weak_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool

    def not : run Π (b : Bool) → Bool :=
      λ (b : Bool) →
        match b motive (λ _ → Bool)
          | true => false
          | false => true

    def not_true : evidence {not true ≡ false : Bool} := refl
    """
  end

  defp same_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool

    def same : run Π (b : Bool) → Nat :=
      λ (b : Bool) →
        match b motive (λ _ → Nat)
          | true => plus 0 0
          | false => 0

    def same_true : evidence {same true ≡ 0 : Nat} := refl
    def same_false : evidence {same false ≡ 0 : Nat} := refl
    """
  end

  defp deps_src do
    """
    def a : run Nat := 0
    def b : run Nat := 0
    def a_ok : evidence {a ≡ 0 : Nat} := refl
    def b_ok : evidence {b ≡ 0 : Nat} := refl
    """
  end

  defp fuel_src(k) do
    n = numeral(k)

    """
    def dear : run Π (n : Nat) → Π (m : Nat) → Nat :=
      λ (n : Nat) → λ (m : Nat) →
        match n motive (λ _ → Nat)
          | 0 => m
          | suc np => suc(dear np m)

    def cheap : run Π (n : Nat) → Π (m : Nat) → Nat :=
      λ (n : Nat) → λ (m : Nat) → m

    def use : run Π (+ n : Nat) → Nat :=
      λ (+ n : Nat) → cheap n n

    def use_ok : evidence {use #{n} ≡ #{n} : Nat} := refl
    """
  end

  defp numeral(0), do: "0"
  defp numeral(k) when k > 0, do: "suc(#{numeral(k - 1)})"

  defp find_true_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    data Key : Type where
      wild : Key
      named : Nat → Key

    def eq-nat : run Π (a : Nat) → Π (b : Nat) → Bool :=
      λ (a : Nat) → λ (b : Nat) →
        match a motive (λ _ → Bool)
          | 0 => (match b motive (λ _ → Bool) | 0 => true | suc _ => false)
          | suc p => (match b motive (λ _ → Bool) | 0 => false | suc q => eq-nat p q)

    def eq-key : run Π (k : Key) → Π (j : Key) → Bool :=
      λ (k : Key) → λ (j : Key) →
        match k motive (λ _ → Bool)
          | wild => (match j motive (λ _ → Bool) | wild => true | named _ => false)
          | named n => (match j motive (λ _ → Bool) | wild => false | named m => eq-nat n m)

    def or : run Π (a : Bool) → Π (b : Bool) → Bool :=
      λ (a : Bool) → λ (b : Bool) → match a motive (λ _ → Bool) | true => true | false => b

    def find : run Π (+ k : Key) → Π (t : List Key) → Bool :=
      λ (+ k : Key) → λ (t : List Key) →
        match t motive (λ _ → Bool)
          | nil => false
          | cons x xs => or (find k xs) (eq-key k x)

    def g : run Π (+ k : Key) → Π (t : List Key) → Bool :=
      λ (+ k : Key) → λ (t : List Key) → find k t

    def g-is-find : evidence Π (k : Key) → Π (t : List Key) → {g k t ≡ find k t : Bool} :=
      λ (k : Key) → λ (t : List Key) → refl
    def same-key : evidence Π (t : List Key) → {find wild t ≡ find wild t : Bool} :=
      λ (t : List Key) → refl
    """
  end
end
