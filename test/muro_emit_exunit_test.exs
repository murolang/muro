defmodule Muro.EmitExunitTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @pass """
  def round : run Π (n : Nat) → Nat :=
    λ (n : Nat) → n
  def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
  def all-n : evidence Π (n : Nat) → {round n ≡ n : Nat} :=
    λ (n : Nat) → refl
  def zero-eq : evidence {0 ≡ 0 : Nat} := refl
  """

  @book """
  def round : run Π (n : Nat) → Nat :=
    λ (n : Nat) → n
  def golden : run Nat := suc (suc 0)
  def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
  def golden-ok : evidence {golden ≡ suc (suc 0) : Nat} := refl
  def round-golden : evidence {round golden ≡ suc (suc 0) : Nat} := refl
  def all-n : evidence Π (n : Nat) → {round n ≡ n : Nat} :=
    λ (n : Nat) → refl
  def zero-eq : evidence {0 ≡ 0 : Nat} := refl
  def step : run internal Π (n : Nat) → Nat :=
    λ (n : Nat) → suc n
  def step-ok : evidence {step 0 ≡ suc 0 : Nat} := refl
  def pred-ok : evidence {pred (suc 0) ≡ 0 : Nat} := refl
  def proof : evidence Nat := suc 0
  def via-proof : evidence {round proof ≡ suc 0 : Nat} := refl
  def marker : spec Nat := suc 0
  def mark-eq : evidence {marker ≡ suc 0 : Nat} := refl
  def fun-eq : evidence {round ≡ round : Π (n : Nat) → Nat} := refl
  def id : run Π (-A : Type) → Π (a : A) → A :=
    λ (-A : Type) → λ (a : A) → a
  def erased-ok : evidence {id Nat (suc 0) ≡ suc 0 : Nat} := refl
  ν Stream (A : Type) : Type where
    uncons : Stream A → A × Stream A
  def zeros : run Stream Nat :=
    unfold 0 (λ (_ : Nat) → (0, 0))
  def keep : run Π (s : Stream Nat) → Stream Nat :=
    λ (s : Stream Nat) → s
  def keep-eq : evidence {keep zeros ≡ zeros : Stream Nat} := refl
  def head-zeros : evidence {head zeros ≡ 0 : Nat} := refl
  def idI : run Π (x : I64) → I64 :=
    λ (x : I64) → x
  def i64-eq : evidence {idI (toI64 0) ≡ toI64 0 : I64} := refl
  data Result (E : Type) (A : Type) : Type where
    ok    : A → Result E A
    error : E → Result E A
  def pred2 : run Π (n : Nat) → Result Unit Nat :=
    λ (n : Nat) →
      match n motive (λ _ → Result Unit Nat)
        | 0 => error tt
        | suc p => ok p
  def pred-two : evidence {pred2 (suc (suc 0)) ≡ ok (suc 0) : Result Unit Nat} := refl
  def pair : run Nat × Nat := (suc 0, suc (suc 0))
  def pair-ok : evidence {pair ≡ (suc 0, suc (suc 0)) : Nat × Nat} := refl
  def Arr : spec Type := Π (n : Nat) → Nat
  def apply : run Arr := λ (n : Nat) → n
  def apply-eq : evidence {apply (suc 0) ≡ suc 0 : Nat} := refl
  """

  @tests ~w(round-ok golden-ok round-golden pred-two pair-ok)
  @skips ~w(step-ok pred-ok via-proof mark-eq fun-eq erased-ok keep-eq i64-eq apply-eq)
  @ignored ~w(all-n zero-eq head-zeros)

  test "closed equations become tests and the rest are skipped or ignored" do
    {dir, path} = book("round.muro", @book)

    assert {:ok, %{source: source, skips: skips, tests: 5}} =
             Muro.emit_exunit(path, RoundTest, root: dir, book: "round.muro")

    assert Enum.map(skips, & &1.name) == @skips
    assert test_labels(source) == Enum.map(@tests, &label(&1, @book))

    assert reasons(skips) == %{
             "step-ok" => "step is run internal and is not exported",
             "pred-ok" => "pred is a prelude run and is not defined by the book",
             "via-proof" => "argument 1 is not closed (free variable or unresolved param)",
             "mark-eq" => "marker is not a run definition",
             "fun-eq" => "result normal form is a function",
             "erased-ok" => "argument passed at an erased binder of id",
             "keep-eq" => "argument 1 normal form is a stream",
             "i64-eq" => "argument 1 normal form is a machine term",
             "apply-eq" => "apply is applied to more arguments than its type lists"
           }

    for skip <- skips do
      assert skip.file == "round.muro"
      assert skip.line == line_of(@book, skip.name)
      assert source =~ "#   #{skip.name} (round.muro:#{skip.line}): #{skip.reason}"
    end

    assert source =~ "# Skipped: 9"
    refute Enum.any?(@ignored, &(&1 in Enum.map(skips, fn s -> s.name end)))
    refute source =~ "all-n"
    refute source =~ "zero-eq"
    refute source =~ "head-zeros"
    assert source =~ "impl.round({:suc, {:suc, 0}}) == {:suc, {:suc, 0}}"
    assert source =~ "impl.golden() == {:suc, {:suc, 0}}"
    assert source =~ "impl.pred2({:suc, {:suc, 0}}) == {:ok, {:suc, 0}}"
    assert source =~ "impl.pair() == {{:suc, 0}, {:suc, {:suc, 0}}}"
    assert source =~ "@callback round(term()) :: term()"
    assert source =~ "@callback golden() :: term()"
    assert source =~ "@impl_mod Round"
    assert source =~ "async: false"
    assert source =~ "@muro_book #{inspect(Muro.Gen.book_hash(dir, "round.muro"))}"
    refute source =~ dir

    again = Muro.emit_exunit(path, RoundTest, root: dir, book: "round.muro")
    assert {:ok, %{source: ^source}} = again
  end

  test "the suite passes on the emitted module and names each wrong answer" do
    {dir, path} = book("round.muro", @book)

    {:ok, %{source: source, tests: 5}} =
      Muro.emit_exunit(path, RoundTest, root: dir, book: "round.muro")

    {:ok, emitted} = Muro.emit_file(path, Round)
    File.write!(Path.join(dir, "suite.ex"), source)
    File.write!(Path.join(dir, "emitted.ex"), emitted)

    passed = elixir!(dir, run_script(nil))
    assert passed =~ "total: 5"
    assert passed =~ "failures: 0"

    failed =
      elixir!(
        dir,
        run_script("""
        defmodule BadRound do
          def round(_), do: 0
          def golden, do: 0
          def pred2(_), do: 0
          def pair, do: 0
        end
        Application.put_env(:muro, RoundTest, BadRound)
        """)
      )

    assert failed =~ "failures: 5"

    for name <- @tests do
      assert failed =~ label(name, @book)
    end
  end

  test "a missing module or a missing callback fails in setup and names the module" do
    {dir, path} = book("round.muro", @pass)
    {:ok, %{source: source}} = Muro.emit_exunit(path, RoundTest, root: dir, book: "round.muro")
    {:ok, emitted} = Muro.emit_file(path, Round)
    File.write!(Path.join(dir, "suite.ex"), source)
    File.write!(Path.join(dir, "emitted.ex"), emitted)

    missing =
      elixir!(
        dir,
        run_script("Application.put_env(:muro, RoundTest, Missing.Adapter)\n")
      )

    assert missing =~ "Missing.Adapter"
    assert missing =~ "is not loaded"

    partial =
      elixir!(
        dir,
        run_script("""
        defmodule Partial do
        end
        Application.put_env(:muro, RoundTest, Partial)
        """)
      )

    assert partial =~ "does not export"
    assert partial =~ "round/1"
    assert partial =~ "Partial"
  end

  test "an adapter's @behaviour is checked only after the behaviour module is loaded" do
    {dir, path} = book("round.muro", @pass)

    {:ok, %{source: source}} =
      Muro.emit_exunit(path, RoundSuite, root: dir, book: "round.muro", impl: Round)

    File.write!(Path.join(dir, "suite.ex"), source)

    File.write!(Path.join(dir, "good.ex"), """
    defmodule GoodRound do
      @behaviour RoundSuite.Behaviour
      def round(n), do: n
    end
    """)

    File.write!(Path.join(dir, "bad.ex"), """
    defmodule BadRound do
      @behaviour RoundSuite.Behaviour
    end
    """)

    early =
      elixir!(dir, """
      try do
        Code.compile_file("bad.ex")
        IO.puts("EARLY OK")
      rescue
        error ->
          IO.puts("EARLY " <> Exception.format(:error, error))
      end
      """)

    assert early =~ "EARLY OK"
    assert early =~ "@behaviour RoundSuite.Behaviour does not exist"
    assert early =~ "BadRound"

    checked =
      elixir!(dir, """
      ExUnit.start(autorun: false)
      Code.compile_file("suite.ex")

      {_, good} =
        Code.with_diagnostics(fn ->
          Code.compile_file("good.ex")
        end)

      {_, bad} =
        Code.with_diagnostics(fn ->
          Code.compile_file("bad.ex")
        end)

      IO.puts("GOOD " <> inspect(Enum.map(good, & &1.message)))
      IO.puts("BAD " <> inspect(Enum.map(bad, & &1.message)))
      """)

    assert checked =~ "GOOD []"
    assert checked =~ "round/1"
    assert checked =~ "RoundSuite.Behaviour"
    assert checked =~ "not implemented"
  end

  @tag timeout: 120_000
  test "a test/support .ex suite is registered from test_helper and runs" do
    dir = tmp_dir()
    path = write_book(dir, "round.muro", @pass)
    {:ok, emitted} = Muro.emit_file(path, Round)

    {:ok, %{source: source}} =
      Muro.emit_exunit(path, RoundSuite, root: dir, book: "round.muro", impl: Round)

    File.mkdir_p!(Path.join(dir, "lib"))
    File.mkdir_p!(Path.join(dir, "test/support"))
    File.write!(Path.join(dir, "lib/round.ex"), emitted)
    File.write!(Path.join(dir, "test/support/round_suite.ex"), source)

    File.write!(Path.join(dir, "test/support/good_round.ex"), """
    defmodule GoodRound do
      @behaviour RoundSuite.Behaviour
      def round(n), do: n
    end
    """)

    File.write!(Path.join(dir, "test/support/bad_round.ex"), """
    defmodule IncompleteRound do
      @behaviour RoundSuite.Behaviour
    end
    """)

    File.write!(Path.join(dir, "test/test_helper.exs"), """
    ExUnit.start()
    Code.ensure_loaded!(RoundSuite)
    ExUnit.Server.add_module(RoundSuite, RoundSuite.__ex_unit__(:config))
    """)

    # mix test with no *_test.exs file calls ExUnit.run/0 with the
    # formatters removed and then prints "There are no tests to run".
    File.write!(Path.join(dir, "test/anchor_test.exs"), """
    # Keeps mix test on the path that prints registered cases.
    """)

    File.write!(Path.join(dir, "mix.exs"), """
    defmodule ExunitProbe.MixProject do
      use Mix.Project

      def project do
        [
          app: :exunit_probe,
          version: "0.0.1",
          elixir: "~> 1.15",
          elixirc_paths: elixirc_paths(Mix.env())
        ]
      end

      defp elixirc_paths(:test), do: ["lib", "test/support"]
      defp elixirc_paths(_env), do: ["lib"]
    end
    """)

    {out, status} =
      System.cmd("mix", ["test", "--trace"],
        cd: dir,
        stderr_to_stdout: true,
        env: [{"MIX_BUILD_PATH", Path.join(dir, "_build")}]
      )

    if status != 0, do: flunk(out)
    assert out =~ "round-ok (round.muro:"
    assert out =~ "0 failures" or out =~ "Result: 1 passed"
    refute out =~ "There are no tests to run"
    assert out =~ "function round/1 required by behaviour RoundSuite.Behaviour is not implemented"
    assert out =~ "IncompleteRound"
  end

  test "mix muro.emit --backend exunit prints the module and the skips" do
    {_dir, path} = book("round.muro", @book)
    {:ok, %{source: source, skips: skips, tests: n}} = Muro.emit_exunit(path, RoundTest)

    {stdout, stderr} = capture_emit([path, "--backend", "exunit"])
    assert String.trim_trailing(stdout) == String.trim_trailing(source)
    assert stderr =~ "#{n} tests, #{length(skips)} skipped"

    for skip <- skips do
      assert stderr =~ "skipped #{skip.name} (#{skip.file}:#{skip.line}): #{skip.reason}"
    end

    refute stdout =~ "skipped "
    refute source =~ ~r/test "\//

    assert_raise Mix.Error, ~r/unknown backend: no-such/, fn ->
      Mix.Tasks.Muro.Emit.run([path, "--backend", "no-such"])
    end

    assert_raise Mix.Error, ~r/--node writes the placement calls/, fn ->
      Mix.Tasks.Muro.Emit.run([path, "--backend", "exunit", "--node", "a"])
    end
  end

  test "a nullary run used as a result is inlined, and imported evidence stays out" do
    dir = tmp_dir()

    write_book(
      dir,
      "nat.muro",
      "def n : run Nat := suc 0\ndef n-ok : evidence {n ≡ suc 0 : Nat} := refl\n"
    )

    path =
      write_book(dir, "use.muro", """
      import "nat.muro"
      def m : run Nat := n
      def m-ok : evidence {m ≡ n : Nat} := refl
      """)

    assert {:ok, %{source: source, skips: [], tests: 1}} =
             Muro.emit_exunit(path, UseTest, root: dir, book: "use.muro")

    assert source =~ "impl.m() == {:suc, 0}"
    refute source =~ "n-ok"
    refute source =~ "impl.n"
  end

  test "fuel exhaustion is a skip, and the same book is a test with more fuel" do
    tower = Enum.reduce(1..40, "0", fn _, acc -> "suc(#{acc})" end)

    source = """
    def idn : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    def fuel-eq : evidence {idn (plus #{tower} 0) ≡ plus #{tower} 0 : Nat} := refl
    """

    {dir, path} = book("fuel.muro", source)

    assert {:ok, %{tests: 0, skips: [skip]}} =
             Muro.emit_exunit(path, FuelTest, fuel: 40, root: dir, book: "fuel.muro")

    assert skip.name == "fuel-eq"
    assert skip.reason == "argument 1 did not normalize within fuel"

    assert {:ok, %{tests: 1, skips: []}} =
             Muro.emit_exunit(path, FuelTest, fuel: 200, root: dir, book: "fuel.muro")
  end

  test "the stem names the implementation and the test module gains Test" do
    {dir, path} = book("my-book.muro", @pass)

    assert Muro.Emit.elixir_module(path) == MyBook
    assert Muro.Emit.exunit_module(path) == MyBookTest

    assert {:ok, %{source: source, skips: []}} =
             Muro.emit_exunit(path, MyBookTest,
               impl: MyApp.Rounding,
               root: dir,
               book: "my-book.muro"
             )

    assert source =~ "defmodule MyBookTest do\n"
    assert source =~ "defmodule MyBookTest.Behaviour do\n"
    assert source =~ "@impl_mod MyApp.Rounding"
    assert source =~ "# Skipped: none"
  end

  defp label(name, source), do: "#{name} (round.muro:#{line_of(source, name)})"

  defp reasons(skips), do: Map.new(skips, fn skip -> {skip.name, skip.reason} end)

  defp test_labels(source) do
    Regex.scan(~r/^\s*test ("(?:\\.|[^"])*"),/m, source)
    |> Enum.map(fn [_, quoted] ->
      {label, []} = Code.eval_string(quoted)
      label
    end)
  end

  defp line_of(source, name) do
    source
    |> String.split("\n")
    |> Enum.with_index(1)
    |> Enum.find_value(fn {line, number} ->
      if String.starts_with?(String.trim_leading(line), "def #{name} "), do: number
    end)
  end

  defp run_script(prelude) do
    """
    ExUnit.start(autorun: false, colors: [enabled: false], trace: true)
    Code.compile_file("emitted.ex")
    Code.compile_file("suite.ex")
    #{prelude}
    result = ExUnit.run()
    IO.puts("RESULT " <> inspect(result))
    """
  end

  defp elixir!(dir, script) do
    File.write!(Path.join(dir, "runner.exs"), script)
    {out, status} = System.cmd("elixir", ["runner.exs"], cd: dir, stderr_to_stdout: true)
    if status != 0, do: flunk(out)
    out
  end

  defp capture_emit(args) do
    parent = self()

    stdout =
      capture_io(fn ->
        stderr =
          capture_io(:stderr, fn ->
            Mix.Tasks.Muro.Emit.run(args)
          end)

        send(parent, {:stderr, stderr})
      end)

    assert_received {:stderr, stderr}
    {stdout, stderr}
  end

  defp book(name, source) do
    dir = tmp_dir()
    {dir, write_book(dir, name, source)}
  end

  defp write_book(dir, name, source) do
    path = Path.join(dir, name)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, source)
    path
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_exunit_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
