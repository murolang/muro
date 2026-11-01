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

  @param_tests ~w(
    nil-k0 nil-k1 a-k0 a-k1 b-k0 b-k1 sil-k0 sil-k1 sil-deep b-deep a-deep
    golden-a-k0 ok-true same-nil
  )

  @open_param """
  param p : run Nat
  param p-is : evidence {p ≡ 0 : Nat}
  def held : evidence {p ≡ 0 : Nat} := p-is
  """

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

  test "a book without params keeps the 0.16.76 text apart from the test name" do
    {dir, path} = book("round.muro", @book)

    assert {:ok, %{source: source}} =
             Muro.emit_exunit(path, RoundTest, root: dir, book: "round.muro")

    legacy = to_legacy(source)

    assert test_labels(legacy) ==
             Enum.map(@tests, fn name -> "#{name} (round.muro:#{line_of(@book, name)})" end)

    assert blank_strings(source) == blank_strings(legacy)
    assert source =~ "#   step-ok (round.muro:"
    assert source =~ "# Skipped: 9"
    refute source =~ "round-ok (round.muro:"
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
      assert failed =~ "round.muro:#{line_of(@book, name)} #{name}"
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
    assert out =~ "round.muro round-ok"
    assert out =~ ~r/(^|[^0-9])0 failures|^Result: \d+ passed/m
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

  @tag timeout: 120_000
  test "a param library is the suite every implementation runs" do
    dir = tmp_dir()
    write_conformance(dir)
    lib = Path.join(dir, "conformance.muro")
    impl = Path.join(dir, "impl.muro")
    lib_src = File.read!(lib)

    assert {:error, refused} = Muro.check_file(lib, root: dir)
    assert refused =~ "param decide is supplied by a file that imports this one"

    assert {:ok, %{source: source, skips: skips, tests: 14}} =
             Muro.emit_exunit(lib, ConformanceTest, root: dir, book: "conformance.muro")

    assert Enum.map(skips, & &1.name) ==
             ~w(f-nil inside observe-eq hoist-eq ticks-eq widen-eq)

    assert reasons(skips) == %{
             "f-nil" => "calls param decide through f",
             "inside" => "calls param decide inside a value",
             "observe-eq" => "param observe takes a stream",
             "hoist-eq" => "param hoist takes a function",
             "ticks-eq" => "param ticks returns a stream",
             "widen-eq" => "param widen arguments are not data"
           }

    assert callbacks_of(source) == ["decide", "ok"]
    assert source =~ "@callback decide(term(), term()) :: term()"
    assert source =~ "@callback ok() :: term()"
    assert source =~ "@callbacks [decide: 2, ok: 0]"
    refute source =~ "decide-is-rule"
    refute source =~ "all-nil"

    for name <- @param_tests do
      line = line_of(lib_src, name)
      assert source =~ "test \"conformance.muro #{name}\""
      assert source =~ "\"conformance.muro:#{line} #{name}\""
    end

    assert source =~ "impl.decide(:k0, {:cons, :a, :nil}) == :true"
    assert source =~ "impl.decide(:k0, :nil) == impl.decide(:k1, :nil)"
    refute source =~ dir

    {:ok, emitted} = Muro.emit_file(impl, Impl)
    assert emitted =~ "def decide("
    File.write!(Path.join(dir, "suite.ex"), source)
    File.write!(Path.join(dir, "emitted.ex"), emitted)

    passed = elixir!(dir, run_script("Application.put_env(:muro, ConformanceTest, Impl)\n"))
    assert passed =~ "total: 14"
    assert passed =~ "failures: 0"

    hand = elixir!(dir, run_script(hand_adapter()))
    assert hand =~ "failures: 0"

    mutant = elixir!(dir, run_script(mutant_adapter()))
    assert mutant =~ "total: 14"
    assert mutant =~ "failures: 3"

    failed =
      Regex.scan(~r/\d+\) test (conformance\.muro \S+)/, mutant)
      |> Enum.map(fn [_, name] -> name end)
      |> Enum.sort()

    assert failed == [
             "conformance.muro sil-deep",
             "conformance.muro sil-k0",
             "conformance.muro sil-k1"
           ]

    for name <- ~w(sil-k0 sil-k1 sil-deep) do
      assert mutant =~ "conformance.muro:#{line_of(lib_src, name)} #{name}"
    end
  end

  test "imports collects direct equations and leaves today's suite alone when off" do
    dir = tmp_dir()
    write_conformance(dir)
    impl = Path.join(dir, "impl.muro")
    lib = Path.join(dir, "conformance.muro")

    assert {:ok, %{tests: 0, skips: []}} =
             Muro.emit_exunit(impl, ImplTest, root: dir, book: "impl.muro")

    assert {:ok, %{source: imported, tests: 16, skips: skips}} =
             Muro.emit_exunit(impl, ImplTest, root: dir, book: "impl.muro", imports: true)

    labels = test_labels(imported)
    assert hd(labels) == "conformance.muro nil-k0"
    assert "conformance.muro golden-a-k0" in labels
    assert "conformance.muro f-nil" in labels
    assert "conformance.muro inside" in labels
    refute Enum.any?(labels, &String.starts_with?(&1, "rule.muro "))
    assert Enum.map(skips, & &1.file) |> Enum.uniq() == ["conformance.muro"]
    assert length(skips) == 4

    again = Muro.emit_exunit(impl, ImplTest, root: dir, book: "impl.muro", imports: true)
    assert {:ok, %{source: ^imported}} = again

    {:ok, emitted} = Muro.emit_file(impl, Impl)
    File.write!(Path.join(dir, "suite.ex"), imported)
    File.write!(Path.join(dir, "emitted.ex"), emitted)
    passed = elixir!(dir, run_script(nil))
    assert passed =~ "total: 16"
    assert passed =~ "failures: 0"

    assert {:ok, %{source: with_rule}} =
             Muro.emit_exunit(lib, ConformanceTest,
               root: dir,
               book: "conformance.muro",
               imports: true
             )

    rule_labels = test_labels(with_rule)
    assert hd(rule_labels) == "conformance.muro nil-k0"
    assert List.last(rule_labels) == "rule.muro rule-ok"
    assert length(rule_labels) == 15
  end

  test "direct imports keep declaration order, once, and do not follow further" do
    dir = tmp_dir()

    write_book(dir, "d.muro", """
    def d : run Nat := 0
    def d-ok : evidence {d ≡ 0 : Nat} := refl
    """)

    write_book(dir, "right.muro", """
    import "d.muro"
    def r : run Nat := suc 0
    def r-ok : evidence {r ≡ suc 0 : Nat} := refl
    """)

    write_book(dir, "left.muro", """
    import "d.muro"
    def l : run Nat := suc (suc 0)
    def l-ok : evidence {l ≡ suc (suc 0) : Nat} := refl
    """)

    top =
      write_book(dir, "top.muro", """
      import "right.muro"
      import "left.muro"
      import "right.muro"
      def t : run Nat := suc (suc (suc 0))
      def t-ok : evidence {t ≡ suc (suc (suc 0)) : Nat} := refl
      """)

    assert {:ok, %{source: source, tests: 3, skips: []}} =
             Muro.emit_exunit(top, TopTest, root: dir, book: "top.muro", imports: true)

    assert test_labels(source) == ["top.muro t-ok", "right.muro r-ok", "left.muro l-ok"]
    refute source =~ "d.muro"
    refute source =~ dir

    again = Muro.emit_exunit(top, TopTest, root: dir, book: "top.muro", imports: true)
    assert {:ok, %{source: ^source}} = again
  end

  test "a package import is a direct import, named by its path under the root" do
    dir = tmp_dir()
    wire = "def wire : run Nat := 0\ndef wire-ok : evidence {wire ≡ 0 : Nat} := refl\n"
    write_book(dir, "muro_deps/shared/wire.muro", wire)

    use =
      write_book(dir, "use.muro", """
      import "pkg:shared/wire.muro"
      def use : run Nat := wire
      def use-ok : evidence {use ≡ suc 0 : Nat} := refl
      """)

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "#{Mix.Tasks.Muro.version()}",
      muro_deps: [
        shared: {:git, "https://example.com/shared.git", tag: "v1.0.0"}
      ],
      modules: []
    ]
    """)

    write_lock(dir, %{"muro_deps/shared/wire.muro" => wire})

    assert {:error, _} =
             Muro.emit_exunit(use, UseTest, root: dir, book: "use.muro", imports: true)

    write_book(dir, "use.muro", """
    import "pkg:shared/wire.muro"
    def use : run Nat := wire
    def use-ok : evidence {use ≡ 0 : Nat} := refl
    """)

    assert {:ok, %{source: source, tests: 2, skips: []}} =
             Muro.emit_exunit(use, UseTest, root: dir, book: "use.muro", imports: true)

    assert test_labels(source) == ["use.muro use-ok", "muro_deps/shared/wire.muro wire-ok"]
    refute source =~ "pkg:"
    refute source =~ dir
  end

  test "every backend but exunit still refuses an unsupplied param" do
    {dir, path} = book("lib.muro", @open_param)

    assert {:error, message} = Muro.check_file(path)
    assert message =~ "param p is supplied by a file that imports this one"

    for call <- [
          fn -> Muro.emit_file(path, Lib) end,
          fn -> Muro.emit_c(path) end,
          fn -> Muro.emit_rust(path) end,
          fn -> Muro.emit_zig(path) end,
          fn -> Muro.emit_asm(path) end,
          fn -> Muro.emit_otp(path) end,
          fn -> Muro.emit_node(path, :a) end,
          fn -> Muro.emit_fsm(path, LibFsm) end
        ] do
      assert {:error, refused} = call.()
      assert refused =~ "param p is supplied by a file that imports this one"
    end

    assert {:ok, %{tests: 1, skips: [], source: source}} =
             Muro.emit_exunit(path, LibTest, root: dir, book: "lib.muro")

    assert source =~ "@callback p() :: term()"
    assert source =~ "test \"lib.muro held\""
    refute source =~ "@callback p_is"

    for backend <- ["elixir", "c", "rust", "zig", "asm", "otp", "fsm"] do
      assert_raise Mix.Error, ~r/param p is supplied by a file that imports this one/, fn ->
        Mix.Tasks.Muro.Emit.run([path, "--backend", backend])
      end

      assert_raise Mix.Error, ~r/--imports is only valid with --backend exunit/, fn ->
        Mix.Tasks.Muro.Emit.run([path, "--backend", backend, "--imports"])
      end
    end

    assert_raise Mix.Error, ~r/param p is supplied by a file that imports this one/, fn ->
      Mix.Tasks.Muro.Emit.run([path])
    end

    assert_raise Mix.Error, ~r/param p is supplied by a file that imports this one/, fn ->
      Mix.Tasks.Muro.Emit.run([path, "--node", "a"])
    end

    {stdout, stderr} = capture_emit([path, "--backend", "exunit"])
    assert stdout =~ "defmodule LibTest do\n"
    assert stderr =~ "1 tests, 0 skipped"

    {same, other} = book("same.muro", "param p : run Nat\ndef p : run Nat := 0\n")
    assert {:error, dup} = Muro.check_file(other)
    assert dup =~ "duplicate name p"
    refute dup =~ "is supplied by a file that imports this one"
    _ = same

    session = """
    session ping := recv Nat (send Nat end)
    param talk : run ping
    """

    {_dir, talk} = book("talk.muro", session)

    assert {:error, sess} = Muro.emit_exunit(talk, TalkTest, book: "talk.muro")
    assert sess =~ "ping is a session, not a definition"
  end

  defp label(name, _source), do: "round.muro #{name}"

  # Put the 0.16.76 test name and assertion message back. Nothing else moves.
  defp to_legacy(source) do
    Regex.replace(
      ~r/^( *)test "([^"\n]+) ([^"\n]+)", %\{impl: impl\} do\n( *)assert (.*), "\2:(\d+) \3"\n/m,
      source,
      fn _, indent, file, name, aindent, call, line ->
        old = "#{name} (#{file}:#{line})"

        """
        #{indent}test #{inspect(old)}, %{impl: impl} do
        #{aindent}assert #{call}, #{inspect(old)}
        """
      end
    )
  end

  defp blank_strings(source), do: String.replace(source, ~r/"[^"\n]*"/, "\"\"")

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

  defp callbacks_of(source) do
    Regex.scan(~r/@callback ([A-Za-z0-9_]+)\(/, source)
    |> Enum.map(fn [_, name] -> name end)
  end

  defp hand_adapter do
    """
    defmodule Hand do
      @behaviour ConformanceTest.Behaviour
      def decide(_k, :nil), do: true
      def decide(_k, {:cons, :b, _}), do: false
      def decide(_k, {:cons, :silence, _}), do: true
      def decide(_k, {:cons, :a, _}), do: true
      def ok, do: true
    end
    Application.put_env(:muro, ConformanceTest, Hand)
    """
  end

  defp mutant_adapter do
    """
    defmodule Mutant do
      @behaviour ConformanceTest.Behaviour
      def decide(_k, :nil), do: true
      def decide(_k, {:cons, :b, _}), do: false
      def decide(_k, {:cons, :silence, _}), do: false
      def decide(_k, _), do: true
      def ok, do: true
    end
    Application.put_env(:muro, ConformanceTest, Mutant)
    """
  end

  defp write_lock(dir, files) do
    {:ok, deps} = Muro.Manifest.load_deps(dir)

    packages =
      Map.new(deps, fn dep ->
        prefix = "muro_deps/" <> dep.name <> "/"

        hashed =
          files
          |> Enum.filter(fn {rel, _bytes} -> String.starts_with?(rel, prefix) end)
          |> Map.new(fn {rel, bytes} ->
            {String.replace_prefix(rel, prefix, ""), Muro.Hash.sha256(bytes)}
          end)

        {dep.name,
         %{
           files: hashed,
           resolved: {:git, String.duplicate("ab", 20)},
           source: dep.source,
           version: "1.0.0"
         }}
      end)

    File.write!(Path.join(dir, "muro.lock"), Muro.Lock.encode(packages))
  end

  defp write_conformance(dir) do
    write_book(dir, "rule.muro", """
    data Key : Type where
      k0 : Key
      k1 : Key

    data Item : Type where
      a : Item
      b : Item
      silence : Item

    data Bool : Type where
      true : Bool
      false : Bool

    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A

    def not : run Π (b : Bool) → Bool :=
      λ (b : Bool) →
        match b motive (λ _ → Bool)
          | true => false
          | false => true

    def rule : run Π (k : Key) → Π (t : List Item) → Bool :=
      λ (k : Key) → λ (t : List Item) →
        match t motive (λ _ → Bool)
          | nil => true
          | cons x _ =>
            match x motive (λ _ → Bool)
              | a => true
              | b => false
              | silence => true

    def rule-ok : evidence {rule k0 nil ≡ true : Bool} := refl
    """)

    write_book(dir, "conformance.muro", """
    import "rule.muro"

    param decide : run Π (k : Key) → Π (t : List Item) → Bool
    param decide-is-rule : evidence Π (k : Key) → Π (t : List Item) → {decide k t ≡ rule k t : Bool}

    def golden-a : run List Item := cons a nil
    def ok : run Bool := true

    def nil-k0 : evidence {decide k0 nil ≡ true : Bool} :=
      rewrite (decide-is-rule k0 nil) motive (λ z → {z ≡ true : Bool}) in refl
    def nil-k1 : evidence {decide k1 nil ≡ true : Bool} :=
      rewrite (decide-is-rule k1 nil) motive (λ z → {z ≡ true : Bool}) in refl
    def a-k0 : evidence {decide k0 (cons a nil) ≡ true : Bool} :=
      rewrite (decide-is-rule k0 (cons a nil)) motive (λ z → {z ≡ true : Bool}) in refl
    def a-k1 : evidence {decide k1 (cons a nil) ≡ true : Bool} :=
      rewrite (decide-is-rule k1 (cons a nil)) motive (λ z → {z ≡ true : Bool}) in refl
    def b-k0 : evidence {decide k0 (cons b nil) ≡ false : Bool} :=
      rewrite (decide-is-rule k0 (cons b nil)) motive (λ z → {z ≡ false : Bool}) in refl
    def b-k1 : evidence {decide k1 (cons b nil) ≡ false : Bool} :=
      rewrite (decide-is-rule k1 (cons b nil)) motive (λ z → {z ≡ false : Bool}) in refl
    def sil-k0 : evidence {decide k0 (cons silence nil) ≡ true : Bool} :=
      rewrite (decide-is-rule k0 (cons silence nil)) motive (λ z → {z ≡ true : Bool}) in refl
    def sil-k1 : evidence {decide k1 (cons silence nil) ≡ true : Bool} :=
      rewrite (decide-is-rule k1 (cons silence nil)) motive (λ z → {z ≡ true : Bool}) in refl
    def sil-deep : evidence {decide k0 (cons silence (cons a nil)) ≡ true : Bool} :=
      rewrite (decide-is-rule k0 (cons silence (cons a nil))) motive (λ z → {z ≡ true : Bool}) in refl
    def b-deep : evidence {decide k0 (cons b (cons a nil)) ≡ false : Bool} :=
      rewrite (decide-is-rule k0 (cons b (cons a nil))) motive (λ z → {z ≡ false : Bool}) in refl
    def a-deep : evidence {decide k0 (cons a (cons silence nil)) ≡ true : Bool} :=
      rewrite (decide-is-rule k0 (cons a (cons silence nil))) motive (λ z → {z ≡ true : Bool}) in refl
    def golden-a-k0 : evidence {decide k0 golden-a ≡ true : Bool} :=
      rewrite (decide-is-rule k0 golden-a) motive (λ z → {z ≡ true : Bool}) in refl

    def ok-true : evidence {ok ≡ true : Bool} := refl

    def all-nil : evidence Π (k : Key) → {decide k nil ≡ true : Bool} :=
      λ (k : Key) →
        rewrite (decide-is-rule k nil) motive (λ z → {z ≡ true : Bool}) in refl

    def f : run Π (t : List Item) → Bool :=
      λ (t : List Item) → not (decide k0 t)
    def f-nil : evidence {f nil ≡ false : Bool} :=
      rewrite (decide-is-rule k0 nil) motive (λ z → {not z ≡ false : Bool}) in refl

    def idb : run Π (b : Bool) → Bool :=
      λ (b : Bool) → b
    def inside : evidence {idb (decide k0 nil) ≡ true : Bool} :=
      rewrite (decide-is-rule k0 nil) motive (λ z → {idb z ≡ true : Bool}) in refl

    param observe : run Π (s : Stream Nat) → Nat
    def zeros : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))
    param observe-holds : evidence Π (s : Stream Nat) → {observe s ≡ 0 : Nat}
    def observe-eq : evidence {observe zeros ≡ 0 : Nat} := observe-holds zeros

    param hoist : run Π (f : Π (b : Bool) → Bool) → Π (b : Bool) → Bool
    param hoist-holds : evidence Π (b : Bool) → {hoist idb b ≡ b : Bool}
    def hoist-eq : evidence {hoist idb true ≡ true : Bool} := hoist-holds true

    param ticks : run Π (n : Nat) → Stream Nat
    param ticks-holds : evidence Π (n : Nat) → {ticks n ≡ zeros : Stream Nat}
    def ticks-eq : evidence {ticks 0 ≡ zeros : Stream Nat} := ticks-holds 0

    param widen : run Π (x : I64) → I64
    param widen-holds : evidence Π (x : I64) → {widen x ≡ x : I64}
    def widen-eq : evidence {widen (toI64 0) ≡ toI64 0 : I64} := widen-holds (toI64 0)

    param spare : run Π (n : Nat) → Nat

    def same-nil : evidence {decide k0 nil ≡ decide k1 nil : Bool} :=
      rewrite (decide-is-rule k0 nil) motive (λ z → {z ≡ decide k1 nil : Bool}) in
      rewrite (decide-is-rule k1 nil) motive (λ z → {true ≡ z : Bool}) in
      refl
    """)

    write_book(dir, "impl.muro", """
    import "conformance.muro"

    def decide : run Π (k : Key) → Π (t : List Item) → Bool :=
      λ (k : Key) → λ (t : List Item) → rule k t

    def decide-is-rule : evidence Π (k : Key) → Π (t : List Item) → {decide k t ≡ rule k t : Bool} :=
      λ (k : Key) → λ (t : List Item) → refl

    def observe : run Π (s : Stream Nat) → Nat :=
      λ (_ : Stream Nat) → 0

    def observe-holds : evidence Π (s : Stream Nat) → {observe s ≡ 0 : Nat} :=
      λ (_ : Stream Nat) → refl

    def hoist : run Π (f : Π (b : Bool) → Bool) → Π (b : Bool) → Bool :=
      λ (f : Π (b : Bool) → Bool) → λ (b : Bool) → f b

    def hoist-holds : evidence Π (b : Bool) → {hoist idb b ≡ b : Bool} :=
      λ (b : Bool) → refl

    def ticks : run Π (n : Nat) → Stream Nat :=
      λ (_ : Nat) → zeros

    def ticks-holds : evidence Π (n : Nat) → {ticks n ≡ zeros : Stream Nat} :=
      λ (_ : Nat) → refl

    def widen : run Π (x : I64) → I64 :=
      λ (x : I64) → x

    def widen-holds : evidence Π (x : I64) → {widen x ≡ x : I64} :=
      λ (x : I64) → refl

    def spare : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    """)
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
