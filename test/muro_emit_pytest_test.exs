defmodule Muro.EmitPytestTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.Emit.Pytest

  # Resolved when this file is compiled. MURO_PYTEST_PYTHON names the
  # interpreter when it is set. Otherwise this is python3 on PATH.
  # The live tests run `python3 -m pytest`. A missing pytest skips
  # them locally. CI raises so the job cannot pass without it.
  @python (
            env = System.get_env("MURO_PYTEST_PYTHON")

            cond do
              is_binary(env) and env != "" and File.regular?(env) ->
                env

              is_binary(env) and env != "" ->
                System.find_executable(env)

              true ->
                System.find_executable("python3")
            end
          )

  @have_pytest is_binary(@python) and
                 match?(
                   {_, 0},
                   System.cmd(@python, ["-c", "import pytest"], stderr_to_stdout: true)
                 )

  if (System.get_env("CI") not in [nil, ""] or System.get_env("GITHUB_ACTIONS") not in [nil, ""]) and
       not @have_pytest do
    raise "python3 -m pytest is required in CI and was not found"
  end

  @pytest_skip if(@have_pytest, do: false, else: "python3 -m pytest is not available")

  @book """
  data Color : Type where
    red : Color
    box : Nat → Color
  data List (A : Type) : Type where
    nil : List A
    cons : A → List A → List A
  def round : run Π (n : Nat) → Nat :=
    λ (n : Nat) → n
  def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
  def round_ok : evidence {round (suc (suc 0)) ≡ suc (suc 0) : Nat} := refl
  def unit : run Unit := tt
  def unit-ok : evidence {unit ≡ tt : Unit} := refl
  def paint : run Color := red
  def paint-ok : evidence {paint ≡ red : Color} := refl
  def boxed : run Color := box (suc (suc 0))
  def boxed-ok : evidence {boxed ≡ box (suc (suc 0)) : Color} := refl
  def pair : run Nat × Nat := (suc 0, suc (suc 0))
  def pair-ok : evidence {pair ≡ (suc 0, suc (suc 0)) : Nat × Nat} := refl
  def bite : run U8 := toU8 5
  def bite-ok : evidence {bite ≡ toU8 5 : U8} := refl
  def neg : run I64 := subi (toI64 0) (toI64 (suc 0))
  def neg-ok : evidence {neg ≡ subi (toI64 0) (toI64 (suc 0)) : I64} := refl
  def flag : run WBool := wtrue
  def flag-ok : evidence {flag ≡ wtrue : WBool} := refl
  def hole : run Opt U8 := wnone
  def hole-ok : evidence {hole ≡ wnone : Opt U8} := refl
  def hit : run Opt U8 := wsome (toU8 5)
  def hit-ok : evidence {hit ≡ wsome (toU8 5) : Opt U8} := refl
  def say : run String := "hi"
  def say-ok : evidence {say ≡ "hi" : String} := refl
  def raw : run Bytes := b"ab"
  def raw-ok : evidence {raw ≡ b"ab" : Bytes} := refl
  def nums : run List Nat := cons (suc 0) nil
  def nums-ok : evidence {nums ≡ cons (suc 0) nil : List Nat} := refl
  ν Stream (A : Type) : Type where
    uncons : Stream A → A × Stream A
  def zeros : run Stream Nat :=
    unfold 0 (λ (_ : Nat) → (0, 0))
  def keep : run Π (s : Stream Nat) → Stream Nat :=
    λ (s : Stream Nat) → s
  def keep-eq : evidence {keep zeros ≡ zeros : Stream Nat} := refl
  def class : run Unit := tt
  def class-ok : evidence {class ≡ tt : Unit} := refl
  """

  @names ~w(
    round-ok round_ok unit-ok paint-ok boxed-ok pair-ok bite-ok neg-ok
    flag-ok hole-ok hit-ok say-ok raw-ok nums-ok keep-eq class-ok
  )

  @open_param """
  param p : run Nat
  param p-is : evidence {p ≡ 0 : Nat}
  def held : evidence {p ≡ 0 : Nat} := p-is
  """

  test "a hyphen folds, a keyword gains a trailing underscore, and a digit is prefixed" do
    assert Pytest.python_base("round-ok") == "round_ok"
    assert Pytest.python_base("class") == "class_"
    assert Pytest.python_base("None") == "None_"
    assert Pytest.python_base("lambda") == "lambda_"
    assert Pytest.python_base("def") == "def_"
    assert Pytest.python_base("2nd") == "muro_2nd"
    assert Pytest.python_base("match") == "match"
    assert Pytest.python_base("case") == "case"
    assert Pytest.python_module("rounding.muro") == "rounding"
    assert Pytest.python_module("/tmp/word-kind.muro") == "word_kind"
    assert Pytest.python_module("half_ok.muro") == "half_ok"
    assert Pytest.impl_env("examples/rounding.muro") == "MURO_IMPL_ROUNDING"
    assert Pytest.impl_env("word-kind.muro") == "MURO_IMPL_WORD_KIND"
    assert Pytest.impl_env("half_ok.muro") == "MURO_IMPL_HALF_OK"
    assert Pytest.impl_env("foo-bar.muro") == "MURO_IMPL_FOO_BAR"
    assert Pytest.impl_env("foo_bar.muro") == Pytest.impl_env("foo-bar.muro")
    assert Pytest.impl_env("a/foo-bar.muro") == Pytest.impl_env("b/foo_bar.muro")
    assert Pytest.module_name?("pkg.rounding")
    refute Pytest.module_name?("class")
    refute Pytest.module_name?("my.class")
    refute Pytest.module_name?(".rounding")
    refute Pytest.module_name?("1bad")
    refute Pytest.module_name?("")
  end

  test "print_value renders the host literals" do
    assert Pytest.print_value(:ze, []) == {:ok, "0"}
    assert Pytest.print_value({:nat, 2}, []) == {:ok, "2"}
    assert Pytest.print_value(:one, []) == {:ok, "None"}
    assert Pytest.print_value({:pair, {:nat, 1}, {:nat, 2}}, []) == {:ok, "(1, 2)"}
    assert Pytest.print_value({:word, {:lit, :u8, 5}, []}, []) == {:ok, "5"}
    assert Pytest.print_value({:word, {:lit, :i64, 0}, []}, []) == {:ok, "0"}

    assert Pytest.print_value({:word, {:lit, :i64, 18_446_744_073_709_551_615}, []}, []) ==
             {:ok, "-1"}

    assert Pytest.print_value({:word, {:lit, :i64, 9_223_372_036_854_775_808}, []}, []) ==
             {:ok, "-9223372036854775808"}

    assert Pytest.print_value({:word, true, []}, []) == {:ok, "\"wtrue\""}
    assert Pytest.print_value({:word, :none, []}, []) == {:ok, "\"wnone\""}
    assert Pytest.print_value({:slit, "hi"}, []) == {:ok, "\"hi\""}
    assert Pytest.print_value({:slit, "a\"b"}, []) == {:ok, "\"a\\\"b\""}
    assert Pytest.print_value({:blit, "ab"}, []) == {:ok, "b\"ab\""}
    assert Pytest.print_value({:blit, <<255>>}, []) == {:ok, "b\"\\xff\""}
    assert Pytest.print_value({:lam, :affine, :nat, "n", :ze}, []) == {:error, :function}
    assert Pytest.print_value({:unf, :ze, :ze}, []) == {:error, :stream}
  end

  test "a book with n closed equations emits n tests, and words are literals" do
    {dir, path} = book("rounding.muro", @book)

    assert {:ok, %{source: source, skips: skips, tests: tests}} =
             Muro.emit_pytest(path, root: dir, book: "rounding.muro")

    assert tests + length(skips) == length(@names)
    assert length(skips) == 1
    assert hd(skips).name == "keep-eq"
    assert hd(skips).reason =~ "stream"
    assert Enum.map(test_funs(source), & &1) |> length() == length(@names)
    assert ids(source) == Enum.map(@names, &"rounding.muro #{&1}")

    assert source =~ "def test_round_ok("
    assert source =~ "def test_round_ok_2("
    assert source =~ "muro_impl.round(1) == 1"
    assert source =~ "muro_impl.round(2) == 2"
    assert source =~ "muro_impl.unit() == None"
    assert source =~ "muro_impl.paint() == \"red\""
    assert source =~ "muro_impl.boxed() == (\"box\", 2)"
    assert source =~ "muro_impl.pair() == (1, 2)"
    assert source =~ "muro_impl.bite() == 5"
    assert source =~ "muro_impl.neg() == -1"
    assert source =~ "muro_impl.flag() == \"wtrue\""
    assert source =~ "muro_impl.hole() == \"wnone\""
    assert source =~ "muro_impl.hit() == (\"wsome\", 5)"
    assert source =~ "muro_impl.say() == \"hi\""
    assert source =~ "muro_impl.raw() == b\"ab\""
    assert source =~ "muro_impl.nums() == (\"cons\", 1, \"nil\")"
    assert source =~ "muro_impl.class_() == None"
    assert source =~ "(\"class_\", 0)"
    refute source =~ "muro_impl.keep("

    keep = hd(skips)
    reason = "#{keep.name} (#{keep.file}:#{keep.line}): #{keep.reason}"
    assert source =~ "@pytest.mark.skip(reason=#{inspect_py(reason)})"
    assert source =~ "def test_keep_eq(_muro_id):"

    assert source =~ "MURO_BOOK = \"#{Muro.Gen.book_hash(dir, "rounding.muro")}\""
    assert source =~ "_MURO_IMPL_ENV = \"MURO_IMPL_ROUNDING\""
    assert source =~ "_MURO_IMPL_DEFAULT = \"rounding\""
    assert source =~ "os.environ.get(_MURO_IMPL_ENV)"
    refute source =~ dir

    # ExUnit skips neg-ok because that normal form is a machine term.
    # Pytest keeps the equation. The candidate counts match. This does
    # not compare the ExUnit source.
    {:ok, ex} = Muro.emit_exunit(path, RoundingTest, root: dir, book: "rounding.muro")
    assert ex.tests + length(ex.skips) == length(@names)
    assert "neg-ok" in Enum.map(ex.skips, & &1.name)
    assert Enum.find(ex.skips, &(&1.name == "neg-ok")).reason =~ "machine term"
    refute Enum.any?(skips, &(&1.name == "neg-ok"))

    {stdout, stderr} = capture_emit([path, "--backend", "pytest"])
    assert stdout =~ "def test_round_ok("
    assert stderr =~ "#{tests} tests, #{length(skips)} skipped"
    assert stderr =~ "skipped keep-eq ("
    assert stderr =~ "): argument 1 normal form is a stream"
  end

  test "--impl bakes the module, and another backend refuses the flag" do
    {dir, path} = book("rounding.muro", @book)

    assert {:ok, %{source: source}} =
             Muro.emit_pytest(path, root: dir, book: "rounding.muro", impl: "pkg.rounding")

    assert source =~ "_MURO_IMPL_DEFAULT = \"pkg.rounding\""
    assert source =~ "_MURO_IMPL_ENV = \"MURO_IMPL_ROUNDING\""

    assert {:raise, "", "--impl must be a Python module name, got: \"class\""} =
             Muro.CLI.Emit.run([path, "--backend", "pytest", "--impl", "class"])

    assert {:raise, "", "--impl is only valid with --backend pytest"} =
             Muro.CLI.Emit.run([path, "--backend", "exunit", "--impl", "rounding"])

    assert_raise Mix.Error, ~r/--impl is only valid with --backend pytest/, fn ->
      Mix.Tasks.Muro.Emit.run([path, "--impl", "rounding"])
    end
  end

  test "pytest accepts an unsupplied param and --imports" do
    {dir, path} = book("lib.muro", @open_param)

    assert {:error, refused} = Muro.emit_file(path, Lib)
    assert refused =~ "param p is supplied by a file that imports this one"

    assert {:ok, %{tests: 1, skips: [], source: source}} =
             Muro.emit_pytest(path, root: dir, book: "lib.muro")

    assert source =~ "muro_impl.p() == 0"
    assert source =~ "(\"p\", 0)"

    write_book(dir, "use.muro", """
    import "lib.muro"
    def q : run Nat := 0
    def q-ok : evidence {q ≡ 0 : Nat} := refl
    """)

    use = Path.join(dir, "use.muro")

    assert {:ok, %{tests: 1, skips: []}} =
             Muro.emit_pytest(use, root: dir, book: "use.muro")

    assert {:ok, %{tests: 2, skips: [], source: imported}} =
             Muro.emit_pytest(use, root: dir, book: "use.muro", imports: true)

    assert ids(imported) == ["use.muro q-ok", "lib.muro held"]
  end

  test "mix muro.gen writes a pytest file and --check sees drift" do
    dir = tmp_dir()

    write_book(dir, "priv/muro/round.muro", """
    def round : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
    def step : run internal Π (n : Nat) → Nat :=
      λ (n : Nat) → suc n
    def step-ok : evidence {step 0 ≡ suc 0 : Nat} := refl
    """)

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "#{Mix.Tasks.Muro.version()}",
      modules: [
        {"priv/muro/round.muro", "test/test_round.py", [kind: :pytest, impl: "host.rounding"]}
      ]
    ]
    """)

    output =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run([]) end)
      end)

    assert output =~ "written test/test_round.py\n"
    assert output =~ "skipped test/test_round.py: step-ok (priv/muro/round.muro:"

    suite = File.read!(Path.join(dir, "test/test_round.py"))
    assert {:ok, header} = Muro.Gen.parse_header(suite)
    assert header.book == "priv/muro/round.muro"
    assert header.version == Mix.Tasks.Muro.version()
    assert header.book_hash == Muro.Gen.book_hash(dir, "priv/muro/round.muro")
    assert header.body_hash == Muro.Gen.body_hash(header.body)
    assert header.body =~ "def test_round_ok("
    assert header.body =~ "@pytest.mark.skip(reason="
    assert header.body =~ "_MURO_IMPL_DEFAULT = \"host.rounding\""
    assert suite =~ "# Generated by Muro #{Mix.Tasks.Muro.version()}"
    refute suite =~ dir

    again =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run([]) end)
      end)

    assert again =~ "unchanged test/test_round.py\n"
    assert File.read!(Path.join(dir, "test/test_round.py")) == suite

    check =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run(["--check"]) end)
      end)

    assert check == "ok\n"

    File.write!(
      Path.join(dir, "test/test_round.py"),
      String.replace(suite, "rounding", "other", global: false)
    )

    assert check_error(dir) =~ "hand-edited target"

    File.write!(Path.join(dir, "test/test_round.py"), suite)

    write_book(dir, "priv/muro/round.muro", """
    def round : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
    def step : run internal Π (n : Nat) → Nat :=
      λ (n : Nat) → suc n
    def step-ok : evidence {step 0 ≡ suc 0 : Nat} := refl
    def extra : evidence {round 0 ≡ 0 : Nat} := refl
    """)

    assert check_error(dir) =~ "stale target"
  end

  @tag skip: @pytest_skip
  test "pytest passes a correct implementation and names the equation it fails" do
    {dir, path} = book("rounding.muro", @book)

    assert {:ok, %{source: source, tests: tests, skips: skips}} =
             Muro.emit_pytest(path, root: dir, book: "rounding.muro")

    File.write!(Path.join(dir, "rounding_test.py"), source)
    File.write!(Path.join(dir, "rounding.py"), correct_impl())

    {out, code} = pytest(dir)
    assert code == 0, out
    assert out =~ "#{tests} passed"
    assert out =~ "#{length(skips)} skipped"

    File.write!(Path.join(dir, "rounding.py"), wrong_impl())
    {bad, bad_code} = pytest(dir)
    assert bad_code == 1
    line = line_of(@book, "round-ok")
    assert bad =~ "rounding.muro:#{line} round-ok"

    File.write!(Path.join(dir, "rounding.py"), missing_round())
    {missing, missing_code} = pytest(dir)
    assert missing_code == 1
    assert missing =~ "round/1"
    assert missing =~ "rounding"

    File.rm!(Path.join(dir, "rounding.py"))
    {gone, gone_code} = pytest(dir)
    assert gone_code == 1
    assert gone =~ "implementation module rounding could not be imported"

    File.write!(Path.join(dir, "rounding.py"), wrong_impl())
    File.write!(Path.join(dir, "rounding_good.py"), correct_impl())
    {over, over_code} = pytest(dir, %{"MURO_IMPL_ROUNDING" => "rounding_good"})
    assert over_code == 0, over
    assert File.read!(Path.join(dir, "rounding_test.py")) == source
    assert source =~ "_MURO_IMPL_DEFAULT = \"rounding\""
    refute source =~ "rounding_good"
  end

  @tag skip: @pytest_skip
  test "round/2 where round/1 is expected names round/1" do
    {dir, path} = book("rounding.muro", @book)

    assert {:ok, %{source: source}} =
             Muro.emit_pytest(path, root: dir, book: "rounding.muro")

    File.write!(Path.join(dir, "rounding_test.py"), source)
    File.write!(Path.join(dir, "rounding.py"), wrong_arity())

    {out, code} = pytest(dir)
    assert code == 1
    assert out =~ "implementation module rounding does not export round/1"
  end

  test "mix muro.gen refuses pytest entries that share one MURO_IMPL variable" do
    dir = tmp_dir()
    write_book(dir, "foo-bar.muro", "def n : run Nat := 0\n")
    write_book(dir, "foo_bar.muro", "def n : run Nat := 0\n")
    write_book(dir, "other.muro", "def n : run Nat := 0\n")

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "#{Mix.Tasks.Muro.version()}",
      modules: [
        {"foo-bar.muro", "test/foo_bar_a.py", [kind: :pytest]},
        {"other.muro", "test/other_test.py", [kind: :pytest]},
        {"foo_bar.muro", "test/foo_bar_b.py", [kind: :pytest]}
      ]
    ]
    """)

    message = check_error(dir, [])

    assert message =~
             "MURO_IMPL_FOO_BAR is shared by pytest modules entries 1 (foo-bar.muro), 3 (foo_bar.muro)"

    refute File.exists?(Path.join(dir, "test/foo_bar_a.py"))
    refute File.exists?(Path.join(dir, "test/other_test.py"))
  end

  defp correct_impl do
    ~S"""
    def round(n):
        return n

    def unit():
        return None

    def paint():
        return "red"

    def boxed():
        return ("box", 2)

    def pair():
        return (1, 2)

    def bite():
        return 5

    def neg():
        return -1

    def flag():
        return "wtrue"

    def hole():
        return "wnone"

    def hit():
        return ("wsome", 5)

    def say():
        return "hi"

    def raw():
        return b"ab"

    def nums():
        return ("cons", 1, "nil")

    def class_():
        return None
    """
  end

  defp wrong_impl do
    String.replace(correct_impl(), "return n", "return n + 1")
  end

  defp missing_round do
    String.replace(correct_impl(), ~r/def round\(n\):\n    return n\n\n/, "")
  end

  defp wrong_arity do
    String.replace(correct_impl(), "def round(n):", "def round(n, extra):")
  end

  defp pytest(dir, extra \\ %{}) do
    env =
      System.get_env()
      |> Map.merge(extra)
      |> Map.merge(%{"PYTHONPATH" => dir, "PYTHONDONTWRITEBYTECODE" => "1"})

    {out, code} =
      System.cmd(
        @python,
        ["-m", "pytest", "-q", "--tb=short", "-p", "no:cacheprovider", "rounding_test.py"],
        cd: dir,
        env: env,
        stderr_to_stdout: true
      )

    {out, code}
  end

  defp inspect_py(text) do
    case Pytest.print_value({:slit, text}, []) do
      {:ok, src} -> src
    end
  end

  defp test_funs(source) do
    Regex.scan(~r/^def (test_[A-Za-z_][A-Za-z0-9_]*)\(/m, source)
    |> Enum.map(fn [_, name] -> name end)
  end

  defp ids(source) do
    Regex.scan(~r/ids=\["((?:\\.|[^"\\])*)"\]/, source)
    |> Enum.map(fn [_, id] -> Macro.unescape_string(id) end)
  end

  defp line_of(source, name) do
    source
    |> String.split("\n")
    |> Enum.find_index(&String.starts_with?(&1, "def #{name} :"))
    |> Kernel.+(1)
  end

  defp capture_emit(args) do
    ref = make_ref()
    parent = self()

    capture_io(:stderr, fn ->
      out = capture_io(fn -> Mix.Tasks.Muro.Emit.run(args) end)
      send(parent, {ref, out})
    end)
    |> then(fn err ->
      receive do
        {^ref, out} -> {out, err}
      end
    end)
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

  defp check_error(dir, args \\ ["--check"]) do
    in_dir(dir, fn ->
      assert_raise Mix.Error, fn -> Mix.Tasks.Muro.Gen.run(args) end
    end).message
  end

  defp in_dir(dir, fun), do: File.cd!(dir, fun)

  defp capture(fun) do
    fun
    |> ExUnit.CaptureIO.capture_io()
    |> String.replace(~r/^==> \S+\n/m, "")
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_pytest_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
