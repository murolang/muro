defmodule Muro.EmitRustTestSuiteTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.Emit.RustTest

  # Resolved when this file is compiled. A missing rustc skips the
  # live tests. CI does not raise: a runner without rustc still
  # checks the source the emitter prints.
  @rustc (
           path =
             System.find_executable("rustc") ||
               Path.join(System.user_home!(), ".cargo/bin/rustc")

           if is_binary(path) and File.regular?(path), do: path, else: nil
         )

  @rustc_skip if(@rustc, do: false, else: "rustc is not available")

  @golden """
  def round : run Π (n : Nat) → Nat :=
    λ (n : Nat) → n
  def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
  def step : run internal Π (n : Nat) → Nat :=
    λ (n : Nat) → suc n
  def step-ok : evidence {step 0 ≡ suc 0 : Nat} := refl
  """

  @live """
  data Color : Type where
    red : Color
    box : Nat → Color
  data NatList : Type where
    nil : NatList
    cons : Nat → NatList → NatList
  unboxed data Flag : Type where
    on : Flag
    off : Flag
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
  def nums : run NatList := cons (suc 0) nil
  def nums-ok : evidence {nums ≡ cons (suc 0) nil : NatList} := refl
  def mark : run Atom := :asc
  def mark-ok : evidence {mark ≡ :asc : Atom} := refl
  def lit : run Flag := on
  def lit-ok : evidence {lit ≡ on : Flag} := refl
  def loop : evidence {round 0 ≡ 0 : Nat} := refl
  def crate : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
  def fn : evidence {unit ≡ tt : Unit} := refl
  def class : run Unit := tt
  def class-ok : evidence {class ≡ tt : Unit} := refl
  def step : run internal Π (n : Nat) → Nat :=
    λ (n : Nat) → suc n
  def step-ok : evidence {step 0 ≡ suc 0 : Nat} := refl
  """

  @skips_book """
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
  data List (A : Type) : Type where
    nil : List A
    cons : A → List A → List A
  def nums : run List Nat := cons (suc 0) nil
  def nums-ok : evidence {nums ≡ cons (suc 0) nil : List Nat} := refl
  def Arr : spec Type := Π (n : Nat) → Nat
  def apply : run Arr := λ (n : Nat) → n
  def apply-eq : evidence {apply (suc 0) ≡ suc 0 : Nat} := refl
  def big : run Nat := 18446744073709551616
  def big-ok : evidence {big ≡ 18446744073709551616 : Nat} := refl
  unboxed data Flag : Type where
    on : Flag
    off : Flag
  def wrapped : run Opt Flag := wsome on
  def wrapped-ok : evidence {wrapped ≡ wsome on : Opt Flag} := refl
  def pair-flag : run Flag × Nat := (on, 0)
  def pair-flag-ok : evidence {pair-flag ≡ (on, 0) : Flag × Nat} := refl
  def t1 : run Tensor I64 (toI64 suc(suc 0)) :=
    packI (toI64 suc 0) (toI64 suc(suc 0))
  def t-eq : evidence {t1 ≡ t1 : Tensor I64 (toI64 suc(suc 0))} := refl
  """

  @skip_reasons %{
    "step-ok" => "step is run internal and is not exported",
    "pred-ok" => "pred is a prelude run and is not defined by the book",
    "via-proof" => "argument 1 is not closed (free variable or unresolved param)",
    "mark-eq" => "marker is not a run definition",
    "fun-eq" => "result normal form is a function",
    "erased-ok" => "argument passed at an erased binder of id",
    "keep-eq" => "argument 1 normal form is a stream",
    "nums-ok" => "result normal form is not comparable in Rust",
    "apply-eq" => "apply is applied to more arguments than its type lists",
    "big-ok" => "result normal form is a Nat that does not fit in u64",
    "wrapped-ok" => "result normal form is an unboxed Opt",
    "pair-flag-ok" => "result normal form is unboxed data in a pair",
    "t-eq" => "result normal form is a machine term"
  }

  @open_param """
  param p : run Nat
  param p-is : evidence {p ≡ 0 : Nat}
  def held : evidence {p ≡ 0 : Nat} := p-is
  """

  test "a hyphen folds, a keyword is raw, and a raw-forbidden name gains a suffix" do
    assert RustTest.test_ident("round-ok") == "round_ok"
    assert RustTest.test_ident("loop") == "r#loop"
    assert RustTest.test_ident("fn") == "r#fn"
    assert RustTest.test_ident("type") == "r#type"
    assert RustTest.test_ident("crate") == "crate_"
    assert RustTest.test_ident("self") == "self_"
    assert RustTest.test_ident("super") == "super_"
    assert RustTest.test_ident("Self") == "Self_"
    assert RustTest.test_ident("2nd") == "muro_2nd"
    assert RustTest.test_ident("u64") == "u64"
    assert RustTest.test_ident("true") == "r#true"
    assert RustTest.module_ident("rounding.muro") == "rounding"
    assert RustTest.module_ident("/tmp/word-kind.muro") == "word_kind"
    assert RustTest.module_ident("fn.muro") == "r#fn"
    assert RustTest.module_ident("crate.muro") == "crate_"
    assert RustTest.module_ident("2nd.muro") == "muro_2nd"
    assert RustTest.sibling_file("word-kind.muro") == "word-kind.rs"
    assert RustTest.module_path?("crate::rounding")
    assert RustTest.module_path?("self::a")
    assert RustTest.module_path?("r#fn")
    assert RustTest.module_path?("rounding")
    refute RustTest.module_path?("fn")
    refute RustTest.module_path?("r#crate")
    refute RustTest.module_path?("a::")
    refute RustTest.module_path?("::rounding")
    refute RustTest.module_path?("1bad")
    refute RustTest.module_path?("")
  end

  test "print_value renders the host literals" do
    assert RustTest.print_value(:ze, []) == {:ok, "muro__from_u64(0)"}
    assert RustTest.print_value({:nat, 2}, []) == {:ok, "muro__from_u64(2)"}

    assert RustTest.print_value({:nat, 18_446_744_073_709_551_615}, []) ==
             {:ok, "muro__from_u64(18446744073709551615)"}

    assert RustTest.print_value({:nat, 18_446_744_073_709_551_616}, []) ==
             {:error, {:text, "normal form is a Nat that does not fit in u64"}}

    assert RustTest.print_value(:one, []) == {:ok, "muro__Unit"}

    assert RustTest.print_value({:pair, {:nat, 1}, {:nat, 2}}, []) ==
             {:ok, "muro__pair(muro__from_u64(1), muro__from_u64(2))"}

    assert RustTest.print_value({:word, {:lit, :u8, 5}, []}, []) == {:ok, "5u8"}
    assert RustTest.print_value({:word, {:lit, :i64, 0}, []}, []) == {:ok, "0i64"}

    assert RustTest.print_value({:word, {:lit, :i64, 18_446_744_073_709_551_615}, []}, []) ==
             {:ok, "(18446744073709551615u64 as i64)"}

    assert RustTest.print_value({:word, true, []}, []) == {:ok, "true"}
    assert RustTest.print_value({:word, :none, []}, []) == {:ok, "::std::option::Option::None"}

    assert RustTest.print_value({:word, :some, [{:word, {:lit, :u8, 5}, []}]}, []) ==
             {:ok, "::std::option::Option::Some(5u8)"}

    assert RustTest.print_value({:slit, "hi"}, []) ==
             {:ok,
              "{ let muro__b: &'static [u8] = &[104, 105]; muro__str { p: muro__b.as_ptr(), n: muro__b.len() } }"}

    assert RustTest.print_value({:blit, "ab"}, []) ==
             {:ok,
              "{ let muro__b: &'static [u8] = &[97, 98]; muro__slice { p: muro__b.as_ptr(), n: muro__b.len() } }"}

    assert RustTest.print_value({:lam, :affine, :nat, "n", :ze}, []) == {:error, :function}
    assert RustTest.print_value({:unf, :ze, :ze}, []) == {:error, :stream}
    assert RustTest.print_value({:toi64, :ze}, []) == {:error, :machine}
    assert RustTest.print_value(:erased, []) == {:error, {:text, "normal form is erased"}}
  end

  test "the golden file is one test and one ignored test" do
    {dir, path} = book("golden.muro", @golden)

    assert {:ok, %{source: source, skips: skips, tests: 1}} =
             Muro.emit_rust_test(path, root: dir, book: "golden.muro")

    assert length(skips) == 1
    assert hd(skips).name == "step-ok"
    assert hd(skips).reason == "step is run internal and is not exported"
    assert test_count(source) == 2
    hash = Muro.Gen.book_hash(dir, "golden.muro")

    assert source == """
           // Closed equations of golden.muro as Rust tests.
           // The tests call golden, the module in golden.rs beside this file.
           // `rustc --test` accepts the two files as siblings.
           // A Cargo `tests/` directory passes `--impl crate::module`.
           #![allow(unused, non_snake_case, non_camel_case_types)]

           const MURO_BOOK: &str = "#{hash}";
           #[path = "golden.rs"]
           mod golden;

           #[test]
           fn round_ok() {
               assert_eq!(golden::round(golden::muro__from_u64(1)), golden::muro__from_u64(1), "golden.muro:3 round-ok");
           }

           #[test]
           #[ignore = "step-ok (golden.muro:6): step is run internal and is not exported"]
           fn step_ok() {}
           """

    refute source =~ dir
  end

  test "a book with no closed equations prints the scaffold" do
    {dir, path} = book("empty.muro", "def round : run Π (n : Nat) → Nat := λ (n : Nat) → n\n")

    assert {:ok, %{source: source, skips: [], tests: 0}} =
             Muro.emit_rust_test(path, root: dir, book: "empty.muro")

    assert source =~ "#[path = \"empty.rs\"]\nmod empty;"
    assert source =~ "const MURO_BOOK"
    refute source =~ "#[test]"
    refute source =~ "fn "

    {stdout, stderr} = capture_emit([path, "--backend", "rust-test"])
    assert stdout =~ "mod empty;"
    assert stderr == "0 tests, 0 skipped\n"
  end

  test "structural skips stay in the file, and a word literal is a test" do
    {dir, path} = book("round.muro", @skips_book)

    assert {:ok, %{source: source, skips: skips, tests: tests}} =
             Muro.emit_rust_test(path, root: dir, book: "round.muro")

    assert tests == 4
    assert length(skips) == 13
    assert tests + length(skips) == test_count(source)
    assert Map.new(skips, &{&1.name, &1.reason}) == @skip_reasons

    for skip <- skips do
      reason = "#{skip.name} (round.muro:#{skip.line}): #{skip.reason}"
      assert source =~ "#[ignore = #{inspect(reason)}]"
      assert skip.line == line_of(@skips_book, skip.name)
    end

    assert source =~ "fn round_ok()"
    assert source =~ "round::round(round::muro__from_u64(1))"
    assert source =~ "fn i64_eq()"
    assert source =~ "round::idI(0i64)"
    assert source =~ "fn keep_eq() {}"
    refute source =~ "round::keep("
    refute source =~ "all-n"
    refute source =~ "zero-eq"
    refute source =~ "head-zeros"
    refute Enum.any?(skips, &(&1.name == "i64-eq"))
    refute source =~ dir

    {stdout, stderr} = capture_emit([path, "--backend", "rust-test"])
    assert stdout =~ "fn round_ok()"
    assert stderr =~ "4 tests, 13 skipped"
    assert stderr =~ "skipped big-ok ("
    assert stderr =~ "): result normal form is a Nat that does not fit in u64"
  end

  test "a keyword module reserves the raw name, and --impl bakes a path" do
    {dir, path} =
      book("fn.muro", """
      def round : run Π (n : Nat) → Nat :=
        λ (n : Nat) → n
      def fn : evidence {round 0 ≡ 0 : Nat} := refl
      """)

    assert {:ok, %{source: source, tests: 1, skips: []}} =
             Muro.emit_rust_test(path, root: dir, book: "fn.muro")

    assert source =~ "#[path = \"fn.rs\"]\nmod r#fn;"
    assert source =~ "fn fn_2()"
    assert source =~ "r#fn::round(r#fn::muro__from_u64(0))"
    refute source =~ "fn r#fn()"

    assert {:ok, %{source: baked}} =
             Muro.emit_rust_test(path, root: dir, book: "fn.muro", impl: "crate::rounding")

    assert baked =~ "// The tests call crate::rounding."
    assert baked =~ "crate::rounding::round("
    refute baked =~ "#[path"

    assert {:raise, "", "--impl must be a Rust path, got: \"fn\""} =
             Muro.CLI.Emit.run([path, "--backend", "rust-test", "--impl", "fn"])

    assert {:raise, "", "--node writes the placement calls"} =
             Muro.CLI.Emit.run([path, "--backend", "rust-test", "--node", "a"])
  end

  test "rust-test accepts an unsupplied param and --imports" do
    {dir, path} = book("lib.muro", @open_param)

    assert {:error, refused} = Muro.emit_file(path, Lib)
    assert refused =~ "param p is supplied by a file that imports this one"

    assert {:ok, %{tests: 1, skips: [], source: source}} =
             Muro.emit_rust_test(path, root: dir, book: "lib.muro")

    assert source =~ "lib::p()"
    assert source =~ "lib::muro__from_u64(0)"

    write_book(dir, "use.muro", """
    import "lib.muro"
    def q : run Nat := 0
    def q-ok : evidence {q ≡ 0 : Nat} := refl
    """)

    use = Path.join(dir, "use.muro")

    assert {:ok, %{tests: 1, skips: []}} =
             Muro.emit_rust_test(use, root: dir, book: "use.muro")

    assert {:ok, %{tests: 2, skips: [], source: imported}} =
             Muro.emit_rust_test(use, root: dir, book: "use.muro", imports: true)

    assert imported =~ "use.muro:3 q-ok"
    assert imported =~ "lib.muro:3 held"
  end

  test "mix muro.gen writes a rust test file and --check sees drift" do
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
        {"priv/muro/round.muro", "test/rounding_test.rs",
         [kind: :rust_test, impl: "crate::rounding"]}
      ]
    ]
    """)

    output =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run([]) end)
      end)

    assert output =~ "written test/rounding_test.rs\n"
    assert output =~ "skipped test/rounding_test.rs: step-ok (priv/muro/round.muro:"

    suite = File.read!(Path.join(dir, "test/rounding_test.rs"))
    assert {:ok, header} = Muro.Gen.parse_header(suite)
    assert header.book == "priv/muro/round.muro"
    assert header.version == Mix.Tasks.Muro.version()
    assert header.book_hash == Muro.Gen.book_hash(dir, "priv/muro/round.muro")
    assert header.body_hash == Muro.Gen.body_hash(header.body)
    assert header.body =~ "fn round_ok()"
    assert header.body =~ "#[ignore = "
    assert header.body =~ "crate::rounding::round("
    assert suite =~ "// Generated by Muro #{Mix.Tasks.Muro.version()}"
    refute suite =~ dir

    again =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run([]) end)
      end)

    assert again =~ "unchanged test/rounding_test.rs\n"
    assert File.read!(Path.join(dir, "test/rounding_test.rs")) == suite

    check =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run(["--check"]) end)
      end)

    assert check == "ok\n"

    File.write!(
      Path.join(dir, "test/rounding_test.rs"),
      String.replace(suite, "rounding", "other", global: false)
    )

    assert check_error(dir) =~ "hand-edited target"

    File.write!(Path.join(dir, "test/rounding_test.rs"), suite)

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

  @tag skip: @rustc_skip
  test "rustc --test passes the emitted image and names a wrong answer" do
    {dir, path} = book("rounding.muro", @live)

    assert {:ok, %{source: source, tests: 20, skips: skips}} =
             Muro.emit_rust_test(path, root: dir, book: "rounding.muro")

    assert length(skips) == 1
    assert hd(skips).name == "step-ok"
    File.write!(Path.join(dir, "rounding_test.rs"), source)
    assert {:ok, [rs]} = Muro.emit_rust(path)
    assert Path.basename(rs) == "rounding.rs"

    {out, code} = rustc_test(dir, "rounding_test.rs")
    assert code == 0, out
    assert out =~ "20 passed"
    assert out =~ "1 ignored"
    refute out =~ "warning:", out

    impl = File.read!(Path.join(dir, "rounding.rs"))

    File.write!(
      Path.join(dir, "rounding.rs"),
      String.replace(
        impl,
        "pub fn round(n: muro__Nat) -> muro__Nat {\n    n.clone()\n}",
        "pub fn round(n: muro__Nat) -> muro__Nat {\n    muro__from_u64(0)\n}",
        global: false
      )
    )

    {bad, bad_code} = rustc_test(dir, "rounding_test.rs")
    # rustc's test harness exits 101 when an assertion fails.
    assert bad_code == 101
    line = line_of(@live, "round-ok")
    assert bad =~ "rounding.muro:#{line} round-ok"
  end

  defp test_count(source) do
    Regex.scan(~r/^fn /m, source) |> length()
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
    dir = Path.join(System.tmp_dir!(), "muro_rust_test_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp rustc_test(dir, file) do
    System.cmd(@rustc, ["--edition", "2021", "--test", file, "-o", "suite"],
      cd: dir,
      stderr_to_stdout: true
    )
    |> then(fn {compiled, status} ->
      if status == 0 do
        {ran, ran_status} = System.cmd(Path.join(dir, "suite"), [], stderr_to_stdout: true)
        {compiled <> ran, ran_status}
      else
        {compiled, status}
      end
    end)
  end
end
