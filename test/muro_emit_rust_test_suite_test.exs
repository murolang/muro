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

  # A direct boxed cycle is walked on a heap stack. `Nest` is that cycle
  # and also stores itself in a pair, so the pair is on the same walk.
  # `Twin` reaches itself only through a pair, so it keeps the derived walk.
  # `Spine` carries a `Mark` that can cross the 1024-byte print.
  @deep """
  data Color : Type where
    red : Color
    box : Nat → Color
  data NatList : Type where
    nil : NatList
    cons : Nat → NatList → NatList
  data Knot : Type where
    go : Knot → Knot
  data A : Type where
    a0 : A
    a1 : B → A
  data B : Type where
    b0 : B
    b1 : A → B
  data Twin : Type where
    tip : Twin
    bin : Twin × Twin → Twin
  data Nest : Type where
    tipn : Nest
    grow : Nest → Nest
    wrap : Nest × Unit → Nest
  data Mark : Type where
    aaaaaaaaaaaaaaaaaaaaaaa : Mark
    baaaaaaaaaaaaaaaaaaaaaa : Mark
  data Spine : Type where
    stop : Spine
    link : Mark → Spine → Spine
  def len0 : run Π (xs : NatList) → Nat :=
    λ (xs : NatList) →
      match xs motive (λ _ → Nat)
        | nil => 0
        | cons _ _ => suc 0
  def peel : run Π (k : Knot) → Nat :=
    λ (k : Knot) →
      match k motive (λ _ → Nat)
        | go _ => 0
  def keep : run Π (xs : NatList) → NatList :=
    λ (xs : NatList) → xs
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
             {:error, {:text, "normal form is a Nat above 100000"}}

    assert RustTest.print_value({:nat, 100_000}, []) == {:ok, "muro__from_u64(100000)"}

    assert RustTest.print_value({:nat, 100_001}, []) ==
             {:error, {:text, "normal form is a Nat above 100000"}}

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

  @forbidden_clash """
  def round : run Π (n : Nat) → Nat :=
    λ (n : Nat) → n
  def crate : evidence {round 0 ≡ 0 : Nat} := refl
  def crate_ : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
  def self : evidence {round 0 ≡ 0 : Nat} := refl
  def self_ : evidence {round 0 ≡ 0 : Nat} := refl
  def super : evidence {round 0 ≡ 0 : Nat} := refl
  def super_ : evidence {round 0 ≡ 0 : Nat} := refl
  def Self : evidence {round 0 ≡ 0 : Nat} := refl
  def Self_ : evidence {round 0 ≡ 0 : Nat} := refl
  """

  test "a finished keyword does not collide with an evidence of that spelling" do
    {dir, path} = book("idents.muro", @forbidden_clash)

    assert {:ok, %{source: source, tests: 8, skips: []}} =
             Muro.emit_rust_test(path, root: dir, book: "idents.muro")

    assert fn_names(source) == [
             "crate_",
             "crate__2",
             "self_",
             "self__2",
             "super_",
             "super__2",
             "Self_",
             "Self__2"
           ]

    assert {:ok, %{source: baked, tests: 8, skips: []}} =
             Muro.emit_rust_test(path, root: dir, book: "idents.muro", impl: "crate::idents")

    assert fn_names(baked) == fn_names(source)
    assert baked =~ "crate::idents::round("
    refute baked =~ "#[path"

    {dir, crate_path} = book("crate.muro", @forbidden_clash)

    assert {:ok, %{source: reserved}} =
             Muro.emit_rust_test(crate_path, root: dir, book: "crate.muro")

    assert reserved =~ "mod crate_;"
    assert fn_names(reserved) |> Enum.take(2) == ["crate_2", "crate__2"]
    refute reserved =~ "fn crate_()"

    assert {:ok, %{source: crate_baked}} =
             Muro.emit_rust_test(crate_path, root: dir, book: "crate.muro", impl: "crate::idents")

    assert fn_names(crate_baked) |> Enum.take(2) == ["crate_", "crate__2"]
    refute crate_baked =~ "fn crate_2()"
  end

  test "a Nat above 100000 used as an argument is a skip" do
    {dir, path} =
      book("wide.muro", """
      def round : run Π (n : Nat) → Nat :=
        λ (n : Nat) → n
      def wide-arg : evidence {round 100001 ≡ 100001 : Nat} := refl
      def fit : evidence {round 100000 ≡ 100000 : Nat} := refl
      """)

    assert {:ok, %{source: source, tests: 1, skips: skips}} =
             Muro.emit_rust_test(path, root: dir, book: "wide.muro")

    assert [%{name: "wide-arg", reason: reason, line: line}] = skips
    assert reason == "argument 1 normal form is a Nat above 100000"
    assert source =~ "#[ignore = #{inspect("wide-arg (wide.muro:#{line}): #{reason}")}]"
    assert source =~ "fn fit()"
    assert source =~ "muro__from_u64(100000)"
    refute source =~ "100001"
  end

  @tag skip: @rustc_skip
  test "rustc compares two Nats of 100000, equal and unequal" do
    {dir, path} =
      book("wide.muro", """
      def round : run Π (n : Nat) → Nat :=
        λ (n : Nat) → n
      def wide-arg : evidence {round 100001 ≡ 100001 : Nat} := refl
      def fit : evidence {round 100000 ≡ 100000 : Nat} := refl
      """)

    assert {:ok, %{source: source, tests: 1, skips: skips}} =
             Muro.emit_rust_test(path, root: dir, book: "wide.muro")

    assert length(skips) == 1
    assert source =~ "fn fit()"

    # `fit` is the emitted equality. This second test is the unequal
    # pair, a failing `assert_eq!` that prints both counts, a shared
    # clone, and `Drop`, on a stack too small for a recursive walk of
    # 100000 successors.
    extra = """
    #[test]
    fn cap_ne() {
        let ran = ::std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let a = wide::muro__from_u64(100000);
                let b = wide::muro__from_u64(100000);
                assert!(a == b);
                let d = wide::muro__from_u64(99999);
                assert!(a != d);
                let prev = ::std::panic::take_hook();
                ::std::panic::set_hook(Box::new(|_| {}));
                let failed = ::std::panic::catch_unwind(::std::panic::AssertUnwindSafe(|| {
                    assert_eq!(a, d, "wide.muro:4 fit");
                }));
                ::std::panic::set_hook(prev);
                let c = a.clone();
                assert!(a == c);
                drop(c);
                assert!(wide::muro__to_u64(&a) == 100000);
                drop(a);
                drop(b);
                drop(d);
                failed
            })
            .unwrap()
            .join();
        let payload = match ran {
            ::std::result::Result::Ok(::std::result::Result::Err(payload)) => payload,
            _ => panic!("expected the compare to fail"),
        };
        let msg = match payload.downcast_ref::<::std::string::String>() {
            ::std::option::Option::Some(text) => text.clone(),
            ::std::option::Option::None => match payload.downcast_ref::<&str>() {
                ::std::option::Option::Some(text) => (*text).to_string(),
                ::std::option::Option::None => ::std::string::String::new(),
            },
        };
        assert!(msg.contains("wide.muro:4 fit"), "{msg}");
        assert!(msg.contains("muro__Nat(100000)"), "{msg}");
        assert!(msg.contains("muro__Nat(99999)"), "{msg}");
    }
    """

    File.write!(Path.join(dir, "wide_test.rs"), source <> "\n" <> extra)
    assert {:ok, [rs]} = Muro.emit_rust(path)
    assert Path.basename(rs) == "wide.rs"
    image = File.read!(rs)

    assert String.contains?(image, "impl ::std::cmp::PartialEq for muro__Nat")
    assert String.contains?(image, "impl ::std::fmt::Debug for muro__Nat")
    assert String.contains?(image, "impl ::std::ops::Drop for muro__Nat")
    refute String.contains?(image, "impl ::std::fmt::Debug for muro__NatNode")

    refute String.contains?(image, "fmt::Debug)]\npub struct muro__Nat")
    refute String.contains?(image, "fmt::Debug)]\nenum muro__NatNode")

    {out, code} = rustc_test(dir, "wide_test.rs", ["--test-threads=1"])
    assert code == 0, out
    assert out =~ "2 passed"
    assert out =~ "1 ignored"
    refute out =~ "stack overflow"
    refute out =~ "warning:", out
  end

  test "a boxed cycle walks on a heap stack and a pair cycle stays derived" do
    {_dir, path} = book("deep.muro", @deep)
    assert {:ok, [rs]} = Muro.emit_rust(path)
    image = File.read!(rs)

    assert image =~ "#[derive(::std::clone::Clone)]\npub struct NatList("
    refute image =~ "fmt::Debug)]\npub struct NatList("
    assert image =~ "impl ::std::cmp::PartialEq for NatList"
    assert image =~ "impl ::std::fmt::Debug for NatList"
    assert image =~ "impl ::std::ops::Drop for NatList"
    assert image =~ "fn muro__eq_NatList("
    assert image =~ "fn muro__fmt_NatList("
    assert image =~ "fn muro__drop_NatList("
    assert image =~ "out.push_str(\"...\")"
    assert image =~ "1024usize.saturating_sub(out.len())"
    assert image =~ "is_char_boundary(end)"
    refute image =~ "out.len() >= 1024"
    refute image =~ "Owned(::std::format!"
    assert image =~ "if !stopped {"
    assert image =~ "::std::boxed::Box::new(move || ::std::format!"
    assert image =~ "NatList({}: {})"
    assert image =~ "impl ::std::cmp::PartialEq for Nest"
    assert image =~ "impl ::std::fmt::Debug for Nest"
    assert image =~ "impl ::std::ops::Drop for Nest"
    assert image =~ "muro__try_reveal::<Nest>"
    assert image =~ "downcast::<Nest>"
    assert image =~ "impl ::std::fmt::Debug for Spine"

    assert image =~
             "enum muro__node_NatList {\n    nil,\n    cons(muro__Nat, NatList),\n}"

    assert image =~
             "#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]\npub struct Color("

    refute image =~ "impl ::std::ops::Drop for Color"

    assert image =~ "enum muro__node_Knot {\n    go(Knot),\n    muro__hole,\n}"
    assert image =~ "impl ::std::ops::Drop for Knot"
    assert image =~ "_ => ::std::process::abort()"
    assert length(String.split(image, "_ => ::std::process::abort()")) == 2

    assert image =~ "impl ::std::cmp::PartialEq for A {"
    assert image =~ "impl ::std::cmp::PartialEq for B {"
    assert image =~ "impl ::std::ops::Drop for A {"
    assert image =~ "impl ::std::ops::Drop for B {"
    assert image =~ "muro__drop_A(muro__drop_frame_A::B("
    refute image =~ "fn muro__drop_B("

    assert image =~
             "#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]\npub struct Twin("

    refute image =~ "impl ::std::cmp::PartialEq for Twin"
    refute image =~ "impl ::std::fmt::Debug for Twin"
    refute image =~ "impl ::std::ops::Drop for Twin"
    assert image =~ "pub fn len0("
    assert image =~ "pub fn peel("
  end

  @tag skip: @rustc_skip
  @tag timeout: 180_000
  test "rustc compares, prints, and frees a deep declared value on a small stack" do
    {dir, path} = book("deep.muro", @deep)
    assert {:ok, [rs]} = Muro.emit_rust(path)
    assert Path.basename(rs) == "deep.rs"

    File.write!(Path.join(dir, "deep_test.rs"), """
    #[path = "deep.rs"]
    mod deep;

    fn caught(f: impl FnOnce()) -> ::std::string::String {
        let prev = ::std::panic::take_hook();
        ::std::panic::set_hook(Box::new(|_| {}));
        let failed = ::std::panic::catch_unwind(::std::panic::AssertUnwindSafe(f));
        ::std::panic::set_hook(prev);
        match failed {
            ::std::result::Result::Ok(()) => panic!("expected a failing compare"),
            ::std::result::Result::Err(payload) => match payload.downcast_ref::<::std::string::String>() {
                ::std::option::Option::Some(text) => text.clone(),
                ::std::option::Option::None => match payload.downcast_ref::<&str>() {
                    ::std::option::Option::Some(text) => (*text).to_string(),
                    ::std::option::Option::None => ::std::string::String::new(),
                },
            },
        }
    }

    #[test]
    fn deep_cap() {
        let ran = ::std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                assert!(deep::tip() == deep::tip());
                let z = deep::muro__from_u64(0);
                let one = deep::muro__from_u64(1);
                let p0 = deep::cons(z.clone(), deep::cons(z.clone(), deep::nil()));
                let p1 = deep::cons(one.clone(), deep::cons(z.clone(), deep::nil()));
                assert!(p0 != p1);
                let s0 = ::std::format!("{:?}", p0);
                let s1 = ::std::format!("{:?}", p1);
                assert!(s0 != s1, "{s0} vs {s1}");
                assert!(s0.contains("NatList(3:"), "{s0}");
                assert!(s1.contains("NatList(3:"), "{s1}");
                assert!(s0.contains("muro__Nat(0)"), "{s0}");
                assert!(s1.contains("muro__Nat(1)"), "{s1}");
                assert!(!s0.contains("muro__Nat(1)"), "{s0}");
                assert!(!s0.ends_with("..."), "{s0}");
                assert!(!s1.ends_with("..."), "{s1}");
                drop(p0);
                drop(p1);
                drop(one);
                let natlist = |n: u64| {
                    let mut xs = deep::nil();
                    let mut i = 0u64;
                    while i < n {
                        xs = deep::cons(z.clone(), xs);
                        i += 1;
                    }
                    xs
                };
                let a = natlist(100000);
                let b = natlist(100000);
                assert!(a == b);
                drop(b);
                let shown = ::std::format!("{:?}", a);
                assert!(shown.starts_with("NatList(100001:"), "{shown}");
                assert!(shown.contains("muro__Nat(0)"), "{shown}");
                assert!(shown.len() < 2048, "{}", shown.len());
                assert!(shown.ends_with("...)"), "{shown}");
                let c = natlist(99999);
                let shown_c = ::std::format!("{:?}", c);
                assert!(shown_c.starts_with("NatList(100000:"), "{shown_c}");
                assert!(shown_c.ends_with("...)"), "{shown_c}");
                let nmsg = caught(|| assert_eq!(a, c, "natlist cap"));
                drop(a);
                drop(c);
                drop(z);

                let chain = |n: u64| {
                    let mut a = deep::a0();
                    let mut i = 0u64;
                    while i < n {
                        let b = deep::b1(a);
                        a = deep::a1(b);
                        i += 1;
                    }
                    a
                };
                let m0 = chain(8192);
                let m1 = chain(8192);
                assert!(m0 == m1);
                drop(m1);
                let m2 = chain(8191);
                let amsg = caught(|| assert_eq!(m0, m2, "mutual cap"));
                drop(m0);
                drop(m2);

                let spine = |last_diff: bool| {
                    let same = deep::aaaaaaaaaaaaaaaaaaaaaaa();
                    let diff = deep::baaaaaaaaaaaaaaaaaaaaaa();
                    let mut s = deep::stop();
                    let mut n = 0u64;
                    while n < 24 {
                        let mark = if n == 0 && last_diff { diff.clone() } else { same.clone() };
                        s = deep::link(mark, s);
                        n += 1;
                    }
                    s
                };
                let s0 = spine(false);
                let s1 = spine(true);
                let t0 = ::std::format!("{:?}", s0);
                let t1 = ::std::format!("{:?}", s1);
                drop(s0);
                drop(s1);

                let nest = |n: u64| {
                    let mut v = deep::tipn();
                    let mut i = 0u64;
                    while i < n {
                        if i % 2 == 0 {
                            v = deep::wrap(deep::muro__pair(v, deep::muro__Unit));
                        } else {
                            v = deep::grow(v);
                        }
                        i += 1;
                    }
                    v
                };
                let u0 = nest(100000);
                let u1 = nest(100000);
                assert!(u0 == u1);
                drop(u1);
                let u2 = nest(99999);
                assert!(u0 != u2);
                let d0 = ::std::format!("{:?}", u0);
                let d2 = ::std::format!("{:?}", u2);
                drop(u0);
                drop(u2);
                (nmsg, amsg, t0, t1, d0, d2)
            })
            .unwrap()
            .join();
        let (nmsg, amsg, t0, t1, d0, d2) = match ran {
            ::std::result::Result::Ok(msgs) => msgs,
            ::std::result::Result::Err(_) => panic!("deep walk panicked"),
        };
        assert!(nmsg.contains("natlist cap"), "{nmsg}");
        assert!(nmsg.contains("NatList(100001:"), "{nmsg}");
        assert!(nmsg.contains("NatList(100000:"), "{nmsg}");
        assert!(amsg.contains("mutual cap"), "{amsg}");
        assert!(amsg.contains("A(16385:"), "{amsg}");
        assert!(amsg.contains("A(16383:"), "{amsg}");
        assert!(t0.starts_with("Spine(25:"), "{t0}");
        assert!(t1.starts_with("Spine(25:"), "{t1}");
        let body0 = t0.split_once(": ").unwrap().1.strip_suffix(')').unwrap();
        let body1 = t1.split_once(": ").unwrap().1.strip_suffix(')').unwrap();
        assert!(body0.ends_with("..."), "{body0}");
        assert!(body1.ends_with("..."), "{body1}");
        let p0 = &body0[..body0.len() - 3];
        let p1 = &body1[..body1.len() - 3];
        assert_eq!(p0.len(), 1024, "{}", p0.len());
        assert_eq!(p1.len(), 1024, "{}", p1.len());
        let diff = p0.bytes().zip(p1.bytes()).position(|(x, y)| x != y);
        let at = diff.expect("prints matched");
        assert_eq!(at, 1006, "diff at {at}: {:?} vs {:?}", &p0[at.saturating_sub(16)..at + 8], &p1[at..at + 8]);
        assert_eq!(&p0[..at], &p1[..at]);
        assert!(d0.starts_with("Nest(100001:"), "{d0}");
        assert!(d2.starts_with("Nest(100000:"), "{d2}");
        assert!(d0.ends_with("...)"), "{d0}");
        assert!(d2.ends_with("...)"), "{d2}");
        assert_ne!(d0, d2);
    }
    """)

    {out, code} = rustc_test(dir, "deep_test.rs", ["--test-threads=1"])
    assert code == 0, out
    assert out =~ "1 passed"
    refute out =~ "stack overflow"
    refute out =~ "warning:", out
  end

  @tag skip: @rustc_skip
  test "rustc accepts a finished keyword beside the suffixed evidence" do
    {dir, path} = book("idents.muro", @forbidden_clash)

    assert {:ok, %{source: source}} =
             Muro.emit_rust_test(path, root: dir, book: "idents.muro")

    File.write!(Path.join(dir, "idents_test.rs"), source)
    assert {:ok, [rs]} = Muro.emit_rust(path)
    assert Path.basename(rs) == "idents.rs"

    {out, code} = rustc_test(dir, "idents_test.rs")
    assert code == 0, out
    assert out =~ "8 passed"
    refute out =~ "warning:", out

    assert {:ok, %{source: baked}} =
             Muro.emit_rust_test(path, root: dir, book: "idents.muro", impl: "idents")

    File.write!(Path.join(dir, "idents_impl_test.rs"), baked)

    {impl_out, impl_code} = rustc_extern_test(dir, "idents_impl_test.rs", "idents")
    assert impl_code == 0, impl_out
    assert impl_out =~ "8 passed"
    refute impl_out =~ "warning:", impl_out
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

  test "muro.toml backend rust-test is written by muro gen" do
    dir = tmp_dir()

    write_book(dir, "priv/muro/round.muro", """
    def round : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
    def wide : run Nat := 100001
    def wide-ok : evidence {wide ≡ 100001 : Nat} := refl
    """)

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "#{Mix.Tasks.Muro.version()}"
    backend = "rust-test"

    [[modules]]
    book = "priv/muro/round.muro"
    target = "test/rounding_test.rs"
    impl = "crate::rounding"
    """)

    output =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run([]) end)
      end)

    assert output =~ "written test/rounding_test.rs\n"
    assert output =~ "skipped test/rounding_test.rs: wide-ok (priv/muro/round.muro:"
    assert output =~ "normal form is a Nat above 100000"

    suite = File.read!(Path.join(dir, "test/rounding_test.rs"))
    assert {:ok, header} = Muro.Gen.parse_header(suite)
    assert header.book == "priv/muro/round.muro"
    assert header.version == Mix.Tasks.Muro.version()
    assert header.body =~ "fn round_ok()"
    assert header.body =~ "crate::rounding::round("
    assert header.body =~ "#[ignore = "
    assert header.body =~ "normal form is a Nat above 100000"
    refute suite =~ "muro__from_u64(100001)"
    refute suite =~ dir

    check =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run(["--check"]) end)
      end)

    assert check == "ok\n"
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

  defp fn_names(source) do
    ~r/^fn ([^\(]+)\(\)/m
    |> Regex.scan(source)
    |> Enum.map(fn [_, name] -> name end)
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

  defp rustc_test(dir, file, args \\ []) do
    System.cmd(@rustc, ["--edition", "2021", "--test", file, "-o", "suite"],
      cd: dir,
      stderr_to_stdout: true
    )
    |> then(fn {compiled, status} ->
      if status == 0 do
        {ran, ran_status} =
          System.cmd(Path.join(dir, "suite"), args, stderr_to_stdout: true)

        {compiled <> ran, ran_status}
      else
        {compiled, status}
      end
    end)
  end

  defp rustc_extern_test(dir, file, crate) do
    {lib_out, lib_status} =
      System.cmd(
        @rustc,
        [
          "--edition",
          "2021",
          "--crate-type",
          "lib",
          "--crate-name",
          crate,
          "#{crate}.rs",
          "-o",
          "lib#{crate}.rlib"
        ],
        cd: dir,
        stderr_to_stdout: true
      )

    if lib_status == 0 do
      System.cmd(
        @rustc,
        [
          "--edition",
          "2021",
          "--test",
          "--extern",
          "#{crate}=lib#{crate}.rlib",
          file,
          "-o",
          "suite-impl"
        ],
        cd: dir,
        stderr_to_stdout: true
      )
      |> then(fn {compiled, status} ->
        if status == 0 do
          {ran, ran_status} =
            System.cmd(Path.join(dir, "suite-impl"), [], stderr_to_stdout: true)

          {lib_out <> compiled <> ran, ran_status}
        else
          {lib_out <> compiled, status}
        end
      end)
    else
      {lib_out, lib_status}
    end
  end
end
