defmodule Muro.EmitCSharpSuiteTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.Emit.CSharpTest

  # Resolved when this file is compiled. MURO_DOTNET names the executable
  # when it is set. Otherwise this is ~/.dotnet/dotnet, then dotnet on PATH.
  # The live test is skipped when none of those is a file, including in CI.
  # The workflow files are not the place that installs the SDK.
  @dotnet (
            env = System.get_env("MURO_DOTNET")
            home = Path.expand("~/.dotnet/dotnet")

            cond do
              is_binary(env) and env != "" and File.regular?(env) ->
                env

              is_binary(env) and env != "" ->
                System.find_executable(env)

              File.regular?(home) ->
                home

              true ->
                System.find_executable("dotnet")
            end
          )

  @have_dotnet is_binary(@dotnet)
  @dotnet_skip if(@have_dotnet, do: false, else: "dotnet is not available")

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

  @idents """
  def zero : run Nat := 0
  def Equals : evidence {zero ≡ 0 : Nat} := refl
  def Equals_ : evidence {zero ≡ 0 : Nat} := refl
  def class : evidence {zero ≡ 0 : Nat} := refl
  def class_ : evidence {zero ≡ 0 : Nat} := refl
  def MURO_BOOK : evidence {zero ≡ 0 : Nat} := refl
  data Wrap : Type where
    record : Wrap
    MuroBytes : Wrap
    MuroNat : Wrap
    Values : Wrap
    MuroValues : Wrap
  def mark : run Wrap := record
  def mark-ok : evidence {mark ≡ record : Wrap} := refl
  def bare : run Wrap := MuroBytes
  def bare-ok : evidence {bare ≡ MuroBytes : Wrap} := refl
  def natc : run Wrap := MuroNat
  def natc-ok : evidence {natc ≡ MuroNat : Wrap} := refl
  def boxv : run Wrap := Values
  def boxv-ok : evidence {boxv ≡ Values : Wrap} := refl
  def nestv : run Wrap := MuroValues
  def nestv-ok : evidence {nestv ≡ MuroValues : Wrap} := refl
  def tag : run Atom := :red
  def tag-ok : evidence {tag ≡ :red : Atom} := refl
  """

  # Elixir eats `\x` and `\"` in a heredoc. The book muro checks is the
  # text after those escapes, so the backslash is written twice here.
  @shapes """
  data Color : Type where
    red : Color
  def wide32 : run U32 := toU32 5
  def wide32-ok : evidence {wide32 ≡ toU32 5 : U32} := refl
  def wide64 : run U64 := toU64 5
  def wide64-ok : evidence {wide64 ≡ toU64 5 : U64} := refl
  def huge : run Nat := 18446744073709551616
  def huge-ok : evidence {huge ≡ 18446744073709551616 : Nat} := refl
  def bot : run I64 := toI64 9223372036854775808
  def bot-ok : evidence {bot ≡ toI64 9223372036854775808 : I64} := refl
  def quoted : run String := "a\\"b"
  def quoted-ok : evidence {quoted ≡ "a\\"b" : String} := refl
  def raw : run Bytes := b"\\xFF"
  def raw-ok : evidence {raw ≡ b"\\xFF" : Bytes} := refl
  def nest : run Nat × Color := (suc 0, red)
  def nest-ok : evidence {nest ≡ (suc 0, red) : Nat × Color} := refl
  """

  test "a hyphen folds, an object method gains a trailing underscore, and a keyword gains @" do
    assert CSharpTest.ident("round-ok") == "round_ok"
    assert CSharpTest.ident("class") == "@class"
    assert CSharpTest.ident("class_") == "class_"
    assert CSharpTest.ident("Equals") == "Equals_"
    assert CSharpTest.ident("record") == "@record"
    assert CSharpTest.ident("field") == "@field"
    assert CSharpTest.ident("extension") == "@extension"
    assert CSharpTest.ident("allows") == "@allows"
    assert CSharpTest.ident("2nd") == "muro_2nd"
    assert CSharpTest.ident("GetHashCode") == "GetHashCode_"
    assert CSharpTest.ident("red") == "red"
    assert CSharpTest.type_ident("Equals") == "Equals"
    assert CSharpTest.type_ident("record") == "@record"
    assert CSharpTest.type_ident("field") == "@field"
    assert CSharpTest.type_ident("extension") == "@extension"
    assert CSharpTest.type_ident("allows") == "@allows"
    assert CSharpTest.type_ident("class") == "@class"
    assert CSharpTest.type_ident("red") == "red_"
    assert CSharpTest.class_name("rounding.muro") == "roundingTests"
    assert CSharpTest.class_name("/tmp/word-kind.muro") == "word_kindTests"
    assert CSharpTest.class_name("class.muro") == "classTests"
    assert CSharpTest.class_name("2nd.muro") == "muro_2ndTests"
    assert CSharpTest.impl_type("rounding.muro") == "rounding"
    assert CSharpTest.impl_type("class.muro") == "@class"
    assert CSharpTest.impl_type("2nd.muro") == "muro_2nd"
    assert CSharpTest.type_name?("Host.Rounding")
    assert CSharpTest.type_name?("@class")
    assert CSharpTest.type_name?("@int")
    refute CSharpTest.type_name?("class")
    refute CSharpTest.type_name?("int")
    refute CSharpTest.type_name?("1bad")
    refute CSharpTest.type_name?(".Rounding")
    refute CSharpTest.type_name?("Rounding.")
    refute CSharpTest.type_name?("")
  end

  test "print_value renders the host literals" do
    assert CSharpTest.print_value(:ze, []) == {:ok, "MuroValues.MuroNat(\"0\")"}
    assert CSharpTest.print_value({:nat, 2}, []) == {:ok, "MuroValues.MuroNat(\"2\")"}

    assert CSharpTest.print_value({:nat, 18_446_744_073_709_551_616}, []) ==
             {:ok, "MuroValues.MuroNat(\"18446744073709551616\")"}

    assert CSharpTest.print_value(:one, []) == {:ok, "new MuroValues.Unit()"}

    assert CSharpTest.print_value({:pair, {:nat, 1}, {:nat, 2}}, []) ==
             {:ok, "(MuroValues.MuroNat(\"1\"), MuroValues.MuroNat(\"2\"))"}

    assert CSharpTest.print_value({:word, {:lit, :u8, 5}, []}, []) == {:ok, "(byte)5"}
    assert CSharpTest.print_value({:word, {:lit, :u8, 255}, []}, []) == {:ok, "(byte)255"}
    assert CSharpTest.print_value({:word, {:lit, :u32, 5}, []}, []) == {:ok, "5u"}

    assert CSharpTest.print_value({:word, {:lit, :u64, 18_446_744_073_709_551_615}, []}, []) ==
             {:ok, "18446744073709551615UL"}

    assert CSharpTest.print_value({:word, {:lit, :i64, 18_446_744_073_709_551_615}, []}, []) ==
             {:ok, "-1L"}

    assert CSharpTest.print_value({:word, {:lit, :i64, 9_223_372_036_854_775_808}, []}, []) ==
             {:ok, "long.MinValue"}

    assert CSharpTest.print_value({:word, true, []}, []) ==
             {:ok, "new MuroValues.MuroWBool(true)"}

    assert CSharpTest.print_value({:word, false, []}, []) ==
             {:ok, "new MuroValues.MuroWBool(false)"}

    assert CSharpTest.print_value({:word, :none, []}, []) == {:ok, "new MuroValues.MuroNone()"}

    assert CSharpTest.print_value({:word, :some, [{:word, {:lit, :u8, 5}, []}]}, []) ==
             {:ok, "new MuroValues.MuroSome<byte>((byte)5)"}

    assert CSharpTest.print_value({:slit, "hi"}, []) == {:ok, "\"hi\""}
    assert CSharpTest.print_value({:slit, "a\"b"}, []) == {:ok, "\"a\\\"b\""}

    assert CSharpTest.print_value({:blit, "ab"}, []) ==
             {:ok, "new MuroValues.MuroBytes(\"6162\")"}

    assert CSharpTest.print_value({:blit, <<255>>}, []) ==
             {:ok, "new MuroValues.MuroBytes(\"ff\")"}

    assert CSharpTest.print_value({:atom, "red"}, []) ==
             {:ok, "new MuroValues.MuroAtom(\"red\")"}

    assert CSharpTest.print_value({:lam, :affine, :nat, "n", :ze}, []) == {:error, :function}
    assert CSharpTest.print_value({:unf, :ze, :ze}, []) == {:error, :stream}
    assert CSharpTest.print_value({:addi, :ze, :ze}, []) == {:error, :machine}
  end

  test "a book with n closed equations emits n facts, and words are literals" do
    {dir, path} = book("rounding.muro", @book)

    assert {:ok, %{source: source, skips: skips, tests: tests}} =
             Muro.emit_csharp_test(path, root: dir, book: "rounding.muro")

    assert tests + length(skips) == length(@names)
    assert length(skips) == 1
    assert hd(skips).name == "keep-eq"
    assert hd(skips).reason =~ "stream"
    assert tests == 15

    assert fact_names(source) == [
             "round_ok",
             "round_ok_2",
             "unit_ok",
             "paint_ok",
             "boxed_ok",
             "pair_ok",
             "bite_ok",
             "neg_ok",
             "flag_ok",
             "hole_ok",
             "hit_ok",
             "say_ok",
             "raw_ok",
             "nums_ok",
             "keep_eq",
             "class_ok"
           ]

    assert source =~ "public class roundingTests"
    assert source =~ "using System.Globalization;"
    assert source =~ "using System.Numerics;"
    refute source =~ "using Xunit"
    refute source =~ "byte[]"
    refute source =~ "MuroAtom"

    assert source =~ "public readonly record struct Unit;"
    assert source =~ "public readonly record struct MuroBytes(string Hex);"
    assert source =~ "public readonly record struct MuroNone;"
    assert source =~ "public readonly record struct MuroSome<T0>(T0 F0);"
    assert source =~ "public readonly record struct MuroWBool(bool Value);"
    assert source =~ "public static BigInteger MuroNat(string digits) =>"
    assert source =~ "BigInteger.Parse(digits, NumberStyles.None, CultureInfo.InvariantCulture);"
    assert source =~ "public readonly record struct red_;"
    assert source =~ "public readonly record struct box_<T0>(T0 F0);"
    assert source =~ "public readonly record struct nil_;"
    assert source =~ "public readonly record struct cons_<T0, T1>(T0 F0, T1 F1);"

    assert source =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"1\"), MuroValues.MuroNat(\"1\"));"

    assert source =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"2\"), MuroValues.MuroNat(\"2\"));"

    assert source =~ "Xunit.Assert.Equal(new MuroValues.Unit(), new MuroValues.Unit());"
    assert source =~ "Xunit.Assert.Equal(new MuroValues.red_(), new MuroValues.red_());"

    assert source =~
             "Xunit.Assert.Equal(new MuroValues.box_<BigInteger>(MuroValues.MuroNat(\"2\")), new MuroValues.box_<BigInteger>(MuroValues.MuroNat(\"2\")));"

    assert source =~
             "Xunit.Assert.Equal((MuroValues.MuroNat(\"1\"), MuroValues.MuroNat(\"2\")), (MuroValues.MuroNat(\"1\"), MuroValues.MuroNat(\"2\")));"

    assert source =~ "Xunit.Assert.Equal((byte)5, (byte)5);"
    assert source =~ "Xunit.Assert.Equal(-1L, -1L);"

    assert source =~
             "Xunit.Assert.Equal(new MuroValues.MuroWBool(true), new MuroValues.MuroWBool(true));"

    assert source =~ "Xunit.Assert.Equal(new MuroValues.MuroNone(), new MuroValues.MuroNone());"

    assert source =~
             "Xunit.Assert.Equal(new MuroValues.MuroSome<byte>((byte)5), new MuroValues.MuroSome<byte>((byte)5));"

    assert source =~ "Xunit.Assert.Equal(\"hi\", \"hi\");"

    assert source =~
             "Xunit.Assert.Equal(new MuroValues.MuroBytes(\"6162\"), new MuroValues.MuroBytes(\"6162\"));"

    assert source =~
             "Xunit.Assert.Equal(new MuroValues.cons_<BigInteger, MuroValues.nil_>(MuroValues.MuroNat(\"1\"), new MuroValues.nil_()), new MuroValues.cons_<BigInteger, MuroValues.nil_>(MuroValues.MuroNat(\"1\"), new MuroValues.nil_()));"

    refute source =~ "keep("

    keep = hd(skips)
    reason = "#{keep.name} (#{keep.file}:#{keep.line}): #{keep.reason}"
    assert source =~ "Skip = #{cs(reason)}"
    assert source =~ "public void keep_eq()"
    assert source =~ "DisplayName = "

    assert source =~
             "public const string MURO_BOOK = #{cs(Muro.Gen.book_hash(dir, "rounding.muro"))};"

    refute source =~ dir

    assert {:ok, %{source: again}} =
             Muro.emit_csharp_test(path, root: dir, book: "rounding.muro")

    assert again == source

    {:ok, ex} = Muro.emit_exunit(path, RoundingTest, root: dir, book: "rounding.muro")
    assert ex.tests + length(ex.skips) == length(@names)
    assert "neg-ok" in Enum.map(ex.skips, & &1.name)
    refute Enum.any?(skips, &(&1.name == "neg-ok"))

    {stdout, stderr} = capture_emit([path, "--backend", "csharp-test"])
    assert stdout =~ "public class roundingTests"
    assert stderr =~ "#{tests} tests, #{length(skips)} skipped"
    assert stderr =~ "skipped keep-eq ("
    assert stderr =~ "): argument 1 normal form is a stream"
  end

  test "--impl names the type, and a bare keyword is refused" do
    {dir, path} = book("rounding.muro", @book)

    assert {:ok, %{source: source, tests: 15, skips: skips}} =
             Muro.emit_csharp_test(path, root: dir, book: "rounding.muro", impl: "Host.Rounding")

    assert length(skips) == 1
    assert source =~ "Each fact calls Host.Rounding."

    assert source =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"1\"), Host.Rounding.round(MuroValues.MuroNat(\"1\")));"

    assert source =~ "Xunit.Assert.Equal(new MuroValues.Unit(), Host.Rounding.unit());"
    assert source =~ "Xunit.Assert.Equal(new MuroValues.Unit(), Host.Rounding.@class());"
    refute source =~ "MuroValues.MuroNat(\"1\"), MuroValues.MuroNat(\"1\")"

    assert {:error, "impl must be a C# type name, got: \"class\""} =
             Muro.emit_csharp_test(path, root: dir, book: "rounding.muro", impl: "class")

    assert {:raise, "", "--impl must be a C# type name, got: \"class\""} =
             Muro.CLI.Emit.run([path, "--backend", "csharp-test", "--impl", "class"])

    assert {:raise, "", "--node writes the placement calls"} =
             Muro.CLI.Emit.run([path, "--backend", "csharp-test", "--node", "a"])
  end

  test "csharp-test accepts an unsupplied param and --imports" do
    {dir, path} = book("lib.muro", @open_param)

    assert {:error, refused} = Muro.emit_file(path, Lib)
    assert refused =~ "param p is supplied by a file that imports this one"

    assert {:ok, %{tests: 1, skips: [], source: source}} =
             Muro.emit_csharp_test(path, root: dir, book: "lib.muro")

    assert source =~ "Xunit.Assert.Equal(MuroValues.MuroNat(\"0\"), global::lib.p());"
    assert source =~ "public class libTests"

    write_book(dir, "use.muro", """
    import "lib.muro"
    def q : run Nat := 0
    def q-ok : evidence {q ≡ 0 : Nat} := refl
    """)

    use = Path.join(dir, "use.muro")

    assert {:ok, %{tests: 1, skips: []}} =
             Muro.emit_csharp_test(use, root: dir, book: "use.muro")

    assert {:ok, %{tests: 2, skips: [], source: imported}} =
             Muro.emit_csharp_test(use, root: dir, book: "use.muro", imports: true)

    assert imported =~ "use.muro:"
    assert imported =~ "q-ok"
    assert imported =~ "lib.muro:"
    assert imported =~ "held"
    assert imported =~ "global::use.p()"
  end

  test "a finished object method does not collide with an evidence of that spelling" do
    {dir, path} = book("idents.muro", @idents)

    assert {:ok, %{source: source, tests: 11, skips: []}} =
             Muro.emit_csharp_test(path, root: dir, book: "idents.muro")

    assert fact_names(source) == [
             "Equals_",
             "Equals__2",
             "@class",
             "class_",
             "MURO_BOOK_2",
             "mark_ok",
             "bare_ok",
             "natc_ok",
             "boxv_ok",
             "nestv_ok",
             "tag_ok"
           ]

    assert source =~ "new MuroValues.@record()"
    assert source =~ "new MuroValues.MuroBytes_2()"
    assert source =~ "new MuroValues.MuroNat_2()"
    assert source =~ "new MuroValues.Values()"
    assert source =~ "new MuroValues.MuroValues_2()"
    assert source =~ "new MuroValues.MuroAtom(\"red\")"
    assert source =~ "public readonly record struct @record;"
    assert source =~ "public readonly record struct MuroBytes_2;"
    assert source =~ "public readonly record struct MuroNat_2;"
    assert source =~ "public readonly record struct Values;"
    assert source =~ "public readonly record struct MuroValues_2;"
    refute source =~ "public void Equals()"
    refute source =~ "public void MURO_BOOK()"
    refute source =~ "public void MuroValues()"
    refute source =~ "public readonly record struct MuroBytes;"
    refute source =~ "public readonly record struct MuroValues;"

    assert {:ok, %{source: baked, tests: 11}} =
             Muro.emit_csharp_test(path, root: dir, book: "idents.muro", impl: "Host.Idents")

    assert fact_names(baked) == fact_names(source)
    assert baked =~ "Host.Idents.zero()"
  end

  test "words, a Nat above ulong, and a record inside a pair are literals" do
    {dir, path} = book("shapes.muro", @shapes)

    assert {:ok, %{source: source, tests: 7, skips: []}} =
             Muro.emit_csharp_test(path, root: dir, book: "shapes.muro")

    assert source =~ "Xunit.Assert.Equal(5u, 5u);"
    assert source =~ "Xunit.Assert.Equal(5UL, 5UL);"

    assert source =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"18446744073709551616\"), MuroValues.MuroNat(\"18446744073709551616\"));"

    assert source =~ "Xunit.Assert.Equal(long.MinValue, long.MinValue);"
    assert source =~ "Xunit.Assert.Equal(\"a\\\"b\", \"a\\\"b\");"

    assert source =~
             "Xunit.Assert.Equal(new MuroValues.MuroBytes(\"ff\"), new MuroValues.MuroBytes(\"ff\"));"

    assert source =~
             "Xunit.Assert.Equal((MuroValues.MuroNat(\"1\"), new MuroValues.red_()), (MuroValues.MuroNat(\"1\"), new MuroValues.red_()));"
  end

  test "a book with no equation is a class and no fact" do
    {dir, path} = book("idle.muro", "def idle : run Nat := 0\n")

    assert {:ok, %{source: source, tests: 0, skips: []}} =
             Muro.emit_csharp_test(path, root: dir, book: "idle.muro")

    assert source =~ "public class idleTests"
    assert source =~ "public const string MURO_BOOK = "
    refute source =~ "Xunit.Fact"
    refute source =~ "class MuroValues"
    refute source =~ "using "
  end

  @values_host """
  param p : run Nat
  param p-is : evidence {p ≡ 0 : Nat}
  def held : evidence {p ≡ 0 : Nat} := p-is
  def zero : run Nat := 0
  def zero-ok : evidence {zero ≡ 0 : Nat} := refl
  """

  test "a stem or --impl named Values is not shadowed by the helper class" do
    {dir, path} = book("Values.muro", @values_host)

    assert {:ok, %{source: source, tests: 2, skips: []}} =
             Muro.emit_csharp_test(path, root: dir, book: "Values.muro")

    assert source =~ "public static class MuroValues"
    refute source =~ "public static class Values"
    assert source =~ "public class ValuesTests"

    assert source =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"0\"), global::Values.p());"

    assert source =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"0\"), MuroValues.MuroNat(\"0\"));"

    refute source =~ ", Values.p()"

    assert {:ok, %{source: baked, tests: 2, skips: []}} =
             Muro.emit_csharp_test(path, root: dir, book: "Values.muro", impl: "Values")

    assert baked =~ "Each fact calls Values."
    assert baked =~ "public static class MuroValues"

    assert baked =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"0\"), global::Values.p());"

    assert baked =~
             "Xunit.Assert.Equal(MuroValues.MuroNat(\"0\"), global::Values.zero());"

    refute baked =~ ", Values.p()"
    refute baked =~ ", Values.zero()"
  end

  test "mix muro.gen writes a C# file and --check sees drift" do
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
        {"priv/muro/round.muro", "test/rounding_test.cs",
         [kind: :csharp_test, impl: "Host.Rounding"]}
      ]
    ]
    """)

    output =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run([]) end)
      end)

    assert output =~ "written test/rounding_test.cs\n"
    assert output =~ "skipped test/rounding_test.cs: step-ok (priv/muro/round.muro:"

    suite = File.read!(Path.join(dir, "test/rounding_test.cs"))
    assert {:ok, header} = Muro.Gen.parse_header(suite)
    assert header.book == "priv/muro/round.muro"
    assert header.version == Mix.Tasks.Muro.version()
    assert header.book_hash == Muro.Gen.book_hash(dir, "priv/muro/round.muro")
    assert header.body_hash == Muro.Gen.body_hash(header.body)
    assert header.body =~ "public void round_ok()"
    assert header.body =~ "Skip = "
    assert header.body =~ "Host.Rounding.round("
    assert suite =~ "// Generated by Muro #{Mix.Tasks.Muro.version()}"
    refute suite =~ dir

    again =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run([]) end)
      end)

    assert again =~ "unchanged test/rounding_test.cs\n"
    assert File.read!(Path.join(dir, "test/rounding_test.cs")) == suite

    check =
      in_dir(dir, fn ->
        capture(fn -> Mix.Tasks.Muro.Gen.run(["--check"]) end)
      end)

    assert check == "ok\n"

    File.write!(
      Path.join(dir, "test/rounding_test.cs"),
      String.replace(suite, "Rounding", "Other", global: false)
    )

    assert check_error(dir) =~ "hand-edited target"

    File.write!(Path.join(dir, "test/rounding_test.cs"), suite)

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

  @tag skip: @dotnet_skip
  @tag timeout: 180_000
  test "dotnet build -warnaserror accepts the file and a wrong expected value fails" do
    {dir, path} = book("rounding.muro", @book)
    shapes = write_book(dir, "shapes.muro", @shapes)
    idents = write_book(dir, "idents.muro", @idents)
    values = write_book(dir, "Values.muro", @values_host)

    assert {:ok, %{source: rounding, tests: round_n, skips: round_skips}} =
             Muro.emit_csharp_test(path, root: dir, book: "rounding.muro")

    assert {:ok, %{source: shapes_src, tests: shapes_n, skips: []}} =
             Muro.emit_csharp_test(shapes, root: dir, book: "shapes.muro")

    assert {:ok, %{source: idents_src, tests: idents_n, skips: []}} =
             Muro.emit_csharp_test(idents, root: dir, book: "idents.muro")

    assert {:ok, %{source: values_src, tests: values_n, skips: []}} =
             Muro.emit_csharp_test(values, root: dir, book: "Values.muro")

    proj = Path.join(dir, "proj")

    {new_out, new_code} =
      dotnet(["new", "xunit", "-n", "Probe", "--framework", "net8.0", "-o", proj])

    assert new_code == 0, new_out

    unit = Path.join(proj, "UnitTest1.cs")
    if File.regular?(unit), do: File.rm!(unit)

    File.write!(Path.join(proj, "Rounding.cs"), rounding)
    File.write!(Path.join(proj, "Shapes.cs"), shapes_src)
    File.write!(Path.join(proj, "Idents.cs"), idents_src)
    File.write!(Path.join(proj, "ValuesBook.cs"), values_src)

    File.write!(Path.join(proj, "ValuesHost.cs"), """
    public static class Values
    {
        public static System.Numerics.BigInteger p() =>
            System.Numerics.BigInteger.Zero;
    }
    """)

    {build_out, build_code} = dotnet(["build", proj, "-warnaserror", "--nologo"])
    assert build_code == 0, build_out
    assert build_out =~ "0 Warning(s)"
    assert build_out =~ "0 Error(s)"

    {test_out, test_code} = dotnet(["test", proj, "--no-build", "--nologo"])
    assert test_code == 0, test_out

    passed = round_n + shapes_n + idents_n + values_n
    skipped = length(round_skips)

    assert test_out =~ ~r/Failed:\s+0,\s+Passed:\s+#{passed},\s+Skipped:\s+#{skipped}/

    broken =
      String.replace(
        rounding,
        "Xunit.Assert.Equal(MuroValues.MuroNat(\"1\"), MuroValues.MuroNat(\"1\"));",
        "Xunit.Assert.Equal(MuroValues.MuroNat(\"0\"), MuroValues.MuroNat(\"1\"));",
        global: false
      )

    assert broken != rounding
    File.write!(Path.join(proj, "Rounding.cs"), broken)

    {_rebuild, rebuild_code} = dotnet(["build", proj, "-warnaserror", "--nologo"])
    assert rebuild_code == 0

    {fail_out, fail_code} = dotnet(["test", proj, "--no-build", "--nologo"])
    assert fail_code != 0
    assert fail_out =~ "Failed!"
  end

  defp cs(text) do
    case CSharpTest.print_value({:slit, text}, []) do
      {:ok, src} -> src
    end
  end

  defp fact_names(source) do
    Regex.scan(~r/public void ([@A-Za-z_][A-Za-z0-9_]*)\(\)/, source)
    |> Enum.map(fn [_, name] -> name end)
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
    dir = Path.join(System.tmp_dir!(), "muro_csharp_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp dotnet(args) do
    System.cmd(@dotnet, args,
      stderr_to_stdout: true,
      env: [
        {"DOTNET_CLI_TELEMETRY_OPTOUT", "1"},
        {"DOTNET_NOLOGO", "1"},
        {"DOTNET_SKIP_FIRST_TIME_EXPERIENCE", "1"}
      ]
    )
  end
end
