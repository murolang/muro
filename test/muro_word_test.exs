defmodule Muro.WordTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Parser}

  @moduletag timeout: 180_000

  test "closed word equations reduce and check by refl" do
    assert Check.check_sig(book!(edges_src())) == :ok
  end

  test "closed numerals at the word boundaries check, and a wrong one is refused" do
    assert check_src(boundary_src()) == :ok
    assert Check.check_sig(book!(boundary_src()), fuel: 40) == :ok

    assert {:error, msg} = check_src(boundary_wrong_src())
    refute Check.out_of_fuel?(msg)
    assert msg =~ "cannot convert"
  end

  test "toNat of U64 max normalises to a closed numeral" do
    book =
      book!("""
      def n : spec Nat := toNat (noti (toU64 0))
      """)

    assert {:ok, [d]} = Muro.Ast.book_to_db(book)
    n = 18_446_744_073_709_551_615
    assert {:ok, {:nat, ^n}} = Check.normalize([], d.body, 30)
    assert Muro.Word.step(:ton, [Muro.Word.lit(:u64, n)], 1) == {:ok, {:nat, n}}
    assert Muro.Word.from_nat({:nat, n}) == {:ok, n}
  end

  test "fnv.muro checks and its hashes are the 32-bit FNV-1a values" do
    assert Muro.check_file("examples/fnv.muro") == :ok
    dir = tmp("fnv")
    File.cp!("examples/fnv.muro", Path.join(dir, "fnv.muro"))

    assert {:ok, ex} = Muro.emit_file(Path.join(dir, "fnv.muro"), Muro.FnvEx)
    Code.compile_string(ex)
    assert apply(Muro.FnvEx, :hashEmpty, []) == 2_166_136_261
    assert apply(Muro.FnvEx, :hashA, []) == 3_826_002_220

    assert {:ok, [h, _c]} = Muro.emit_c(Path.join(dir, "fnv.muro"), nif: false)
    assert File.read!(h) =~ "uint32_t hashEmpty(void);"
    assert File.read!(h) =~ "uint8_t muro__f_0;"

    File.write!(Path.join(dir, "main.c"), """
    #include "fnv.h"
    #include <stdio.h>
    int main(void) {
      printf("%u\\n%u\\n", hashEmpty(), hashA());
      return 0;
    }
    """)

    assert gcc!(dir, "fnv.c", "fnv.o") == :ok
    assert gcc!(dir, "main.c", "main.o") == :ok
    assert link!(dir, ~w(fnv.o main.o), "fnvbin") == :ok
    assert run!(dir, "fnvbin") == "2166136261\n3826002220\n"
  end

  test "elixir backend evaluates each word edge" do
    src = edges_src()
    assert {:ok, ex} = emit_elixir(src, Muro.WordEdges)
    Code.compile_string(ex)

    for spec <- specs() do
      got = apply(Muro.WordEdges, String.to_atom(spec.name), [])
      assert got == host(spec), spec.name
    end

    assert apply(Muro.WordEdges, :incu8, [255]) == 0
    assert apply(Muro.WordEdges, :incu8, [0]) == 1

    assert apply(Muro.WordEdges, :inci64, [9_223_372_036_854_775_807]) ==
             9_223_372_036_854_775_808

    assert apply(Muro.WordEdges, :divu8, [1, 0]) == :none
    assert apply(Muro.WordEdges, :divu8, [5, 2]) == {:some, 2}
  end

  test "c backend compiles each word edge without undefined behavior" do
    dir = emit_native!(edges_src(), "edges", :c)

    main = [
      "#include \"edges.h\"",
      "#include <stdio.h>",
      "#include <stdint.h>",
      "int main(void) {"
    ]

    main =
      Enum.reduce(specs(), main, fn spec, acc ->
        acc ++ [c_print(spec)]
      end)

    main =
      main ++
        [
          ~s|printf("incu8 %u\\n", (unsigned)incu8(255));|,
          ~s|printf("inci64 %llu\\n", (unsigned long long)inci64(INT64_MAX));|,
          ~s|muro__opt_u8 d0 = divu8(1, 0);|,
          ~s|printf("divu80 %u %llu\\n", d0.tag, (unsigned long long)d0.val);|,
          ~s|muro__opt_u8 d5 = divu8(5, 2);|,
          ~s|printf("divu85 %u %llu\\n", d5.tag, (unsigned long long)d5.val);|,
          "return 0;",
          "}"
        ]

    File.write!(Path.join(dir, "main.c"), Enum.join(main, "\n"))
    assert gcc!(dir, "edges.c", "edges.o") == :ok
    assert gcc!(dir, "main.c", "main.o") == :ok
    assert link!(dir, ~w(edges.o main.o), "edgesbin") == :ok
    lines = run!(dir, "edgesbin") |> String.split("\n", trim: true)
    assert_lines(lines)

    assert Enum.at(lines, length(specs())) == "incu8 0"
    assert Enum.at(lines, length(specs()) + 1) == "inci64 9223372036854775808"
    assert Enum.at(lines, length(specs()) + 2) == "divu80 0 0"
    assert Enum.at(lines, length(specs()) + 3) == "divu85 1 2"
  end

  test "zig backend compiles each word edge" do
    dir = emit_native!(edges_src(), "edges", :zig)

    body =
      specs()
      |> Enum.map_join("\n        ", &zig_expect/1)

    File.write!(Path.join(dir, "check.zig"), """
    const std = @import("std");
    const m = @import("edges.zig");

    test "edges" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const a = arena.allocator();
        #{body}
        try std.testing.expectEqual(@as(u8, 0), try m.incu8(a, 255));
        try std.testing.expectEqual(@as(u8, 1), try m.incu8(a, 0));
        try std.testing.expectEqual(@as(u64, 9223372036854775808), @as(u64, @bitCast(try m.inci64(a, 9223372036854775807))));
        try std.testing.expect(try m.divu8(a, 1, 0) == null);
        try std.testing.expectEqual(@as(u8, 2), (try m.divu8(a, 5, 2)).?);
    }
    """)

    {out, status} = System.cmd(zig!(), ["test", "check.zig"], cd: dir, stderr_to_stdout: true)
    assert status == 0, out
    assert out =~ "All 1 tests passed."
  end

  test "rust backend compiles each word edge" do
    dir = emit_native!(edges_src(), "edges", :rust)

    asserts =
      specs()
      |> Enum.map_join("\n    ", &rust_expect/1)

    File.write!(Path.join(dir, "main.rs"), """
    extern crate edges;
    fn main() {
        #{asserts}
        assert_eq!(edges::incu8(255), 0u8);
        assert_eq!(edges::incu8(0), 1u8);
        assert_eq!(edges::inci64(9223372036854775807), 9223372036854775808u64 as i64);
        assert!(edges::divu8(1, 0).is_none());
        assert_eq!(edges::divu8(5, 2), Some(2u8));
    }
    """)

    {lib, status} =
      System.cmd(
        rustc!(),
        ~w(--edition 2021 --crate-type lib --crate-name edges edges.rs -o libedges.rlib),
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, lib
    refute lib =~ "warning:", lib

    {bin, status} =
      System.cmd(
        rustc!(),
        ~w(--edition 2021 main.rs --extern edges=libedges.rlib -o edgesbin),
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, bin
    {ran, status} = System.cmd(Path.join(dir, "edgesbin"), [], stderr_to_stdout: true)
    assert status == 0, ran
  end

  defp assert_lines(lines) do
    specs()
    |> Enum.with_index()
    |> Enum.each(fn {spec, i} ->
      assert Enum.at(lines, i) == c_line(spec), spec.name
    end)
  end

  defp book!(src) do
    assert {:ok, book} = Parser.parse(src)
    book
  end

  defp check_src(src) do
    with {:ok, book} <- Parser.parse(src), do: Check.check_sig(book)
  end

  # Check only. These equations name residues near 2^32 and 2^64, so they
  # stay out of the emitted edge suite.
  defp boundary_src do
    """
    def pred : evidence Π (n : Nat) → Nat :=
      λ (n : Nat) →
        match n motive (λ _ → Nat)
          | 0 => 0
          | suc k => k
    def u8nat : evidence {toNat (noti (toU8 0)) ≡ 255 : Nat} := refl
    def u8wrap : evidence {addi (noti (toU8 0)) (toU8 1) ≡ toU8 0 : U8} := refl
    def u8cadd : evidence {addc (noti (toU8 0)) (toU8 1) ≡ wnone : Opt U8} := refl
    def u32nat : evidence {toNat (noti (toU32 0)) ≡ 4294967295 : Nat} := refl
    def u32wrap : evidence {addi (noti (toU32 0)) (toU32 1) ≡ toU32 0 : U32} := refl
    def u32cadd : evidence {addc (noti (toU32 0)) (toU32 1) ≡ wnone : Opt U32} := refl
    def u32of : evidence {toU32 4294967297 ≡ toU32 1 : U32} := refl
    def u32cast : evidence {asU32 (noti (toU64 0)) ≡ noti (toU32 0) : U32} := refl
    def u32shl : evidence {shli (toU32 1) 32 ≡ toU32 0 : U32} := refl
    def u64nat : evidence {toNat (noti (toU64 0)) ≡ 18446744073709551615 : Nat} := refl
    def u64zero : evidence {toNat (toU64 0) ≡ 0 : Nat} := refl
    def u64wrap : evidence {addi (noti (toU64 0)) (toU64 1) ≡ toU64 0 : U64} := refl
    def u64cadd : evidence {addc (noti (toU64 0)) (toU64 1) ≡ wnone : Opt U64} := refl
    def u64csub : evidence {subc (toU64 0) (toU64 1) ≡ wnone : Opt U64} := refl
    def u64of : evidence {toU64 18446744073709551616 ≡ toU64 0 : U64} := refl
    def u64round : evidence {toU64 (toNat (noti (toU64 0))) ≡ noti (toU64 0) : U64} := refl
    def u64shl : evidence {toNat (shli (toU64 1) 63) ≡ 9223372036854775808 : Nat} := refl
    def u64shl0 : evidence {shli (toU64 1) 64 ≡ toU64 0 : U64} := refl
    def i64min : evidence {toNat (shli (toI64 1) 63) ≡ 9223372036854775808 : Nat} := refl
    def i64max : evidence {toNat (noti (shli (toI64 1) 63)) ≡ 9223372036854775807 : Nat} := refl
    def i64neg : evidence {toNat (noti (toI64 0)) ≡ 18446744073709551615 : Nat} := refl
    def i64ofmin : evidence {toI64 9223372036854775808 ≡ shli (toI64 1) 63 : I64} := refl
    def i64ofneg : evidence {toI64 18446744073709551615 ≡ noti (toI64 0) : I64} := refl
    def i64wrap : evidence {addi (noti (shli (toI64 1) 63)) (toI64 1) ≡ shli (toI64 1) 63 : I64} := refl
    def i64cmax : evidence {addc (noti (shli (toI64 1) 63)) (toI64 1) ≡ wnone : Opt I64} := refl
    def i64cmin : evidence {addc (shli (toI64 1) 63) (shli (toI64 1) 63) ≡ wnone : Opt I64} := refl
    def i64div : evidence {divi (shli (toI64 1) 63) (noti (toI64 0)) ≡ wnone : Opt I64} := refl
    def i64cast : evidence {asU64 (noti (toI64 0)) ≡ noti (toU64 0) : U64} := refl
    def i64bit : evidence {asI64 (noti (toU64 0)) ≡ noti (toI64 0) : I64} := refl
    def i64lt : evidence {lti (shli (toI64 1) 63) (toI64 0) ≡ wtrue : WBool} := refl
    def peel0 : evidence {pred (toNat (toU64 0)) ≡ 0 : Nat} := refl
    def peel1 : evidence {pred (toNat (toU8 1)) ≡ 0 : Nat} := refl
    def peelBig : evidence {pred 18446744073709551615 ≡ 18446744073709551614 : Nat} := refl
    def big : run Nat := 18446744073709551615
    def wide : run U64 := toU64 18446744073709551617
    def wide-ok : evidence {wide ≡ toU64 1 : U64} := refl
    """
  end

  defp boundary_wrong_src do
    """
    def badNat : evidence {toNat (noti (toU64 0)) ≡ 0 : Nat} := refl
    def badWrap : evidence {addi (noti (toU32 0)) (toU32 1) ≡ toU32 1 : U32} := refl
    def badCadd : evidence {addc (noti (toU64 0)) (toU64 1) ≡ wsome (toU64 0) : Opt U64} := refl
    def badOf : evidence {toI64 9223372036854775808 ≡ toI64 0 : I64} := refl
    """
  end

  defp emit_elixir(src, mod) do
    path = Path.join(tmp("ex"), "edges.muro")
    File.write!(path, src)
    Muro.emit_file(path, mod)
  end

  defp emit_native!(src, stem, backend) do
    dir = tmp(Atom.to_string(backend))
    path = Path.join(dir, stem <> ".muro")
    File.write!(path, src)

    {:ok, files} =
      case backend do
        :c -> Muro.emit_c(path, nif: false)
        :zig -> Muro.emit_zig(path)
        :rust -> Muro.emit_rust(path)
      end

    assert Enum.all?(files, &File.regular?/1)
    dir
  end

  defp edges_src do
    evid =
      Enum.map_join(specs(), "\n", fn spec ->
        """
        def #{spec.name} : run #{spec.ty} :=
          #{spec.lhs}
        def #{spec.name}-ok : evidence {#{spec.lhs} ≡ #{spec.rhs} : #{spec.ty}} :=
          refl
        """
      end)

    evid <>
      """
      def incu8 : run Π (x : U8) → U8 :=
        λ (x : U8) → addi x (toU8 (suc 0))
      def inci64 : run Π (x : I64) → I64 :=
        λ (x : I64) → addi x (toI64 (suc 0))
      def divu8 : run Π (x : U8) → Π (y : U8) → Opt U8 :=
        λ (x : U8) → λ (y : U8) → divi x y
      """
  end

  defp specs do
    z8 = "toU8 0"
    o8 = "toU8 (suc 0)"
    max8 = "noti (#{z8})"
    z32 = "toU32 0"
    o32 = "toU32 (suc 0)"
    max32 = "noti (#{z32})"
    z64 = "toU64 0"
    o64 = "toU64 (suc 0)"
    max64 = "noti (#{z64})"
    z = "toI64 0"
    o = "toI64 (suc 0)"
    neg = "noti (#{z})"
    two = "toI64 (suc (suc 0))"
    min = "shli (#{o}) (#{p(63)})"
    max = "noti (#{min})"

    [
      s("wu8add", "U8", "addi (#{max8}) (#{o8})", z8, {:u8, 0}),
      s("wu8sub", "U8", "subi (#{z8}) (#{o8})", max8, {:u8, 255}),
      s(
        "wu8mul",
        "U8",
        "muli (#{max8}) (toU8 (suc (suc 0)))",
        "subi (#{max8}) (#{o8})",
        {:u8, 254}
      ),
      s("wu8cadd0", "Opt U8", "addc (#{z8}) (#{z8})", "wsome (#{z8})", {:opt, :u8, {:some, 0}}),
      s("wu8caddx", "Opt U8", "addc (#{max8}) (#{o8})", "wnone", {:opt, :u8, :none}),
      s("wu8csubx", "Opt U8", "subc (#{z8}) (#{o8})", "wnone", {:opt, :u8, :none}),
      s("wu8csub0", "Opt U8", "subc (#{o8}) (#{z8})", "wsome (#{o8})", {:opt, :u8, {:some, 1}}),
      s(
        "wu8cmulx",
        "Opt U8",
        "mulc (shli (#{o8}) (#{p(4)})) (shli (#{o8}) (#{p(4)}))",
        "wnone",
        {:opt, :u8, :none}
      ),
      s(
        "wu8cmulok",
        "Opt U8",
        "mulc (shli (#{o8}) (#{p(3)})) (shli (#{o8}) (#{p(3)}))",
        "wsome (shli (#{o8}) (#{p(6)}))",
        {:opt, :u8, {:some, 64}}
      ),
      s("wu8div0", "Opt U8", "divi (#{o8}) (#{z8})", "wnone", {:opt, :u8, :none}),
      s(
        "wu8div",
        "Opt U8",
        "divi (toU8 (#{p(5)})) (toU8 (#{p(2)}))",
        "wsome (toU8 (#{p(2)}))",
        {:opt, :u8, {:some, 2}}
      ),
      s(
        "wu8rem",
        "Opt U8",
        "remi (toU8 (#{p(5)})) (toU8 (#{p(2)}))",
        "wsome (#{o8})",
        {:opt, :u8, {:some, 1}}
      ),
      s("wu8eq", "WBool", "eqi (#{z8}) (#{z8})", "wtrue", {:bool, true}),
      s("wu8ne", "WBool", "eqi (#{z8}) (#{o8})", "wfalse", {:bool, false}),
      s("wu8lt", "WBool", "lti (#{z8}) (#{o8})", "wtrue", {:bool, true}),
      s("wu8ltmax", "WBool", "lti (#{max8}) (#{z8})", "wfalse", {:bool, false}),
      s("wu8le", "WBool", "lei (#{z8}) (#{z8})", "wtrue", {:bool, true}),
      s("wu8and", "U8", "andi (#{max8}) (#{o8})", o8, {:u8, 1}),
      s("wu8or", "U8", "ori (#{z8}) (#{o8})", o8, {:u8, 1}),
      s("wu8xor", "U8", "xori (#{o8}) (#{o8})", z8, {:u8, 0}),
      s("wu8not", "U8", "noti (#{max8})", z8, {:u8, 0}),
      s("wu8shl0", "U8", "shli (#{o8}) 0", o8, {:u8, 1}),
      s("wu8shl7", "U8", "shli (#{o8}) (#{p(7)})", "toU8 (#{p(128)})", {:u8, 128}),
      s("wu8shl8", "U8", "shli (#{o8}) (#{p(8)})", z8, {:u8, 0}),
      s("wu8shl9", "U8", "shli (#{o8}) (#{p(9)})", z8, {:u8, 0}),
      s("wu8shr7", "U8", "shri (#{max8}) (#{p(7)})", o8, {:u8, 1}),
      s("wu8shr8", "U8", "shri (#{max8}) (#{p(8)})", z8, {:u8, 0}),
      s("wu8cast", "U8", "asU8 (#{max32})", max8, {:u8, 255}),
      s("wu8round", "U8", "toU8 (toNat (#{max8}))", max8, {:u8, 255}),
      s("wu32add", "U32", "addi (#{max32}) (#{o32})", z32, {:u32, 0}),
      s("wu32sub", "U32", "subi (#{z32}) (#{o32})", max32, {:u32, 4_294_967_295}),
      s("wu32caddx", "Opt U32", "addc (#{max32}) (#{o32})", "wnone", {:opt, :u32, :none}),
      s("wu32csubx", "Opt U32", "subc (#{z32}) (#{o32})", "wnone", {:opt, :u32, :none}),
      s("wu32div0", "Opt U32", "divi (#{o32}) (#{z32})", "wnone", {:opt, :u32, :none}),
      s("wu32shl", "U32", "shli (#{o32}) (#{p(32)})", z32, {:u32, 0}),
      s("wu32hi", "WBool", "lti (#{z32}) (shli (#{o32}) (#{p(31)}))", "wtrue", {:bool, true}),
      s(
        "wu32hiw",
        "U32",
        "shli (#{o32}) (#{p(31)})",
        "shli (#{o32}) (#{p(31)})",
        {:u32, 2_147_483_648}
      ),
      s("wu64add", "U64", "addi (#{max64}) (#{o64})", z64, {:u64, 0}),
      s("wu64sub", "U64", "subi (#{z64}) (#{o64})", max64, {:u64, 18_446_744_073_709_551_615}),
      s("wu64caddx", "Opt U64", "addc (#{max64}) (#{o64})", "wnone", {:opt, :u64, :none}),
      s("wu64div0", "Opt U64", "divi (#{o64}) (#{z64})", "wnone", {:opt, :u64, :none}),
      s("wu64shl", "U64", "shli (#{o64}) (#{p(64)})", z64, {:u64, 0}),
      s("wu64hi", "WBool", "lti (#{z64}) (shli (#{o64}) (#{p(63)}))", "wtrue", {:bool, true}),
      s("wi64add", "I64", "addi (#{neg}) (#{o})", z, {:i64, 0}),
      s("wi64mul", "I64", "muli (#{neg}) (#{neg})", o, {:i64, 1}),
      s("wi64cadd", "Opt I64", "addc (#{neg}) (#{o})", "wsome (#{z})", {:opt, :i64, {:some, 0}}),
      s("wi64cmin", "Opt I64", "addc (#{min}) (#{min})", "wnone", {:opt, :i64, :none}),
      s("wi64cmax", "Opt I64", "addc (#{max}) (#{o})", "wnone", {:opt, :i64, :none}),
      s("wi64csub", "Opt I64", "subc (#{z}) (#{o})", "wsome (#{neg})", {:opt, :i64, {:some, -1}}),
      s("wi64cmul", "Opt I64", "mulc (#{min}) (#{neg})", "wnone", {:opt, :i64, :none}),
      s("wi64div0", "Opt I64", "divi (#{o}) (#{z})", "wnone", {:opt, :i64, :none}),
      s("wi64divmin", "Opt I64", "divi (#{min}) (#{neg})", "wnone", {:opt, :i64, :none}),
      s("wi64remmin", "Opt I64", "remi (#{min}) (#{neg})", "wnone", {:opt, :i64, :none}),
      s("wi64div", "Opt I64", "divi (#{neg}) (#{two})", "wsome (#{z})", {:opt, :i64, {:some, 0}}),
      s(
        "wi64rem",
        "Opt I64",
        "remi (#{neg}) (#{two})",
        "wsome (#{neg})",
        {:opt, :i64, {:some, -1}}
      ),
      s("wi64lt", "WBool", "lti (#{neg}) (#{z})", "wtrue", {:bool, true}),
      s("wi64gt", "WBool", "lti (#{z}) (#{neg})", "wfalse", {:bool, false}),
      s("wi64le", "WBool", "lei (#{min}) (#{min})", "wtrue", {:bool, true}),
      s("wi64minlt", "WBool", "lti (#{min}) (#{z})", "wtrue", {:bool, true}),
      s("wi64cast", "U64", "asU64 (#{neg})", max64, {:u64, 18_446_744_073_709_551_615}),
      s("wi64bit", "I64", "asI64 (#{max64})", neg, {:i64, -1}),
      s("wi64shr", "I64", "shri (#{neg}) (suc 0)", neg, {:i64, -1}),
      s("wi64shroob", "I64", "shri (#{neg}) (#{p(64)})", neg, {:i64, -1}),
      s("wi64shr0", "I64", "shri (#{o}) (#{p(64)})", z, {:i64, 0}),
      s("wi64shlmin", "I64", "shli (#{min}) (suc 0)", z, {:i64, 0}),
      s("wmin", "I64", min, min, {:i64, -9_223_372_036_854_775_808}),
      s(
        "wu8and64",
        "U64",
        "asU64 (andi (asI64 (shli (#{o64}) (#{p(63)}))) (#{neg}))",
        "shli (#{o64}) (#{p(63)})",
        {:u64, 9_223_372_036_854_775_808}
      )
    ]
  end

  defp s(name, ty, lhs, rhs, expect) do
    %{name: name, ty: ty, lhs: lhs, rhs: rhs, expect: expect}
  end

  defp p(0), do: "0"
  defp p(n) when n > 0, do: "suc (" <> p(n - 1) <> ")"

  defp host(%{expect: {:bool, b}}), do: b
  defp host(%{expect: {:opt, _, :none}}), do: :none
  defp host(%{expect: {:opt, k, {:some, n}}}), do: {:some, residue(k, n)}
  defp host(%{expect: {k, n}}), do: residue(k, n)

  defp residue(k, n), do: Muro.Word.residue(k, n)

  defp c_print(%{name: name, expect: {:bool, _}}) do
    ~s|printf("#{name} %u\\n", (unsigned)#{name}());|
  end

  defp c_print(%{name: name, expect: {:opt, k, _}}) do
    ty = opt_c(k)

    """
    #{ty} #{name}_v = #{name}();
    printf("#{name} %u %llu\\n", #{name}_v.tag, (unsigned long long)#{name}_v.val);
    """
    |> String.trim()
  end

  defp c_print(%{name: name, expect: {:u8, _}}) do
    ~s|printf("#{name} %u\\n", (unsigned)#{name}());|
  end

  defp c_print(%{name: name, expect: {:u32, _}}) do
    ~s|printf("#{name} %u\\n", (unsigned)#{name}());|
  end

  defp c_print(%{name: name}) do
    ~s|printf("#{name} %llu\\n", (unsigned long long)#{name}());|
  end

  defp c_line(%{name: name, expect: {:bool, b}}) do
    "#{name} #{if b, do: 1, else: 0}"
  end

  defp c_line(%{name: name, expect: {:opt, _k, :none}}) do
    "#{name} 0 0"
  end

  defp c_line(%{name: name, expect: {:opt, k, {:some, n}}}) do
    "#{name} 1 #{residue(k, n)}"
  end

  defp c_line(%{name: name, expect: {k, n}}) do
    "#{name} #{residue(k, n)}"
  end

  defp opt_c(:u8), do: "muro__opt_u8"
  defp opt_c(:u32), do: "muro__opt_u32"
  defp opt_c(:u64), do: "muro__opt_u64"
  defp opt_c(:i64), do: "muro__opt_i64"

  defp zig_expect(%{name: name, expect: {:bool, true}}) do
    "try std.testing.expectEqual(@as(u8, 1), try m.#{name}(a));"
  end

  defp zig_expect(%{name: name, expect: {:bool, false}}) do
    "try std.testing.expectEqual(@as(u8, 0), try m.#{name}(a));"
  end

  defp zig_expect(%{name: name, expect: {:opt, _, :none}}) do
    "try std.testing.expect(try m.#{name}(a) == null);"
  end

  defp zig_expect(%{name: name, expect: {:opt, k, {:some, n}}}) do
    "try std.testing.expectEqual(@as(#{zty(k)}, #{zlit(k, n)}), (try m.#{name}(a)).?);"
  end

  defp zig_expect(%{name: name, expect: {:i64, n}}) do
    "try std.testing.expectEqual(@as(u64, #{residue(:i64, n)}), @as(u64, @bitCast(try m.#{name}(a))));"
  end

  defp zig_expect(%{name: name, expect: {k, n}}) do
    "try std.testing.expectEqual(@as(#{zty(k)}, #{residue(k, n)}), try m.#{name}(a));"
  end

  defp zty(:u8), do: "u8"
  defp zty(:u32), do: "u32"
  defp zty(:u64), do: "u64"
  defp zty(:i64), do: "i64"

  defp zlit(:i64, n), do: "@as(i64, @bitCast(@as(u64, #{residue(:i64, n)})))"
  defp zlit(k, n), do: Integer.to_string(residue(k, n))

  defp rust_expect(%{name: name, expect: {:bool, b}}) do
    "assert_eq!(edges::#{name}(), #{b});"
  end

  defp rust_expect(%{name: name, expect: {:opt, _, :none}}) do
    "assert!(edges::#{name}().is_none());"
  end

  defp rust_expect(%{name: name, expect: {:opt, k, {:some, n}}}) do
    "assert_eq!(edges::#{name}(), Some(#{rlit(k, n)}));"
  end

  defp rust_expect(%{name: name, expect: {k, n}}) do
    "assert_eq!(edges::#{name}(), #{rlit(k, n)});"
  end

  defp rlit(:i64, n), do: "#{residue(:i64, n)}u64 as i64"
  defp rlit(k, n), do: "#{residue(k, n)}#{k}"

  defp gcc!(dir, src, obj) do
    {out, status} =
      System.cmd(
        "gcc",
        ~w(-Wall -Wextra -Werror -std=c11 -c) ++ [src, "-o", obj],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
    :ok
  end

  defp link!(dir, objs, bin) do
    {out, status} = System.cmd("gcc", objs ++ ["-o", bin], cd: dir, stderr_to_stdout: true)
    assert status == 0, out
    :ok
  end

  defp run!(dir, bin) do
    {out, status} = System.cmd(Path.join(dir, bin), [], stderr_to_stdout: true)
    assert status == 0, out
    out
  end

  defp zig! do
    path = System.find_executable("zig")
    assert is_binary(path)
    path
  end

  defp rustc! do
    path = System.find_executable("rustc") || Path.join(System.user_home!(), ".cargo/bin/rustc")
    assert File.regular?(path)
    path
  end

  defp tmp(kind) do
    dir = Path.join(System.tmp_dir!(), "muro_word_#{kind}_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
