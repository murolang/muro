defmodule Muro.StringTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.{Lexer, Parser, Print}

  @zig System.find_executable("zig") ||
         if(File.regular?("/opt/homebrew/bin/zig"), do: "/opt/homebrew/bin/zig")

  if System.get_env("CI") && is_nil(@zig) do
    raise "zig is required when CI is set and was not found on PATH"
  end

  test "a core literal keeps the escapes and rejects a surrogate" do
    assert {:ok, [defn]} = Parser.parse("def hello : run String := \"hello\"\n")
    assert defn.body == {:slit, "hello"}

    assert {:ok, [wave]} = Parser.parse("def wave : run String := \"\\u{1F44B}\"\n")
    assert wave.body == {:slit, "👋"}
    assert Print.scalar_count(wave.body |> elem(1)) == 1

    assert {:ok, [accent]} = Parser.parse("def accent : run String := \"é\"\n")
    assert accent.body == {:slit, <<195, 169>>}
    assert Print.scalar_count(<<195, 169>>) == 1

    assert {:ok, [two]} = Parser.parse("def two : run String := \"e\\u{0301}\"\n")
    assert two.body == {:slit, <<101, 204, 129>>}
    assert Print.scalar_count(<<101, 204, 129>>) == 2

    assert {:ok, [nul]} = Parser.parse("def nul : run String := \"\\u{0}\"\n")
    assert nul.body == {:slit, <<0>>}

    assert {:ok, [letter]} = Parser.parse("def letter : run String := \"\\u{41}\"\n")
    assert letter.body == {:slit, "A"}

    assert {:ok, [max]} = Parser.parse("def max : run String := \"\\u{10FFFF}\"\n")
    assert Print.scalar_count(elem(max.body, 1)) == 1

    assert {:ok, [past]} = Parser.parse("def past : run String := \"\\u{E000}\"\n")
    assert Print.scalar_count(elem(past.body, 1)) == 1

    assert {:ok, [nl]} = Parser.parse("def nl : run String := \"a\\nb\"\n")
    assert nl.body == {:slit, "a\nb"}

    assert {:ok, [quoted]} = Parser.parse("def quoted : run String := \"a\\\"b\"\n")
    assert quoted.body == {:slit, "a\"b"}

    assert {:ok, [slash]} = Parser.parse("def slash : run String := \"a\\\\b\"\n")
    assert slash.body == {:slit, "a\\b"}

    assert {:ok, [cat]} = Parser.parse("def parts : run String := strCat \"hel\" \"lo\"\n")
    assert cat.body == {:scat, {:slit, "hel"}, {:slit, "lo"}}

    assert {:ok, [len]} = Parser.parse("def n : run Nat := strLen \"é\"\n")
    assert len.body == {:slen, {:slit, <<195, 169>>}}

    assert {:ok, [eq]} = Parser.parse("def yes : run WBool := strEq \"a\" \"a\"\n")
    assert eq.body == {:seq, {:slit, "a"}, {:slit, "a"}}

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\t\"\n")
    assert msg =~ "bad escape"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u\"\n")
    assert msg =~ "bad escape"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{D800}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{dfff}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{110000}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{0000041}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{41\"\n")
    assert msg =~ "unclosed unicode escape"

    assert {:error, msg} = Parser.parse("def bad : run String := \"a\nb\"\n")
    assert msg =~ "unclosed string"
  end

  test "an escaped quote is one string token" do
    src = "\"a\\\"b\""
    assert [{:string, 0, stop}] = Lexer.tokenize(src)
    assert stop == byte_size(src)

    slash = "\"a\\\\b\""
    assert [{:string, 0, stop}] = Lexer.tokenize(slash)
    assert stop == byte_size(slash)
  end

  test "a repr string and an import path keep a raw backslash" do
    assert {:ok, [imp, defn, repr]} =
             Parser.parse("""
             import "a\\\\b.muro"
             def core : run String := "a\\\\b"
             repr Box := map { "a\\\\b" => integer }
             """)

    assert imp.path == "a\\\\b.muro"
    assert defn.body == {:slit, "a\\b"}
    assert {:map, false, [{"a\\\\b", {:integer}}]} = repr.body
  end

  test "the worked book checks, and a string is not an atom" do
    assert Muro.check_file("examples/string.muro") == :ok

    assert {:error, msg} = check("def bad : run String := :hello\n")
    assert msg =~ "cannot convert Atom ≁ String"

    assert {:error, msg} = check("def bad : run Atom := \"hello\"\n")
    assert msg =~ "cannot convert String ≁ Atom"

    assert {:error, msg} = check("def bad : run String := String\n")
    assert msg =~ "no promotion: String is an erased term"

    assert {:error, msg} = check("def bad : run WBool := strEq :hello \"hello\"\n")
    assert msg =~ "cannot convert Atom ≁ String"

    assert {:error, msg} =
             check("""
             def bad : run Π (s : String) → String :=
               λ (s : String) → strCat s s
             """)

    assert msg =~ "affine variable used twice"

    assert check("def S : spec Type := String\n") == :ok

    assert {:error, msg} = check("session s := send String end\n")
    assert msg =~ "ill-formed payload"

    assert {:error, msg} = check("session s := send \"hello\" end\n")
    assert msg =~ "expected a payload"
  end

  test "Elixir emits a binary, and canon quotes it" do
    dir = tmp_dir()
    path = Path.join(dir, "strings.muro")
    File.cp!("examples/string.muro", path)

    mod = Module.concat(Muro.StringProbe, "M#{System.unique_integer([:positive])}")
    assert {:ok, src} = Muro.emit_file(path, mod)
    assert src =~ ":erlang.length(:unicode.characters_to_list("
    assert src =~ "<>"
    refute src =~ "String.length"

    [{^mod, _bin}] = Code.compile_string(src)

    on_exit(fn ->
      :code.delete(mod)
      :code.purge(mod)
    end)

    assert apply(mod, :hello, []) == "hello"
    assert apply(mod, :tag, []) == :hello
    assert apply(mod, :n, []) == 1
    assert apply(mod, :two, []) == 2
    assert apply(mod, :wave_n, []) == 1
    assert apply(mod, :nul_n, []) == 1
    assert apply(mod, :empty_n, []) == 0
    assert apply(mod, :yes, []) == true
    assert apply(mod, :no, []) == false
    assert apply(mod, :parts, []) == "hello"
    assert apply(mod, :nl, []) == "a\nb"
    assert apply(mod, :quoted, []) == "a\"b"
    assert apply(mod, :slash, []) == "a\\b"
    assert apply(mod, :nul, []) == <<0>>
    assert apply(mod, :accent, []) == "é"
    assert apply(mod, :twice, ["ab"]) == "abab"
    assert apply(mod, :twice, ["é"]) == "éé"
    assert Print.scalar_count(apply(mod, :wave, [])) == 1

    assert Print.quote_string("hello") == "\"hello\""
    assert Print.quote_string("a\nb") == "\"a\\nb\""
    assert Print.quote_string("a\"b") == "\"a\\\"b\""
    assert Print.quote_string("a\\b") == "\"a\\\\b\""
    assert Print.quote_string(<<0>>) == "\"\\u{0}\""
    assert Print.quote_string("hello") != "hello"
  end

  test "JavaScript boxes a string and leaves an atom as a string" do
    dir = tmp_dir()
    path = Path.join(dir, "string.muro")
    File.cp!("examples/string.muro", path)

    assert {:ok, [mjs, dts]} = Muro.emit_js(path)
    source = File.read!(mjs)
    types = File.read!(dts)

    assert source =~ "{ string: \"hello\" }"
    assert source =~ "return (\"hello\")"
    assert source =~ "Array.from(a.string)"
    assert source =~ "typeof v.string === \"string\""
    refute source =~ "c:string"

    assert types =~ "export type Atom = string;"
    assert types =~ "export type String = { readonly string: string };"
    assert types =~ "export function twice(s: String): String;"
    assert types =~ "export function tag(): Atom;"
    assert types =~ "export function hello(): String;"
  end

  test "assembly refuses a string, and evidence that only mentions one is omitted" do
    dir = tmp_dir()
    path = Path.join(dir, "string.muro")
    File.cp!("examples/string.muro", path)

    for backend <- ~w(c rust zig) do
      capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", backend]) end)
    end

    assert File.regular?(Path.join(dir, "string.c"))
    assert File.regular?(Path.join(dir, "string.rs"))
    assert File.regular?(Path.join(dir, "string.zig"))

    assert_raise Mix.Error, ~r/\Ac:string\z/, fn ->
      Mix.Tasks.Muro.Emit.run([path, "--backend", "asm"])
    end

    evidence = Path.join(dir, "kept.muro")

    File.write!(evidence, """
    def n : run Nat := 0
    def accent_ok : evidence {strLen "é" ≡ suc 0 : Nat} := refl
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([evidence, "--backend", "c"]) end)
    assert File.regular?(Path.join(dir, "kept.c"))
    capture_io(fn -> Mix.Tasks.Muro.Emit.run([evidence, "--backend", "asm"]) end)
    assert File.regular?(Path.join(dir, "kept.s"))

    body = Path.join(dir, "len.muro")
    File.write!(body, "def n : run Nat := strLen \"é\"\n")
    capture_io(fn -> Mix.Tasks.Muro.Emit.run([body, "--backend", "c"]) end)
    assert File.regular?(Path.join(dir, "len.c"))

    assert_raise Mix.Error, ~r/\Ac:string\z/, fn ->
      Mix.Tasks.Muro.Emit.run([body, "--backend", "asm"])
    end
  end

  test "C, Rust, and Zig run examples/string.muro" do
    dir = tmp_dir()
    path = Path.join(dir, "string.muro")
    File.cp!("examples/string.muro", path)

    assert {:ok, _} = Muro.emit_c(path, nif: false)
    assert {:ok, _} = Muro.emit_rust(path)
    assert {:ok, _} = Muro.emit_zig(path)

    File.write!(Path.join(dir, "main.c"), string_c_main())
    assert gcc!(dir, "string.c", "string.o", ["-c"]) == :ok
    assert gcc!(dir, "main.c", "string_bin") == :ok
    assert run!(dir, "string_bin") =~ "OK"

    File.write!(
      Path.join(dir, "bin.rs"),
      File.read!(Path.join(dir, "string.rs")) <> string_rust_main()
    )

    assert rustc!(dir, "string.rs") == :ok
    assert rustc_bin!(dir, "bin.rs", "string_bin_rs") == :ok
    assert run!(dir, "string_bin_rs") =~ "OK"

    File.write!(Path.join(dir, "check.zig"), string_zig_main())
    assert zig_test!(dir) == :ok
  end

  test "C, Rust, and Zig run an open string, a zero scalar, and strBytes" do
    dir = tmp_dir()
    path = Path.join(dir, "native.muro")
    File.write!(path, native_book())
    assert Muro.check_file(path) == :ok

    mod = Module.concat(Muro.StringNative, "M#{System.unique_integer([:positive])}")
    assert {:ok, src} = Muro.emit_file(path, mod)
    [{^mod, _bin}] = Code.compile_string(src)

    on_exit(fn ->
      :code.delete(mod)
      :code.purge(mod)
    end)

    assert apply(mod, :interior, []) == "a\0b"
    assert apply(mod, :interior_len, []) == 3
    assert apply(mod, :interior_eq, []) == true
    assert apply(mod, :interior_ne, []) == false
    assert apply(mod, :interior_bytes, []) == <<0x61, 0, 0x62>>
    assert apply(mod, :accent_octets, []) == <<0xC3, 0xA9>>
    assert apply(mod, :open_octets, []) == "éé"
    assert apply(mod, :bytes_of, ["a\0b"]) == <<0x61, 0, 0x62>>
    assert apply(mod, :bytes_of, ["é"]) == <<0xC3, 0xA9>>
    assert apply(mod, :len_of, ["é"]) == 1
    assert apply(mod, :len_of, ["e\u0301"]) == 2
    assert apply(mod, :len_of, ["a\0b"]) == 3
    assert apply(mod, :eq_of, ["a\0b", "a\0b"]) == true
    assert apply(mod, :eq_of, ["a\0b", "ab"]) == false
    assert apply(mod, :cat_of, ["a\0", "b"]) == "a\0b"
    assert apply(mod, :joined, []) == "ab"
    assert apply(mod, :glued, []) == "a\0b"
    assert apply(mod, :some_text, []) == "hi"
    assert apply(mod, :none_text, []) == ""
    assert apply(mod, :noted, []) == "hi"
    assert apply(mod, :first_two, []) == "aab"

    assert {:ok, _} = Muro.emit_c(path, nif: false)
    assert {:ok, _} = Muro.emit_rust(path)
    assert {:ok, _} = Muro.emit_zig(path)

    File.write!(Path.join(dir, "main.c"), native_c_main())
    assert gcc!(dir, "native.c", "native.o", ["-c"]) == :ok
    assert gcc!(dir, "main.c", "native_bin") == :ok
    assert run!(dir, "native_bin") =~ "OK"

    File.write!(
      Path.join(dir, "bin.rs"),
      File.read!(Path.join(dir, "native.rs")) <> native_rust_main()
    )

    assert rustc!(dir, "native.rs") == :ok
    assert rustc_bin!(dir, "bin.rs", "native_bin_rs") == :ok
    assert run!(dir, "native_bin_rs") =~ "OK"

    File.write!(Path.join(dir, "check.zig"), native_zig_main())
    assert zig_test!(dir) == :ok
  end

  defp native_book do
    """
    def interior : run String := "a\\u{0}b"

    def interior_len : run Nat := strLen interior

    def interior_eq : run WBool := strEq interior "a\\u{0}b"

    def interior_ne : run WBool := strEq interior "ab"

    def interior_bytes : run Bytes := strBytes interior

    def accent_octets : run Bytes := strBytes "é"

    def open_octets : run Bytes := strBytes (strCat "é" "é")

    def bytes_of : run Π (s : String) → Bytes :=
      λ (s : String) → strBytes s

    def len_of : run Π (s : String) → Nat :=
      λ (s : String) → strLen s

    def eq_of : run Π (x : String) → Π (y : String) → WBool :=
      λ (x : String) → λ (y : String) → strEq x y

    def cat_of : run Π (x : String) → Π (y : String) → String :=
      λ (x : String) → λ (y : String) → strCat x y

    def joined : run String := let (left, right) = ("a", "b") in strCat left right

    def glued : run String := let (left, right) = ("a\\u{0}", "b") in strCat left right

    def unwrap : run Π (o : Opt String) → String :=
      λ (o : Opt String) →
        match o motive (λ _ → String)
          | wsome text => text
          | wnone => ""

    def some_text : run String := unwrap (wsome "hi")

    def none_text : run String := unwrap wnone

    data Note : Type where
      note : String → Note

    def unpack : run Π (item : Note) → String :=
      λ (item : Note) →
        match item motive (λ _ → String)
          | note text => text

    def noted : run String := unpack (note "hi")

    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def letters : run Stream String :=
      unfold "a" (λ (+ k : String) → (k, strCat k "b"))

    def first_two : run String :=
      let (h, rest) = uncons letters in
        let (h2, rest2) = uncons rest in
          strCat h h2
    """
  end

  defp string_c_main do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>
    #include <stdint.h>
    #include <stddef.h>
    static size_t allocs;
    static void *counting_alloc(size_t n) { allocs++; return malloc(n); }
    #define muro__ALLOC(n) counting_alloc(n)
    #include "string.c"
    static int nat_to(muro__nat *n) {
      int k = 0;
      while (n && n->muro__field_tag == 1) { k++; n = n->muro__field_suc; }
      return k;
    }
    static int fail(const char *m) { fprintf(stderr, "%s\\n", m); return 1; }
    static int eqmem(muro__str s, const unsigned char *lit, size_t n) {
      if (s.n != n) return 0;
      if (n == 0) return 1;
      return memcmp(s.p, lit, n) == 0;
    }
    int main(void) {
      size_t base = allocs;
      if (!eqmem(hello_2(), (const unsigned char *)"hello", 5)) return fail("hello");
      if (allocs != base) return fail("hello alloc");
      base = allocs;
      if (!eqmem(nul(), (const unsigned char *)"\\0", 1) || nul().p[0] != 0) return fail("nul");
      if (allocs != base) return fail("nul alloc");
      base = allocs;
      if (!yes()) return fail("yes");
      if (no()) return fail("no");
      if (allocs != base) return fail("eq alloc");
      base = allocs;
      if (nat_to(n()) != 1) return fail("accent len");
      if (allocs != base + 2) return fail("accent nat");
      base = allocs;
      if (nat_to(two()) != 2) return fail("combining");
      if (allocs != base + 3) return fail("combining nat");
      if (nat_to(wavezun()) != 1) return fail("wave");
      if (nat_to(nulzun()) != 1) return fail("nul len");
      if (nat_to(emptyzun()) != 0) return fail("empty len");
      base = allocs;
      if (!eqmem(parts(), (const unsigned char *)"hello", 5)) return fail("parts");
      if (allocs != base + 1) return fail("parts alloc");
      base = allocs;
      muro__str ab = twice((muro__str){(const unsigned char *)"ab", 2});
      if (!eqmem(ab, (const unsigned char *)"abab", 4)) return fail("twice");
      if (allocs != base + 1) return fail("twice alloc");
      muro__str ee = twice(accent());
      if (ee.n != 4 || ee.p[0] != 195) return fail("twice accent");
      if (!eqmem(nl(), (const unsigned char *)"a\\nb", 3)) return fail("nl");
      if (tag() != hello) return fail("tag");
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp native_c_main do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>
    #include <stdint.h>
    #include <stddef.h>
    static size_t allocs;
    static void *counting_alloc(size_t n) { allocs++; return malloc(n); }
    #define muro__ALLOC(n) counting_alloc(n)
    #include "native.c"
    static int nat_to(muro__nat *n) {
      int k = 0;
      while (n && n->muro__field_tag == 1) { k++; n = n->muro__field_suc; }
      return k;
    }
    static int fail(const char *m) { fprintf(stderr, "%s\\n", m); return 1; }
    static int eqmem(muro__str s, const unsigned char *lit, size_t n) {
      if (s.n != n) return 0;
      if (n == 0) return 1;
      return memcmp(s.p, lit, n) == 0;
    }
    static int eqslice(muro__slice s, const unsigned char *lit, size_t n) {
      if (s.n != n) return 0;
      if (n == 0) return 1;
      return memcmp(s.p, lit, n) == 0;
    }
    int main(void) {
      const unsigned char raw[] = {0x61, 0x00, 0x62};
      const unsigned char accent[] = {0xC3, 0xA9};
      const unsigned char cat[] = {0x61, 0x00, 0x62, 0x61, 0x00, 0x62};
      muro__str s = {raw, 3};
      muro__str e = {accent, 2};
      size_t base = allocs;
      if (!eqmem(interior(), raw, 3)) return fail("interior");
      if (allocs != base) return fail("interior alloc");
      if (nat_to(interiorzulen()) != 3) return fail("interior len");
      base = allocs;
      if (!interiorzueq()) return fail("interior eq");
      if (interiorzune()) return fail("interior ne");
      if (allocs != base) return fail("eq alloc");
      base = allocs;
      muro__slice zb = interiorzubytes();
      if (!eqslice(zb, raw, 3) || zb.p != interior().p) return fail("interior bytes");
      if (allocs != base) return fail("bytes alloc");
      if (!eqslice(accentzuoctets(), accent, 2)) return fail("accent octets");
      if (!eqslice(openzuoctets(), (const unsigned char *)"\\xC3\\xA9\\xC3\\xA9", 4)) return fail("open octets");
      base = allocs;
      if (!eqslice(byteszuof(s), raw, 3)) return fail("bytes of");
      if (allocs != base) return fail("open bytes alloc");
      if (nat_to(lenzuof(e)) != 1) return fail("len accent");
      if (nat_to(lenzuof(s)) != 3) return fail("len zero");
      if (!eqzuof(s, s)) return fail("eq zero");
      muro__str other = {(const unsigned char *)"ab", 2};
      if (eqzuof(s, other)) return fail("ne zero");
      base = allocs;
      muro__str doubled = catzuof(s, s);
      if (!eqmem(doubled, cat, 6)) return fail("cat zero");
      if (allocs != base + 1) return fail("cat alloc");
      if (!eqmem(joined(), (const unsigned char *)"ab", 2)) return fail("joined");
      if (!eqmem(glued(), raw, 3)) return fail("glued");
      if (!eqmem(somezutext(), (const unsigned char *)"hi", 2)) return fail("some");
      if (!eqmem(nonezutext(), (const unsigned char *)"", 0)) return fail("none");
      if (!eqmem(noted(), (const unsigned char *)"hi", 2)) return fail("noted");
      if (!eqmem(firstzutwo(), (const unsigned char *)"aab", 3)) return fail("stream");
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp string_rust_main do
    """

    fn bytes_of(s: muro__str) -> Vec<u8> {
        if s.n == 0 { return Vec::new(); }
        unsafe { ::std::slice::from_raw_parts(s.p, s.n).to_vec() }
    }
    fn main() {
        assert_eq!(bytes_of(hello()), b"hello");
        assert_eq!(muro__to_u64(&n()), 1);
        assert_eq!(muro__to_u64(&two()), 2);
        assert_eq!(muro__to_u64(&wavezun()), 1);
        assert_eq!(muro__to_u64(&nulzun()), 1);
        assert_eq!(muro__to_u64(&emptyzun()), 0);
        assert!(yes());
        assert!(!no());
        assert_eq!(bytes_of(parts()), b"hello");
        let z = nul();
        assert_eq!(z.n, 1);
        assert_eq!(unsafe { *z.p }, 0);
        let ab = muro__str { p: b"ab".as_ptr(), n: 2 };
        assert_eq!(bytes_of(twice(ab)), b"abab");
        assert_eq!(twice(accent()).n, 4);
        assert_eq!(bytes_of(nl()), b"a\\nb");
        assert!(tag() == muro__Atom::hello);
        println!("OK");
    }
    """
  end

  defp native_rust_main do
    """

    fn bytes_of(s: muro__str) -> Vec<u8> {
        if s.n == 0 { return Vec::new(); }
        unsafe { ::std::slice::from_raw_parts(s.p, s.n).to_vec() }
    }
    fn slice_of(s: muro__slice) -> Vec<u8> {
        if s.n == 0 { return Vec::new(); }
        unsafe { ::std::slice::from_raw_parts(s.p, s.n).to_vec() }
    }
    fn main() {
        let raw: &[u8] = &[0x61, 0x00, 0x62];
        let accent: &[u8] = &[0xC3, 0xA9];
        assert_eq!(bytes_of(interior()), raw);
        assert_eq!(muro__to_u64(&interiorzulen()), 3);
        assert!(interiorzueq());
        assert!(!interiorzune());
        assert_eq!(slice_of(interiorzubytes()), raw);
        assert_eq!(interiorzubytes().p, interior().p);
        assert_eq!(slice_of(accentzuoctets()), accent);
        assert_eq!(slice_of(openzuoctets()), &[0xC3, 0xA9, 0xC3, 0xA9]);
        let s = muro__str { p: raw.as_ptr(), n: 3 };
        let e = muro__str { p: accent.as_ptr(), n: 2 };
        assert_eq!(slice_of(byteszuof(s)), raw);
        assert_eq!(muro__to_u64(&lenzuof(e)), 1);
        assert_eq!(muro__to_u64(&lenzuof(s)), 3);
        assert!(eqzuof(s, s));
        let other = muro__str { p: b"ab".as_ptr(), n: 2 };
        assert!(!eqzuof(s, other));
        assert_eq!(bytes_of(catzuof(s, s)), &[0x61, 0x00, 0x62, 0x61, 0x00, 0x62]);
        assert_eq!(bytes_of(joined()), b"ab");
        assert_eq!(bytes_of(glued()), raw);
        assert_eq!(bytes_of(somezutext()), b"hi");
        assert_eq!(bytes_of(nonezutext()), b"");
        assert_eq!(bytes_of(noted()), b"hi");
        assert_eq!(bytes_of(firstzutwo()), b"aab");
        println!("OK");
    }
    """
  end

  defp string_zig_main do
    """
    const std = @import("std");
    const s = @import("string.zig");
    fn nat(n: *const s.muro__Nat) u64 { return s.muro__to_u64(n); }
    test "string" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const a = arena.allocator();
        const hello = try s.hello(a);
        try std.testing.expectEqualSlices(u8, "hello", hello.p[0..hello.n]);
        try std.testing.expectEqual(@as(u64, 1), nat(try s.n(a)));
        try std.testing.expectEqual(@as(u64, 2), nat(try s.two(a)));
        try std.testing.expectEqual(@as(u64, 1), nat(try s.wavezun(a)));
        try std.testing.expectEqual(@as(u64, 1), nat(try s.nulzun(a)));
        try std.testing.expectEqual(@as(u64, 0), nat(try s.emptyzun(a)));
        try std.testing.expectEqual(@as(u8, 1), try s.yes(a));
        try std.testing.expectEqual(@as(u8, 0), try s.no(a));
        const parts = try s.parts(a);
        try std.testing.expectEqualSlices(u8, "hello", parts.p[0..parts.n]);
        const z = try s.nul(a);
        try std.testing.expectEqual(@as(usize, 1), z.n);
        try std.testing.expectEqual(@as(u8, 0), z.p[0]);
        const ab = s.muro__str{ .p = @as([*]const u8, @ptrCast("ab")), .n = 2 };
        const twice = try s.twice(a, ab);
        try std.testing.expectEqualSlices(u8, "abab", twice.p[0..twice.n]);
        const accent = try s.accent(a);
        const ee = try s.twice(a, accent);
        try std.testing.expectEqual(@as(usize, 4), ee.n);
        const nl = try s.nl(a);
        try std.testing.expectEqualSlices(u8, "a\\nb", nl.p[0..nl.n]);
        const tag = try s.tag(a);
        try std.testing.expect(tag.* == .hello);
    }
    """
  end

  defp native_zig_main do
    """
    const std = @import("std");
    const m = @import("native.zig");
    fn nat(n: *const m.muro__Nat) u64 { return m.muro__to_u64(n); }
    fn expect_str(s: m.muro__str, lit: []const u8) !void {
        try std.testing.expectEqual(lit.len, s.n);
        if (lit.len != 0) try std.testing.expectEqualSlices(u8, lit, s.p[0..s.n]);
    }
    fn expect_slice(s: m.muro__slice, lit: []const u8) !void {
        try std.testing.expectEqual(lit.len, s.n);
        if (lit.len != 0) try std.testing.expectEqualSlices(u8, lit, s.p[0..s.n]);
    }
    test "native string" {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const a = arena.allocator();
        const raw = [_]u8{ 0x61, 0x00, 0x62 };
        const accent = [_]u8{ 0xC3, 0xA9 };
        const interior = try m.interior(a);
        try expect_str(interior, &raw);
        try std.testing.expectEqual(@as(u64, 3), nat(try m.interiorzulen(a)));
        try std.testing.expectEqual(@as(u8, 1), try m.interiorzueq(a));
        try std.testing.expectEqual(@as(u8, 0), try m.interiorzune(a));
        const zb = try m.interiorzubytes(a);
        try expect_slice(zb, &raw);
        try std.testing.expectEqual(interior.p, zb.p);
        try expect_slice(try m.accentzuoctets(a), &accent);
        try expect_slice(try m.openzuoctets(a), &[_]u8{ 0xC3, 0xA9, 0xC3, 0xA9 });
        const s = m.muro__str{ .p = @as([*]const u8, @ptrCast(&raw)), .n = 3 };
        const e = m.muro__str{ .p = @as([*]const u8, @ptrCast(&accent)), .n = 2 };
        try expect_slice(try m.byteszuof(a, s), &raw);
        try std.testing.expectEqual(@as(u64, 1), nat(try m.lenzuof(a, e)));
        try std.testing.expectEqual(@as(u64, 3), nat(try m.lenzuof(a, s)));
        try std.testing.expectEqual(@as(u8, 1), try m.eqzuof(a, s, s));
        const other = m.muro__str{ .p = @as([*]const u8, @ptrCast("ab")), .n = 2 };
        try std.testing.expectEqual(@as(u8, 0), try m.eqzuof(a, s, other));
        try expect_str(try m.catzuof(a, s, s), &[_]u8{ 0x61, 0x00, 0x62, 0x61, 0x00, 0x62 });
        try expect_str(try m.joined(a), "ab");
        try expect_str(try m.glued(a), &raw);
        try expect_str(try m.somezutext(a), "hi");
        try expect_str(try m.nonezutext(a), "");
        try expect_str(try m.noted(a), "hi");
        try expect_str(try m.firstzutwo(a), "aab");
    }
    """
  end

  defp gcc!(dir, src, bin, extra \\ []) do
    {out, status} =
      System.cmd("cc", extra ++ ["-Wall", "-Wextra", "-Werror", "-std=c11", src, "-o", bin],
        cd: dir,
        stderr_to_stdout: true
      )

    if status == 0, do: :ok, else: {status, out}
  end

  defp run!(dir, bin) do
    {out, status} = System.cmd(Path.join(dir, bin), [], cd: dir, stderr_to_stdout: true)
    if status == 0, do: out, else: flunk(out)
  end

  defp rustc!(dir, src) do
    {out, status} =
      System.cmd("rustc", ["--edition", "2021", "--crate-type", "lib", src],
        cd: dir,
        stderr_to_stdout: true
      )

    cond do
      status != 0 -> {status, out}
      out =~ "warning:" -> {:warning, out}
      true -> :ok
    end
  end

  defp rustc_bin!(dir, src, bin) do
    {out, status} =
      System.cmd("rustc", ["--edition", "2021", src, "-o", bin],
        cd: dir,
        stderr_to_stdout: true
      )

    cond do
      status != 0 -> {status, out}
      out =~ "warning:" -> {:warning, out}
      true -> :ok
    end
  end

  defp zig_test!(dir) do
    zig = @zig || flunk("zig not on PATH")

    {out, status} =
      System.cmd(zig, ["test", "check.zig"],
        cd: dir,
        stderr_to_stdout: true
      )

    if status == 0, do: :ok, else: {status, out}
  end

  defp check(src) do
    path =
      Path.join(System.tmp_dir!(), "muro_string_#{System.unique_integer([:positive])}.muro")

    File.write!(path, src)
    on_exit(fn -> File.rm(path) end)
    Muro.check_file(path)
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_string_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
