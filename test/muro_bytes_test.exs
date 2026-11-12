defmodule Muro.BytesTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.{Lexer, Parser, Print}

  @node System.find_executable("node") ||
          if(File.regular?("/opt/homebrew/bin/node"), do: "/opt/homebrew/bin/node")

  @zig System.find_executable("zig") ||
         if(File.regular?("/opt/homebrew/bin/zig"), do: "/opt/homebrew/bin/zig")

  if System.get_env("CI") && is_nil(@node) do
    raise "node is required when CI is set and was not found on PATH"
  end

  if System.get_env("CI") && is_nil(@zig) do
    raise "zig is required when CI is set and was not found on PATH"
  end

  @node_skip if(is_nil(@node), do: "node not on PATH", else: false)
  @zig_skip if(is_nil(@zig), do: "zig not on PATH", else: false)
  @n 16_384

  test "a bytes literal keeps octet escapes and is not a string" do
    assert {:ok, [hello]} = Parser.parse("def hello : run Bytes := b\"hello\"\n")
    assert hello.body == {:blit, "hello"}

    assert {:ok, [ff]} = Parser.parse("def ff : run Bytes := b\"\\xFF\"\n")
    assert ff.body == {:blit, <<255>>}

    assert {:ok, [low]} = Parser.parse("def low : run Bytes := b\"\\xff\"\n")
    assert low.body == {:blit, <<255>>}

    assert {:ok, [nul]} = Parser.parse("def nul : run Bytes := b\"\\x00\"\n")
    assert nul.body == {:blit, <<0>>}

    assert {:ok, [nl]} = Parser.parse("def nl : run Bytes := b\"\\n\"\n")
    assert nl.body == {:blit, "\n"}

    assert {:ok, [cr]} = Parser.parse("def cr : run Bytes := b\"\\r\"\n")
    assert cr.body == {:blit, "\r"}

    assert {:ok, [tab]} = Parser.parse("def tab : run Bytes := b\"\\t\"\n")
    assert tab.body == {:blit, "\t"}

    assert {:ok, [quoted]} = Parser.parse("def quoted : run Bytes := b\"a\\\"b\"\n")
    assert quoted.body == {:blit, "a\"b"}

    assert {:ok, [slash]} = Parser.parse("def slash : run Bytes := b\"a\\\\b\"\n")
    assert slash.body == {:blit, "a\\b"}

    assert {:ok, [raw]} = Parser.parse("def raw : run Bytes := b\"\\xFFF\"\n")
    assert raw.body == {:blit, <<255, ?F>>}

    assert {:ok, [accent]} = Parser.parse("def accent : run Bytes := b\"é\"\n")
    assert accent.body == {:blit, <<195, 169>>}

    assert {:ok, [cat]} = Parser.parse("def parts : run Bytes := bytesCat b\"hel\" b\"lo\"\n")
    assert cat.body == {:bcat, {:blit, "hel"}, {:blit, "lo"}}

    assert {:error, msg} = Parser.parse("def bad : run Bytes := b\"\\xF\"\n")
    assert msg =~ "bad escape"

    assert {:error, msg} = Parser.parse("def bad : run Bytes := b\"\\x\"\n")
    assert msg =~ "bad escape"

    assert {:error, msg} = Parser.parse("def bad : run Bytes := b\"\\u{41}\"\n")
    assert msg =~ "bad escape"

    assert {:error, msg} = Parser.parse("def bad : run Bytes := b\"a\nb\"\n")
    assert msg =~ "unclosed bytes"

    src = "b\"a\\\"b\""
    assert [{:string, 0, stop}] = Lexer.tokenize(src)
    assert stop == byte_size(src)

    assert [{:name, 0, 2}, {:string, 2, 6}] = Lexer.tokenize("ab\"cd\"")
  end

  test "bytes, strings, and atoms stay distinct, and a session refuses both" do
    assert Muro.check_file("examples/bytes.muro") == :ok
    assert Muro.check_file("examples/bytes-uncons.muro") == :ok
    assert Muro.check_file("examples/request-line.muro") == :ok
    assert Muro.check_file("examples/fnv_slice.muro") == :ok
    assert Muro.check_file("examples/fnv.muro") == :ok
    assert Muro.check_file("examples/string.muro") == :ok

    assert {:error, msg} = check("def bad : run String := b\"hello\"\n")
    assert msg =~ "cannot convert Bytes ≁ String"

    assert {:error, msg} = check("def bad : run Bytes := \"hello\"\n")
    assert msg =~ "cannot convert String ≁ Bytes"

    assert {:error, msg} = check("def bad : run Atom := b\"hello\"\n")
    assert msg =~ "cannot convert Bytes ≁ Atom"

    assert {:error, msg} = check("def bad : run Bytes := :hello\n")
    assert msg =~ "cannot convert Atom ≁ Bytes"

    assert {:error, msg} = check("def bad : evidence {b\"hello\" ≡ \"hello\" : Bytes} := refl\n")
    assert msg =~ "cannot convert"

    assert check("def view : run Slice := b\"ab\"\n") == :ok

    assert {:error, msg} = check("def bad : evidence {b\"ab\" ≡ \"ab\" : Slice} := refl\n")
    assert msg =~ "cannot convert"

    assert {:error, msg} = check("session s := send Bytes end\n")
    assert msg =~ "ill-formed payload"

    assert {:error, msg} = check("session s := send Slice end\n")
    assert msg =~ "ill-formed payload"

    assert {:error, msg} = check("def bad : run Bytes := Bytes\n")
    assert msg =~ "no promotion: Bytes is an erased term"
  end

  test "two views of one buffer need +s" do
    two = """
    def two : run Π (s : Slice) → Slice × Slice :=
      λ (s : Slice) → (slice s (toU64 0) (toU64 2), slice s (toU64 2) (toU64 3))
    """

    assert {:error, msg} = check(two)
    assert msg =~ "affine variable used twice"

    reused = """
    def two : run Π (+ s : Slice) → Slice × Slice :=
      λ (+ s : Slice) → (slice s (toU64 0) (toU64 2), slice s (toU64 2) (toU64 3))
    def views : run Slice × Slice := two b"hello"
    """

    assert check(reused) == :ok
  end

  test "canon prints a bytes literal, not a string and not an atom" do
    assert Print.quote_bytes("hello") == "b\"hello\""
    assert Print.quote_bytes(<<255>>) == "b\"\\xff\""
    assert Print.quote_bytes(<<0>>) == "b\"\\x00\""
    assert Print.quote_bytes("\n") == "b\"\\n\""
    assert Print.quote_bytes("\r") == "b\"\\r\""
    assert Print.quote_bytes("\t") == "b\"\\t\""
    assert Print.quote_bytes("a\"b") == "b\"a\\\"b\""
    assert Print.quote_bytes("a\\b") == "b\"a\\\\b\""
    assert Print.quote_bytes(<<195, 169>>) == "b\"\\xc3\\xa9\""
    assert Print.quote_bytes("hello") != Print.quote_string("hello")
    assert Print.quote_bytes("hello") != ":hello"

    assert {:ok, book} = Parser.parse("def h : run Bytes := b\"\\xFF\"\n")
    printed = Print.term(hd(book).body)
    assert printed == "b\"\\xff\""
  end

  test "Elixir emits a binary and agrees with the closed runs" do
    dir = tmp("ex")
    File.cp!("examples/bytes.muro", Path.join(dir, "bytes.muro"))
    mod = Module.concat(Muro.BytesProbe, "M#{System.unique_integer([:positive])}")
    assert {:ok, src} = Muro.emit_file(Path.join(dir, "bytes.muro"), mod)
    assert src =~ "byte_size"
    assert src =~ ":binary.part"
    assert src =~ "<<255>>"
    refute src =~ "muro__ALLOC"

    [{^mod, _bin}] = Code.compile_string(src)

    on_exit(fn ->
      :code.delete(mod)
      :code.purge(mod)
    end)

    assert apply(mod, :hello, []) == "hello"
    assert apply(mod, :ff, []) == <<255>>
    assert apply(mod, :nul, []) == <<0>>
    assert apply(mod, :accent, []) == <<195, 169>>
    assert apply(mod, :n_hello, []) == 5
    assert apply(mod, :n_accent, []) == 2
    assert apply(mod, :n_ff, []) == 1
    assert apply(mod, :parts, []) == "hello"
    assert apply(mod, :from_str, []) == "hello"
    assert apply(mod, :yes, []) == true
    assert apply(mod, :no, []) == false
    assert apply(mod, :mid, []) == "ell"
    assert apply(mod, :past, []) == ""
    assert apply(mod, :over, []) == ""
    assert apply(mod, :at0, []) == {:some, 97}
    assert apply(mod, :at1, []) == {:some, 98}
    assert apply(mod, :miss, []) == :none
    assert apply(mod, :method, []) == "GET"
    assert apply(mod, :whole, []) == "GET"
    assert apply(mod, :path, []) == "/x"
    assert apply(mod, :no_path, []) == ""
    assert apply(mod, :sum2, []) == 3
    assert apply(mod, :empty, []) == ""
  end

  test "C emits a pointer and a length, and a request line does not copy" do
    dir = tmp("c")
    File.cp!("examples/bytes.muro", Path.join(dir, "bytes.muro"))
    assert {:ok, [h, c]} = Muro.emit_c(Path.join(dir, "bytes.muro"), nif: false)
    header = File.read!(h)
    source = File.read!(c)

    assert header =~ "typedef struct { const uint8_t *p; size_t n; } muro__slice;"
    assert header =~ "static const uint8_t muro__empty_bytes[1] = {0};"
    assert header =~ "muro__slice_of(const uint8_t *p, size_t n)"
    assert source =~ "static const uint8_t muro__s_0[]"
    assert source =~ "s.p + (size_t)off"
    assert source =~ "muro__ALLOC(n)"
    assert source =~ "if (b.n > SIZE_MAX - a.n) abort();"
    refute source =~ "typedef struct muro__ByteList"
    refute source =~ "typedef struct { uint8_t *p;"

    File.cp!("examples/request-line.muro", Path.join(dir, "request-line.muro"))
    assert {:ok, _} = Muro.emit_c(Path.join(dir, "request-line.muro"), nif: false)
    File.write!(Path.join(dir, "req_main.c"), req_main())
    assert gcc!(dir, "req_main.c", "req") == :ok
    assert run!(dir, "req") == "OK\n"

    File.write!(Path.join(dir, "cat_overflow.c"), cat_overflow_main())
    assert gcc!(dir, "cat_overflow.c", "cat_overflow") == :ok

    {out, status} =
      System.cmd(Path.join(dir, "cat_overflow"), [], cd: dir, stderr_to_stdout: true)

    assert status != 0, "overflowing concat should abort, got 0: #{out}"
    refute out =~ "ALLOC called"
    refute out =~ "no abort"
  end

  test "a flat slice hashes a buffer without allocating a cell per byte" do
    dir = tmp("bench")
    File.cp!("examples/fnv.muro", Path.join(dir, "fnv.muro"))
    File.cp!("examples/fnv_slice.muro", Path.join(dir, "fnv_slice.muro"))
    assert {:ok, [fh, _]} = Muro.emit_c(Path.join(dir, "fnv.muro"), nif: false)
    assert {:ok, _} = Muro.emit_c(Path.join(dir, "fnv_slice.muro"), nif: false)
    fnv_h = File.read!(fh)
    assert fnv_h =~ "ByteList"
    refute fnv_h =~ "muro__slice"

    File.write!(Path.join(dir, "bench.c"), bench())
    assert gcc!(dir, "bench.c", "bench_cons", []) == :ok
    assert gcc!(dir, "bench.c", "bench_slice", ["-D", "SLICE"]) == :ok
    cons = run!(dir, "bench_cons")
    slice = run!(dir, "bench_slice")

    assert cons =~ "build_allocs=#{@n}"
    assert cons =~ "hash="
    assert slice =~ "walk_allocs=0"
    assert hash_of(cons) == hash_of(slice)
  end

  test "Rust emits a pointer and a length" do
    dir = tmp("rust")
    File.cp!("examples/bytes.muro", Path.join(dir, "bytes.muro"))
    path = Path.join(dir, "bytes.muro")

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "rust"]) end)
    rust = File.read!(Path.join(dir, "bytes.rs"))
    assert rust =~ "pub struct muro__slice { pub p: *const u8, pub n: usize }"
    assert rust =~ "pub fn muro__slice_of"
    assert rust =~ "with_capacity"
    refute rust =~ "c:bytes"
    assert rustc!(dir, "bytes.rs") == :ok
  end

  @tag skip: @zig_skip
  test "Zig emits a pointer and a length" do
    dir = tmp("zig")
    File.cp!("examples/bytes.muro", Path.join(dir, "bytes.muro"))
    path = Path.join(dir, "bytes.muro")

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "zig"]) end)
    zig = File.read!(Path.join(dir, "bytes.zig"))
    assert zig =~ "pub const muro__slice = extern struct { p: [*]const u8, n: usize }"
    assert zig =~ "pub fn muro__slice_of"
    assert zig =~ "muro__allocator.alloc(u8, n)"
    assert zig =~ "@addWithOverflow(a.n, b.n)"
    assert zig =~ "return error.Overflow"
    refute zig =~ "c:bytes"
    File.write!(Path.join(dir, "check.zig"), zig_main())
    assert zig_test!(dir) == :ok
  end

  @tag skip: @node_skip
  test "JavaScript emits a Uint8Array and canon prints the literal" do
    dir = tmp("js")
    File.cp!("examples/bytes.muro", Path.join(dir, "bytes.muro"))
    File.cp!("examples/bytes-uncons.muro", Path.join(dir, "bytes-uncons.muro"))
    assert {:ok, [mjs, dts]} = Muro.emit_js(Path.join(dir, "bytes.muro"))
    assert {:ok, _} = Muro.emit_js(Path.join(dir, "bytes-uncons.muro"))
    source = File.read!(mjs)
    types = File.read!(dts)
    assert source =~ "new Uint8Array([255])"
    assert source =~ ".subarray("
    assert types =~ "export type Bytes = Uint8Array;"
    assert types =~ "export type Slice = Uint8Array;"
    assert types =~ "export function hello(): Bytes;"
    refute source =~ "{ string: \"hello\" }"

    File.write!(Path.join(dir, "check.mjs"), js_main())
    {out, status} = System.cmd(@node, ["check.mjs"], cd: dir, stderr_to_stdout: true)
    assert status == 0, out
    assert String.trim(out) == "OK"
  end

  test "evidence that mentions bytes is omitted, and assembly refuses a bytes run" do
    dir = tmp("omit")

    File.write!(Path.join(dir, "kept.muro"), """
    def n : run Nat := 0
    def mentioned : evidence {bytesLen b"ab" ≡ toU64 2 : U64} := refl
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([Path.join(dir, "kept.muro"), "--backend", "c"]) end)
    body = File.read!(Path.join(dir, "kept.c"))
    refute body =~ "muro__slice"
    assert body =~ "muro__zero"

    capture_io(fn ->
      Mix.Tasks.Muro.Emit.run([Path.join(dir, "kept.muro"), "--backend", "asm"])
    end)

    assert File.regular?(Path.join(dir, "kept.s"))

    File.cp!("examples/bytes.muro", Path.join(dir, "bytes.muro"))

    assert_raise Mix.Error, ~r/\Aasm:scope\z/, fn ->
      Mix.Tasks.Muro.Emit.run([Path.join(dir, "bytes.muro"), "--backend", "asm"])
    end
  end

  defp hash_of(text) do
    [_, n] = Regex.run(~r/hash=(\d+)/, text)
    n
  end

  defp check(src) do
    path = Path.join(System.tmp_dir!(), "muro_bytes_#{System.unique_integer([:positive])}.muro")
    File.write!(path, src)
    on_exit(fn -> File.rm(path) end)
    Muro.check_file(path)
  end

  defp tmp(tag) do
    dir = Path.join(System.tmp_dir!(), "muro_bytes_#{tag}_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp gcc!(dir, src, bin, extra \\ []) do
    {out, status} =
      System.cmd("gcc", extra ++ ["-Wall", "-Wextra", "-Werror", "-std=c11", src, "-o", bin],
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

  defp zig_test!(dir) do
    {out, status} =
      System.cmd(@zig, ["test", "check.zig"],
        cd: dir,
        stderr_to_stdout: true
      )

    if status == 0, do: :ok, else: {status, out}
  end

  defp cat_overflow_main do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>
    #include <stdint.h>
    #include <stddef.h>
    static void *muro_test_alloc(size_t n) {
      fprintf(stderr, "ALLOC called n=%zu\\n", n);
      exit(3);
    }
    #define muro__ALLOC(n) muro_test_alloc(n)
    #include "bytes.c"
    int main(void) {
      static const uint8_t one = 1;
      muro__slice a = muro__slice_of(&one, SIZE_MAX);
      muro__slice b = muro__slice_of(&one, (size_t)1);
      (void)muro__bytes_cat(a, b);
      fprintf(stderr, "no abort\\n");
      return 2;
    }
    """
  end

  defp req_main do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>
    #include <stdint.h>
    #include <stddef.h>
    static size_t allocs;
    #define muro__ALLOC(n) (allocs++, malloc(n))
    #include "request-line.c"
    static int fail(const char *m) { fprintf(stderr, "%s\\n", m); return 1; }
    static int inside(muro__slice s, muro__slice whole) {
      return s.p >= whole.p && s.p <= whole.p + whole.n && s.p + s.n <= whole.p + whole.n;
    }
    int main(void) {
      const char *get = "GET /feed HTTP/1.1\\r\\n";
      muro__slice s = muro__slice_of((const uint8_t *)get, strlen(get));
      size_t base = allocs;
      muro__slice m = method(s);
      muro__slice p = path(s);
      if (allocs != base) return fail("alloc get");
      if (m.n != 3 || memcmp(m.p, "GET", 3) != 0) return fail("method");
      if (p.n != 5 || memcmp(p.p, "/feed", 5) != 0) return fail("path");
      if (!inside(m, s) || !inside(p, s)) return fail("inside");
      if (m.p != s.p || p.p != s.p + 4) return fail("ptr");
      const char *post = "POST /x HTTP/1.1\\r\\n";
      muro__slice ps = muro__slice_of((const uint8_t *)post, strlen(post));
      base = allocs;
      muro__slice pm = method(ps);
      muro__slice pp = path(ps);
      if (allocs != base) return fail("alloc post");
      if (pm.n != 4 || memcmp(pm.p, "POST", 4) != 0) return fail("post method");
      if (pp.n != 2 || memcmp(pp.p, "/x", 2) != 0) return fail("post path");
      if (!inside(pm, ps) || !inside(pp, ps)) return fail("post inside");
      const char *glued_s = "GET/feed";
      muro__slice gs = muro__slice_of((const uint8_t *)glued_s, strlen(glued_s));
      base = allocs;
      muro__slice gm = method(gs);
      muro__slice gp = path(gs);
      if (allocs != base) return fail("alloc glued");
      if (gm.n != strlen(glued_s) || gm.p != gs.p) return fail("glued method");
      if (gp.n != 0 || gp.p != muro__slice_empty().p) return fail("glued path");
      const char *gap_s = "GET  HTTP/1.1\\r\\n";
      muro__slice as = muro__slice_of((const uint8_t *)gap_s, strlen(gap_s));
      base = allocs;
      muro__slice am = method(as);
      muro__slice ap = path(as);
      if (allocs != base) return fail("alloc gap");
      if (am.n != 3 || am.p != as.p) return fail("gap method");
      if (ap.n != 0 || ap.p != as.p + 4) return fail("gap path");
      if (ap.p == muro__slice_empty().p) return fail("gap static");
      if (allocs != 0) return fail("total");
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp bench do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>
    #include <stdint.h>
    #include <time.h>
    #define N #{@n}
    static size_t allocs;
    #define muro__ALLOC(n) (allocs++, malloc(n))
    #ifdef SLICE
    #include "fnv_slice.c"
    #else
    #include "fnv.c"
    #endif
    static double ms_since(clock_t t0) {
      return 1000.0 * (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
    }
    int main(void) {
    #ifdef SLICE
      static uint8_t buf[N];
      memset(buf, 97, N);
      muro__slice s = muro__slice_of(buf, N);
      size_t before = allocs;
      clock_t t0 = clock();
      uint32_t h = hash(s);
      printf("slice hash=%u walk_allocs=%zu pre_allocs=%zu ms=%.3f n=%d\\n",
             h, allocs - before, before, ms_since(t0), N);
      return allocs - before == 0 ? 0 : 1;
    #else
      clock_t tb = clock();
      ByteList *xs = nil();
      int i;
      for (i = 0; i < N; i++) xs = cons(97, xs);
      double build_ms = ms_since(tb);
      size_t built = allocs;
      clock_t t0 = clock();
      uint32_t h = fnv(xs);
      printf("cons hash=%u walk_allocs=%zu build_allocs=%zu build_ms=%.3f walk_ms=%.3f n=%d\\n",
             h, allocs - built, built, build_ms, ms_since(t0), N);
      return 0;
    #endif
    }
    """
  end

  defp zig_main do
    """
    const std = @import("std");
    const bytes = @import("bytes.zig");
    test "bytes" {
      var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
      defer arena.deinit();
      const ally = arena.allocator();
      const hello = try bytes.hello(ally);
      try std.testing.expectEqual(@as(usize, 5), hello.n);
      try std.testing.expectEqual(@as(u8, 104), hello.p[0]);
      const n = try bytes.nzuhello(ally);
      try std.testing.expectEqual(@as(u64, 5), n);
      const ff = try bytes.ff(ally);
      try std.testing.expectEqual(@as(usize, 1), ff.n);
      try std.testing.expectEqual(@as(u8, 255), ff.p[0]);
      const mid = try bytes.mid(ally);
      try std.testing.expectEqual(@as(usize, 3), mid.n);
      try std.testing.expectEqual(@as(u8, 101), mid.p[0]);
      const past = try bytes.past(ally);
      try std.testing.expectEqual(@as(usize, 0), past.n);
      const sum = try bytes.sum2(ally);
      try std.testing.expectEqual(@as(u64, 3), sum);
      const at = try bytes.at0(ally);
      try std.testing.expect(at != null);
      try std.testing.expectEqual(@as(u8, 97), at.?);
      const miss = try bytes.miss(ally);
      try std.testing.expect(miss == null);
    }
    """
  end

  defp js_main do
    """
    import * as B from "./bytes.mjs";
    import * as U from "./bytes-uncons.mjs";
    function fail(m) { console.error(m); process.exit(1); }
    if (B.n_hello() !== 5n) fail("len");
    if (B.n_accent() !== 2n) fail("accent");
    if (B.n_ff() !== 1n) fail("ff");
    if (B.ff()[0] !== 255) fail("ff byte");
    if (B.hello().length !== 5) fail("hello");
    const mid = B.mid();
    if (mid.length !== 3 || mid[0] !== 101) fail("mid");
    if (mid.buffer !== B.mid().buffer) {
      // each call builds its own literal; the view shares that call's buffer
    }
    const raw = new Uint8Array([104, 101, 108, 108, 111]);
    const view = raw.subarray(1, 4);
    if (view.buffer !== raw.buffer || view.byteOffset !== 1) fail("share");
    if (B.past().length !== 0) fail("past");
    if (B.at0().k !== "some" || B.at0().v !== 97n) fail("get");
    if (B.miss().k !== "none") fail("miss");
    if (B.sum2() !== 3n) fail("sum");
    if (B.muro__canon(B.ff()) !== 'b"\\\\xff"') fail("canon " + B.muro__canon(B.ff()));
    if (B.muro__canon(B.hello()) !== 'b"hello"') fail("canon hello");
    const one = U.one();
    if (one.tag !== "just" || one.fields[0][0] !== 97n) fail("uncons");
    if (U.muro__canon(one) !== 'just((97,b"b"))') fail("canon uncons " + U.muro__canon(one));
    console.log("OK");
    """
  end
end
