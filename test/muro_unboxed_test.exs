defmodule Muro.UnboxedTest do
  use ExUnit.Case, async: false

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

  test "an unboxed product checks, and a misuse is refused" do
    assert Muro.check_file("examples/unboxed.muro") == :ok
    assert Muro.check_file("examples/word_kind.muro") == :ok
    assert Muro.check_file("examples/request-line.muro") == :ok
    assert Muro.check_file("examples/fnv_slice.muro") == :ok
    assert Muro.check_file("examples/fnv.muro") == :ok
    assert check("def unboxed : run Nat := 0") == :ok
    assert check(erased_field()) == :ok
    assert check(opt_field()) == :ok

    assert {:error, msg} = check(nat_field())

    assert msg =~
             "unboxed field is not a machine word, WBool, Slice, Opt of those, or unboxed data"

    assert {:error, msg} = check(opt_of_unboxed())

    assert msg =~
             "unboxed field is not a machine word, WBool, Slice, Opt of those, or unboxed data"

    assert {:error, msg} = check(params())
    assert msg =~ "unboxed data has parameters"

    assert {:error, msg} = check(indexed())
    assert msg =~ "unboxed data is indexed"

    assert {:error, msg} = check(recursive())
    assert msg =~ "unboxed data is recursive"

    assert {:error, msg} = check(mutual())
    assert msg =~ "unboxed data is recursive"
  end

  test "C folds an unboxed product without allocating, and the boxed twin allocates once" do
    dir = tmp("c")
    File.cp!("examples/unboxed.muro", Path.join(dir, "unboxed.muro"))
    assert {:ok, [h, c]} = Muro.emit_c(Path.join(dir, "unboxed.muro"), nif: false)
    header = File.read!(h)
    source = File.read!(c)

    assert header =~ "typedef struct Acc Acc;"
    assert header =~ "Acc scan(muro__slice s);"
    assert header =~ "uint64_t muro__f_0;"
    assert header =~ "muro__slice muro__f_2;"
    refute header =~ "Acc *scan"

    acc = body(source, "static Acc acc(", "static Cell *cell(")
    step = body(source, "static Acc muro__step_0(", "Acc scan(")
    scan = body(source, "Acc scan(", "uint64_t nOf(")
    cell = body(source, "static Cell *cell(", "static Acc muro__step_0(")

    refute acc =~ "muro__ALLOC"
    refute step =~ "muro__ALLOC"
    refute scan =~ "muro__ALLOC"
    assert acc =~ "return (Acc){"
    assert cell =~ "muro__ALLOC"
    assert scan =~ "muro__s_2 = muro__step_0"

    File.write!(Path.join(dir, "main.c"), c_main())
    assert gcc!(dir, "main.c", "main") == :ok
    assert run!(dir, "main") == "OK\n"
  end

  test "C evaluates a nested word operation and a nullary word name" do
    dir = tmp("kind")
    File.cp!("examples/word_kind.muro", Path.join(dir, "word_kind.muro"))
    assert {:ok, [_h, _c]} = Muro.emit_c(Path.join(dir, "word_kind.muro"), nif: false)
    File.write!(Path.join(dir, "main.c"), kind_main())
    assert gcc!(dir, "main.c", "kind") == :ok
    assert run!(dir, "kind") == "OK\n"
  end

  test "a pair of unboxed data, and a stream of it, are c:unboxed" do
    dir = tmp("pair")
    path = Path.join(dir, "pair.muro")
    File.write!(path, pair_book())
    assert {:error, "c:unboxed"} = Muro.emit_c(path, nif: false)
    assert {:error, "c:unboxed"} = Muro.emit_rust(path)
    assert {:error, "c:unboxed"} = Muro.emit_zig(path)

    stream = Path.join(dir, "stream.muro")
    File.write!(stream, stream_book())
    assert Muro.check_file(stream) == :ok
    assert {:error, "c:unboxed"} = Muro.emit_c(stream, nif: false)
    assert {:error, "c:unboxed"} = Muro.emit_rust(stream)
    assert {:error, "c:unboxed"} = Muro.emit_zig(stream)
  end

  test "an unboxed field embeds by value, and Opt of a word stays by value" do
    dir = tmp("nest")
    path = Path.join(dir, "nest.muro")
    File.write!(path, nest_book())
    assert {:ok, [h, c]} = Muro.emit_c(path, nif: false)
    header = File.read!(h)
    source = File.read!(c)
    assert header =~ "typedef struct Inner Inner;"
    assert match?([_, _], String.split(header, "struct Inner {", parts: 2))
    [_, after_inner] = String.split(header, "struct Inner {", parts: 2)
    assert after_inner =~ "struct Outer {"
    assert header =~ "Inner muro__f_0;"
    refute header =~ "Inner *muro__f_0;"
    inner = body(source, "static Inner inner(", "static Outer outer(")
    outer = body(source, "static Outer outer(", "Outer wrap(")
    refute inner =~ "muro__ALLOC"
    refute outer =~ "muro__ALLOC"
    assert gcc_obj!(dir, c) == :ok

    opt = Path.join(dir, "opt.muro")
    File.write!(opt, opt_field())
    assert {:ok, [oh, _oc]} = Muro.emit_c(opt, nif: false)
    oheader = File.read!(oh)
    assert oheader =~ "struct muro__opt_u64 { uint8_t tag; uint64_t val; };"
    assert oheader =~ "muro__opt_u64 muro__f_0;"
    refute oheader =~ "muro__opt_u64 *muro__f_0;"
  end

  test "Rust folds an unboxed product without allocating, and the boxed twin allocates" do
    dir = tmp("rust")
    File.cp!("examples/unboxed.muro", Path.join(dir, "unboxed.muro"))
    assert {:ok, [rs]} = Muro.emit_rust(Path.join(dir, "unboxed.muro"))
    source = File.read!(rs)
    assert source =~ "#[derive(::std::clone::Clone, ::std::marker::Copy)]"
    assert source =~ "pub enum Acc"
    scan = rust_fn(source, "scan")
    refute scan =~ "Rc::new"
    assert source =~ "Rc::new(muro__node_Cell::cell"
    assert rustc_lib!(dir, "unboxed") == :ok

    File.write!(
      Path.join(dir, "unboxed_body.rs"),
      String.replace(source, "#![allow", "#[allow", global: false)
    )

    File.write!(Path.join(dir, "run.rs"), rust_main())
    assert rustc_bin!(dir, "run.rs", "run") == :ok
    assert run!(dir, "run") == "OK\n"
  end

  @tag skip: @zig_skip
  test "Zig folds an unboxed product without allocating" do
    dir = tmp("zig")
    File.cp!("examples/unboxed.muro", Path.join(dir, "unboxed.muro"))
    assert {:ok, [zig]} = Muro.emit_zig(Path.join(dir, "unboxed.muro"))
    source = File.read!(zig)
    scan = zig_fn(source, "scan")
    step = body(source, "fn muro__step_0(", "pub fn nOf(")
    refute scan =~ ".create"
    refute step =~ ".create"
    assert source =~ "muro__allocator.create(Cell)"
    File.write!(Path.join(dir, "check.zig"), zig_main())
    assert zig_test!(dir) == :ok
  end

  @tag skip: @node_skip
  test "JavaScript folds an unboxed product and the view shares the buffer" do
    dir = tmp("js")
    File.cp!("examples/unboxed.muro", Path.join(dir, "unboxed.muro"))
    assert {:ok, [mjs, _dts]} = Muro.emit_js(Path.join(dir, "unboxed.muro"))
    source = File.read!(mjs)
    assert source =~ "muro__btil"
    File.write!(Path.join(dir, "check.mjs"), js_main())
    {out, status} = System.cmd(@node, ["check.mjs"], cd: dir, stderr_to_stdout: true)
    assert status == 0, out
    assert String.trim(out) == "OK"
  end

  test "assembly refuses an unboxed product" do
    dir = tmp("asm")
    File.cp!("examples/unboxed.muro", Path.join(dir, "unboxed.muro"))

    assert_raise Mix.Error, ~r/\Aasm:scope\z/, fn ->
      Mix.Tasks.Muro.Emit.run([Path.join(dir, "unboxed.muro"), "--backend", "asm"])
    end
  end

  test "Elixir evaluates a nested word operation and a nullary word name" do
    assert {:ok, src} = Muro.emit_file("examples/word_kind.muro", Muro.WordKindEx)
    Code.compile_string(src)
    assert apply(Muro.WordKindEx, :nestedOne, []) == 1
    assert apply(Muro.WordKindEx, :masked, [255]) == 248

    assert {:ok, acc} = Muro.emit_file("examples/unboxed.muro", Muro.UnboxedEx)
    Code.compile_string(acc)
    assert apply(Muro.UnboxedEx, :scan, ["abcd"]) == {:acc, 4, 0, "abcd"}
    assert apply(Muro.UnboxedEx, :scan, ["ab\ncd"]) == {:acc, 5, 1, "ab"}
    assert apply(Muro.UnboxedEx, :nOf, [{:acc, 5, 1, "ab"}]) == 5
    assert apply(Muro.UnboxedEx, :marksOf, [{:acc, 5, 1, "ab"}]) == 1
    assert apply(Muro.UnboxedEx, :viewOf, [{:acc, 5, 1, "ab"}]) == "ab"
  end

  test "C emits Opt of boxed data, and the program exercises both arms" do
    dir = tmp("optcell")
    path = Path.join(dir, "cell.muro")
    File.write!(path, opt_cell())
    assert Muro.check_file(path) == :ok
    assert {:ok, [h, c]} = Muro.emit_c(path, nif: false)
    header = File.read!(h)
    source = File.read!(c)
    assert header =~ "typedef struct Cell Cell;"
    assert header =~ "struct muro__opt_d_Cell { uint8_t tag; Cell *val; };"
    assert header =~ "struct Cell {"
    opt_at = :binary.match(header, "struct muro__opt_d_Cell") |> elem(0)
    body_at = :binary.match(header, "struct Cell {") |> elem(0)
    assert opt_at < body_at
    assert source =~ "Cell *"
    File.write!(Path.join(dir, "main.c"), opt_cell_main())
    assert gcc!(dir, "main.c", "cell") == :ok
    assert run!(dir, "cell") == "OK\n"
  end

  test "C, Rust, and Zig refuse Opt of unboxed data" do
    dir = tmp("optw")
    path = Path.join(dir, "optw.muro")
    File.write!(path, opt_unboxed_run())
    assert Muro.check_file(path) == :ok
    assert {:error, "c:unboxed"} = Muro.emit_c(path, nif: false)
    assert {:error, "c:unboxed"} = Muro.emit_rust(path)
    assert {:error, "c:unboxed"} = Muro.emit_zig(path)
  end

  test "a nullary unboxed constructor does not allocate, and both arms run" do
    dir = tmp("flag")
    path = Path.join(dir, "flag.muro")
    File.write!(path, flag_book())
    assert Muro.check_file(path) == :ok
    assert {:ok, [_h, c]} = Muro.emit_c(path, nif: false)
    source = File.read!(c)
    go = body(source, "static Flag go(", "static Flag stop(")
    stop = body(source, "static Flag stop(", "uint64_t code(")
    refute go =~ "muro__ALLOC"
    refute stop =~ "muro__ALLOC"
    File.write!(Path.join(dir, "main.c"), flag_main())
    assert gcc!(dir, "main.c", "flag") == :ok
    assert run!(dir, "flag") == "OK\n"

    assert {:ok, [rs]} = Muro.emit_rust(path)
    rust = File.read!(rs)
    rgo = body(rust, "fn go(", "fn stop(")
    rstop = body(rust, "fn stop(", "pub fn code(")
    refute rgo =~ "Rc::new"
    refute rstop =~ "Rc::new"
    assert rustc_lib!(dir, "flag") == :ok

    if @zig do
      assert {:ok, [zig]} = Muro.emit_zig(path)
      zsrc = File.read!(zig)
      zgo = body(zsrc, "fn go(", "fn stop(")
      zstop = body(zsrc, "fn stop(", "pub fn code(")
      refute zgo =~ "create"
      refute zstop =~ "create"
      File.write!(Path.join(dir, "check.zig"), flag_zig())
      assert zig_test!(dir) == :ok
    end
  end

  test "Elixir reads a word kind through a match, and C runs the same book" do
    dir = tmp("mkind")
    path = Path.join(dir, "match_kind.muro")
    File.write!(path, match_kind())
    assert Muro.check_file(path) == :ok
    assert {:ok, src} = Muro.emit_file(path, Muro.MatchKindEx)
    Code.compile_string(src)
    assert apply(Muro.MatchKindEx, :yes, []) == Muro.Word.bnot(:u64, 1)
    assert apply(Muro.MatchKindEx, :no, []) == Muro.Word.bnot(:u64, 0)
    assert apply(Muro.MatchKindEx, :four, []) == 4
    assert apply(Muro.MatchKindEx, :five, []) == 5
    assert apply(Muro.MatchKindEx, :flagGo, []) == Muro.Word.bnot(:u64, 1)
    assert apply(Muro.MatchKindEx, :flagStop, []) == Muro.Word.bnot(:u64, 0)
    assert apply(Muro.MatchKindEx, :fromSome, []) == Muro.Word.bnot(:u64, 3)
    assert apply(Muro.MatchKindEx, :fromNone, []) == Muro.Word.bnot(:u64, 0)

    assert {:ok, [_h, _c]} = Muro.emit_c(path, nif: false)
    File.write!(Path.join(dir, "main.c"), match_kind_main())
    assert gcc!(dir, "main.c", "mkind") == :ok
    assert run!(dir, "mkind") == "OK\n"
    assert {:ok, [_rs]} = Muro.emit_rust(path)
    assert rustc_lib!(dir, "match_kind") == :ok
  end

  defp nat_field do
    """
    unboxed data Bad : Type where
      bad : Π (n : Nat) → Bad
    """
  end

  defp opt_of_unboxed do
    """
    unboxed data Inner : Type where
      inner : Π (n : U64) → Inner

    unboxed data Bad : Type where
      bad : Π (o : Opt Inner) → Bad
    """
  end

  defp params do
    """
    unboxed data Bad (A : Type) : Type where
      bad : Π (a : A) → Bad A
    """
  end

  defp indexed do
    """
    unboxed data Bad : Nat → Type where
      bad : Π (n : Nat) → Bad n
    """
  end

  defp recursive do
    """
    unboxed data Bad : Type where
      bad : Π (x : Bad) → Bad
    """
  end

  defp mutual do
    """
    unboxed data A : Type where
      a : Π (b : B) → A

    unboxed data B : Type where
      b : Π (a : A) → B
    """
  end

  defp erased_field do
    """
    unboxed data E : Type where
      e : Π (- n : Nat) → Π (+ k : U64) → E

    def make : run Π (k : U64) → E :=
      λ (k : U64) → e 0 k
    """
  end

  defp opt_field do
    """
    unboxed data Hold : Type where
      hold : Π (+ o : Opt U64) → Π (+ b : WBool) → Π (+ s : Slice) → Hold

    def holdOf : run Π (n : U64) → Hold :=
      λ (n : U64) → hold (wsome n) wtrue b""
    """
  end

  defp pair_book do
    """
    unboxed data W : Type where
      w : Π (+ n : U64) → W

    def both : run Π (+ n : U64) → (W × U64) :=
      λ (+ n : U64) → (w n, n)
    """
  end

  defp stream_book do
    """
    unboxed data W : Type where
      w : Π (+ n : U64) → W

    def seed : run W := w (toU64 0)

    def zs : run Stream W :=
      unfold seed (λ (+ s : W) → (s, s))
    """
  end

  defp nest_book do
    """
    unboxed data Inner : Type where
      inner : Π (+ n : U64) → Inner

    unboxed data Outer : Type where
      outer : Π (+ i : Inner) → Π (+ n : U64) → Outer

    def wrap : run Π (+ n : U64) → Outer :=
      λ (+ n : U64) → outer (inner n) n
    """
  end

  defp check(src) do
    path = Path.join(System.tmp_dir!(), "muro_ub_#{System.unique_integer([:positive])}.muro")
    File.write!(path, src)
    on_exit(fn -> File.rm(path) end)
    Muro.check_file(path)
  end

  defp body(source, start, stop) do
    [_, rest] = String.split(source, start, parts: 2)
    [text, _] = String.split(rest, stop, parts: 2)
    text
  end

  defp rust_fn(source, name) do
    [_, rest] = String.split(source, "pub fn #{name}(", parts: 2)
    [text, _] = String.split(rest, "\npub fn ", parts: 2)
    text
  end

  defp zig_fn(source, name) do
    [_, rest] = String.split(source, "pub fn #{name}(", parts: 2)
    [text, _] = String.split(rest, "\npub fn ", parts: 2)
    text
  end

  defp tmp(tag) do
    dir = Path.join(System.tmp_dir!(), "muro_ub_#{tag}_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp gcc!(dir, src, bin) do
    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11) ++ [src, "-o", bin],
        cd: dir,
        stderr_to_stdout: true
      )

    if status == 0, do: :ok, else: {status, out}
  end

  defp gcc_obj!(dir, src) do
    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11 -c) ++ [src],
        cd: dir,
        stderr_to_stdout: true
      )

    if status == 0, do: :ok, else: {status, out}
  end

  defp rustc_bin do
    path =
      System.find_executable("rustc") ||
        Path.join(System.user_home!(), ".cargo/bin/rustc")

    assert File.regular?(path), "rustc not found"
    path
  end

  defp rustc_lib!(dir, name) do
    {out, status} =
      System.cmd(
        rustc_bin(),
        ~w(--edition 2021 --crate-type lib --crate-name) ++
          [name, "#{name}.rs", "-o", "lib#{name}.rlib"],
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
      System.cmd(rustc_bin(), ~w(--edition 2021) ++ [src, "-o", bin],
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
    {out, status} = System.cmd(@zig, ["test", "check.zig"], cd: dir, stderr_to_stdout: true)
    if status == 0, do: :ok, else: {status, out}
  end

  defp run!(dir, bin) do
    {out, status} = System.cmd(Path.join(dir, bin), [], cd: dir, stderr_to_stdout: true)
    if status == 0, do: out, else: flunk(out)
  end

  defp c_main do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>
    #include <stdint.h>
    #include <stddef.h>
    static size_t allocs;
    #define muro__ALLOC(n) (allocs++, malloc(n))
    #include "unboxed.c"
    static int fail(const char *m) { fprintf(stderr, "%s\\n", m); return 1; }
    int main(void) {
      const char *plain = "abcd";
      const char *nl = "ab\\ncd";
      muro__slice p = muro__slice_of((const uint8_t *)plain, 4);
      muro__slice s = muro__slice_of((const uint8_t *)nl, 5);
      size_t base = allocs;
      Acc a = scan(p);
      if (allocs != base) return fail("plain alloc");
      if (nOf(a) != 4 || marksOf(a) != 0) return fail("plain");
      muro__slice v = viewOf(a);
      if (v.p != (const uint8_t *)plain || v.n != 4) return fail("plain view");
      Acc b = scan(s);
      if (allocs != base) return fail("nl alloc");
      if (nOf(b) != 5 || marksOf(b) != 1) return fail("nl");
      muro__slice w = viewOf(b);
      if (w.p != (const uint8_t *)nl || w.n != 2 || w.p[0] != 'a' || w.p[1] != 'b') return fail("nl view");
      base = allocs;
      Cell *c = bump(3);
      if (allocs != base + 1) return fail("counter");
      if (c->muro__as.cell.muro__f_0 != 3) return fail("cell");
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp kind_main do
    """
    #include <stdio.h>
    #include "word_kind.c"
    int main(void) {
      if (nestedOne() != 1) return 1;
      if (masked(255) != 248) return 2;
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp rust_main do
    """
    #![allow(dead_code, unused_variables, non_snake_case, non_camel_case_types, unused_parens)]
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicUsize, Ordering};
    static HITS: AtomicUsize = AtomicUsize::new(0);
    struct Cnt;
    unsafe impl GlobalAlloc for Cnt {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            HITS.fetch_add(1, Ordering::SeqCst);
            System.alloc(layout)
        }
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            System.dealloc(ptr, layout)
        }
    }
    #[global_allocator]
    static G: Cnt = Cnt;
    include!("unboxed_body.rs");
    fn main() {
        let plain = b"abcd";
        let nl = b"ab\\ncd";
        let p = muro__slice { p: plain.as_ptr(), n: 4 };
        let s = muro__slice { p: nl.as_ptr(), n: 5 };
        let before = HITS.load(Ordering::SeqCst);
        let a = scan(p);
        let b = scan(s);
        assert_eq!(HITS.load(Ordering::SeqCst), before);
        assert_eq!(nOf(a), 4);
        assert_eq!(marksOf(a), 0);
        let v = viewOf(a);
        assert_eq!(v.p, plain.as_ptr());
        assert_eq!(v.n, 4);
        assert_eq!(nOf(b), 5);
        assert_eq!(marksOf(b), 1);
        let w = viewOf(b);
        assert_eq!(w.p, nl.as_ptr());
        assert_eq!(w.n, 2);
        let mid = HITS.load(Ordering::SeqCst);
        let c = bump(3);
        assert!(HITS.load(Ordering::SeqCst) > mid);
        match ((*c.0).clone()) {
            muro__node_Cell::cell(n) => assert_eq!(n, 3),
        }
        println!("OK");
    }
    """
  end

  defp zig_main do
    """
    const std = @import("std");
    const u = @import("unboxed.zig");
    test "scan allocates nothing" {
        const ally = std.testing.failing_allocator;
        const plain = "abcd";
        const nl = "ab\\ncd";
        const p: u.muro__slice = .{ .p = plain.ptr, .n = 4 };
        const s: u.muro__slice = .{ .p = nl.ptr, .n = 5 };
        const a = try u.scan(ally, p);
        try std.testing.expectEqual(@as(u64, 4), try u.nOf(ally, a));
        try std.testing.expectEqual(@as(u64, 0), try u.marksOf(ally, a));
        const v = try u.viewOf(ally, a);
        try std.testing.expect(v.p == plain.ptr);
        try std.testing.expectEqual(@as(usize, 4), v.n);
        const b = try u.scan(ally, s);
        try std.testing.expectEqual(@as(u64, 5), try u.nOf(ally, b));
        try std.testing.expectEqual(@as(u64, 1), try u.marksOf(ally, b));
        const w = try u.viewOf(ally, b);
        try std.testing.expect(w.p == nl.ptr);
        try std.testing.expectEqual(@as(usize, 2), w.n);
    }
    """
  end

  defp opt_cell do
    """
    data Cell : Type where
      cell : Π (n : U64) → Cell

    def miss : run Opt Cell := wnone

    def take : run Π (o : Opt Cell) → U64 :=
      λ (o : Opt Cell) →
        match o motive (λ _ → U64)
          | wsome c => (match c motive (λ _ → U64) | cell n => n)
          | wnone => toU64 0
    """
  end

  defp opt_cell_main do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #define muro__ALLOC(n) malloc(n)
    #include "cell.c"
    int main(void) {
      muro__opt_d_Cell none = miss();
      if (none.tag != 0) return 1;
      if (take(none) != 0) return 2;
      Cell cell = {0};
      cell.muro__field_tag = 0;
      cell.muro__as.cell.muro__f_0 = 7;
      muro__opt_d_Cell some;
      some.tag = 1;
      some.val = &cell;
      if (take(some) != 7) return 3;
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp opt_unboxed_run do
    """
    unboxed data W : Type where
      w : Π (n : U64) → W

    def o : run Opt W := wnone
    """
  end

  defp flag_book do
    """
    unboxed data Flag : Type where
      go : Flag
      stop : Flag

    def code : run Π (f : Flag) → U64 :=
      λ (f : Flag) →
        match f motive (λ _ → U64)
          | go => toU64 1
          | stop => toU64 2

    def on : run U64 := code go
    def off : run U64 := code stop
    """
  end

  defp flag_main do
    """
    #include <stdio.h>
    #include <stdlib.h>
    #define muro__ALLOC(n) malloc(n)
    #include "flag.c"
    int main(void) {
      if (on() != 1) return 1;
      if (off() != 2) return 2;
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp flag_zig do
    """
    const std = @import("std");
    const f = @import("flag.zig");
    test "both arms" {
        const ally = std.testing.failing_allocator;
        try std.testing.expectEqual(@as(u64, 1), try f.on(ally));
        try std.testing.expectEqual(@as(u64, 2), try f.off(ally));
    }
    """
  end

  defp match_kind do
    """
    def bits : run Π (b : WBool) → U64 :=
      λ (b : WBool) →
        noti (match b motive (λ _ → U64)
          | wtrue => toU64 1
          | wfalse => toU64 0)

    def both : run Π (b : WBool) → U64 :=
      λ (b : WBool) →
        addi (match b motive (λ _ → U64)
          | wtrue => toU64 1
          | wfalse => toU64 2) (toU64 3)

    def yes : run U64 := bits wtrue
    def no : run U64 := bits wfalse
    def four : run U64 := both wtrue
    def five : run U64 := both wfalse

    data Flag : Type where
      go : Flag
      stop : Flag

    def ofFlag : run Π (f : Flag) → U64 :=
      λ (f : Flag) →
        noti (match f motive (λ _ → U64)
          | go => toU64 1
          | stop => toU64 0)

    def flagGo : run U64 := ofFlag go
    def flagStop : run U64 := ofFlag stop

    def fromOpt : run Π (o : Opt U64) → U64 :=
      λ (o : Opt U64) →
        noti (match o motive (λ _ → U64)
          | wsome n => n
          | wnone => toU64 0)

    def fromSome : run U64 := fromOpt (wsome (toU64 3))
    def fromNone : run U64 := fromOpt wnone
    """
  end

  defp match_kind_main do
    not1 = Muro.Word.bnot(:u64, 1)
    not0 = Muro.Word.bnot(:u64, 0)
    not3 = Muro.Word.bnot(:u64, 3)

    """
    #include <stdio.h>
    #include <stdlib.h>
    #include <stdint.h>
    #define muro__ALLOC(n) malloc(n)
    #include "match_kind.c"
    int main(void) {
      if (yes() != #{not1}ull) return 1;
      if (no() != #{not0}ull) return 2;
      if (four() != 4) return 3;
      if (five() != 5) return 4;
      if (flagGo() != #{not1}ull) return 5;
      if (flagStop() != #{not0}ull) return 6;
      if (fromSome() != #{not3}ull) return 7;
      if (fromNone() != #{not0}ull) return 8;
      printf("OK\\n");
      return 0;
    }
    """
  end

  defp js_main do
    """
    import { scan, nOf, marksOf, viewOf } from "./unboxed.mjs";
    const plain = new Uint8Array([97, 98, 99, 100]);
    const nl = new Uint8Array([97, 98, 10, 99, 100]);
    const a = scan(plain);
    const b = scan(nl);
    if (nOf(a) !== 4n || marksOf(a) !== 0n) throw new Error("plain");
    const va = viewOf(a);
    if (va !== plain || va.length !== 4) throw new Error("plain view");
    if (nOf(b) !== 5n || marksOf(b) !== 1n) throw new Error("nl");
    const vb = viewOf(b);
    if (vb.buffer !== nl.buffer || vb.length !== 2 || vb[0] !== 97 || vb[1] !== 98) throw new Error("nl view");
    console.log("OK");
    """
  end
end
