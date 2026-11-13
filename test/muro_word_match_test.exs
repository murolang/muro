defmodule Muro.WordMatchTest do
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

  test "match on WBool and Opt checks, and a missing or misspelled arm is refused" do
    assert Muro.check_file("examples/word_match.muro") == :ok
    assert Muro.check_file("examples/request-line.muro") == :ok
    assert Muro.check_file("examples/fnv_slice.muro") == :ok
    assert Muro.check_file("examples/fnv.muro") == :ok
    assert Muro.check_file("examples/string.muro") == :ok

    assert {:error, msg} = check(miss_bool())
    assert msg =~ "missing branch for wfalse"

    assert {:error, msg} = check(miss_opt())
    assert msg =~ "missing branch for wnone"

    assert {:error, msg} = check(misspelled())
    assert msg =~ "expected constructor wfalse, got wfals"

    assert {:error, msg} = check(not_word())
    assert msg =~ "expected data type, got WBool"

    assert {:error, msg} = check(bad_motive())
    assert msg =~ "cannot convert Nat"

    assert {:error, msg} = check(bad_arm())
    assert msg =~ "cannot convert U64"
  end

  test "C matches WBool and Opt without allocating, and a Slice arm stays in the buffer" do
    dir = tmp("c")
    File.cp!("examples/word_match.muro", Path.join(dir, "word_match.muro"))
    assert {:ok, [h, c]} = Muro.emit_c(Path.join(dir, "word_match.muro"), nif: false)
    header = File.read!(h)
    source = File.read!(c)

    assert header =~ "struct muro__opt_u8 { uint8_t tag; uint8_t val; };"
    assert header =~ "struct muro__opt_u64 { uint8_t tag; uint64_t val; };"
    assert source =~ "{ .muro__field_tag = 0, .muro__as = { .muro__unused = 0 } }"
    assert source =~ "__attribute__((unused)) static Status *unusedCtor(void)"
    assert source =~ "(void)zu;"

    pick = body(source, "uint64_t pickWord", "uint64_t eqByte")
    eqb = body(source, "uint64_t eqByte", "uint8_t headByte")
    head = body(source, "uint8_t headByte", "uint64_t eqBytes")
    eq = body(source, "uint64_t eqBytes", "muro__slice eqView")
    view = body(source, "muro__slice eqView", "uint64_t nested")
    drop = body(source, "muro__slice dropCR", "muro__slice pickBytes")
    bytes = body(source, "muro__slice pickBytes", "muro__nat *oneField")
    one = body(source, "muro__nat *oneField", "muro__nat *ignore")

    for part <- [pick, eqb, head, eq, view, drop, bytes] do
      refute part =~ "muro__suc", part
      refute part =~ "muro__zero", part
      refute part =~ "muro__ALLOC", part
    end

    assert pick =~ "if (muro__s_0)"
    assert head =~ "muro__opt_u8"
    assert head =~ ".tag"
    assert head =~ ".val"
    assert view =~ "muro__slice muro__t_0 = {0};"
    assert drop =~ "muro__slice muro__t_0 = {0};"
    assert drop =~ "muro__slice_sub"
    refute one =~ "muro__f_1"

    File.write!(Path.join(dir, "main.c"), c_main())
    assert gcc!(dir, "main.c", "main") == :ok
    assert run!(dir, "main") == "OK\n"
  end

  test "a match on divi declares Opt U64 even when the function returns a word" do
    dir = tmp("div")
    path = Path.join(dir, "quot.muro")

    File.write!(path, """
    def quot : run Π (n : U64) → U64 :=
      λ (n : U64) →
        match (divi n (toU64 2)) motive (λ _ → U64)
          | wsome q => q
          | wnone => toU64 0
    """)

    assert {:ok, [h, _c]} = Muro.emit_c(path, nif: false)
    assert File.read!(h) =~ "struct muro__opt_u64 { uint8_t tag; uint64_t val; };"

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include <stdlib.h>
    #define muro__ALLOC(n) malloc(n)
    #include "quot.c"
    int main(void) {
      if (quot(8) != 4) return 1;
      if (quot(0) != 0) return 1;
      printf("OK\\n");
      return 0;
    }
    """)

    assert gcc!(dir, "main.c", "main") == :ok
    assert run!(dir, "main") == "OK\n"
  end

  test "Elixir matches WBool and Opt, and a Slice arm is the view" do
    dir = tmp("ex")
    File.cp!("examples/word_match.muro", Path.join(dir, "word_match.muro"))
    assert {:ok, src} = Muro.emit_file(Path.join(dir, "word_match.muro"), WordMatch)
    assert src =~ "true ->"
    assert src =~ "false ->"
    assert src =~ "{:some, x1} -> x1"
    assert src =~ ":none ->"

    on_exit(fn ->
      :code.delete(WordMatch)
      :code.purge(WordMatch)
    end)

    [{WordMatch, _bin}] = Code.compile_string(src)
    call = fn fun, args -> apply(WordMatch, fun, args) end
    assert call.(:pick, [true]) == 0
    assert call.(:pick, [false]) == {:suc, 0}
    assert call.(:pickWord, [true]) == 0
    assert call.(:pickWord, [false]) == 1
    assert call.(:eqByte, [97, 97]) == 1
    assert call.(:eqByte, [97, 98]) == 0
    assert call.(:headByte, ["ab"]) == 97
    assert call.(:headByte, [""]) == 0
    assert call.(:eqBytes, ["a", "a"]) == 1
    assert call.(:eqBytes, ["a", "b"]) == 0
    assert call.(:eqView, ["a"]) == "a"
    assert call.(:eqView, ["b"]) == ""
    assert call.(:unwrap, [{:some, 19}]) == 19
    assert call.(:unwrap, [:none]) == 0
    assert call.(:nested, [true, {:some, 19}]) == 19
    assert call.(:nested, [false, {:some, 19}]) == 0
    assert call.(:nested2, [{:some, true}]) == 1
    assert call.(:nested2, [{:some, false}]) == 0
    assert call.(:nested2, [:none]) == 0
    assert call.(:dropCR, ["ab", :kept]) == "b"
    assert call.(:dropCR, ["ab", :empty]) == "ab"
    assert call.(:pickBytes, [true]) == "a"
    assert call.(:pickBytes, [false]) == "b"
    assert call.(:oneField, [{:rec, 3, 4}]) == 3
    assert call.(:ignore, [0]) == 0
    assert call.(:seeOk, [:ok]) == 0
    assert call.(:seeOk, [:bad]) == {:suc, 0}
  end

  test "Rust matches WBool and Opt without allocating, and a Slice arm stays in the buffer" do
    dir = tmp("rust")
    File.cp!("examples/word_match.muro", Path.join(dir, "word_match.muro"))
    assert {:ok, [rs]} = Muro.emit_rust(Path.join(dir, "word_match.muro"))
    source = File.read!(rs)
    assert source =~ "pub fn pickWord(b: bool) -> u64"
    assert source =~ "::std::option::Option::Some(n)"
    assert source =~ "::std::option::Option::None"

    for name <- ["pickWord", "eqByte", "headByte", "eqBytes", "eqView", "nested", "nested2"] do
      part = rust_fn(source, name)
      refute part =~ "Rc::new", part
      refute part =~ "muro__suc", part
      refute part =~ "muro__zero", part
    end

    drop = rust_fn(source, "dropCR")
    assert drop =~ "muro__slice_sub"
    refute drop =~ "Rc::new"

    assert rustc_lib!(dir, "word_match") == :ok

    File.write!(
      Path.join(dir, "word_body.rs"),
      String.replace(source, "#![allow", "#[allow", global: false)
    )

    File.write!(Path.join(dir, "run.rs"), rust_main())
    assert rustc_bin!(dir, "run.rs", "run") == :ok
    assert run!(dir, "run") == "OK\n"
  end

  @tag skip: @zig_skip
  test "Zig matches WBool and Opt without allocating, and a Slice arm stays in the buffer" do
    dir = tmp("zig")
    File.cp!("examples/word_match.muro", Path.join(dir, "word_match.muro"))
    assert {:ok, [zig]} = Muro.emit_zig(Path.join(dir, "word_match.muro"))
    source = File.read!(zig)

    for name <- ["pickWord", "eqByte", "headByte", "eqBytes", "eqView", "dropCR", "pickBytes"] do
      part = zig_fn(source, name)
      refute part =~ "muro__suc", part
      refute part =~ ".create", part
    end

    assert source =~ "if ((b) == 0)"
    assert source =~ "if (muro__s) |n|"
    File.write!(Path.join(dir, "check.zig"), zig_main())
    assert zig_test!(dir) == :ok
  end

  @tag skip: @node_skip
  test "JavaScript matches WBool and Opt, and a Slice arm shares the buffer" do
    dir = tmp("js")
    File.cp!("examples/word_match.muro", Path.join(dir, "word_match.muro"))
    assert {:ok, [mjs, _dts]} = Muro.emit_js(Path.join(dir, "word_match.muro"))
    source = File.read!(mjs)
    assert source =~ "muro__scrut.k === \"some\""
    assert source =~ "s.subarray"
    File.write!(Path.join(dir, "check.mjs"), js_main())
    {out, status} = System.cmd(@node, ["check.mjs"], cd: dir, stderr_to_stdout: true)
    assert status == 0, out
    assert String.trim(out) == "OK"
  end

  test "assembly refuses a match on WBool" do
    dir = tmp("asm")
    File.cp!("examples/word_match.muro", Path.join(dir, "word_match.muro"))

    assert_raise Mix.Error, ~r/\Aasm:scope\z/, fn ->
      Mix.Tasks.Muro.Emit.run([Path.join(dir, "word_match.muro"), "--backend", "asm"])
    end
  end

  defp miss_bool do
    """
    def pick : run Π (b : WBool) → Nat :=
      λ (b : WBool) → match b motive (λ _ → Nat) | wtrue => 0
    """
  end

  defp miss_opt do
    """
    def unwrap : run Π (o : Opt U64) → U64 :=
      λ (o : Opt U64) → match o motive (λ _ → U64) | wsome n => n
    """
  end

  defp misspelled do
    """
    def pick : run Π (b : WBool) → Nat :=
      λ (b : WBool) → match b motive (λ _ → Nat) | wtrue => 0 | wfals => 0
    """
  end

  defp not_word do
    """
    def pick : run Π (b : WBool) → Nat :=
      λ (b : WBool) → match b motive (λ _ → Nat) | foo => 0
    """
  end

  defp bad_motive do
    """
    def pick : run Π (b : WBool) → U64 :=
      λ (b : WBool) → match b motive (λ _ → Nat) | wtrue => 0 | wfalse => 0
    """
  end

  defp bad_arm do
    """
    def pick : run Π (b : WBool) → Nat :=
      λ (b : WBool) → match b motive (λ _ → Nat) | wtrue => toU64 0 | wfalse => 0
    """
  end

  defp check(src) do
    path = Path.join(System.tmp_dir!(), "muro_wm_#{System.unique_integer([:positive])}.muro")
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
    dir = Path.join(System.tmp_dir!(), "muro_wm_#{tag}_#{System.unique_integer([:positive])}")
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
    #include "word_match.c"
    static int fail(const char *m) { fprintf(stderr, "%s\\n", m); return 1; }
    int main(void) {
      const char *buf = "ab";
      muro__slice s = muro__slice_of((const uint8_t *)buf, 2);
      size_t base = allocs;
      if (pickWord(1) != 0 || pickWord(0) != 1) return fail("pick");
      if (eqByte(97, 97) != 1 || eqByte(97, 98) != 0) return fail("eq");
      if (headByte(s) != 97) return fail("head");
      muro__slice none_s = muro__slice_of(0, 0);
      if (headByte(none_s) != 0) return fail("head miss");
      muro__slice a = muro__slice_of((const uint8_t *)"a", 1);
      muro__slice b = muro__slice_of((const uint8_t *)"b", 1);
      if (eqBytes(a, a) != 1 || eqBytes(a, b) != 0) return fail("bytes");
      muro__slice hit = eqView(a);
      if (hit.p != a.p || hit.n != 1) return fail("view");
      if (eqView(b).n != 0) return fail("view miss");
      muro__opt_u64 some; some.tag = 1; some.val = 19;
      muro__opt_u64 none; none.tag = 0; none.val = 0;
      if (unwrap(some) != 19 || unwrap(none) != 0) return fail("unwrap");
      if (nested(1, some) != 19 || nested(0, some) != 0) return fail("nested");
      muro__opt_bool bt; bt.tag = 1; bt.val = 1;
      muro__opt_bool bf; bf.tag = 1; bf.val = 0;
      muro__opt_bool bn; bn.tag = 0; bn.val = 0;
      if (nested2(bt) != 1 || nested2(bf) != 0 || nested2(bn) != 0) return fail("nested2");
      Flag *k = kept();
      muro__slice d = dropCR(s, k);
      if (d.n != 1 || d.p != s.p + 1 || d.p[0] != 'b') return fail("drop");
      muro__slice whole = dropCR(s, empty());
      if (whole.p != s.p || whole.n != 2) return fail("empty");
      muro__slice pb = pickBytes(0);
      if (pb.n != 1 || pb.p[0] != 'b') return fail("pickBytes");
      if (allocs != base) return fail("alloc");
      base = allocs;
      (void)pick(0);
      if (allocs == base) return fail("counter");
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
    include!("word_body.rs");
    fn quiet<T>(f: impl FnOnce() -> T) -> T {
        let before = HITS.load(Ordering::SeqCst);
        let v = f();
        assert_eq!(HITS.load(Ordering::SeqCst), before);
        v
    }
    fn main() {
        assert_eq!(quiet(|| pickWord(true)), 0);
        assert_eq!(quiet(|| pickWord(false)), 1);
        assert_eq!(quiet(|| eqByte(97, 97)), 1);
        assert_eq!(quiet(|| eqByte(97, 98)), 0);
        let raw = b"ab";
        let s = muro__slice { p: raw.as_ptr(), n: 2 };
        assert_eq!(quiet(|| headByte(s)), 97);
        let a = muro__slice { p: b"a".as_ptr(), n: 1 };
        let b = muro__slice { p: b"b".as_ptr(), n: 1 };
        assert_eq!(quiet(|| eqBytes(a, a)), 1);
        assert_eq!(quiet(|| eqBytes(a, b)), 0);
        let hit = quiet(|| eqView(a));
        assert_eq!(hit.p, a.p);
        assert_eq!(hit.n, 1);
        assert_eq!(quiet(|| eqView(b)).n, 0);
        assert_eq!(quiet(|| unwrap(Some(19))), 19);
        assert_eq!(quiet(|| unwrap(None)), 0);
        assert_eq!(quiet(|| nested(true, Some(19))), 19);
        assert_eq!(quiet(|| nested(false, Some(19))), 0);
        assert_eq!(quiet(|| nested2(Some(true))), 1);
        assert_eq!(quiet(|| nested2(Some(false))), 0);
        assert_eq!(quiet(|| nested2(None)), 0);
        let before = HITS.load(Ordering::SeqCst);
        let flag = kept();
        assert!(HITS.load(Ordering::SeqCst) > before);
        let mid = HITS.load(Ordering::SeqCst);
        let dropped = dropCR(s, flag);
        assert_eq!(HITS.load(Ordering::SeqCst), mid);
        assert_eq!(dropped.n, 1);
        assert_eq!(dropped.p, unsafe { s.p.add(1) });
        assert_eq!(unsafe { *dropped.p }, b'b');
        let whole = dropCR(s, empty());
        assert_eq!(whole.p, s.p);
        assert_eq!(whole.n, 2);
        let pb = quiet(|| pickBytes(false));
        assert_eq!(pb.n, 1);
        assert_eq!(unsafe { *pb.p }, b'b');
        println!("OK");
    }
    """
  end

  defp zig_main do
    """
    const std = @import("std");
    const wm = @import("word_match.zig");
    test "word match allocates nothing" {
        const ally = std.testing.failing_allocator;
        try std.testing.expectEqual(@as(u64, 0), try wm.pickWord(ally, 1));
        try std.testing.expectEqual(@as(u64, 1), try wm.pickWord(ally, 0));
        try std.testing.expectEqual(@as(u64, 1), try wm.eqByte(ally, 97, 97));
        try std.testing.expectEqual(@as(u64, 0), try wm.eqByte(ally, 97, 98));
        const raw = "ab";
        const s = wm.muro__slice_of(raw, 2);
        try std.testing.expectEqual(@as(u8, 97), try wm.headByte(ally, s));
        try std.testing.expectEqual(@as(u8, 0), try wm.headByte(ally, wm.muro__slice_of(raw, 0)));
        const a = wm.muro__slice_of("a", 1);
        const b = wm.muro__slice_of("b", 1);
        try std.testing.expectEqual(@as(u64, 1), try wm.eqBytes(ally, a, a));
        try std.testing.expectEqual(@as(u64, 0), try wm.eqBytes(ally, a, b));
        const hit = try wm.eqView(ally, a);
        try std.testing.expect(hit.p == a.p and hit.n == 1);
        try std.testing.expectEqual(@as(usize, 0), (try wm.eqView(ally, b)).n);
        try std.testing.expectEqual(@as(u64, 19), try wm.unwrap(ally, 19));
        try std.testing.expectEqual(@as(u64, 0), try wm.unwrap(ally, null));
        try std.testing.expectEqual(@as(u64, 19), try wm.nested(ally, 1, 19));
        try std.testing.expectEqual(@as(u64, 0), try wm.nested(ally, 0, 19));
        try std.testing.expectEqual(@as(u64, 1), try wm.nested2(ally, @as(u8, 1)));
        try std.testing.expectEqual(@as(u64, 0), try wm.nested2(ally, @as(u8, 0)));
        try std.testing.expectEqual(@as(u64, 0), try wm.nested2(ally, null));
        const kept: wm.Flag = .kept;
        const dropped = try wm.dropCR(ally, s, &kept);
        try std.testing.expect(dropped.p == s.p + 1 and dropped.n == 1 and dropped.p[0] == 'b');
        const flag_empty: wm.Flag = .empty;
        const whole = try wm.dropCR(ally, s, &flag_empty);
        try std.testing.expect(whole.p == s.p and whole.n == 2);
        const pb = try wm.pickBytes(ally, 0);
        try std.testing.expect(pb.n == 1 and pb.p[0] == 'b');
    }
    """
  end

  defp js_main do
    """
    import * as W from "./word_match.mjs";
    function fail(m) { console.error(m); process.exit(1); }
    if (W.pickWord(true) !== 0n) fail("pick true");
    if (W.pickWord(false) !== 1n) fail("pick false");
    if (W.eqByte(97n, 97n) !== 1n) fail("eq");
    if (W.eqByte(97n, 98n) !== 0n) fail("neq");
    const raw = new Uint8Array([97, 98]);
    if (W.headByte(raw) !== 97n) fail("head");
    if (W.headByte(new Uint8Array(0)) !== 0n) fail("head miss");
    const a = new Uint8Array([97]);
    const b = new Uint8Array([98]);
    if (W.eqBytes(a, a) !== 1n || W.eqBytes(a, b) !== 0n) fail("bytes");
    const hit = W.eqView(a);
    if (hit.buffer !== a.buffer || hit.byteOffset !== a.byteOffset || hit.length !== 1) fail("view");
    if (W.eqView(b).length !== 0) fail("view miss");
    if (W.unwrap({ k: "some", v: 19n }) !== 19n) fail("some");
    if (W.unwrap({ k: "none" }) !== 0n) fail("none");
    if (W.nested(true, { k: "some", v: 19n }) !== 19n) fail("nested");
    if (W.nested(false, { k: "some", v: 19n }) !== 0n) fail("nested f");
    if (W.nested2({ k: "some", v: true }) !== 1n) fail("n2t");
    if (W.nested2({ k: "some", v: false }) !== 0n) fail("n2f");
    if (W.nested2({ k: "none" }) !== 0n) fail("n2n");
    const dropped = W.dropCR(raw, { tag: "kept", fields: [] });
    if (dropped.buffer !== raw.buffer || dropped.byteOffset !== 1 || dropped.length !== 1 || dropped[0] !== 98) fail("drop");
    const whole = W.dropCR(raw, { tag: "empty", fields: [] });
    if (whole.buffer !== raw.buffer || whole.byteOffset !== 0 || whole.length !== 2) fail("empty");
    const pb = W.pickBytes(false);
    if (pb.length !== 1 || pb[0] !== 98) fail("pb");
    console.log("OK");
    """
  end
end
