defmodule Muro.IRShareTest do
  use ExUnit.Case, async: true

  # count folds the slice. wrap only calls it. twice and viaWrap
  # compute count s twice on every path. both computes it in each arm,
  # so on every path. nested computes it twice, only in the no arm.
  # branchy computes it only on some paths, once per pickCount, so
  # nothing there may be hoisted above the match.
  @book """
  data Pick : Type where
    yes : Pick
    no : Pick

  def count : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) →
      sliceFold U64 (toU64 0)
        (λ (_b : U8) → λ (_r : Slice) → λ (acc : U64) → addi acc (toU64 1))
        s

  def wrap : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) → count s

  def twice : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) → addi (count s) (count s)

  def viaWrap : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) → addi (wrap s) (muli (count s) (toU64 10))

  def both : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      match p motive (λ _ → U64)
        | yes => addi (count s) (toU64 100)
        | no => muli (count s) (count s)

  def nested : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      match p motive (λ _ → U64)
        | yes => toU64 100
        | no => muli (count s) (count s)

  def pickCount : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      match p motive (λ _ → U64)
        | yes => count s
        | no => toU64 7

  def branchy : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      addi (pickCount p s) (pickCount p s)

  -- seen stays 1 once it has seen an x, so hasX may stop there.
  -- tally reads the octet before it keeps acc, so it may not stop.
  def seen : run Π (b : U8) → Π (+ acc : U64) → U64 :=
    λ (b : U8) → λ (+ acc : U64) →
      match (eqi acc (toU64 0)) motive (λ _ → U64)
        | wtrue =>
            (match (eqi b (toU8 120)) motive (λ _ → U64)
              | wtrue => toU64 1
              | wfalse => toU64 0)
        | wfalse => acc

  def hasX : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) →
      sliceFold U64 (toU64 0)
        (λ (b : U8) → λ (_r : Slice) → λ (acc : U64) → seen b acc)
        s

  def tally : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) →
      sliceFold U64 (toU64 0)
        (λ (b : U8) → λ (_r : Slice) → λ (acc : U64) →
          match (eqi b (toU8 120)) motive (λ _ → U64)
            | wtrue => acc
            | wfalse => addi acc (toU64 1))
        s

  def twice-ok : evidence {twice b"abc" ≡ toU64 6 : U64} := refl
  def via-ok : evidence {viaWrap b"abc" ≡ toU64 33 : U64} := refl
  def branchy-ok : evidence {branchy no b"abc" ≡ toU64 14 : U64} := refl
  """

  setup_all do
    dir = Path.join(System.tmp_dir!(), "muro_share_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "shared.muro")
    File.write!(path, @book)
    {:ok, book} = Muro.Load.file(path)
    book = Muro.Prelude.for_emit(book)
    {:ok, funs} = Muro.IR.elaborate(book)
    {:ok, dir: dir, book: book, funs: funs}
  end

  defp body(funs, name),
    do: Enum.find(funs, &(&1.name == name and not Map.get(&1, :generated, false))).body

  defp body_gen(funs, name),
    do: Enum.find(funs, &(&1.name == name and Map.get(&1, :generated, false))).body

  defp calls(t, name) do
    own = if match?({:call, ^name, _}, t), do: 1, else: 0

    sub =
      cond do
        is_tuple(t) -> t |> Tuple.to_list() |> Enum.map(&calls(&1, name)) |> Enum.sum()
        is_list(t) -> t |> Enum.map(&calls(&1, name)) |> Enum.sum()
        true -> 0
      end

    own + sub
  end

  # Text of one emitted C function, from its signature to the closing brace.
  defp c_fun(src, name) do
    [_, rest] = String.split(src, ~r/\n[^\n;]*\b#{name}\([^;\n]*\)\s*\{/, parts: 2)
    [text | _] = String.split(rest, "\n}\n", parts: 2)
    text
  end

  test "a repeated pure call is bound once", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)
    assert calls(body(funs, "twice"), "count") == 2
    assert calls(body(shared, "twice"), "count") == 1
    assert {:let, _, :u64, {:call, "count", [var: "s"]}, _} = body(shared, "twice")
  end

  test "a wrapper is inlined so its call is shared with the caller's", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)
    assert calls(body(funs, "viaWrap"), "count") == 1
    assert calls(body(funs, "viaWrap"), "wrap") == 1
    assert calls(body(shared, "viaWrap"), "wrap") == 0
    assert calls(body(shared, "viaWrap"), "count") == 1
  end

  test "a call every arm makes is bound once above the match", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)

    assert {:let, _, :u64, {:call, "count", [var: "s"]}, {:match, {:var, "p"}, _}} =
             body(shared, "both")

    assert calls(body(shared, "both"), "count") == 1
  end

  test "a call is shared inside the arm that repeats it", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)

    assert {:match, {:var, "p"}, [{:arm, "yes", [], yes}, {:arm, "no", [], no}]} =
             body(shared, "nested")

    assert calls(yes, "count") == 0
    assert {:let, _, :u64, {:call, "count", _}, _} = no
    assert calls(no, "count") == 1
  end

  test "a call only some paths make is not hoisted above the branch", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)
    # Inlining both pickCounts would expose two count calls, each under
    # its own yes arm. Neither is on every path, so no count is bound
    # above a match. pickCount p s itself is on every path: bound once.
    b = body(shared, "branchy")
    assert count_outside_arms(b) == 0
    assert calls(b, "pickCount") == 1
    assert {:let, _, :u64, {:call, "pickCount", [var: "p", var: "s"]}, _} = b
    assert body(shared, "pickCount") == body(funs, "pickCount")
  end

  test "share: false and inline: false", %{funs: funs} do
    assert Muro.IR.Share.funs(funs, share: false) == funs
    hoisted = Muro.IR.Share.funs(funs, inline: false)
    assert calls(body(hoisted, "twice"), "count") == 1
    assert calls(body(hoisted, "viaWrap"), "wrap") == 1
  end

  test "inline: false and the default agree on a directly repeated call", %{funs: funs} do
    plain = Muro.IR.Share.funs(funs, inline: false)
    full = Muro.IR.Share.funs(funs)

    for {name, callee} <- [
          {"twice", "count"},
          {"both", "count"},
          {"nested", "count"},
          {"branchy", "pickCount"}
        ] do
      assert calls(body(plain, name), callee) == calls(body(full, name), callee), name
    end
  end

  test "grow_max: 0 and inline: false never share more than the default", %{funs: funs} do
    full = Muro.IR.Share.funs(funs)

    for opts <- [[inline: false], [grow_max: 0]] do
      less = Muro.IR.Share.funs(funs, opts)

      for f <- funs, not Map.get(f, :generated, false) do
        a = Muro.IR.Share.path_work(full, body(full, f.name))
        b = Muro.IR.Share.path_work(less, body(less, f.name))
        assert a <= b, inspect({f.name, opts, a, b})
      end
    end
  end

  test "the C emitter calls the fold once in twice and viaWrap", %{book: book} do
    {:ok, {_h, src}} = Muro.Emit.C.render(book, "shared")
    {:ok, {_h, plain}} = Muro.Emit.C.render(book, "shared", share: false)
    assert length(Regex.scan(~r/\bcount\(/, c_fun(plain, "twice"))) == 2
    assert length(Regex.scan(~r/\bcount\(/, c_fun(src, "twice"))) == 1
    assert length(Regex.scan(~r/\bcount\(/, c_fun(src, "viaWrap"))) == 1
    refute c_fun(src, "viaWrap") =~ ~r/\bwrap\(/
    assert length(Regex.scan(~r/\bpickCount\(/, c_fun(plain, "branchy"))) == 2
    assert length(Regex.scan(~r/\bpickCount\(/, c_fun(src, "branchy"))) == 1
  end

  test "grow_max reaches the C emitter" do
    # fat2 adds nodes around count s, so with no budget viaFat keeps
    # calling it, and with the default it inlines it and folds once.
    extra = """

    def fat2 : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) → addi (addi (count s) (toU64 1)) (muli (toU64 2) (toU64 3))

    def viaFat : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) → addi (fat2 s) (count s)
    """

    dir = Path.join(System.tmp_dir!(), "muro_share_g#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "fat.muro")
    File.write!(path, @book <> extra)
    {:ok, b} = Muro.Load.file(path)
    b = Muro.Prelude.for_emit(b)
    {:ok, {_h, none}} = Muro.Emit.C.render(b, "fat", grow_max: 0)
    {:ok, {_h, full}} = Muro.Emit.C.render(b, "fat")
    assert c_fun(none, "viaFat") =~ ~r/\bfat2\(/
    refute c_fun(full, "viaFat") =~ ~r/\bfat2\(/
    assert length(Regex.scan(~r/\bcount\(/, c_fun(full, "viaFat"))) == 1
  end

  test "the Rust emitter calls the fold once in twice", %{book: book} do
    {:ok, src} = Muro.Emit.Rust.render(book, "shared")
    [_, rest] = String.split(src, ~r/fn twice\(/, parts: 2)
    [text | _] = String.split(rest, "\n}\n", parts: 2)
    assert length(Regex.scan(~r/\bcount\(/, text)) == 1
  end

  test "C, Rust, and Zig pass the share options through", %{book: book} do
    {:ok, {_h, plain}} = Muro.Emit.C.render(book, "shared", share: false)
    {:ok, {_h, noinl}} = Muro.Emit.C.render(book, "shared", inline: false)
    assert length(Regex.scan(~r/\bcount\(/, c_fun(plain, "twice"))) == 2
    # Without inlining, wrap stays a call in viaWrap.
    assert c_fun(noinl, "viaWrap") =~ ~r/\bwrap\(/

    keys = [
      share: true,
      inline: true,
      inline_max: 9,
      grow_max: 7,
      cost: false,
      spec: false,
      dup_max: 3,
      inline_small: 4
    ]

    assert Muro.IR.Share.opts(keys ++ [path: "x", c_prefix: "p_"]) == keys

    for mod <- [Muro.Emit.Rust, Muro.Emit.Zig] do
      {:ok, on} = mod.render(book, "shared")
      {:ok, off} = mod.render(book, "shared", share: false)
      assert on != off
      {:ok, noinl} = mod.render(book, "shared", inline: false)
      [_, rest] = String.split(noinl, ~r/fn viaWrap\(/, parts: 2)
      [text | _] = String.split(rest, "\n}\n", parts: 2)
      assert text =~ ~r/\bwrap\(/
    end
  end

  # A toolchain that is missing skips its test, and ExUnit reports the
  # skip with this reason. Under CI (`CI` set) the test runs and fails.
  @rustc System.find_executable("rustc") ||
           (fn p -> if File.regular?(p), do: p end).(
             Path.join(System.user_home!(), ".cargo/bin/rustc")
           )
  @tag :rust
  if is_nil(@rustc) and is_nil(System.get_env("CI")), do: @tag(skip: "rustc is not on PATH")

  test "the shared Rust computes twice and viaWrap", %{book: book, dir: dir} do
    rustc = @rustc
    assert rustc, "rustc is not on PATH and CI is set"
    sub = Path.join(dir, "rs")
    File.mkdir_p!(sub)
    {:ok, src} = Muro.Emit.Rust.render(book, "shared")
    File.write!(Path.join(sub, "shared.rs"), src)

    File.write!(Path.join(sub, "main.rs"), """
    mod shared;
    fn main() {
        for s in ["abc", "", "hello, world"] {
            let b = s.as_bytes();
            let sl = shared::muro__slice_of(b.as_ptr(), b.len());
            println!("{} {}", shared::twice(sl), shared::viaWrap(sl));
        }
    }
    """)

    {out, 0} =
      System.cmd(rustc, ~w(--edition 2021 -A warnings main.rs -o main_rs),
        cd: sub,
        stderr_to_stdout: true
      )

    assert out == ""
    assert {"6 33\n0 0\n24 132\n", 0} = System.cmd(Path.join(sub, "main_rs"), [])
  end

  @zig System.find_executable("zig")
  @tag :zig
  if is_nil(@zig) and is_nil(System.get_env("CI")), do: @tag(skip: "zig is not on PATH")

  test "the shared Zig computes twice and viaWrap", %{book: book, dir: dir} do
    zig = @zig
    assert zig, "zig is not on PATH and CI is set"
    sub = Path.join(dir, "zig")
    File.mkdir_p!(sub)
    {:ok, src} = Muro.Emit.Zig.render(book, "shared")
    File.write!(Path.join(sub, "shared.zig"), src)

    File.write!(Path.join(sub, "main.zig"), """
    const std = @import("std");
    const shared = @import("shared.zig");
    pub fn main() !void {
        const a = std.heap.page_allocator;
        const out = std.fs.File.stdout();
        for ([_][]const u8{ "abc", "", "hello, world" }) |s| {
            const sl = shared.muro__slice_of(s.ptr, s.len);
            var buf: [64]u8 = undefined;
            const line = try std.fmt.bufPrint(&buf, "{d} {d}\\n", .{ try shared.twice(a, sl), try shared.viaWrap(a, sl) });
            try out.writeAll(line);
        }
    }
    """)

    assert {"6 33\n0 0\n24 132\n", 0} =
             System.cmd(zig, ~w(run main.zig --global-cache-dir) ++ [Path.join(sub, ".zcache")],
               cd: sub
             )
  end

  test "the Zig emitter calls the fold once in twice", %{book: book} do
    {:ok, src} = Muro.Emit.Zig.render(book, "shared")
    [_, rest] = String.split(src, ~r/fn twice\(/, parts: 2)
    [text | _] = String.split(rest, "\n}\n", parts: 2)
    assert length(Regex.scan(~r/\bcount\(/, text)) == 1
  end

  test "a fold whose step keeps its accumulator stops early in C", %{book: book, funs: funs} do
    by_name = for f <- funs, not Map.get(f, :generated, false), into: %{}, do: {f.name, f}
    steps = Enum.filter(funs, &Map.get(&1, :fold, false))
    assert Enum.count(steps, &match?({:ok, _, _}, Muro.IR.Share.stop(&1, by_name))) == 1

    {:ok, {_h, src}} = Muro.Emit.C.render(book, "shared")
    assert c_fun(src, "hasX") =~ ~r/if \(\w+\) break;/
    refute c_fun(src, "tally") =~ ~r/if \(\w+\) break;/
    refute c_fun(src, "count") =~ ~r/if \(\w+\) break;/
  end

  # Hand-built images for the edge cases. `count` folds, so it is heavy;
  # `wrap` and the others only call it.
  defp lit(n), do: {:wrd, :u64, {:lit, :u64, n}, []}
  defp add(a, b), do: {:wrd, :u64, :addi, [a, b]}
  defp cnt(x), do: {:call, "count", [var: x]}

  defp run(name, params, body), do: %{name: name, params: params, ret: :u64, body: body}

  defp image(extra) do
    [
      run("count", [{"s", :slice}], {:bfold, "step0", [], lit(0), {:var, "s"}}),
      run("wrap", [{"s", :slice}], cnt("s"))
      | extra
    ]
  end

  defp shared_body(funs, name, opts \\ []), do: body(Muro.IR.Share.funs(funs, opts), name)

  test "an arm that aborts is a path: nothing the other arms make is hoisted above it" do
    rep = add(cnt("s"), cnt("s"))
    m = {:match, {:var, "p"}, [{:arm, "yes", [], rep}, {:arm, "no", [], :abort}]}
    funs = image([run("f", [{"p", :pick}, {"s", :slice}], m)])

    assert {:match, {:var, "p"}, [{:arm, "yes", [], yes}, {:arm, "no", [], :abort}]} =
             shared_body(funs, "f")

    assert {:let, _, :u64, {:call, "count", [var: "s"]}, _} = yes
    assert calls(yes, "count") == 1
  end

  test "an arm that binds a call before it aborts evaluates it, so it may be hoisted" do
    m =
      {:match, {:var, "p"},
       [
         {:arm, "yes", [], add(cnt("s"), cnt("s"))},
         {:arm, "no", [], {:let, "z", :u64, cnt("s"), :abort}}
       ]}

    funs = image([run("f", [{"p", :pick}, {"s", :slice}], m)])

    assert {:let, v, :u64, {:call, "count", [var: "s"]}, {:match, _, arms}} =
             shared_body(funs, "f")

    assert calls(arms, "count") == 0
    assert [_, {:arm, "no", [], {:let, "z", :u64, {:var, ^v}, :abort}}] = arms
  end

  test "a call in the scrutinee is on every path; one only in an arm is not" do
    m = {:match, cnt("s"), [{:arm, "a", [], cnt("s")}, {:arm, "b", [], lit(1)}]}
    funs = image([run("f", [{"s", :slice}], m)])

    assert {:let, v, :u64, {:call, "count", [var: "s"]},
            {:match, {:var, v}, [{:arm, "a", [], {:var, v}}, {:arm, "b", [], _}]}} =
             shared_body(funs, "f")

    # count s twice, but only in arm a of the inner match: it stays there.
    inner =
      {:match, {:var, "q"}, [{:arm, "a", [], add(cnt("s"), cnt("s"))}, {:arm, "b", [], lit(1)}]}

    outer =
      add(cnt("t"), {:match, {:var, "p"}, [{:arm, "a", [], inner}, {:arm, "b", [], lit(2)}]})

    g = run("g", [{"p", :pick}, {"q", :pick}, {"s", :slice}, {"t", :slice}], outer)
    out = shared_body(image([g]), "g")
    assert {:wrd, :u64, :addi, [{:call, "count", [var: "t"]}, {:match, {:var, "p"}, _}]} = out

    assert {:match, _, [{:arm, "a", [], {:match, {:var, "q"}, [{:arm, "a", [], a}, _]}}, _]} =
             Enum.at(elem(out, 3), 1)

    assert {:let, _, :u64, {:call, "count", [var: "s"]}, _} = a
  end

  test "a call over a shadowed name is not the caller's call" do
    # count s at the top and count s under an arm that rebinds s are two
    # values: nothing is shared.
    m = {:match, {:var, "p"}, [{:arm, "c", ["s"], cnt("s")}]}
    f = run("f", [{"p", :pick}, {"s", :slice}], add(cnt("s"), m))
    assert shared_body(image([f]), "f") == f.body

    # Inlining wrap s would expose count s beside the arm's count s, but
    # those differ, so wrap stays a call. count t is still shared.
    g =
      run(
        "g",
        [{"p", :pick}, {"s", :slice}, {"t", :slice}],
        add(add({:call, "wrap", [var: "s"]}, m), add(cnt("t"), cnt("t")))
      )

    out = shared_body(image([g]), "g")
    assert calls(out, "wrap") == 1
    assert calls(out, "count") == 2
    assert {:let, _, :u64, {:call, "count", [var: "t"]}, _} = out
  end

  test "inlining never does more heavy work than inline: false on the worst path" do
    pick = fn x ->
      {:match, {:var, "p"}, [{:arm, "yes", [], cnt(x)}, {:arm, "no", [], lit(7)}]}
    end

    pc = run("pickCount", [{"p", :pick}, {"s", :slice}], pick.("s"))
    call_pc = {:call, "pickCount", [var: "p", var: "s"]}

    shapes = [
      # Inlining both pickCounts leaves two count s, each under its own
      # yes arm; count t is hoisted either way.
      add(add(call_pc, call_pc), add(cnt("t"), cnt("t"))),
      # Same, with the repeat that makes some hoist succeed on the other
      # side.
      add(add(cnt("t"), cnt("t")), add(call_pc, add(call_pc, call_pc)))
    ]

    for b <- shapes do
      f = run("f", [{"p", :pick}, {"s", :slice}, {"t", :slice}], b)
      funs = image([pc, f])
      plain = Muro.IR.Share.funs(funs, inline: false)
      full = Muro.IR.Share.funs(funs)

      assert Muro.IR.Share.path_work(full, body(full, "f")) <=
               Muro.IR.Share.path_work(plain, body(plain, "f"))

      assert Muro.IR.Share.path_work(full, body(full, "f")) == 2
      assert Muro.IR.Share.path_work(plain, body(plain, "f")) == 2
      assert calls(body(full, "f"), "pickCount") == 1
    end
  end

  test "the heavy-work oracle counts folds, streams and uncons" do
    stream = {:stream, lit(0), [], "step"}
    assert Muro.IR.Share.path_work([], stream) == 1
    assert Muro.IR.Share.path_work([], {:uncons, stream}) == 2
    assert Muro.IR.Share.path_work([], {:bfold, "step", [], lit(0), {:var, "s"}}) == 1

    assert Muro.IR.Share.path_work(
             [],
             {:match, lit(0), [{:arm, "a", [], stream}, {:arm, "b", [], {:uncons, stream}}]}
           ) == 2

    # A missing callee costs 0, so a hit of 1 is the followed body,
    # not a hard-coded name.
    assert Muro.IR.Share.path_work([], cnt("s")) == 0

    # A call to count is followed through its bfold body, not hard-coded.
    assert Muro.IR.Share.path_work(image([]), cnt("s")) == 1

    # Follow-through of a callee whose body is two folds is 2, not 1.
    two =
      run(
        "two",
        [{"s", :slice}],
        add(
          {:bfold, "step0", [], lit(0), {:var, "s"}},
          {:bfold, "step1", [], lit(0), {:var, "s"}}
        )
      )

    assert Muro.IR.Share.path_work([two], {:call, "two", [var: "s"]}) == 2

    # A run with no fold, stream, or uncons, and none in what it calls,
    # is outside the heavy set: the call costs nothing.
    light = run("light", [], add(lit(1), lit(2)))
    assert Muro.IR.Share.path_work([light], {:call, "light", []}) == 0

    # A run that is heavy only because of an erased let still has the
    # same max(body, 1) floor as work/2, even when the body walks to 0.
    erased = run("erased", [], {:let, "x", :erased, lit(0), lit(1)})
    assert Muro.IR.Share.path_work([erased], {:call, "erased", []}) == 1
  end

  test "a self-recursive heavy run breaks the cycle at :busy -> 1" do
    # loop s = addi (loop s) (fold s). The recursive call is busy, so it
    # costs 1, plus the fold, so a call of loop is 2. Measured as a
    # term, the body is that call (2) plus the fold again (1).
    loop =
      run(
        "loop",
        [{"s", :slice}],
        add({:call, "loop", [var: "s"]}, {:bfold, "step0", [], lit(0), {:var, "s"}})
      )

    call = {:call, "loop", [var: "s"]}
    assert Muro.IR.Share.path_work([loop], call) == 2
    assert Muro.IR.Share.path_work([loop], loop.body) == 3
  end

  test "a generated step that would grow is not inlined into and draws nothing" do
    fat = run("fat", [{"s", :slice}], add(add(cnt("s"), lit(1)), add(lit(2), lit(3))))
    body = add(add({:call, "fat", [var: "s"]}, cnt("s")), cnt("s"))
    step = Map.put(run("a0", [{"s", :slice}], body), :generated, true)
    g = run("g", [{"s", :slice}], body)
    one = Muro.IR.Share.size(fat.body) - Muro.IR.Share.size({:call, "fat", [var: "s"]})

    out = Muro.IR.Share.funs(image([fat, step, g]), grow_max: one)
    # The step keeps calling fat and still shares count s; g has the whole
    # budget.
    assert calls(body_gen(out, "a0"), "fat") == 1
    assert calls(body_gen(out, "a0"), "count") == 1
    assert calls(body(out, "g"), "fat") == 0
  end

  test "the image grows by at most grow_max nodes, smallest growth first" do
    # fat s adds nodes around count s, so inlining it grows a run.
    fat = run("fat", [{"s", :slice}], add(add(cnt("s"), lit(1)), add(lit(2), lit(3))))
    body = add(add({:call, "fat", [var: "s"]}, cnt("s")), cnt("s"))
    f = run("f", [{"s", :slice}], body)
    g = run("g", [{"s", :slice}], body)
    funs = image([fat, f, g])

    # Inlining fat s puts fat's body, over s, where the call was: in the
    # pass's own measure that is 8 - 2 nodes per run.
    one = Muro.IR.Share.size(fat.body) - Muro.IR.Share.size({:call, "fat", [var: "s"]})
    assert one == 6

    fats = fn fs -> {calls(body(fs, "f"), "fat"), calls(body(fs, "g"), "fat")} end

    # Below one run's growth: fat stays a call, count s is still hoisted.
    none = Muro.IR.Share.funs(funs, grow_max: one - 1)
    assert fats.(none) == {1, 1}
    assert calls(body(none, "f"), "count") == 1
    nobody = fn fs -> Enum.map(fs, &normal(&1.body)) end
    assert nobody.(none) == nobody.(Muro.IR.Share.funs(funs, inline: false))

    # Room for one run: f and g grow alike, so the name decides, in
    # either list order.
    assert fats.(Muro.IR.Share.funs(funs, grow_max: one)) == {0, 1}
    assert fats.(Muro.IR.Share.funs(funs, grow_max: 2 * one - 1)) == {0, 1}
    assert fats.(Muro.IR.Share.funs(image([fat, g, f]), grow_max: one)) == {0, 1}

    # A run that grows less draws first, wherever it is in the list.
    h = run("h", [{"s", :slice}], add({:call, "wrap", [var: "s"]}, cnt("s")))
    big = run("a", [{"s", :slice}], body)
    order = [image([fat, big, h]), image([fat, h, big])]

    for fs <- order do
      out = Muro.IR.Share.funs(fs, grow_max: one - 1)
      assert calls(body(out, "h"), "wrap") == 0
      assert calls(body(out, "a"), "fat") == 1
    end

    # Room for both, and the default budget, take both.
    assert fats.(Muro.IR.Share.funs(funs, grow_max: 2 * one)) == {0, 0}
    assert fats.(Muro.IR.Share.funs(funs)) == {0, 0}
  end

  test "with room in the budget, inlining does not depend on the order runs are visited" do
    # h1 and h2 call each other. Each inlines the other once; the memo
    # must not hand h2 the body it got while h1 was being inlined. The
    # budget is drawn smallest growth first, not in list order (see the
    # grow_max test).
    h1 = run("h1", [{"s", :slice}], add({:call, "h2", [var: "s"]}, cnt("s")))
    h2 = run("h2", [{"s", :slice}], add({:call, "h1", [var: "s"]}, cnt("s")))
    funs = image([h1, h2])
    a = Muro.IR.Share.funs(funs)
    b = Muro.IR.Share.funs(Enum.reverse(funs))

    for n <- ["h1", "h2"] do
      assert normal(body(a, n)) == normal(body(b, n))
    end
  end

  test "a call repeated inside a hoisted value is hoisted too" do
    k = {:call, "pair2", [cnt("s"), cnt("s")]}
    p2 = run("pair2", [{"a", :u64}, {"b", :u64}], add({:var, "a"}, {:var, "b"}))
    funs = image([p2, run("f", [{"s", :slice}], add(k, k))])

    assert {:let, c, :u64, {:call, "count", [var: "s"]},
            {:let, v, :u64, {:call, "pair2", [var: c, var: c]},
             {:wrd, :u64, :addi, [var: v, var: v]}}} = shared_body(funs, "f", inline: false)
  end

  # count calls that are not under a match arm.
  defp count_outside_arms({:match, s, _arms}), do: count_outside_arms(s)
  defp count_outside_arms({:call, "count", args}), do: 1 + count_outside_arms(args)

  defp count_outside_arms(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> count_outside_arms()

  defp count_outside_arms(l) when is_list(l),
    do: l |> Enum.map(&count_outside_arms/1) |> Enum.sum()

  defp count_outside_arms(_), do: 0

  # Fresh names renumbered in order of first appearance.
  defp normal(t) do
    {out, _} = norm(t, %{})
    out
  end

  defp norm(x, m) when is_binary(x) do
    if x =~ ~r/_s\d+$/ do
      case m do
        %{^x => y} -> {y, m}
        _ -> {"v#{map_size(m)}", Map.put(m, x, "v#{map_size(m)}")}
      end
    else
      {x, m}
    end
  end

  defp norm(t, m) when is_tuple(t) do
    {l, m} = norm(Tuple.to_list(t), m)
    {List.to_tuple(l), m}
  end

  defp norm(l, m) when is_list(l), do: Enum.map_reduce(l, m, &norm/2)
  defp norm(x, m), do: {x, m}

  # Same answers with and without sharing, from the compiled C.
  test "shared and plain C agree", %{book: book, dir: dir} do
    inputs = ["a", "abc", "abxcd", "x", "hello, world", String.duplicate("x", 300)]

    outs =
      for {tag, opts} <- [{"on", []}, {"off", [share: false]}] do
        sub = Path.join(dir, tag)
        File.mkdir_p!(sub)
        {:ok, {h, c}} = Muro.Emit.C.render(book, "shared", opts)
        File.write!(Path.join(sub, "shared.h"), h)
        File.write!(Path.join(sub, "shared.c"), c)
        File.write!(Path.join(sub, "main.c"), main_c(inputs))
        cc!(sub, ~w(shared.c main.c -o main_bin))
        {out, 0} = System.cmd(Path.join(sub, "main_bin"), [], stderr_to_stdout: true)
        out
      end

    assert [on, off] = outs
    assert on == off
    assert on =~ "twice 6\n"
    assert on =~ "viaWrap 33\n"
    assert on =~ "branchy-no 14\n"
    assert on =~ "hasX 0\n"
    assert on =~ "n5 1 4 "
    assert on =~ "n300 1 0 "
  end

  defp main_c(inputs) do
    cases =
      Enum.map_join(inputs, "\n", fn s ->
        lit = s |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)
        n = byte_size(s)

        """
          {
            static const uint8_t b[] = {#{lit}};
            muro__slice s = {b, #{n}};
            printf("n%d %llu %llu %llu %llu %llu %llu %llu %llu %llu %llu\\n", #{n},
              (unsigned long long)hasX(s), (unsigned long long)tally(s),
              (unsigned long long)twice(s), (unsigned long long)viaWrap(s),
              (unsigned long long)both(yes, s), (unsigned long long)both(no, s),
              (unsigned long long)nested(yes, s), (unsigned long long)nested(no, s),
              (unsigned long long)branchy(yes, s), (unsigned long long)branchy(no, s));
          }
        """
      end)

    """
    #include <stdio.h>
    #include "shared.h"
    int main(void) {
      Pick yes = muro__tag_Pick_yes;
      Pick no = muro__tag_Pick_no;
      {
        static const uint8_t b[] = {97, 98, 99};
        muro__slice s = {b, 3};
        printf("twice %llu\\n", (unsigned long long)twice(s));
        printf("viaWrap %llu\\n", (unsigned long long)viaWrap(s));
        printf("branchy-no %llu\\n", (unsigned long long)branchy(no, s));
        printf("hasX %llu\\n", (unsigned long long)hasX(s));
      }
    #{cases}
      return 0;
    }
    """
  end

  defp cc!(dir, args) do
    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11) ++ args,
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
  end

  test "the default agrees with cost: false, spec: false on the share book", %{funs: funs} do
    old = Muro.IR.Share.funs(funs, cost: false, spec: false)
    now = Muro.IR.Share.funs(funs)

    for f <- funs, not Map.get(f, :generated, false) do
      assert normal(body(old, f.name)) == normal(body(now, f.name)), f.name
    end
  end

  test "a large exported run used twice stays a call" do
    body = pad(add(cnt("s"), cnt("s")), 90)
    assert Muro.IR.Share.size(body) > 160
    big = run("big", [{"s", :slice}], body)

    caller =
      run("f", [{"s", :slice}], add({:call, "big", [var: "s"]}, {:call, "big", [var: "s"]}))

    for fs <- [image([big, caller]), image([caller, big])] do
      out = Muro.IR.Share.funs(fs)
      assert calls(body(out, "f"), "big") == 1
      assert calls(body(out, "big"), "count") == 1
      assert normal(body(out, "f")) == normal(body(Muro.IR.Share.funs(Enum.reverse(fs)), "f"))
    end

    off = Muro.IR.Share.funs(image([big, caller]), cost: false, spec: false, grow_max: 100_000)
    assert calls(body(off, "f"), "big") == 0
  end

  test "a thin exported wrapper of a large run stays a call" do
    wide = pad(add(cnt("s"), cnt("s")), 90)
    assert Muro.IR.Share.size(wide) > 160
    inner = run("inner", [{"s", :slice}], wide)
    shell = run("shell", [{"s", :slice}], {:call, "inner", [var: "s"]})

    caller =
      run("f", [{"s", :slice}], add({:call, "shell", [var: "s"]}, {:call, "shell", [var: "s"]}))

    out = Muro.IR.Share.funs(image([inner, shell, caller]), grow_max: 100_000)
    assert calls(body(out, "f"), "shell") == 1
    assert calls(body(out, "shell"), "inner") == 1

    off =
      Muro.IR.Share.funs(image([inner, shell, caller]),
        cost: false,
        spec: false,
        grow_max: 100_000
      )

    assert calls(body(off, "f"), "shell") == 0
  end

  # `fat` is above `dup_max: 7`. Inlining it pulls its `count s` onto a
  # caller that already folds `s`, so the worst path folds once instead
  # of twice. The size cap does not block that, exported or not.
  test "a run above dup_max is inlined when that shares the caller's fold" do
    fat = run("fat", [{"s", :slice}], add(add(cnt("s"), lit(1)), add(lit(2), lit(3))))
    assert Muro.IR.Share.size(fat.body) > 7
    caller = run("f", [{"s", :slice}], add(add({:call, "fat", [var: "s"]}, cnt("s")), cnt("s")))
    funs = image([fat, caller])
    assert calls(body(Muro.IR.Share.funs(funs, dup_max: 7), "f"), "fat") == 0
    assert calls(body(Muro.IR.Share.funs(funs), "f"), "fat") == 0

    wide = pad(add(cnt("s"), cnt("s")), 90)
    assert Muro.IR.Share.size(wide) > 160
    one = Map.put(run("wide", [{"s", :slice}], wide), :export, false)
    once = run("once", [{"s", :slice}], add({:call, "wide", [var: "s"]}, cnt("s")))

    twice =
      run("twice", [{"s", :slice}], add({:call, "wide", [var: "s"]}, {:call, "wide", [var: "s"]}))

    fs = image([one, once, twice])
    out = Muro.IR.Share.funs(fs, grow_max: 100_000)
    assert calls(body(out, "once"), "wide") == 0
    assert calls(body(out, "twice"), "wide") == 1

    assert normal(body(out, "once")) ==
             normal(body(Muro.IR.Share.funs(Enum.reverse(fs), grow_max: 100_000), "once"))
  end

  test "a large run is inlined at every site when that lowers worst-path work" do
    wide = pad(add(cnt("s"), cnt("s")), 90)
    assert Muro.IR.Share.size(wide) > 160

    caller =
      run(
        "f",
        [{"s", :slice}],
        add(add({:call, "wide", [var: "s"]}, {:call, "wide", [var: "s"]}), cnt("s"))
      )

    for export <- [true, false] do
      big = Map.put(run("wide", [{"s", :slice}], wide), :export, export)

      for fs <- [image([big, caller]), image([caller, big])] do
        out = Muro.IR.Share.funs(fs, grow_max: 100_000)
        assert calls(body(out, "f"), "wide") == 0, inspect(export)
        assert calls(body(out, "f"), "count") == 1, inspect(export)
        plain = Muro.IR.Share.funs(fs, inline: false)

        assert Muro.IR.Share.path_work(out, body(out, "f")) <
                 Muro.IR.Share.path_work(plain, body(plain, "f"))

        rev = Muro.IR.Share.funs(Enum.reverse(fs), grow_max: 100_000)
        assert normal(body(out, "f")) == normal(body(rev, "f"))
        assert normal(body(out, "wide")) == normal(body(rev, "wide"))
      end
    end
  end

  test "a large run stays a call when inlining it saves no heavy work" do
    wide = pad(add(cnt("s"), cnt("s")), 90)
    assert Muro.IR.Share.size(wide) > 160
    big = run("wide", [{"s", :slice}], wide)
    alone = run("f", [{"s", :slice}], {:call, "wide", [var: "s"]})
    out = Muro.IR.Share.funs(image([big, alone]), grow_max: 100_000)
    assert calls(body(out, "f"), "wide") == 1

    # An internal run the caller names once used to be copied for that
    # reason alone. The copy only repeats a fold `wide` already hoists.
    internal = Map.put(big, :export, false)
    one = Muro.IR.Share.funs(image([internal, alone]), grow_max: 100_000)
    assert calls(body(one, "f"), "wide") == 1

    fat = pad(add(cnt("t"), cnt("t")), 90)

    caller =
      run(
        "g",
        [{"s", :slice}, {"t", :slice}],
        add(add({:call, "wide", [var: "s"]}, cnt("s")), {:call, "fat", [var: "t"]})
      )

    both = image([big, run("fat", [{"t", :slice}], fat), caller])
    merged = Muro.IR.Share.funs(both, grow_max: 100_000)
    assert calls(body(merged, "g"), "wide") == 0
    assert calls(body(merged, "g"), "fat") == 1
    assert calls(body(merged, "g"), "count") == 1
    assert calls(body(merged, "fat"), "count") == 1
  end

  test "a known nonzero end drops the fold, and spec: false keeps it", %{dir: dir} do
    path = Path.join(dir, "hend.muro")
    File.write!(path, File.read!("test/fixtures/share_hend.muro"))
    {:ok, book} = Muro.Load.file(path)
    book = Muro.Prelude.for_emit(book)
    {:ok, funs} = Muro.IR.elaborate(book)
    shared = Muro.IR.Share.funs(funs)
    assert calls(false_arm(body(shared, "hot")), "foldEnd") == 0
    assert calls(false_arm(body(shared, "hot")), "endAt") == 0
    assert calls(true_arm(body(shared, "hot")), "foldEnd") == 1
    assert calls(body(shared, "known"), "foldEnd") == 0
    assert calls(body(shared, "known"), "endAt") == 0

    kept = Muro.IR.Share.funs(funs, spec: false)
    # `eq0 h` is shared. `endAt` is copied into the false arm, and that
    # copy still matches on the same call. Both arms of both matches stay.
    one = lit(1)

    assert {:let, sh, {:data, "Bool"}, {:call, "eq0", [var: "h"]},
            {:match, {:var, sh},
             [
               {:arm, "true", [], {:call, "foldEnd", [var: "s"]}},
               {:arm, "false", [],
                {:wrd, :u64, :add,
                 [
                   {:match, {:var, sh},
                    [
                      {:arm, "true", [], {:call, "foldEnd", [var: "s"]}},
                      {:arm, "false", [], {:var, "h"}}
                    ]},
                   ^one
                 ]}}
             ]}} = body(kept, "hot")

    assert {:match, {:call, "eq0", [var: "h"]},
            [
              {:arm, "true", [], {:call, "foldEnd", [var: "s"]}},
              {:arm, "false", [], {:var, "h"}}
            ]} = body(kept, "endAt")

    # The same bodies either way the runs are listed.
    rev = Muro.IR.Share.funs(Enum.reverse(funs))

    for name <- ["hot", "known", "endAt"] do
      assert normal(body(shared, name)) == normal(body(rev, name))
    end

    outs =
      for {tag, opts} <- [{"on", []}, {"off", [share: false]}] do
        sub = Path.join(dir, "hend_" <> tag)
        File.mkdir_p!(sub)
        {:ok, {h, c}} = Muro.Emit.C.render(book, "hend", opts)
        File.write!(Path.join(sub, "hend.h"), h)
        File.write!(Path.join(sub, "hend.c"), c)

        File.write!(Path.join(sub, "main.c"), """
        #include <stdio.h>
        #include "hend.h"
        int main(void) {
          static const uint8_t b[] = {97, 98};
          muro__slice s = {b, 2};
          printf("%llu %llu %llu\\n",
            (unsigned long long)known(s),
            (unsigned long long)hot(2, s),
            (unsigned long long)hot(0, s));
          return 0;
        }
        """)

        cc!(sub, ~w(hend.c main.c -o main_bin))
        {out, 0} = System.cmd(Path.join(sub, "main_bin"), [], stderr_to_stdout: true)
        out
      end

    assert outs == ["1 3 2\n", "1 3 2\n"]
  end

  test "a fact does not cross a rebinding, a join, a sibling arm, or a different variable" do
    fold = run("headerEnd", [{"s", :slice}], {:bfold, "step0", [], lit(0), {:var, "s"}})
    eq = fn v -> {:wrd, :u64, :eq, [{:var, v}, lit(0)]} end

    inner =
      {:match, eq.("h"),
       [{:arm, "wtrue", [], {:call, "headerEnd", [var: "s"]}}, {:arm, "wfalse", [], {:var, "h"}}]}

    rebound =
      run(
        "rebound",
        [{"h", :u64}, {"z", :u64}, {"s", :slice}],
        {:match, eq.("h"),
         [
           {:arm, "wtrue", [], lit(0)},
           {:arm, "wfalse", [], {:let, "h", :u64, {:var, "z"}, inner}}
         ]}
      )

    joined =
      run(
        "joined",
        [{"p", {:data, "Pick"}}, {"s", :slice}],
        {:let, "b", {:data, "Bool"},
         {:match, {:var, "p"},
          [
            {:arm, "yes", [], {:con, "Bool", "true", []}},
            {:arm, "no", [], {:con, "Bool", "false", []}}
          ]},
         {:match, {:var, "b"},
          [{:arm, "true", [], {:call, "headerEnd", [var: "s"]}}, {:arm, "false", [], lit(0)}]}}
      )

    other =
      run(
        "other",
        [{"h", :u64}, {"z", :u64}, {"s", :slice}],
        {:match, eq.("h"),
         [
           {:arm, "wfalse", [],
            {:match, eq.("z"),
             [{:arm, "wtrue", [], {:call, "headerEnd", [var: "s"]}}, {:arm, "wfalse", [], lit(0)}]}},
           {:arm, "wtrue", [], lit(1)}
         ]}
      )

    sibling =
      run(
        "sibling",
        [{"h", :u64}, {"s", :slice}],
        {:match, eq.("h"),
         [
           {:arm, "wfalse", [], lit(7)},
           {:arm, "wtrue", [], inner}
         ]}
      )

    shadow =
      run(
        "shadow",
        [{"p", {:data, "Pick"}}, {"s", :slice}],
        {:match, {:var, "p"},
         [
           {:arm, "yes", ["p"],
            {:match, {:var, "p"},
             [
               {:arm, "yes", [], {:call, "headerEnd", [var: "s"]}},
               {:arm, "no", [], lit(0)}
             ]}},
           {:arm, "no", [], lit(1)}
         ]}
      )

    unknown =
      run(
        "unknown",
        [{"s", :slice}],
        {:match, {:call, "headerEnd", [var: "s"]},
         [
           {:arm, "a", [], {:call, "headerEnd", [var: "s"]}},
           {:arm, "b", [], lit(0)}
         ]}
      )

    nat =
      run(
        "nat",
        [{"n", :nat}, {"s", :slice}],
        {:match, {:var, "n"},
         [
           {:arm, "zero", [],
            {:match, {:var, "n"},
             [
               {:arm, "zero", [], lit(1)},
               {:arm, "suc", ["k"], {:call, "headerEnd", [var: "s"]}}
             ]}},
           {:arm, "suc", ["n"],
            {:match, {:var, "n"},
             [
               {:arm, "zero", [], {:call, "headerEnd", [var: "s"]}},
               {:arm, "suc", ["k"], lit(3)}
             ]}}
         ]}
      )

    funs = image([fold, rebound, joined, other, sibling, shadow, unknown, nat])
    out = Muro.IR.Share.funs(funs)

    assert calls(false_arm(body(out, "rebound")), "headerEnd") == 1
    assert {:match, {:var, "b"}, [_, _]} = let_body(body(out, "joined"))
    assert calls(body(out, "joined"), "headerEnd") == 1
    assert calls(false_arm(body(out, "other")), "headerEnd") == 1

    # The wtrue arm already knows h = 0, so the inner comparison keeps
    # the fold. The wfalse arm knows h ≠ 0; that fact belongs to the
    # sibling and must not delete the fold.
    sib = true_arm(body(out, "sibling"))
    assert calls(sib, "headerEnd") == 1
    refute match?({:match, _, _}, sib)
    # The payload `p` is a different binding from the parameter. The
    # inner match stays, and the fold stays in its yes arm.
    zero = lit(0)

    assert {:match, {:var, "p"},
            [
              {:arm, "yes", [], {:call, "headerEnd", [var: "s"]}},
              {:arm, "no", [], ^zero}
            ]} = arm_named(body(out, "shadow"), "yes")

    # A call is not a known constructor. Both arms stay. The two
    # identical calls may be hoisted; that does not pick an arm.
    unk = body(out, "unknown")
    assert calls(unk, "headerEnd") == 1
    assert {:match, scrut, [_, _] = arms} = let_body(unk)
    refute match?({:call, _, _}, scrut)

    assert Enum.all?(arms, fn {:arm, _, _, tm} -> tm != :abort end)

    assert calls(arm_named(body(out, "nat"), "zero"), "headerEnd") == 0
    assert calls(arm_named(body(out, "nat"), "suc"), "headerEnd") == 1
  end

  # `eq a b` is false, then `a` is bound again. The new `a` is not the
  # value the comparison rejected. The inner comparison stays.
  test "rebinding a name a comparison mentions does not keep the comparison" do
    arms = [
      {:arm, "wtrue", [], lit(1)},
      {:arm, "wfalse", [], lit(0)}
    ]

    let_a =
      run(
        "let",
        [{"a", :u64}, {"b", :u64}],
        {:match, eq("a", "b"),
         [
           {:arm, "wtrue", [], lit(1)},
           {:arm, "wfalse", [], {:let, "a", :u64, {:var, "b"}, {:match, eq("a", "b"), arms}}}
         ]}
      )

    pair =
      run(
        "letp",
        [{"a", :u64}, {"c", :u64}, {"q", :u64}, {"r", :u64}],
        {:match, eq("a", "c"),
         [
           {:arm, "wtrue", [], lit(1)},
           {:arm, "wfalse", [],
            {:letp, "a", "b", {:pair, {:var, "q"}, {:var, "r"}}, {:match, eq("a", "c"), arms}}}
         ]}
      )

    arm =
      run(
        "arm",
        [{"a", :u64}, {"b", :u64}, {"p", {:data, "Pick"}}],
        {:match, eq("a", "b"),
         [
           {:arm, "wtrue", [], lit(1)},
           {:arm, "wfalse", [],
            {:match, {:var, "p"},
             [
               {:arm, "yes", ["a"], {:match, eq("a", "b"), arms}},
               {:arm, "no", [], lit(2)}
             ]}}
         ]}
      )

    out = Muro.IR.Share.funs([let_a, pair, arm])
    assert {:let, "a", :u64, {:var, "b"}, {:match, _, ^arms}} = false_arm(body(out, "let"))

    assert {:letp, "a", "b", {:pair, {:var, "q"}, {:var, "r"}}, {:match, _, ^arms}} =
             false_arm(body(out, "letp"))

    two = lit(2)

    assert {:match, {:var, "p"},
            [
              {:arm, "yes", ["a"], {:match, _, ^arms}},
              {:arm, "no", [], ^two}
            ]} = false_arm(body(out, "arm"))
  end

  # The field name in the fact is the outer binding. Reusing that name
  # for a new value must not make the match read the new value.
  test "rebinding a field or a successor does not retarget it" do
    field =
      run(
        "field",
        [{"x", {:data, "A"}}, {"y", {:data, "A"}}, {"z", {:data, "A"}}],
        {:let, "v", {:data, "Pair"}, {:con, "Pair", "pair", [{:var, "x"}, {:var, "y"}]},
         {:let, "x", {:data, "A"}, {:var, "z"},
          {:match, {:var, "v"}, [{:arm, "pair", ["a", "b"], {:var, "a"}}]}}}
      )

    suc =
      run(
        "suc",
        [{"p", :nat}, {"q", :nat}],
        {:let, "x", :nat, {:su, {:var, "p"}},
         {:let, "p", :nat, {:var, "q"},
          {:match, {:var, "x"}, [{:arm, "zero", [], lit(0)}, {:arm, "suc", ["k"], {:var, "k"}}]}}}
      )

    # The outer arm is substituted away. Its binder `k` is not in scope.
    # The inner match still reads the predecessor `p`.
    nest =
      run(
        "nest",
        [{"p", :nat}],
        {:let, "x", :nat, {:su, {:var, "p"}},
         {:match, {:var, "x"},
          [
            {:arm, "zero", [], lit(0)},
            {:arm, "suc", ["k"],
             {:match, {:var, "x"},
              [{:arm, "zero", [], lit(1)}, {:arm, "suc", ["m"], {:var, "m"}}]}}
          ]}}
      )

    out = Muro.IR.Share.funs([field, suc, nest])

    assert {:let, "v", {:data, "Pair"}, {:con, "Pair", "pair", [{:var, "x"}, {:var, "y"}]},
            {:let, "x", {:data, "A"}, {:var, "z"},
             {:match, {:var, "v"}, [{:arm, "pair", ["a", "b"], {:var, "a"}}]}}} =
             body(out, "field")

    zero = lit(0)

    assert {:let, "x", :nat, {:su, {:var, "p"}},
            {:let, "p", :nat, {:var, "q"},
             {:match, {:var, "x"}, [{:arm, "zero", [], ^zero}, {:arm, "suc", ["k"], {:var, "k"}}]}}} =
             body(out, "suc")

    assert {:let, "x", :nat, {:su, {:var, "p"}}, {:var, "p"}} = body(out, "nest")
  end

  # `v` is `pair x y`. The arm `pair y x` binds the first field as `y`.
  # That `y` is `x`. A let in the arm that reuses `x` must not capture it.
  test "a permuted pair arm reads the field it names" do
    straight =
      run(
        "straight",
        [{"x", {:data, "A"}}, {"y", {:data, "A"}}],
        {:let, "v", {:data, "Pair"}, {:con, "Pair", "pair", [{:var, "x"}, {:var, "y"}]},
         {:match, {:var, "v"}, [{:arm, "pair", ["y", "x"], {:var, "y"}}]}}
      )

    captured =
      run(
        "captured",
        [{"x", {:data, "A"}}, {"y", {:data, "A"}}, {"z", {:data, "A"}}],
        {:let, "v", {:data, "Pair"}, {:con, "Pair", "pair", [{:var, "x"}, {:var, "y"}]},
         {:match, {:var, "v"},
          [
            {:arm, "pair", ["y", "x"],
             {:let, "x", {:data, "A"}, {:var, "z"}, {:pair, {:var, "x"}, {:var, "y"}}}}
          ]}}
      )

    out = Muro.IR.Share.funs([straight, captured])

    assert {:let, "v", {:data, "Pair"}, {:con, "Pair", "pair", [{:var, "x"}, {:var, "y"}]},
            {:var, "x"}} = body(out, "straight")

    # `y` is the first field, which is `x`. The let reuses `x`. That
    # binder is renamed, then copied to `z`, so the pair is `(z, x)`
    # and not `(x, x)`.
    assert {:let, "v", {:data, "Pair"}, {:con, "Pair", "pair", [{:var, "x"}, {:var, "y"}]},
            {:pair, {:var, "z"}, {:var, "x"}}} = body(out, "captured")
  end

  # `w`'s arm reuses `x` and `y`. Those are `w`'s fields, not `v`'s.
  # The inner match on `v` stays, and its body is its own first field.
  test "a nested rematch under a shadowing arm does not read the outer field" do
    nest =
      run(
        "nest",
        [{"v", {:data, "Pair"}}, {"w", {:data, "Pair"}}],
        {:match, {:var, "v"},
         [
           {:arm, "pair", ["x", "y"],
            {:match, {:var, "w"},
             [
               {:arm, "pair", ["x", "y"],
                {:match, {:var, "v"}, [{:arm, "pair", ["a", "b"], {:var, "a"}}]}}
             ]}}
         ]}
      )

    out = Muro.IR.Share.funs([nest])

    assert {:match, {:var, "v"},
            [
              {:arm, "pair", ["x", "y"],
               {:match, {:var, "w"},
                [
                  {:arm, "pair", ["x", "y"],
                   {:match, {:var, "v"}, [{:arm, "pair", ["a", "b"], {:var, "a"}}]}}
                ]}}
            ]} = body(out, "nest")
  end

  test "shrink inlines a run whose known argument makes it smaller" do
    pick =
      run(
        "pick",
        [{"b", {:data, "Bool"}}],
        {:match, {:var, "b"}, [{:arm, "true", [], lit(1)}, {:arm, "false", [], lit(2)}]}
      )

    known = run("known", [], {:call, "pick", [{:con, "Bool", "true", []}]})

    open = run("open", [{"b", {:data, "Bool"}}], {:call, "pick", [var: "b"]})

    fact =
      run(
        "fact",
        [{"b", {:data, "Bool"}}],
        {:match, {:var, "b"},
         [
           {:arm, "true", [], {:call, "pick", [var: "b"]}},
           {:arm, "false", [], lit(0)}
         ]}
      )

    funs = [pick, known, open, fact]
    out = Muro.IR.Share.funs(funs)
    one = lit(1)
    zero = lit(0)
    assert body(out, "known") == one
    assert calls(body(out, "open"), "pick") == 1

    assert {:match, {:var, "b"},
            [
              {:arm, "true", [], ^one},
              {:arm, "false", [], ^zero}
            ]} = body(out, "fact")

    off = Muro.IR.Share.funs(funs, cost: false)
    assert {:call, "pick", [{:con, "Bool", "true", []}]} = body(off, "known")
    assert calls(body(Muro.IR.Share.funs(funs, spec: false), "fact"), "pick") == 1
  end

  test "a small comparison commutes onto a match, and a large live arm stays a call" do
    cmp =
      run(
        "cmp",
        [{"b", {:data, "Bool"}}],
        {:match, {:var, "b"},
         [
           {:arm, "true", [], {:con, "Bool", "true", []}},
           {:arm, "false", [], {:con, "Bool", "false", []}}
         ]}
      )

    assert Muro.IR.Share.size(cmp.body) <= 48

    caller =
      run(
        "f",
        [{"b", {:data, "Bool"}}],
        {:match, {:call, "cmp", [var: "b"]},
         [{:arm, "true", [], lit(1)}, {:arm, "false", [], lit(2)}]}
      )

    out = Muro.IR.Share.funs([cmp, caller])
    one = lit(1)
    two = lit(2)

    assert {:match, {:var, "b"}, [{:arm, "true", [], ^one}, {:arm, "false", [], ^two}]} =
             body(out, "f")

    assert calls(body(out, "f"), "cmp") == 0

    tiny = Muro.IR.Share.funs([cmp, caller], inline_small: Muro.IR.Share.size(cmp.body) - 1)
    assert {:match, {:call, "cmp", [var: "b"]}, _} = body(tiny, "f")

    big = run("big", [{"s", :slice}], pad(add(lit(1), lit(2)), 80))
    assert Muro.IR.Share.size(big.body) > 160

    gate =
      run(
        "gate",
        [{"b", {:data, "Bool"}}, {"s", :slice}],
        {:match, {:var, "b"},
         [
           {:arm, "true", [], {:call, "big", [var: "s"]}},
           {:arm, "false", [], {:con, "Bool", "false", []}}
         ]}
      )

    assert Muro.IR.Share.size(gate.body) <= 48

    unknown =
      run(
        "unknown",
        [{"b", {:data, "Bool"}}, {"s", :slice}],
        {:match, {:call, "gate", [var: "b", var: "s"]},
         [{:arm, "true", [], lit(1)}, {:arm, "false", [], lit(0)}]}
      )

    known =
      run(
        "known",
        [{"s", :slice}],
        {:match, {:call, "gate", [{:con, "Bool", "true", []}, {:var, "s"}]},
         [{:arm, "true", [], lit(1)}, {:arm, "false", [], lit(0)}]}
      )

    gated = Muro.IR.Share.funs([big, gate, unknown, known], grow_max: 100_000)
    assert calls(body(gated, "unknown"), "gate") == 1
    assert calls(body(gated, "unknown"), "big") == 0

    # The known arm of `gate` is the call. The match stays on that call.
    # `big` is larger than `dup_max` and is not a fold, so it is not copied.
    assert body(gated, "known") ==
             {:match, {:call, "big", [var: "s"]},
              [{:arm, "true", [], lit(1)}, {:arm, "false", [], lit(0)}]}

    assert calls(body(gated, "known"), "big") == 1
    assert Muro.IR.Share.size(body(gated, "known")) < 20
  end

  test "a generated fold or stream step is not specialised" do
    step =
      {:match, {:con, "Bool", "true", []},
       [{:arm, "true", [], lit(1)}, {:arm, "false", [], lit(0)}]}

    fold =
      run("step0", [{"b", :u8}, {"r", :slice}, {"acc", :u64}], step)
      |> Map.merge(%{generated: true, fold: true})

    stream =
      run("step1", [{"seed", :u64}], step)
      |> Map.put(:generated, true)

    plain = run("plain", [], step)
    use = run("use", [{"s", :slice}], {:bfold, "step0", [], lit(0), {:var, "s"}})
    out = Muro.IR.Share.funs([fold, stream, plain, use])
    assert body_gen(out, "step0") == step
    assert body_gen(out, "step1") == step
    assert body(out, "plain") == lit(1)
  end

  test "a large exported run used once stays a call unless the copy lowers worst-path work" do
    wide = pad(add(cnt("s"), cnt("s")), 90)
    assert Muro.IR.Share.size(wide) > 160
    exported = Map.put(run("wide", [{"s", :slice}], wide), :export, true)
    once = run("once", [{"s", :slice}], {:call, "wide", [var: "s"]})
    hot = run("hot", [{"s", :slice}], add({:call, "wide", [var: "s"]}, cnt("s")))

    stayed = Muro.IR.Share.funs(image([exported, once]), grow_max: 100_000)
    assert calls(body(stayed, "once"), "wide") == 1

    saved = Muro.IR.Share.funs(image([exported, hot]), grow_max: 100_000)
    assert calls(body(saved, "hot"), "wide") == 0
    assert calls(body(saved, "hot"), "count") == 1

    plain = Muro.IR.Share.funs(image([exported, hot]), inline: false)

    assert Muro.IR.Share.path_work(saved, body(saved, "hot")) <
             Muro.IR.Share.path_work(plain, body(plain, "hot"))
  end

  test "a large run whose only shared cost is an erased let stays a call" do
    # `leaf` is heavy only because of the erased let. Its walk has no
    # fold, so charging it at one would make the hoisted copy look
    # cheaper than two calls. `wide` really does fold, and copying it
    # removes that fold from the caller.
    leaf = run("leaf", [{"s", :slice}], {:let, "e", :erased, lit(0), lit(1)})
    big = run("big", [{"s", :slice}], pad(add(leaf_call(), leaf_call()), 90))
    assert Muro.IR.Share.size(big.body) > 160
    caller = run("f", [{"s", :slice}], add({:call, "big", [var: "s"]}, leaf_call()))
    out = Muro.IR.Share.funs([leaf, big, caller], grow_max: 100_000)
    assert calls(body(out, "f"), "big") == 1
    assert calls(body(out, "big"), "leaf") == 1

    wide = run("wide", [{"s", :slice}], pad(add(cnt("s"), cnt("s")), 90))
    assert Muro.IR.Share.size(wide.body) > 160
    g = run("g", [{"s", :slice}], add({:call, "wide", [var: "s"]}, cnt("s")))
    saved = Muro.IR.Share.funs(image([wide, g]), grow_max: 100_000)
    assert calls(body(saved, "g"), "wide") == 0
    assert calls(body(saved, "g"), "count") == 1
  end

  test "a mutually recursive large component does not depend on run order" do
    # One fold in `a`, two in `b`, each above `dup_max`. Copying `a`
    # into `use` still calls `b`, which calls `a`, so the fold stays.
    a = run("a", [{"s", :slice}, {"t", :slice}], pad(add(call2("b"), cnt("s")), 90))

    b =
      run("b", [{"s", :slice}, {"t", :slice}], pad(add(call2("a"), add(cnt("s"), cnt("t"))), 90))

    use = run("use", [{"s", :slice}, {"t", :slice}], add(call2("a"), cnt("s")))
    count = run("count", [{"s", :slice}], {:bfold, "step0", [], lit(0), {:var, "s"}})
    assert Muro.IR.Share.size(a.body) > 160
    assert Muro.IR.Share.size(b.body) > 160

    orders = [
      [count, a, b, use],
      [use, b, a, count],
      [count, b, a, use]
    ]

    [first | rest] = Enum.map(orders, &component_image/1)

    for other <- rest do
      for name <- ["count", "a", "b", "use"] do
        assert body(other, name) == body(first, name)
      end
    end

    assert calls(body(first, "use"), "a") == 1
    assert calls(body(first, "a"), "b") == 1
    assert calls(body(first, "b"), "a") == 1

    # The same component, checked and emitted. Descent is the Nat; the
    # chain only makes the body larger than `dup_max`.
    base = ["foldS", "recurA", "recurB", "recurUse"]
    books = [base, Enum.reverse(base), ["foldS", "recurB", "recurA", "recurUse"]]

    rendered =
      Enum.map(books, fn order ->
        path =
          Path.join(System.tmp_dir!(), "muro_scc_#{:erlang.unique_integer([:positive])}.muro")

        File.write!(path, mutual_book(order))
        {:ok, book} = Muro.Load.file(path)
        book = Muro.Prelude.for_emit(book)
        {:ok, funs} = Muro.IR.elaborate(book)
        assert Muro.IR.Share.size(body(funs, "recurA")) > 160
        {:ok, {_h, src}} = Muro.Emit.C.render(book, "scc")
        {funs, src}
      end)

    [{funs, src} | more] = rendered
    rev = Muro.IR.Share.funs(Enum.reverse(funs), grow_max: 100_000)
    swapped = Muro.IR.Share.funs(swap_runs(funs, "recurA", "recurB"), grow_max: 100_000)
    kept = Muro.IR.Share.funs(funs, grow_max: 100_000)

    for name <- ["foldS", "recurA", "recurB", "recurUse"] do
      assert body(rev, name) == body(kept, name)
      assert body(swapped, name) == body(kept, name)
    end

    assert calls(body(kept, "recurUse"), "recurA") == 1

    texts = fn source ->
      Enum.map(["foldS", "recurA", "recurB", "recurUse"], &c_body(source, &1))
    end

    first_c = texts.(src)

    for {_funs, other} <- more do
      assert texts.(other) == first_c
    end

    assert first_c |> Enum.at(3) =~ "recurA("
  end

  test "a successor fact selects the suc arm" do
    # `x` is a word. The comparison copies `y`'s successor onto it.
    # The layout at the match is not `:nat`, so only the fact says so.
    inner = {:match, {:var, "x"}, [{:arm, "zero", [], lit(0)}, {:arm, "suc", ["k"], {:var, "k"}}]}

    arms = [
      {:arm, "wtrue", [], inner},
      {:arm, "wfalse", [], lit(1)}
    ]

    suc =
      run(
        "sucFact",
        [{"x", :u64}, {"p", :nat}],
        {:let, "y", :nat, {:su, {:var, "p"}}, {:match, eq("x", "y"), arms}}
      )

    zero =
      run(
        "zeroFact",
        [{"x", :u64}, {"p", :nat}],
        {:let, "y", :nat, :ze, {:match, eq("x", "y"), arms}}
      )

    out = Muro.IR.Share.funs([suc, zero])

    assert {:let, "y", :nat, {:su, {:var, "p"}},
            {:match, _, [{:arm, "wtrue", [], {:var, "p"}}, {:arm, "wfalse", [], _}]}} =
             body(out, "sucFact")

    assert {:let, "y", :nat, :ze, {:match, _, [{:arm, "wtrue", [], z}, {:arm, "wfalse", [], _}]}} =
             body(out, "zeroFact")

    assert z == lit(0)
  end

  test "Rust and Zig compute the known end", %{dir: dir} do
    path = Path.join(dir, "hend.muro")
    File.write!(path, File.read!("test/fixtures/share_hend.muro"))
    {:ok, book} = Muro.Load.file(path)
    book = Muro.Prelude.for_emit(book)

    if rustc = @rustc do
      sub = Path.join(dir, "hend_rs")
      File.mkdir_p!(sub)
      {:ok, src} = Muro.Emit.Rust.render(book, "hend")
      File.write!(Path.join(sub, "hend.rs"), src)

      File.write!(Path.join(sub, "main.rs"), """
      mod hend;
      fn main() {
          let b = [97u8, 98];
          let s = hend::muro__slice_of(b.as_ptr(), b.len());
          println!("{} {} {}", hend::known(s), hend::hot(2u64, s), hend::hot(0u64, s));
      }
      """)

      {out, 0} =
        System.cmd(rustc, ~w(--edition 2021 -A warnings main.rs -o main_rs),
          cd: sub,
          stderr_to_stdout: true
        )

      assert out == ""
      assert {"1 3 2\n", 0} = System.cmd(Path.join(sub, "main_rs"), [])
    end

    if zig = @zig do
      sub = Path.join(dir, "hend_zig")
      File.mkdir_p!(sub)
      {:ok, src} = Muro.Emit.Zig.render(book, "hend")
      File.write!(Path.join(sub, "hend.zig"), src)

      File.write!(Path.join(sub, "main.zig"), """
      const std = @import("std");
      const hend = @import("hend.zig");
      pub fn main() !void {
          const a = std.heap.page_allocator;
          const raw = [_]u8{97, 98};
          const b: []const u8 = &raw;
          const s = hend.muro__slice_of(b.ptr, b.len);
          const out = std.fs.File.stdout();
          var buf: [64]u8 = undefined;
          const line = try std.fmt.bufPrint(&buf, "{d} {d} {d}\\n", .{
            try hend.known(a, s), try hend.hot(a, 2, s), try hend.hot(a, 0, s)
          });
          try out.writeAll(line);
      }
      """)

      assert {"1 3 2\n", 0} =
               System.cmd(zig, ~w(run main.zig --global-cache-dir) ++ [Path.join(sub, ".zcache")],
                 cd: sub
               )
    end
  end

  defp eq(a, b), do: {:wrd, :u64, :eq, [{:var, a}, {:var, b}]}

  defp pad(t, 0), do: t
  defp pad(t, n), do: pad(add(t, lit(n)), n - 1)

  defp false_arm(t), do: find_arm(t, ["wfalse", "false"])
  defp true_arm(t), do: find_arm(t, ["wtrue", "true"])

  defp find_arm({:let, _, _, _, b}, tags), do: find_arm(b, tags)

  defp find_arm({:match, _, arms}, tags) do
    Enum.find_value(arms, fn
      {:arm, c, _, tm} -> if c in tags, do: tm
      _ -> nil
    end)
  end

  defp arm_named({:match, _, arms}, name) do
    Enum.find_value(arms, fn
      {:arm, ^name, _, tm} -> tm
      _ -> nil
    end)
  end

  defp arm_named({:let, _, _, _, b}, name), do: arm_named(b, name)

  defp let_body({:let, _, _, _, {:match, _, _} = m}), do: m
  defp let_body({:let, _, _, _, b}), do: let_body(b)

  defp leaf_call, do: {:call, "leaf", [var: "s"]}
  defp call2(name), do: {:call, name, [var: "s", var: "t"]}

  defp component_image(funs) do
    Muro.IR.Share.funs(funs, grow_max: 100_000)
  end

  defp swap_runs(funs, x, y) do
    ix = Enum.find_index(funs, &(&1.name == x and not Map.get(&1, :generated, false)))
    iy = Enum.find_index(funs, &(&1.name == y and not Map.get(&1, :generated, false)))
    a = Enum.at(funs, ix)
    b = Enum.at(funs, iy)
    funs |> List.replace_at(ix, b) |> List.replace_at(iy, a)
  end

  # Body of one C function, braces included, from the opening brace.
  defp c_body(src, name) do
    [_, rest] = String.split(src, ~r/\n[^\n;]*\b#{name}\([^;\n]*\)\s*\{/, parts: 2)
    {text, _} = take_braced(rest, 1, [])
    text
  end

  defp take_braced(<<"{" <> rest>>, n, acc), do: take_braced(rest, n + 1, ["{" | acc])
  defp take_braced(<<"}" <> rest>>, 1, acc), do: {IO.iodata_to_binary(Enum.reverse(acc)), rest}
  defp take_braced(<<"}" <> rest>>, n, acc), do: take_braced(rest, n - 1, ["}" | acc])

  defp take_braced(<<c::utf8, rest::binary>>, n, acc),
    do: take_braced(rest, n, [<<c::utf8>> | acc])

  defp mutual_book(order) do
    # A closed chain of `toU64` folds away at elaborate. `w` does not.
    chain = nest_word("w", 90)

    defs = %{
      "foldS" => """
      def foldS : run Π (+ s : Slice) → U64 :=
        λ (+ s : Slice) →
          sliceFold U64 (toU64 0)
            (λ (_b : U8) → λ (_r : Slice) → λ (acc : U64) → addi acc (toU64 1))
            s
      """,
      "recurA" => """
      def recurA : run Π (n : Nat) → Π (+ s : Slice) → Π (+ t : Slice) → Π (+ w : U64) → U64 :=
        λ (n : Nat) → λ (+ s : Slice) → λ (+ t : Slice) → λ (+ w : U64) →
          match n motive (λ _ → U64)
            | 0 => toU64 0
            | suc k => addi (recurB k s t w) (addi (foldS s) #{chain})
      """,
      "recurB" => """
      def recurB : run Π (n : Nat) → Π (+ s : Slice) → Π (+ t : Slice) → Π (+ w : U64) → U64 :=
        λ (n : Nat) → λ (+ s : Slice) → λ (+ t : Slice) → λ (+ w : U64) →
          match n motive (λ _ → U64)
            | 0 => toU64 1
            | suc k => addi (recurA k s t w) (addi (foldS s) (addi (foldS t) #{chain}))
      """,
      "recurUse" => """
      def recurUse : run Π (n : Nat) → Π (+ s : Slice) → Π (+ t : Slice) → Π (+ w : U64) → U64 :=
        λ (n : Nat) → λ (+ s : Slice) → λ (+ t : Slice) → λ (+ w : U64) →
          addi (recurA n s t w) (foldS s)
      """
    }

    Enum.map_join(order, "\n", &Map.fetch!(defs, &1))
  end

  defp nest_word(body, 0), do: body
  defp nest_word(body, n), do: nest_word("(addi (#{body}) w)", n - 1)
end
