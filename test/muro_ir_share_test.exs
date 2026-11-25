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
        a = folds(full, body(full, f.name))
        b = folds(less, body(less, f.name))
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

    keys = [share: true, inline: true, inline_max: 9, grow_max: 7]
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

  test "inlining never folds more than inline: false on the worst path" do
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
      assert folds(full, body(full, "f")) <= folds(plain, body(plain, "f"))
      assert folds(full, body(full, "f")) == 2
      assert folds(plain, body(plain, "f")) == 2
      assert calls(body(full, "f"), "pickCount") == 1
    end
  end

  test "the heavy-work oracle counts folds, streams and uncons" do
    stream = {:stream, lit(0), [], "step"}
    assert folds([], stream) == 1
    assert folds([], {:uncons, stream}) == 2
    assert folds([], {:bfold, "step", [], lit(0), {:var, "s"}}) == 1

    assert folds(
             [],
             {:match, lit(0), [{:arm, "a", [], stream}, {:arm, "b", [], {:uncons, stream}}]}
           ) == 2
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

  # Heavy work on the worst path through `t`, each call expanded through
  # the bodies in `fs`: folds, streams, and uncons, as in Share.work/2.
  defp folds(fs, {:call, "count", args}), do: 1 + folds(fs, args)

  defp folds(fs, {:call, name, args}) do
    case Enum.find(fs, &(&1.name == name and not Map.get(&1, :generated, false))) do
      nil -> folds(fs, args)
      f -> folds(fs, f.body) + folds(fs, args)
    end
  end

  defp folds(fs, {:match, s, arms}),
    do:
      folds(fs, s) +
        (arms |> Enum.map(fn {:arm, _, _, tm} -> folds(fs, tm) end) |> Enum.max(fn -> 0 end))

  defp folds(fs, {:bfold, _, caps, z, bytes}),
    do: 1 + folds(fs, Enum.map(caps, &elem(&1, 1))) + folds(fs, z) + folds(fs, bytes)

  defp folds(fs, {:stream, seed, caps, _step}),
    do: 1 + folds(fs, seed) + folds(fs, Enum.map(caps, &elem(&1, 1)))

  defp folds(fs, {:uncons, stream}), do: 1 + folds(fs, stream)

  defp folds(fs, t) when is_tuple(t), do: folds(fs, Tuple.to_list(t))
  defp folds(fs, l) when is_list(l), do: l |> Enum.map(&folds(fs, &1)) |> Enum.sum()
  defp folds(_fs, _), do: 0

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
              (unsigned long long)both(&yes, s), (unsigned long long)both(&no, s),
              (unsigned long long)nested(&yes, s), (unsigned long long)nested(&no, s),
              (unsigned long long)branchy(&yes, s), (unsigned long long)branchy(&no, s));
          }
        """
      end)

    """
    #include <stdio.h>
    #include "shared.h"
    int main(void) {
      Pick yes = {.muro__field_tag = muro__tag_Pick_yes};
      Pick no = {.muro__field_tag = muro__tag_Pick_no};
      {
        static const uint8_t b[] = {97, 98, 99};
        muro__slice s = {b, 3};
        printf("twice %llu\\n", (unsigned long long)twice(s));
        printf("viaWrap %llu\\n", (unsigned long long)viaWrap(s));
        printf("branchy-no %llu\\n", (unsigned long long)branchy(&no, s));
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
end
