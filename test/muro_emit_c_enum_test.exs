defmodule Muro.EmitCEnumTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "all-nullary data is an enum by value, and a match switches on the tag" do
    dir = tmp_dir()
    path = Path.join(dir, "flags.muro")

    File.write!(path, """
    data Bool : Type where
      true : Bool
      false : Bool

    data Color : Type where
      red : Color
      green : Color
      blue : Color

    def not : run Π (b : Bool) → Bool :=
      λ (b : Bool) →
        match b motive (λ _ → Bool)
          | true => false
          | false => true

    def u64eq : run Π (x : U64) → Π (y : U64) → Bool :=
      λ (x : U64) → λ (y : U64) →
        match (eqi x y) motive (λ _ → Bool)
          | wtrue => true
          | wfalse => false

    def and : run Π (a : Bool) → Π (b : Bool) → Bool :=
      λ (a : Bool) → λ (b : Bool) →
        match a motive (λ _ → Bool)
          | true => b
          | false => false

    def nest : run Π (a : Bool) → Π (b : Bool) → Bool :=
      λ (a : Bool) → λ (b : Bool) →
        match a motive (λ _ → Bool)
          | true =>
              (match b motive (λ _ → Bool)
                | true => true
                | false => false)
          | false => false

    def paint : run Π (c : Color) → U64 :=
      λ (c : Color) →
        match c motive (λ _ → U64)
          | red => toU64 1
          | green => toU64 2
          | blue => toU64 3
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
    header = File.read!(Path.join(dir, "flags.h"))
    source = File.read!(Path.join(dir, "flags.c"))

    true_k = Muro.Emit.C.source_id("true")
    false_k = Muro.Emit.C.source_id("false")
    true_tag = Muro.Emit.C.ctor_tag("Bool", "true")
    false_tag = Muro.Emit.C.ctor_tag("Bool", "false")
    bool_tag_ty = Muro.Emit.C.ctor_tag_type("Bool")
    color_tag_ty = Muro.Emit.C.ctor_tag_type("Color")
    red_tag = Muro.Emit.C.ctor_tag("Color", "red")

    assert header =~ "typedef enum #{bool_tag_ty}"
    assert header =~ "#{true_tag} = 0"
    assert header =~ "#{false_tag} = 1"
    assert header =~ "} Bool;"
    refute header =~ "typedef struct Bool"
    refute header =~ "struct Bool "
    refute header =~ "Bool *"

    assert header =~ "typedef enum #{color_tag_ty}"
    assert header =~ "#{red_tag} = 0"
    assert header =~ "} Color;"
    refute header =~ "Color *"

    assert header =~ "Bool not(Bool b);"
    assert header =~ "Bool u64eq(uint64_t x, uint64_t y);"
    assert header =~ "Bool and(Bool a, Bool b);"
    assert header =~ "Bool nest(Bool a, Bool b);"
    assert header =~ "uint64_t paint(Color c);"

    assert source =~ "static Bool #{true_k}(void) { return #{true_tag}; }"
    assert source =~ "static Bool #{false_k}(void) { return #{false_tag}; }"
    refute source =~ Muro.Emit.Name.gen("obj_Bool_#{true_k}")
    refute source =~ "Bool *"
    refute source =~ "switch (muro__s_0->muro__field_tag)"
    refute source =~ "switch (muro__s_0.muro__field_tag)"
    assert source =~ "switch (muro__s_0)"
    # A match in tail position returns from each arm; no temporary.
    assert source =~ "return #{true_tag};"
    assert source =~ "return #{false_tag};"
    refute source =~ "muro__t_0"
    # Comparisons and matches do not allocate a Bool.
    for fun <- ["Bool not(", "Bool u64eq(", "Bool and(", "Bool nest(", "uint64_t paint("] do
      body = slice_after(source, fun)
      refute body =~ "muro__ALLOC", fun
    end

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include "flags.h"

    int main(void) {
      if (not(#{true_tag}) != #{false_tag}) return 1;
      if (not(#{false_tag}) != #{true_tag}) return 2;
      if (u64eq((uint64_t)3, (uint64_t)3) != #{true_tag}) return 3;
      if (u64eq((uint64_t)3, (uint64_t)4) != #{false_tag}) return 4;
      if (and(#{true_tag}, #{false_tag}) != #{false_tag}) return 5;
      if (and(#{true_tag}, #{true_tag}) != #{true_tag}) return 6;
      if (nest(#{true_tag}, #{true_tag}) != #{true_tag}) return 7;
      if (nest(#{true_tag}, #{false_tag}) != #{false_tag}) return 8;
      if (nest(#{false_tag}, #{true_tag}) != #{false_tag}) return 9;
      if (paint(#{red_tag}) != 1) return 10;
      if (paint(#{Muro.Emit.C.ctor_tag("Color", "green")}) != 2) return 11;
      if (paint(#{Muro.Emit.C.ctor_tag("Color", "blue")}) != 3) return 12;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "flags.c", "flags.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(flags main), "OK\n")
  end

  test "a pair and an Opt of all-nullary data pack the tag, and a mixed type stays boxed" do
    dir = tmp_dir()
    path = Path.join(dir, "pack.muro")

    File.write!(path, """
    data Bool : Type where
      true : Bool
      false : Bool

    data Wrap : Type where
      bare : Wrap
      box : Nat → Wrap

    def both : run Π (a : Bool) → Π (b : Bool) → (Bool × Bool) :=
      λ (a : Bool) → λ (b : Bool) → (a, b)

    def fstB : run Π (p : Bool × Bool) → Bool :=
      λ (p : Bool × Bool) → let (x, y) = p in x

    def sndB : run Π (p : Bool × Bool) → Bool :=
      λ (p : Bool × Bool) → let (x, y) = p in y

    def someT : run Opt Bool := wsome true
    def noneB : run Opt Bool := wnone

    def fromO : run Π (o : Opt Bool) → Bool :=
      λ (o : Opt Bool) →
        match o motive (λ _ → Bool)
          | wsome b => b
          | wnone => false

    def pick : run Π (b : Bool) → Wrap :=
      λ (b : Bool) →
        match b motive (λ _ → Wrap)
          | true => bare
          | false => box 0
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
    header = File.read!(Path.join(dir, "pack.h"))
    source = File.read!(Path.join(dir, "pack.c"))
    true_tag = Muro.Emit.C.ctor_tag("Bool", "true")
    false_tag = Muro.Emit.C.ctor_tag("Bool", "false")
    wrap = Muro.Emit.C.source_id("Wrap")
    bare_obj = Muro.Emit.Name.gen("obj_#{wrap}_bare")

    assert header =~ "struct muro__opt_d_Bool { uint8_t tag; Bool val; };"
    refute header =~ "Bool *val"
    refute header =~ "Wrap val"
    assert header =~ "void *both(Bool a, Bool b);"
    assert header =~ "Bool fstB(void *p);"
    assert header =~ "#{wrap} *pick(Bool b);"

    assert source =~ "(void *)(uintptr_t)(a)"
    assert source =~ "(Bool)(uintptr_t)"
    assert source =~ "static #{wrap} #{bare_obj} ="
    assert source =~ "static #{wrap} *bare(void) { return &#{bare_obj}; }"
    assert source =~ "#{wrap} *box("
    assert source =~ "muro__ALLOC(sizeof *muro__p)"

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include <stdlib.h>
    #include "pack.h"

    static int nats(muro__nat *n) {
      int k = 0;
      while (n->muro__field_tag == 1) {
        n = n->muro__field_suc;
        k++;
      }
      return k;
    }

    int main(void) {
      void *p = both(#{true_tag}, #{false_tag});
      if (fstB(p) != #{true_tag}) return 1;
      if (sndB(p) != #{false_tag}) return 2;
      muro__opt_d_Bool s = someT();
      if (s.tag != 1 || s.val != #{true_tag}) return 3;
      if (fromO(s) != #{true_tag}) return 4;
      muro__opt_d_Bool n = noneB();
      if (n.tag != 0) return 5;
      if (fromO(n) != #{false_tag}) return 6;
      #{wrap} *w = pick(#{true_tag});
      if (w->muro__field_tag != 0) return 7;
      #{wrap} *u = pick(#{false_tag});
      if (u->muro__field_tag != 1) return 8;
      if (nats(u->muro__as.box.muro__f_0) != 0) return 9;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "pack.c", "pack.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(pack main), "OK\n")
  end

  test "a two-constructor enum and its constructors compile and run" do
    dir = tmp_dir()
    path = Path.join(dir, "tok.muro")

    File.write!(path, """
    data Flag : Type where
      zed : Flag
      wob : Flag

    def flip : run Π (t : Flag) → Flag :=
      λ (t : Flag) →
        match t motive (λ _ → Flag)
          | zed => wob
          | wob => zed
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
    header = File.read!(Path.join(dir, "tok.h"))
    source = File.read!(Path.join(dir, "tok.c"))
    zed_tag = Muro.Emit.C.ctor_tag("Flag", "zed")
    wob_tag = Muro.Emit.C.ctor_tag("Flag", "wob")
    zed = Muro.Emit.C.source_id("zed")
    wob = Muro.Emit.C.source_id("wob")

    assert header =~ "typedef enum #{Muro.Emit.C.ctor_tag_type("Flag")}"
    assert header =~ "#{zed_tag} = 0"
    assert header =~ "#{wob_tag} = 1"
    assert header =~ "} Flag;"
    refute header =~ "typedef struct Flag"
    refute header =~ "Flag *"
    assert header =~ "Flag flip(Flag t);"
    assert source =~ "static Flag #{zed}(void) { return #{zed_tag}; }"
    assert source =~ "static Flag #{wob}(void) { return #{wob_tag}; }"
    refute slice_after(source, "Flag flip(") =~ "muro__ALLOC"

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include "tok.h"

    int main(void) {
      Flag t = #{zed_tag};
      if (t != #{zed_tag}) return 1;
      if (flip(t) != #{wob_tag}) return 2;
      if (flip(flip(t)) != #{zed_tag}) return 3;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "tok.c", "tok.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(tok main), "OK\n")
  end

  test "Maybe Bool packs the tag in the void field and unpacks on match" do
    dir = tmp_dir()
    path = Path.join(dir, "mb.muro")

    File.write!(path, """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    def fromM : run Π (m : Maybe Bool) → Bool :=
      λ (m : Maybe Bool) →
        match m motive (λ _ → Bool)
          | nothing => false
          | just b => b

    def wrap : run Π (b : Bool) → Maybe Bool :=
      λ (b : Bool) → just b
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
    header = File.read!(Path.join(dir, "mb.h"))
    source = File.read!(Path.join(dir, "mb.c"))
    true_tag = Muro.Emit.C.ctor_tag("Bool", "true")
    false_tag = Muro.Emit.C.ctor_tag("Bool", "false")

    assert header =~ "void *muro__f_0;"
    assert header =~ "Bool fromM(Maybe *m);"
    assert source =~ "(void *)(uintptr_t)"
    assert source =~ "(Bool)(uintptr_t)"

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include "mb.h"

    int main(void) {
      Maybe *m = wrap(#{true_tag});
      if (fromM(m) != #{true_tag}) return 1;
      Maybe *n = wrap(#{false_tag});
      if (fromM(n) != #{false_tag}) return 2;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "mb.c", "mb.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(mb main), "OK\n")
  end

  test "a stream of all-nullary data packs the seed and a captured flag in the environment" do
    dir = tmp_dir()
    path = Path.join(dir, "flags_stream.muro")

    File.write!(path, """
    data Bool : Type where
      true : Bool
      false : Bool

    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def flags : run Stream Bool :=
      unfold true (λ (b : Bool) → (b, false))

    def hdB : run Π (s : Stream Bool) → Bool :=
      λ (s : Stream Bool) → head s

    def keep : run Π (b : Bool) → Stream Bool :=
      λ (b : Bool) →
        unfold true (λ (_ : Bool) → (b, true))
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
    header = File.read!(Path.join(dir, "flags_stream.h"))
    source = File.read!(Path.join(dir, "flags_stream.c"))
    true_tag = Muro.Emit.C.ctor_tag("Bool", "true")
    false_tag = Muro.Emit.C.ctor_tag("Bool", "false")

    assert header =~ "muro__stream *flags(void);"
    assert header =~ "Bool hdB(muro__stream *s);"
    assert header =~ "muro__stream *keep(Bool b);"
    refute header =~ "Bool *"
    assert source =~ "(void *)(uintptr_t)"
    assert source =~ "(Bool)(uintptr_t)"
    assert source =~ "muro__env_1"
    assert source =~ "muro__ep_1->b = (void *)(uintptr_t)"
    refute source =~ "Bool *"
    refute source =~ "obj_Bool_"
    # Nat helpers still use muro__field_tag; the stream runs must not.
    for fun <- ["muro__stream *flags(", "Bool hdB(", "muro__stream *keep("] do
      body = fun_body(source, fun)
      refute body =~ "->muro__field_tag", fun
      refute body =~ "obj_Bool_", fun
    end

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include "flags_stream.h"

    int main(void) {
      muro__stream *s = flags();
      if (hdB(s) != #{true_tag}) return 1;
      if (hdB(s) != #{true_tag}) return 2;
      muro__stream *k = keep(#{false_tag});
      if (hdB(k) != #{false_tag}) return 3;
      muro__stream *t = keep(#{true_tag});
      if (hdB(t) != #{true_tag}) return 4;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "flags_stream.c", "flags_stream.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(flags_stream main), "OK\n")
  end

  test "a lambda applied on the spot takes and returns an unboxed enum, and may capture one" do
    dir = tmp_dir()
    path = Path.join(dir, "apply_flag.muro")

    File.write!(path, """
    data Bool : Type where
      true : Bool
      false : Bool

    def applyNot : run Π (b : Bool) → Bool :=
      λ (b : Bool) →
        (λ (x : Bool) →
          match x motive (λ _ → Bool)
            | true => false
            | false => true) b

    def andThen : run Π (a : Bool) → Π (b : Bool) → Bool :=
      λ (a : Bool) → λ (b : Bool) →
        (λ (x : Bool) →
          match x motive (λ _ → Bool)
            | true => a
            | false => false) b
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
    header = File.read!(Path.join(dir, "apply_flag.h"))
    source = File.read!(Path.join(dir, "apply_flag.c"))
    true_tag = Muro.Emit.C.ctor_tag("Bool", "true")
    false_tag = Muro.Emit.C.ctor_tag("Bool", "false")

    assert header =~ "Bool applyNot(Bool b);"
    assert header =~ "Bool andThen(Bool a, Bool b);"
    refute header =~ "Bool *"
    refute source =~ "Bool *"
    refute source =~ "obj_Bool_"
    # Nat helpers in the same file still allocate; the Bool runs must not.
    for fun <- ["Bool applyNot(", "Bool andThen("] do
      body = fun_body(source, fun)
      refute body =~ "->muro__field_tag", fun
      refute body =~ "muro__ALLOC", fun
    end

    assert source =~ "if (muro__s_1 == #{true_tag})"
    refute source =~ "switch ("

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include "apply_flag.h"

    int main(void) {
      if (applyNot(#{true_tag}) != #{false_tag}) return 1;
      if (applyNot(#{false_tag}) != #{true_tag}) return 2;
      if (andThen(#{true_tag}, #{true_tag}) != #{true_tag}) return 3;
      if (andThen(#{true_tag}, #{false_tag}) != #{false_tag}) return 4;
      if (andThen(#{false_tag}, #{true_tag}) != #{false_tag}) return 5;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "apply_flag.c", "apply_flag.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(apply_flag main), "OK\n")
  end

  test "mutually referenced boxed data does not loop, and an all-nullary field stays an enum" do
    dir = tmp_dir()
    path = Path.join(dir, "mutual.muro")

    File.write!(path, """
    data Flag : Type where
      zed : Flag
      wob : Flag

    data Node : Type where
      tip : Node
      cell : Flag → Forest → Node

    data Forest : Type where
      empty : Forest
      cons : Node → Forest → Forest

    def flip : run Π (t : Flag) → Flag :=
      λ (t : Flag) →
        match t motive (λ _ → Flag)
          | zed => wob
          | wob => zed

    def tipN : run Node := tip
    """)

    # A walk of field types through `ctype` would loop on Node ↔ Forest.
    task =
      Task.async(fn ->
        capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
        :ok
      end)

    assert {:ok, :ok} ==
             (Task.yield(task, 15_000) || Task.shutdown(task, :brutal_kill)),
           "C emit looped or ran too long on mutually referenced data"

    header = File.read!(Path.join(dir, "mutual.h"))
    source = File.read!(Path.join(dir, "mutual.c"))
    zed_tag = Muro.Emit.C.ctor_tag("Flag", "zed")
    wob_tag = Muro.Emit.C.ctor_tag("Flag", "wob")
    node = Muro.Emit.C.source_id("Node")
    forest = Muro.Emit.C.source_id("Forest")

    assert header =~ "typedef enum #{Muro.Emit.C.ctor_tag_type("Flag")}"
    assert header =~ "#{zed_tag} = 0"
    assert header =~ "} Flag;"
    refute header =~ "typedef struct Flag"
    refute header =~ "Flag *"
    assert header =~ "Flag flip(Flag t);"
    assert header =~ "#{node} *tipN(void);"
    assert header =~ "typedef struct #{node} #{node};"
    assert header =~ "typedef struct #{forest} #{forest};"
    assert header =~ "Flag muro__f_0;"
    refute header =~ "Flag *muro__f_0"
    refute source =~ "Flag *"
    refute slice_after(source, "Flag flip(") =~ "muro__ALLOC"

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include "mutual.h"

    int main(void) {
      if (flip(#{zed_tag}) != #{wob_tag}) return 1;
      if (flip(#{wob_tag}) != #{zed_tag}) return 2;
      #{node} *n = tipN();
      if (n->muro__field_tag != 0) return 3;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "mutual.c", "mutual.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(mutual main), "OK\n")
  end

  test "a type whose constructors have only erased fields is still an enum" do
    dir = tmp_dir()
    path = Path.join(dir, "ghost.muro")

    File.write!(path, """
    data Ghost : Type where
      ghost : Π (- n : Nat) → Ghost
      visible : Ghost

    def flipG : run Π (t : Ghost) → Ghost :=
      λ (t : Ghost) →
        match t motive (λ _ → Ghost)
          | ghost _ => visible
          | visible => ghost 0
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "c"]) end)
    header = File.read!(Path.join(dir, "ghost.h"))
    source = File.read!(Path.join(dir, "ghost.c"))
    typ = Muro.Emit.C.source_id("Ghost")
    ghost = Muro.Emit.C.source_id("ghost")
    visible = Muro.Emit.C.source_id("visible")
    ghost_tag = Muro.Emit.C.ctor_tag("Ghost", "ghost")
    visible_tag = Muro.Emit.C.ctor_tag("Ghost", "visible")

    assert header =~ "typedef enum #{Muro.Emit.C.ctor_tag_type("Ghost")}"
    assert header =~ "#{ghost_tag} = 0"
    assert header =~ "#{visible_tag} = 1"
    assert header =~ "} #{typ};"
    refute header =~ "typedef struct #{typ}"
    refute header =~ "#{typ} *"
    assert header =~ "#{typ} flipG(#{typ} t);"
    assert source =~ "static #{typ} #{ghost}(void) { return #{ghost_tag}; }"
    assert source =~ "static #{typ} #{visible}(void) { return #{visible_tag}; }"
    refute source =~ Muro.Emit.Name.gen("obj_#{typ}_#{ghost}")
    refute slice_after(source, "#{typ} flipG(") =~ "muro__ALLOC"

    File.write!(Path.join(dir, "main.c"), """
    #include <stdio.h>
    #include "ghost.h"

    int main(void) {
      if (flipG(#{ghost_tag}) != #{visible_tag}) return 1;
      if (flipG(#{visible_tag}) != #{ghost_tag}) return 2;
      printf("OK\\n");
      return 0;
    }
    """)

    cc!(dir, "ghost.c", "ghost.o")
    cc!(dir, "main.c", "main.o")
    link_run!(dir, ~w(ghost main), "OK\n")
  end

  defp slice_after(source, fun) do
    [_, rest] = String.split(source, fun, parts: 2)
    rest
  end

  defp fun_body(source, fun) do
    case String.split(slice_after(source, fun), "\n}\n", parts: 2) do
      [body, _] -> body
      [body] -> body
    end
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_c_enum_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    dir
  end

  defp cc!(dir, src, obj) do
    {out, status} =
      System.cmd(
        "cc",
        ~w(-Wall -Wextra -Werror -std=c11 -c) ++ [src, "-o", obj],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
  end

  defp link_run!(dir, objs, expected) do
    {out, status} =
      System.cmd(
        "cc",
        ~w(-Wall -Wextra -Werror -std=c11) ++ Enum.map(objs, &(&1 <> ".o")) ++ ["-o", "main"],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
    {run, status} = System.cmd(Path.join(dir, "main"), [], cd: dir, stderr_to_stdout: true)
    assert status == 0, run
    assert run == expected
  end
end
