defmodule Muro.EmitCGapsTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  # The host program below is the muro-http shape: two books in one
  # translation unit, a constructor word instead of a tag-to-string map,
  # the named stepper constants, and an I64 of −1. A second session book
  # is prefixed so its entry points link beside the first.

  @conn """
  data Piece : Type where
    piece-chunk : Piece
    piece-req : Piece
    piece-bad : Piece

  data Reply : Type where
    reply-ok : Reply
    reply-bad : Reply

  session conn := recv Piece (send Reply end)
  """

  @peer """
  session peer := recv Nat end
  session bitp := recv Bit end
  session unitp := recv Unit end
  session pickp := branch end end
  """

  @wide """
  session wide (a : Nat) (b : Nat) := send Nat end
  """

  @plain """
  def n : run Nat := 0
  """

  @sent """
  def neg : run I64 := subi (toI64 0) (toI64 1)

  def below : run Π (status : I64) → Nat :=
    λ (status : I64) →
      match (lti status (toI64 0)) motive (λ _ → Nat)
        | wtrue => suc 0
        | wfalse => 0
  """

  @left """
  def mark : run internal Nat := 0
  def seen : run Nat := mark
  """

  @right """
  def mark : run internal Nat := suc 0
  def other : run Nat := mark
  """

  @hook_zero """
  def mark : run internal Nat := 0
  def hook : run Nat := 0
  """

  @hook_one """
  def mark : run internal Nat := suc 0
  def hook : run Nat := suc 0
  """

  @id """
  data Path : Type where
    path-health : Path
    path-bad : Path
    path-id : Path

  data IdClass : Type where
    id-none : IdClass
    id-bad : IdClass
    id-unknown : IdClass
    id-missing : IdClass
    id-present : IdClass

  def pathOf : run Π (n : Nat) → Path :=
    λ (n : Nat) →
      match n motive (λ _ → Path)
        | 0 => path-health
        | suc k =>
            match k motive (λ _ → Path)
              | 0 => path-bad
              | suc _ => path-id

  def idClassOf : run Π (n : Nat) → IdClass :=
    λ (n : Nat) →
      match (pathOf n) motive (λ _ → IdClass)
        | path-health => id-none
        | path-bad => id-bad
        | path-id => id-unknown

  def idFrom : run Π (n : Nat) → IdClass :=
    λ (n : Nat) →
      match n motive (λ _ → IdClass)
        | 0 => id-missing
        | suc _ => id-present

  def idNumber : run Π (n : Nat) → I64 :=
    λ (n : Nat) →
      match (idClassOf n) motive (λ _ → I64)
        | id-none => toI64 0
        | id-bad => toI64 0
        | id-unknown => toI64 1
        | id-missing => toI64 0
        | id-present => toI64 0

  def idCount : run Π (n : Nat) → I64 :=
    λ (n : Nat) →
      match (idFrom n) motive (λ _ → I64)
        | id-none => toI64 0
        | id-bad => toI64 0
        | id-unknown => toI64 0
        | id-missing => toI64 2
        | id-present => toI64 3

  def idTag : run Π (i : IdClass) → Nat :=
    λ (i : IdClass) →
      match i motive (λ _ → Nat)
        | id-none => 0
        | id-bad => suc 0
        | id-unknown => suc (suc 0)
        | id-missing => suc (suc (suc 0))
        | id-present => suc (suc (suc (suc 0)))
  """

  test "a word step, named enums, a signed sentinel, and two headers compile together" do
    dir = tmp_dir()
    {conn_h, _conn_c} = emit!(dir, "conn", @conn)
    {peer_h, peer_c} = emit!(dir, "peer", @peer, c_prefix: "p_")
    {_plain_h, _plain_c} = emit!(dir, "plain", @plain)
    {_sent_h, _sent_c} = emit!(dir, "sent", @sent)
    {left_h, left_c} = emit!(dir, "left", @left)
    {_right_h, _right_c} = emit!(dir, "right", @right)
    {zero_h, zero_c} = emit!(dir, "ha", @hook_zero, c_prefix: "a_")
    {_one_h, _one_c} = emit!(dir, "hb", @hook_one, c_prefix: "b_")

    chunk = Muro.Emit.C.ctor_word("conn", "Piece", "piece-chunk")
    reply_ok = Muro.Emit.C.ctor_word("conn", "Reply", "reply-ok")
    reply_bad = Muro.Emit.C.ctor_word("conn", "Reply", "reply-bad")
    reply_tag = Muro.Emit.C.ctor_tag("Reply", "reply-ok")

    assert conn_h =~ "#ifndef MURO__PRELUDE"
    assert conn_h =~ "typedef enum muro__sess_dir"
    assert conn_h =~ "MURO_SESS_SEND = 1"
    assert conn_h =~ "MURO_SESS_RECV = 2"
    assert conn_h =~ "MURO_SESS_PICK = 4"
    assert conn_h =~ "MURO_SESS_DATA = 8"
    assert conn_h =~ "muro__sess_conn_step("
    assert conn_h =~ "muro__sess_conn_step_word("
    assert conn_h =~ "#{chunk} = 0"
    assert conn_h =~ "#{reply_ok} = 3"
    assert conn_h =~ "#{reply_bad} = 4"
    assert conn_h =~ "#{reply_tag} = 0"
    assert conn_h =~ "#define MURO__SESS_SLOTS 1"
    assert peer_h =~ "#define MURO__SESS_SLOTS 1"
    assert peer_h =~ "p_muro__sess_peer_step_word("
    assert peer_h =~ "p_muro__sess_bitp_step_word("
    assert peer_h =~ "p_muro__sess_unitp_step_word("
    assert peer_h =~ "p_muro__sess_pickp_step_word("
    assert peer_h =~ "p_muro__sess_step_word("
    assert peer_c =~ "static muro__sess_res muro__sess_word_step("
    assert peer_c =~ ~s|muro__sess_lit(bad.expected, sizeof bad.expected, "word")|
    refute peer_c =~ "value.tag = (uint8_t)tag"
    assert length(:binary.matches(peer_c, "static muro__sess_res muro__sess_word_step(")) == 1

    refute left_h =~ "mark("
    assert left_c =~ "__attribute__((unused)) static "
    assert left_c =~ "mark("
    assert zero_h =~ "a_hook("
    refute zero_h =~ "a_mark("
    refute zero_h =~ "mark("
    assert zero_c =~ "static "
    assert zero_c =~ "a_mark("

    File.write!(Path.join(dir, "main.c"), """
    #include "plain.h"
    #include "conn.h"
    #include "peer.h"
    #include "sent.h"
    #include "left.h"
    #include "right.h"
    #include "ha.h"
    #include "hb.h"
    #include <stdio.h>
    #include <string.h>

    _Static_assert(MURO_SESS_SEND == 1, "send");
    _Static_assert(MURO_SESS_RECV == 2, "recv");
    _Static_assert(MURO_SESS_NAT == 1, "nat");
    _Static_assert(MURO_SESS_BIT == 2, "bit");
    _Static_assert(MURO_SESS_UNIT == 3, "unit");
    _Static_assert(MURO_SESS_PICK == 4, "pick");
    _Static_assert(MURO_SESS_DATA == 8, "data");
    _Static_assert(#{reply_tag} == 0, "reply tag");
    _Static_assert(#{chunk} == 0, "chunk word");
    _Static_assert(#{reply_ok} == 3, "reply-ok word");
    _Static_assert(#{reply_bad} == 4, "reply-bad word");

    int main(void) {
      muro__sess_res r = muro__sess_conn_init();
      if (r.status != MURO_SESS_OK) return 1;
      r = muro__sess_conn_step_word(r.state, MURO_SESS_RECV, MURO_SESS_DATA, #{chunk});
      if (r.status != MURO_SESS_OK || r.done) return 2;
      {
        muro__sess_res bad = muro__sess_conn_init();
        bad = muro__sess_conn_step_word(bad.state, MURO_SESS_RECV, MURO_SESS_DATA, 99);
        if (bad.status != MURO_SESS_UNEXPECTED) return 3;
      }
      {
        muro__sess_val ev;
        memset(&ev, 0, sizeof ev);
        ev.tag = MURO_SESS_DATA;
        ev.ctor = "reply-ok";
        r = muro__sess_conn_step(r.state, MURO_SESS_SEND, &ev);
        if (r.status != MURO_SESS_OK || !r.done) return 4;
      }
      {
        muro__sess_res p = p_muro__sess_peer_init();
        if (p.status != MURO_SESS_OK) return 5;
        p = p_muro__sess_peer_step_word(p.state, MURO_SESS_RECV, MURO_SESS_NAT, 0);
        if (p.status != MURO_SESS_OK || !p.done) return 15;
        p = p_muro__sess_peer_init();
        p = p_muro__sess_peer_step_word(p.state, MURO_SESS_RECV, 99, 0);
        if (p.status != MURO_SESS_UNEXPECTED) return 16;
      }
      {
        muro__sess_res p = p_muro__sess_bitp_init();
        if (p.status != MURO_SESS_OK) return 17;
        p = p_muro__sess_bitp_step_word(p.state, MURO_SESS_RECV, MURO_SESS_BIT, 1);
        if (p.status != MURO_SESS_OK || !p.done) return 18;
        p = p_muro__sess_bitp_init();
        p = p_muro__sess_bitp_step_word(p.state, MURO_SESS_RECV, MURO_SESS_BIT, 2);
        if (p.status != MURO_SESS_UNEXPECTED) return 19;
      }
      {
        muro__sess_res p = p_muro__sess_unitp_init();
        if (p.status != MURO_SESS_OK) return 20;
        p = p_muro__sess_unitp_step_word(p.state, MURO_SESS_RECV, MURO_SESS_UNIT, 0);
        if (p.status != MURO_SESS_OK || !p.done) return 21;
      }
      {
        muro__sess_res p = p_muro__sess_pickp_init();
        if (p.status != MURO_SESS_OK) return 22;
        p = p_muro__sess_pickp_step_word(p.state, MURO_SESS_RECV, MURO_SESS_PICK, 0);
        if (p.status != MURO_SESS_OK || !p.done) return 23;
        p = p_muro__sess_pickp_init();
        p = p_muro__sess_pickp_step_word(p.state, MURO_SESS_RECV, MURO_SESS_PICK, 2);
        if (p.status != MURO_SESS_UNEXPECTED) return 24;
      }
      if (neg() != (int64_t)-1) return 6;
      if (below((int64_t)-1)->muro__field_tag != 1) return 7;
      if (below((int64_t)0)->muro__field_tag != 0) return 8;
      if (below((int64_t)1)->muro__field_tag != 0) return 9;
      if (n()->muro__field_tag != 0) return 10;
      if (seen()->muro__field_tag != 0) return 11;
      if (other()->muro__field_tag != 1) return 12;
      if (a_hook()->muro__field_tag != 0) return 13;
      if (b_hook()->muro__field_tag != 1) return 14;
      printf("ok\\n");
      return 0;
    }
    """)

    for stem <- ~w(conn peer plain sent left right ha hb main) do
      cc!(dir, "#{stem}.c", "#{stem}.o")
    end

    out = link!(dir, ~w(conn peer plain sent left right ha hb main))
    assert out == "ok\n"
  end

  test "two session headers with different nat-slot counts do not compile together" do
    dir = tmp_dir()
    emit!(dir, "conn", @conn)
    {wide_h, _} = emit!(dir, "wide", @wide)
    assert wide_h =~ "#define MURO__SESS_SLOTS 2"

    File.write!(Path.join(dir, "clash.c"), """
    #include "conn.h"
    #include "wide.h"
    """)

    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11 -c clash.c -o clash.o),
        cd: dir,
        stderr_to_stdout: true
      )

    assert status != 0
    assert out =~ "muro session state slot count differs between headers"
  end

  test "a prefix that is not a C identifier is refused, and elixir refuses the flag" do
    dir = tmp_dir()
    path = Path.join(dir, "plain.muro")
    File.write!(path, @plain)
    {:ok, book} = Muro.Load.file(path)
    book = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()

    assert {:error, "c:prefix"} =
             Muro.Emit.C.prepare(book, "plain", path: path, c_prefix: "1bad")

    assert {:error, "c:prefix"} =
             Muro.Emit.C.prepare(book, "plain", path: path, c_prefix: "admit-")

    assert {:ok, header, _source, sigs} =
             Muro.Emit.C.prepare(book, "plain", path: path, c_prefix: "admit_")

    assert header =~ "admit_n("
    assert Enum.map(sigs, & &1.name) == ["admit_n"]

    assert {:raise, "", "--prefix is only valid with --backend c"} =
             Muro.CLI.Emit.run([path, "--prefix", "admit_"])

    assert {:raise, "", "c:prefix"} =
             Muro.CLI.Emit.run([path, "--backend", "c", "--prefix", "1bad"])
  end

  test "a manifest c_prefix reaches the committed C symbol" do
    dir = tmp_dir()
    File.mkdir_p!(Path.join(dir, "priv/muro"))
    File.write!(Path.join(dir, "priv/muro/one.muro"), "def one : run Nat := 0\n")
    version = Mix.Tasks.Muro.version()

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "#{version}",
      modules: [
        {"priv/muro/one.muro", "lib/one.c", [kind: :c, c_prefix: "admit_"]}
      ]
    ]
    """)

    File.cd!(dir, fn ->
      capture_io(fn -> assert Mix.Tasks.Muro.Gen.run([]) == :ok end)
    end)

    header = File.read!(Path.join(dir, "lib/one.h"))
    assert header =~ "admit_one("
    refute header =~ ~r/(^|[^*_])one\(/
  end

  @piece """
  data Piece : Type where
    piece-chunk : Piece
    piece-req : Piece

  session hold := recv Piece end
  """

  @flag """
  unboxed data Flag : Type where
    flag-up : Flag
    flag-down : Flag

  def up : run Flag := flag-up
  """

  @bytes_left """
  def left : run Bytes := b"ab"
  """

  @bytes_right """
  def right : run Bytes := b"cd"
  """

  @str_hi """
  def hi : run String := "hi"
  """

  @str_yo """
  def yo : run String := "yo"
  """

  test "two prefixed books that declare Piece compile together" do
    dir = tmp_dir()
    {pa_h, pa_c} = emit!(dir, "pa", @piece, c_prefix: "a_")
    {pb_h, pb_c} = emit!(dir, "pb", @piece, c_prefix: "b_")

    tag_a = Muro.Emit.C.ctor_tag("Piece", "piece-chunk", "a_")
    tag_b = Muro.Emit.C.ctor_tag("Piece", "piece-req", "b_")
    type_a = Muro.Emit.C.ctor_tag_type("Piece", "a_")
    type_b = Muro.Emit.C.ctor_tag_type("Piece", "b_")
    struct_a = Muro.Emit.C.data_struct("Piece", "a_")
    struct_b = Muro.Emit.C.data_struct("Piece", "b_")
    word_a = Muro.Emit.C.ctor_word("pa", "Piece", "piece-chunk", "a_")
    word_b = Muro.Emit.C.ctor_word("pb", "Piece", "piece-req", "b_")

    assert pa_h =~ "typedef struct #{struct_a} #{struct_a};"
    assert pb_h =~ "typedef struct #{struct_b} #{struct_b};"
    assert pa_h =~ "typedef enum #{type_a}"
    assert pb_h =~ "typedef enum #{type_b}"
    assert pa_h =~ "#{tag_a} = 0"
    assert pb_h =~ "#{tag_b} = 1"
    assert pa_c =~ "#{struct_a} *"
    assert pb_c =~ "#{struct_b} *"
    refute pa_h =~ "typedef struct Piece "
    refute pb_h =~ "typedef enum muro__tag_Piece "

    File.write!(Path.join(dir, "both.c"), """
    #include "pa.h"
    #include "pb.h"

    int main(void) {
      muro__sess_res a = a_muro__sess_hold_init();
      if (a.status != MURO_SESS_OK) return 1;
      a = a_muro__sess_hold_step_word(a.state, MURO_SESS_RECV, MURO_SESS_DATA, #{word_a});
      if (a.status != MURO_SESS_OK || !a.done) return 2;
      muro__sess_res b = b_muro__sess_hold_init();
      if (b.status != MURO_SESS_OK) return 3;
      b = b_muro__sess_hold_step_word(b.state, MURO_SESS_RECV, MURO_SESS_DATA, #{word_b});
      if (b.status != MURO_SESS_OK || !b.done) return 4;
      return 0;
    }
    """)

    for stem <- ~w(pa pb both) do
      cc!(dir, "#{stem}.c", "#{stem}.o")
    end

    link!(dir, ~w(pa pb both))
  end

  test "a prefixed unboxed data run returns the prefixed struct" do
    dir = tmp_dir()
    {header, _source} = emit!(dir, "flag", @flag, c_prefix: "a_")
    struct_name = Muro.Emit.C.data_struct("Flag", "a_")
    tag = Muro.Emit.C.ctor_tag("Flag", "flag-up", "a_")
    tag_type = Muro.Emit.C.ctor_tag_type("Flag", "a_")

    assert header =~ "typedef struct #{struct_name} #{struct_name};"
    assert header =~ "typedef enum #{tag_type}"
    assert header =~ "#{tag} = 0"
    assert header =~ "#{struct_name} a_up("
    refute header =~ "typedef struct Flag "

    File.write!(Path.join(dir, "main.c"), """
    #include "flag.h"

    int main(void) {
      #{struct_name} f = a_up();
      if (f.muro__field_tag != #{tag}) return 1;
      return 0;
    }
    """)

    cc!(dir, "flag.c", "flag.o")
    cc!(dir, "main.c", "main.o")
    link!(dir, ~w(flag main))
  end

  test "bytes and string headers from several books share one translation unit" do
    dir = tmp_dir()
    {left_h, _} = emit!(dir, "bleft", @bytes_left)
    {right_h, _} = emit!(dir, "bright", @bytes_right)
    {hi_h, _} = emit!(dir, "shi", @str_hi)
    {yo_h, _} = emit!(dir, "syo", @str_yo)

    assert left_h =~ "#ifndef MURO__SLICE"
    assert right_h =~ "#ifndef MURO__SLICE"
    assert hi_h =~ "#ifndef MURO__STR"
    assert yo_h =~ "#ifndef MURO__STR"
    assert left_h =~ "typedef struct { const uint8_t *p; size_t n; } muro__slice;"
    assert hi_h =~ "typedef struct { const uint8_t *p; size_t n; } muro__str;"

    File.write!(Path.join(dir, "main.c"), """
    #include "bleft.h"
    #include "bright.h"
    #include "shi.h"
    #include "syo.h"

    int main(void) {
      muro__slice a = left();
      muro__slice b = right();
      muro__str s = hi();
      muro__str t = yo();
      if (a.n != 2 || b.n != 2 || a.p[0] != 'a' || b.p[0] != 'c') return 1;
      if (s.n != 2 || t.n != 2 || s.p[0] != 'h' || t.p[0] != 'y') return 2;
      return 0;
    }
    """)

    for stem <- ~w(bleft bright shi syo main) do
      cc!(dir, "#{stem}.c", "#{stem}.o")
    end

    link!(dir, ~w(bleft bright shi syo main))
  end

  test "a Nat run emitted with a prefix loads as a NIF that calls the prefixed symbol" do
    dir = tmp_dir()
    path = Path.join(dir, "cgaps_pref.muro")
    File.write!(path, "def one : run Nat := suc 0\n")

    parent = self()

    capture_io(fn ->
      send(parent, {:emit, Muro.emit_c(path, c_prefix: "a_", nif: true)})
    end)

    assert_received {:emit, {:ok, files}}
    nif_path = Enum.find(files, &String.ends_with?(&1, "_nif.c"))
    nif = File.read!(nif_path)
    source = File.read!(Path.join(dir, "cgaps_pref.c"))
    ex = File.read!(Path.join(dir, "cgaps_pref.ex"))

    assert source =~ "a_one("
    assert nif =~ "a_one("
    refute nif =~ ~r/(?<![A-Za-z0-9_])one\(/
    assert ex =~ "def one,"
    refute ex =~ "def a_one"

    on_exit(fn ->
      :code.purge(CgapsPref)
      :code.delete(CgapsPref)
    end)

    Code.compile_file(Path.join(dir, "cgaps_pref.ex"))
    assert apply(CgapsPref, :one, []) == 1
  end

  test "unreachable id-missing and id-present clauses are omitted and the live ones run" do
    dir = tmp_dir()
    path = Path.join(dir, "id.muro")
    File.write!(path, @id)
    assert {:ok, source} = Muro.emit_file(path, CGapsId)

    number = fun_body!(source, "idNumber", "idCount")
    refute number =~ ":id_missing"
    refute number =~ ":id_present"
    assert number =~ ":id_none"
    assert number =~ ":id_bad"
    assert number =~ ":id_unknown"

    count = fun_body!(source, "idCount", "idTag")
    assert count =~ ":id_missing"
    assert count =~ ":id_present"
    refute count =~ ":id_none"
    refute count =~ ":id_bad"
    refute count =~ ":id_unknown"

    tag = fun_body!(source, "idTag", nil)

    for atom <- ~w(:id_none :id_bad :id_unknown :id_missing :id_present) do
      assert tag =~ atom
    end

    mod = compile_source!(source, CGapsId)
    assert mod.idClassOf(0) == :id_none
    assert mod.idClassOf(1) == :id_bad
    assert mod.idClassOf(2) == :id_unknown
    assert mod.idNumber(0) == 0
    assert mod.idNumber(1) == 0
    assert mod.idNumber(2) == 1
    assert mod.idCount(0) == 2
    assert mod.idCount(1) == 3
    assert mod.idTag(:id_missing) == 3
    assert mod.idTag(:id_present) == 4
  end

  defp fun_body!(source, name, next) do
    stop =
      if next,
        do: "\\n+\\s*def #{next}\\b",
        else: "(?:\\n+\\s*defp\\b|\\n+end\\s*\\z|\\s*\\z)"

    regex = Regex.compile!("def #{name}\\(.*?\\n  end(?=#{stop})", "s")

    case Regex.run(regex, source) do
      [body] -> body
      _ -> flunk("no #{name} in\n#{source}")
    end
  end

  defp compile_source!(source, mod) do
    Code.compiler_options(ignore_module_conflict: true)

    {compiled, diagnostics} =
      Code.with_diagnostics(fn ->
        Code.compile_string(source)
      end)

    warnings = for %{severity: :warning, message: message} <- diagnostics, do: message

    if warnings != [] do
      flunk("generated #{inspect(mod)} warned:\n" <> Enum.join(warnings, "\n"))
    end

    [{^mod, _bin}] = compiled

    on_exit(fn ->
      :code.purge(mod)
      :code.delete(mod)
    end)

    mod
  end

  defp emit!(dir, stem, text, opts \\ []) do
    path = Path.join(dir, stem <> ".muro")
    File.write!(path, text)
    {:ok, book} = Muro.Load.file(path)
    book = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()

    assert {:ok, header, source, _sigs} =
             Muro.Emit.C.prepare(book, stem, [path: path] ++ opts)

    File.write!(Path.join(dir, stem <> ".h"), header)
    File.write!(Path.join(dir, stem <> ".c"), source)
    {header, source}
  end

  defp cc!(dir, src, obj) do
    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11 -c) ++ [src, "-o", obj],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
  end

  defp link!(dir, stems) do
    objs = Enum.map(stems, &"#{&1}.o")

    {link, status} =
      System.cmd("cc", objs ++ ["-o", "main_bin"], cd: dir, stderr_to_stdout: true)

    assert status == 0, link
    {out, status} = System.cmd(Path.join(dir, "main_bin"), [], stderr_to_stdout: true)
    assert status == 0, out
    out
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_c_gaps_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
