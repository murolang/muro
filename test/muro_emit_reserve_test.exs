defmodule Muro.EmitReserveTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Emit, Parser, Prelude, Session}
  alias Muro.Emit.{Helpers, Name, Nif}

  @deny MapSet.new(~w(
    moduledoc doc impl on_load callback behaviour behavior spec type
    derive optional_callbacks compile dialyzer after_compile before_compile
    deprecated vsn external_resource typedoc opaque enforce_keys
  ))

  test "template helpers are reserved, and a meeting of each name runs" do
    assert "data_decls" in Helpers.otp()
    assert "run_book" in Helpers.otp()
    assert "ctor_source" in Helpers.otp()
    assert "exchange" in Helpers.otp()
    assert "muro_host" in Helpers.otp()
    assert "start" in Helpers.otp()
    assert "step" in Helpers.otp()
    refute "ctor_atoms" in Helpers.otp()

    assert "muro_nif_load" in Helpers.runs()
    assert "muro_fsm_act" in Helpers.runs()
    assert "muro_fsm_done?" in Helpers.runs()
    assert "muro_fsm_source_tag" in Helpers.runs()
    assert "muro_fsm_tag" in Helpers.runs()
    assert "muro_fsm_safe_to_source" in Helpers.runs()
    assert "muro_fsm_source_to_safe" in Helpers.runs()
    assert "muro_nat_to_int" in Helpers.runs()
    assert "muro_repr_decode_nat" in Helpers.runs()
    assert "muro_repr_nat_max" in Helpers.runs()
    assert "muro_repr_name_term" in Helpers.runs()
    refute "step" in Helpers.runs()
    refute "start" in Helpers.runs()
    refute "init" in Helpers.runs()
    refute "send" in Helpers.runs()
    refute "node" in Helpers.runs()
    refute "muro_book" in Helpers.runs()

    assert "init" in Helpers.fsm_child()
    assert "send" in Helpers.fsm_child()
    assert "recv" in Helpers.fsm_child()
    assert "done?" in Helpers.fsm_child()
    assert "muro_book" in Helpers.exunit()
    assert "callbacks" in Helpers.exunit()
    assert "impl_mod" in Helpers.exunit()
    assert "node" in Helpers.node()
    assert Name.claim("node", Helpers.node()) |> elem(0) == "node_2"

    odd = Helpers.otp() |> Enum.reject(&muro_ident?/1) |> Enum.sort()
    assert odd == ["dat_payload?", "payload?"]

    names = ["ctor_atoms" | Helpers.otp() |> Enum.filter(&muro_ident?/1) |> Enum.sort()]
    book = meeting_book(names) |> checked!()
    assert {:ok, src} = Emit.Otp.render(book, "reserve")
    expected = claimed(names, Helpers.otp())

    for {source, emitted} <- Enum.zip(names, expected) do
      assert src =~ "def #{emitted} do", source

      if source == "ctor_atoms" do
        assert emitted == "ctor_atoms"
      else
        assert emitted == source <> "_2"
      end
    end

    compile!(src)

    for emitted <- expected do
      assert {:ok, left, right, left_ref, right_ref} =
               apply(ReserveOtp, String.to_atom(emitted), [])

      assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
      assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}
    end

    assert_reserved(src, Helpers.otp(), Helpers.otp(), MapSet.new(expected))
  end

  test "a run named after each host helper compiles and runs" do
    helpers = Helpers.runs() |> Enum.filter(&muro_ident?/1) |> Enum.sort()
    skipped = Helpers.runs() |> Enum.reject(&muro_ident?/1) |> Enum.sort()
    assert skipped == ["muro_fsm_dat?", "muro_fsm_done?", "muro_fsm_payload?"]

    names = helpers ++ ["ctor_atoms", "step", "send", "init"]
    {:ok, parsed} = Parser.parse(run_book(names))
    assert Check.check_sig(parsed) == :ok
    mapping = Emit.elixir_names(parsed)

    for name <- helpers do
      assert mapping[name] == name <> "_2"
    end

    assert mapping["ctor_atoms"] == "ctor_atoms"
    assert mapping["step"] == "step"
    assert mapping["send"] == "send"
    assert mapping["init"] == "init"

    src = Emit.emit_module(ReserveRuns, parsed)
    mods = compile!(src)

    for {source, emitted} <- mapping do
      assert apply(ReserveRuns, String.to_atom(emitted), []) == 0, source
    end

    derived = mapping |> Map.values() |> MapSet.new()
    assert_reserved(src, Helpers.runs(), Helpers.runs(), derived)
    assert mods != []
  end

  test "a run named node keeps that name, and the node template keeps node/0" do
    {:ok, parsed} = Parser.parse("def node : run Nat := 0\n")
    assert Emit.elixir_names(parsed)["node"] == "node"
    src = Emit.emit_module(NodeStay, parsed)
    assert src =~ "def node do"
    compile!(src)
    assert apply(NodeStay, :node, []) == 0

    {:ok, node_src} = Emit.Node.render(parsed, "place", :nonode@nohost)
    assert node_src =~ "def node, do:"
    refute node_src =~ "def node("
    assert_reserved(node_src, Helpers.node(), Helpers.node(), MapSet.new())
    compile!(node_src)
    assert apply(PlaceNode, :node, []) == :nonode@nohost
  end

  test "emitted templates reserve every helper they define" do
    fsm_src = """
    session ping := end
    conform pong : ping := done
    """

    fsm =
      fsm_src
      |> checked!()
      |> then(&Emit.Fsm.render(&1, "ping.muro", PingReserve, book: "ping.muro"))

    assert {:ok, fsm} = fsm
    assert_reserved(fsm, Helpers.fsm(), Helpers.fsm_child(), MapSet.new())
    compile!(fsm)

    ex = exunit_source()
    derived = MapSet.new(["round"])
    assert_reserved(ex, Helpers.exunit(), Helpers.exunit(), derived)

    nif = Nif.elixir_module("reserve", [])
    assert nif =~ "def muro_nif_load"
    assert_reserved(nif, Helpers.nif(), Helpers.nif(), MapSet.new())
  end

  test "an escaped constructor tag round-trips through eval_run and a live process" do
    book = escaped_book() |> checked!()

    assert Session.eval_run("seen", [:muro__iszdon], book) == 1
    assert Session.eval_run("seen", [String.to_atom("is-on")], book) == 1
    assert Session.eval_run("seen", [:muro__nope], book) == {:run, "seen", [:muro__nope]}
    assert Session.eval_run("seen", [true], book) == {:run, "seen", [true]}
    assert Session.eval_run("held", [{:muro__holdzdit, 4}], book) == 4
    assert Session.eval_run("held", [{String.to_atom("hold-it"), 4}], book) == 4
    assert Session.eval_run("flag", [true], book) == 1
    assert Session.eval_run("flag", [false], book) == 0
    assert Session.eval_run("unwrap", [:nothing], book) == 0
    assert Session.eval_run("unwrap", [{:just, 3}], book) == 3

    long = String.to_atom(Emit.elixir_atom_name("muro__iszdon"))
    assert Session.eval_run("wrapped", [long], book) == 7
    assert Session.eval_run("wrapped", [String.to_atom("muro__iszdon")], book) == 7
    assert Session.eval_run("seen", [String.to_atom("muro__iszdon")], book) == 1

    assert {:ok, src} = Emit.Otp.render(book, "escaped")
    compile!(src)

    reply = Module.concat(EscapedOtp, Emit.elixir_alias("reply"))
    assert {:ok, pid, ref} = apply(reply, :start, [self()])
    send(pid, {:muro, self(), {:tagged, :muro__iszdon}})
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    assert {:ok, pid, ref} = apply(reply, :start, [self()])
    send(pid, {:muro, self(), {:boxed, {:muro__holdzdit, 4}}})
    assert_receive {:muro, ^pid, 4}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    assert {:ok, fsm} = Emit.Fsm.render(book, "escaped.muro", EscapedFsm, book: "escaped.muro")
    refute fsm =~ "Muro."
    compile!(fsm)

    ask = Module.concat(EscapedFsm, Emit.elixir_alias("choice"))
    assert {:ok, st} = ask.recv(ask.init(), :muro__iszdon)
    assert ask.expected(st) == {:send, :nat}

    box = Module.concat(EscapedFsm, Emit.elixir_alias("box"))
    assert {:ok, st} = box.recv(box.init(), {:muro__holdzdit, 4})
    assert box.expected(st) == {:send, :nat}

    pick = Module.concat(EscapedFsm, Emit.elixir_alias("pick"))
    assert {:ok, st} = pick.recv(pick.init(), :muro__iszdon)
    assert pick.done?(st)
    assert {:ok, st} = pick.recv(pick.init(), String.to_atom("is-off"))
    assert pick.done?(st)
    assert {:error, _} = pick.recv(pick.init(), :muro__nope)

    bits = Module.concat(EscapedFsm, Emit.elixir_alias("bits"))
    assert {:ok, st} = bits.recv(bits.init(), :b0)
    assert bits.done?(st)

    wrap = Module.concat(EscapedFsm, Emit.elixir_alias("wrap"))
    assert {:ok, _} = wrap.recv(wrap.init(), String.to_atom("muro__iszdon"))
    assert {:ok, _} = wrap.recv(wrap.init(), long)
    assert {:error, _} = wrap.recv(wrap.init(), String.to_atom("is-on"))
  end

  defp meeting_book(names) do
    meets = Enum.map_join(names, "\n", &"meet #{&1} : aa_left with aa_right")

    """
    session aa_ping := end
    session aa_back := dual aa_ping
    conform aa_left : aa_ping := done
    conform aa_right : aa_back := done
    #{meets}
    """
  end

  defp run_book(names) do
    Enum.map_join(names, "\n", &"def #{&1} : run Nat := 0") <> "\n"
  end

  defp escaped_book do
    """
    data Choice : Type where
      is-on : Choice
      is-off : Choice

    data Box : Type where
      hold-it : Nat → Box

    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    data Wrap : Type where
      muro__iszdon : Wrap

    data Pack : Type where
      tagged : Choice → Pack
      boxed : Box → Pack

    def seen : run Π (c : Choice) → Nat :=
      λ (c : Choice) →
        match c motive (λ _ → Nat)
          | is-on => suc 0
          | is-off => 0

    def held : run Π (b : Box) → Nat :=
      λ (b : Box) →
        match b motive (λ _ → Nat)
          | hold-it n => n

    def flag : run Π (b : Bool) → Nat :=
      λ (b : Bool) →
        match b motive (λ _ → Nat)
          | true => suc 0
          | false => 0

    def unwrap : run Π (m : Maybe Nat) → Nat :=
      λ (m : Maybe Nat) →
        match m motive (λ _ → Nat)
          | nothing => 0
          | just n => n

    def wrapped : run Π (w : Wrap) → Nat :=
      λ (w : Wrap) →
        match w motive (λ _ → Nat)
          | muro__iszdon => suc (suc (suc (suc (suc (suc (suc 0))))))

    session choice := recv Choice (send Nat end)
    session box := recv Box (send Nat end)

    session ask := recv Pack (send Nat end)
    conform reply : ask :=
      get (p : Pack) (match p
        | tagged c => put (seen c) done
        | boxed b => put (held b) done)

    session pick :=
      recv (c : Choice) (case c
        | is-on => end
        | is-off => end)

    session bits :=
      recv (b : Bit) (case b
        | b0 => end
        | b1 => end)

    session wrap := recv Wrap end
    """
  end

  defp claimed(names, taken) do
    {emitted, _} =
      Enum.map_reduce(names, taken, fn name, used ->
        Name.claim(Emit.elixir_base(name), used)
      end)

    emitted
  end

  defp checked!(src) do
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    Prelude.for_emit(book)
  end

  defp compile!(src) do
    mods = Code.compile_string(src)

    on_exit(fn ->
      for {mod, _} <- mods do
        :code.purge(mod)
        :code.delete(mod)
      end
    end)

    mods
  end

  defp exunit_source do
    dir = Path.join(System.tmp_dir!(), "muro_reserve_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "round.muro")

    File.write!(path, """
    def round : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} := refl
    """)

    assert {:ok, %{source: source}} =
             Muro.emit_exunit(path, RoundReserve, root: dir, book: "round.muro")

    source
  end

  defp muro_ident?(name), do: String.match?(name, ~r/^[A-Za-z_][A-Za-z0-9_'-]*$/)

  defp assert_reserved(src, top_claim, nested_claim, derived) do
    for {mod, defs, nested?} <- quoted_modules(src) do
      claim = if nested?, do: nested_claim, else: top_claim
      extra = defs |> MapSet.difference(claim) |> MapSet.difference(derived)

      assert extra == MapSet.new(),
             "#{inspect(mod)} defines #{inspect(Enum.sort(extra))} outside the reserved set"
    end
  end

  defp quoted_modules(src) do
    {:ok, ast} = Code.string_to_quoted(src)

    case ast do
      {:defmodule, _, _} = quoted -> modules(quoted, false)
      {:__block__, _, _} = quoted -> modules(quoted, false)
    end
  end

  defp modules({:defmodule, _, [name, [do: body]]}, nested?) do
    {defs, nested} = walk(body)
    [{expand_alias(name), MapSet.new(defs), nested?} | Enum.flat_map(nested, &modules(&1, true))]
  end

  defp modules({:__block__, _, stmts}, nested?) do
    Enum.flat_map(stmts, &modules(&1, nested?))
  end

  defp modules(_, _), do: []

  defp walk({:__block__, _, stmts}) do
    Enum.reduce(stmts, {[], []}, fn stmt, {defs, mods} ->
      {more, inner} = walk(stmt)
      {defs ++ more, mods ++ inner}
    end)
  end

  defp walk({:defmodule, _, _} = quoted), do: {[], [quoted]}
  defp walk({:def, _, args}), do: {[fun_name(args)], []}
  defp walk({:defp, _, args}), do: {[fun_name(args)], []}
  defp walk({:defmacro, _, args}), do: {[fun_name(args)], []}
  defp walk({:defmacrop, _, args}), do: {[fun_name(args)], []}

  defp walk({:@, _, [{:on_load, _, [name]}]}) when is_atom(name), do: {[Atom.to_string(name)], []}

  defp walk({:@, _, [{:callback, _, [spec]}]}) do
    {[callback_name(spec)], []}
  end

  defp walk({:@, _, [{name, _, _}]}) when is_atom(name) do
    if Atom.to_string(name) in @deny, do: {[], []}, else: {[Atom.to_string(name)], []}
  end

  defp walk(_), do: {[], []}

  defp fun_name([{:when, _, [head | _]} | _]), do: head_name(head)
  defp fun_name([head | _]), do: head_name(head)

  defp head_name({name, _, _}) when is_atom(name), do: Atom.to_string(name)
  defp head_name({{:unquote, _, [name]}, _, _}) when is_atom(name), do: Atom.to_string(name)

  defp callback_name({:"::", _, [{name, _, _} | _]}) when is_atom(name), do: Atom.to_string(name)

  defp expand_alias({:__aliases__, _, parts}), do: Module.concat(parts)
  defp expand_alias(name) when is_atom(name), do: name
end
