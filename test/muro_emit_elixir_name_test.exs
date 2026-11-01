defmodule Muro.EmitElixirNameTest do
  use ExUnit.Case, async: false

  alias Muro.Emit

  @book """
  def foo-bar : run internal Nat := 0
  def foo_bar : run Nat := suc 0
  def Bit : run Nat := suc (suc 0)
  def bit : run Nat := suc (suc (suc 0))
  def see : run Nat := foo-bar
  def bit-ok : evidence {bit ≡ suc (suc (suc 0)) : Nat} := refl
  def foo-ok : evidence {foo_bar ≡ suc 0 : Nat} := refl
  def see-ok : evidence {see ≡ 0 : Nat} := refl
  def bits-ok : evidence {Bit ≡ suc (suc 0) : Nat} := refl
  session ping := recv Nat (send Nat end)
  session back := dual ping
  place home := ambient
  place away := node a
  scheme local := fixed home
  scheme go-away := fixed home
  endpoint there := back at local
  read stay peer : there at home := put 1 (get Nat done)
  conform pong : ping := get Nat (put 1 done)
  meet wire : pong with peer
  move cross local : away
  move cross local : away
  move cross go-away : away
  """

  test "elixir_base is injective and keeps a plain snake name" do
    assert Emit.elixir_base("foo_bar") == "foo_bar"
    assert Emit.elixir_base("fromMaybe") == "fromMaybe"
    assert Emit.elixir_base("isJust") == "isJust"
    assert Emit.elixir_base("muro_and") == "muro_and"
    assert Emit.elixir_base("bit") == "bit"
    assert Emit.elixir_base("read") == "read"
    assert Emit.elixir_base("Bit") == "muro__Bit"
    assert Emit.elixir_base("foo-bar") == "muro__foozdbar"
    assert Emit.elixir_base("and") == "muro__and"
    assert Emit.elixir_base("end") == "muro__end"
    assert Emit.elixir_base("1foo") == "muro__1foo"
    assert Emit.elixir_base("n'") == "muro__nzq"

    for name <- ["foo?", "foo!", "λ", "1foo"] do
      host = Emit.elixir_base(name)
      assert String.starts_with?(host, "muro__")
      refute String.contains?(host, "?")
      refute String.contains?(host, "!")
      assert String.match?(host, ~r/^[a-z_][A-Za-z0-9_]*$/)
    end

    names = [
      "foo_bar",
      "Bit",
      "bit",
      "foo-bar",
      "and",
      "muro_and",
      "1foo",
      "foo?",
      "foo!",
      "n'",
      "λ",
      "end",
      "in",
      "true",
      "fromMaybe",
      "foo__bar",
      "a_1b",
      "a1b",
      "muro_nif_load"
    ]

    spelled = Enum.map(names, &Emit.elixir_base/1)
    assert length(Enum.uniq(spelled)) == length(names)

    funs = Enum.map_join(spelled, "\n", fn host -> "  def #{host}, do: #{inspect(host)}" end)
    [{mod, _}] = Code.compile_string("defmodule Muro.NameProbe do\n#{funs}\nend")

    for {name, host} <- Enum.zip(names, spelled) do
      assert apply(mod, String.to_atom(host), []) == host, name
    end

    assert Emit.elixir_atom_name("Bit") == "Bit"
    assert Emit.elixir_atom_name("true") == "true"
    assert Emit.elixir_atom_name("nil") == "nil"
    assert Emit.elixir_atom_name("just") == "just"
    assert Emit.elixir_atom_name("and") == "and"
    assert Emit.elixir_atom_name("foo-bar") == "muro__foozdbar"
    assert Emit.elixir_atom_name("foo?") == "foo?"

    assert Emit.elixir_alias("pong") == "Pong"
    assert Emit.elixir_alias("foo_bar") == "FooBar"
    assert Emit.elixir_alias("muro_and") == "MuroAnd"
    assert Emit.elixir_alias("and") == "Mmuro__and"
    assert Emit.elixir_alias("grant-end") == "Mmuro__grantzdend"
    assert Emit.elixir_alias("_foo") == "M_foo"

    claimed = Emit.elixir_modules(["a_1b", "a1b"])
    assert claimed["a_1b"] == "A1b"
    assert claimed["a1b"] == "A1b_2"
  end

  test "run names are claimed for the whole book before a backend filters" do
    src = """
    def muro_nif_load : run internal Nat := 0
    def foo-bar : run internal Nat := 0
    def foo_bar : run Nat := suc 0
    def Bit : run Nat := 0
    def bit : run Nat := suc 0
    """

    assert {:ok, book} = Muro.Parser.parse(src)
    names = Emit.elixir_names(book)
    assert names["muro_nif_load"] == "muro_nif_load_2"
    assert names["foo-bar"] == "muro__foozdbar"
    assert names["foo_bar"] == "foo_bar"
    assert names["Bit"] == "muro__Bit"
    assert names["bit"] == "bit"
  end

  test "Elixir, NIF, OTP, FSM, and ExUnit agree, and the functions run" do
    dir = tmp!()
    path = Path.join(dir, "hosts.muro")
    File.write!(path, @book)

    assert {:ok, elixir} = Muro.emit_file(path, HostsImpl)
    assert {:ok, [c_h, _c | nif_paths]} = Muro.emit_c(path)
    assert File.exists?(c_h)
    refute nif_paths == []
    ex = File.read!(Path.join(dir, "hosts.ex"))
    assert {:ok, [otp_path]} = Muro.emit_otp(path)
    otp_src = File.read!(otp_path)
    assert {:ok, fsm} = Muro.emit_fsm(path, HostsFsm, root: dir, book: "hosts.muro")

    assert {:ok, %{source: suite}} =
             Muro.emit_exunit(path, HostsTest, root: dir, book: "hosts.muro", impl: HostsImpl)

    assert {:ok, [node_path]} = Muro.emit_node(path, node())
    node_src = File.read!(node_path)

    {:ok, loaded} = Muro.Load.file(path)
    book = Muro.Prelude.for_emit(loaded)
    names = Emit.elixir_names(book)

    assert names["foo-bar"] == "muro__foozdbar"
    assert names["foo_bar"] == "foo_bar"
    assert names["Bit"] == "muro__Bit"
    assert names["bit"] == "bit"

    for {source, host} <- Map.to_list(names) do
      assert elixir =~ ~r/defp? #{host}\b/, source
      assert otp_src =~ ~s|defp muro_host(#{inspect(source)}), do: :#{host}|
      assert fsm =~ ~s|defp muro_fsm_host(#{inspect(source)}), do: :#{host}|
    end

    # The internal run is claimed before the NIF drops it, so foo_bar is not foo_bar_2.
    refute ex =~ "def muro__foozdbar"
    assert ex =~ "def foo_bar,"
    assert ex =~ "def muro__Bit,"
    assert ex =~ "def bit,"
    refute ex =~ "def foo_bar_2"
    refute ex =~ "def Bit"

    assert suite =~ "impl.foo_bar()"
    assert suite =~ "impl.muro__Bit()"
    assert suite =~ "impl.bit()"
    assert suite =~ "impl.see()"
    refute suite =~ "impl.foo_bar_2"

    assert [{HostsImpl, _}] = Code.compile_string(elixir)
    assert apply(HostsImpl, :foo_bar, []) == {:suc, 0}
    assert apply(HostsImpl, :muro__Bit, []) == {:suc, {:suc, 0}}
    assert apply(HostsImpl, :bit, []) == {:suc, {:suc, {:suc, 0}}}
    assert apply(HostsImpl, :see, []) == 0

    Code.compile_file(Path.join(dir, "hosts.ex"))
    nif = fn name -> apply(Hosts, name, []) end
    assert nif.(:foo_bar) == 1
    assert nif.(:muro__Bit) == 2
    assert nif.(:bit) == 3
    assert nif.(:see) == 0
    assert_raise UndefinedFunctionError, fn -> nif.(:foo_bar_2) end
    assert_raise UndefinedFunctionError, fn -> nif.(:muro__foozdbar) end

    assert HostsOtp in Enum.map(Code.compile_string(otp_src), &elem(&1, 0))
    assert otp_src =~ "def wire do"
    assert otp_src =~ "defmodule #{Emit.elixir_alias("pong")} do"
    {:ok, left, right, left_ref, right_ref} = apply(HostsOtp, :wire, [])
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    assert HostsFsm in Enum.map(Code.compile_string(fsm), &elem(&1, 0))
    ping = Module.concat(HostsFsm, Emit.elixir_alias("ping"))
    st = ping.init()
    assert {:ok, st} = ping.recv(st, 1)
    assert {:ok, st} = ping.send(st, 1)
    assert ping.done?(st)

    assert [{HostsNode, _}] = Code.compile_string(node_src)
    assert node_src =~ "def cross_local_at_away("
    assert node_src =~ "def cross_local_at_away_2("
    go = Emit.elixir_base("#{byte_size("go-away")}.go-away/#{byte_size("away")}.away")
    assert node_src =~ "def #{go}("
    assert apply(HostsNode, :cross_local_at_away, [50]) == {:error, :noproc}
    assert apply(HostsNode, :cross_local_at_away_2, [50]) == {:error, :noproc}
    assert apply(HostsNode, String.to_atom(go), [50]) == {:error, :noproc}

    File.write!(Path.join(dir, "suite.ex"), suite)
    File.write!(Path.join(dir, "emitted.ex"), elixir)

    script = """
    ExUnit.start(autorun: false, colors: [enabled: false])
    Code.compile_file("emitted.ex")
    Code.compile_file("suite.ex")
    result = ExUnit.run()
    IO.puts("RESULT " <> inspect(result))
    """

    File.write!(Path.join(dir, "runner.exs"), script)
    {out, status} = System.cmd("elixir", ["runner.exs"], cd: dir, stderr_to_stdout: true)
    assert status == 0, out
    assert out =~ "failures: 0"
  end

  defp tmp! do
    dir = Path.join(System.tmp_dir!(), "muro_elixir_name_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn ->
      for mod <- [HostsImpl, Hosts, HostsTest, HostsFsm, HostsOtp, HostsNode] do
        :code.purge(mod)
        :code.delete(mod)
      end

      File.rm_rf!(dir)
    end)

    dir
  end
end
