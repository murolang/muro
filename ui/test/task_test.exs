defmodule MuroVisor.TaskTest do
  use MuroVisor.ConnCase, async: false

  @moduletag timeout: 180_000

  setup do
    on_exit(&silence/0)
    silence()
    :ok
  end

  test "no path is a usage error and a non-zero exit" do
    {output, status} = mix_ui([])
    assert status != 0
    assert output =~ "usage: mix muro.ui path.muro"
    assert refused()
  end

  test "a missing file names itself and exits non-zero" do
    missing = Path.join(System.tmp_dir!(), "no-such-muro-book.muro")
    File.rm(missing)
    {output, status} = mix_ui([missing])
    assert status != 0
    assert output =~ "no such book: #{missing}"
    assert refused()
  end

  test "a book that fails to check exits non-zero with the checker message" do
    path =
      write_book("""
      session choice := choose end (send Nat end)
      session offered := dual choice
      conform taker : choice :=
        pick1 stop
      conform giver : offered :=
        cover done (get Nat done)
      meet arm : taker with giver
      """)

    assert {:error, msg} = Muro.Load.file(path)
    {output, status} = mix_ui([path])
    assert status != 0
    assert output =~ msg
    assert output =~ "diverged"
    assert refused()
  end

  test "a good path starts the endpoint, opens the book, and leaves no listener" do
    path = example("half_ok.muro")
    before = File.read!(path)
    parent = self()

    Application.put_env(:muro_visor, :ui_hold, false)
    Application.put_env(:muro_visor, :browser_open, fn url -> send(parent, {:opened, url}) end)

    Mix.Tasks.Muro.Ui.run([path])

    assert_receive {:opened, url}
    assert url == MuroVisor.url()
    assert {:ok, %{book: loaded}} = MuroVisor.Book.current()
    assert Enum.any?(loaded, &(&1.name == "plus"))

    body = get(URI.parse(url).port)
    assert body =~ "200"
    assert body =~ "muro visor"
    assert body =~ "plus"
    assert File.read!(path) == before

    silence()
    assert refused()
  end

  test "missing endpoint config is filled and the visor application serves the book" do
    path = example("half_ok.muro")
    saved = Application.get_env(:muro_visor, MuroVisor.Endpoint)

    on_exit(fn ->
      Application.put_env(:muro_visor, MuroVisor.Endpoint, saved)
    end)

    Application.delete_env(:muro_visor, MuroVisor.Endpoint)
    Application.put_env(:muro_visor, :ui_hold, false)
    Application.put_env(:muro_visor, :browser_open, fn _url -> :ok end)

    Mix.Tasks.Muro.Ui.run([path])

    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    assert get_in(config, [:http, :port]) == 4017
    assert config[:check_origin] == ["//127.0.0.1", "//localhost"]
    assert Enum.any?(Application.started_applications(), &match?({:muro_visor, _, _}, &1))
    assert {:ok, %{book: loaded}} = MuroVisor.Book.current()
    assert Enum.any?(loaded, &(&1.name == "plus"))

    body = get(4017)
    assert body =~ "200"
    assert body =~ "_csrf_token"
  end

  test "existing endpoint settings keep their port" do
    before = get_in(Application.fetch_env!(:muro_visor, MuroVisor.Endpoint), [:http, :port])
    assert :ok = Mix.Tasks.Muro.Ui.ensure_config!()
    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    assert get_in(config, [:http, :port]) == before
    assert config[:check_origin] == ["//127.0.0.1", "//localhost"]
  end

  test "a port-only http override still binds to loopback" do
    saved = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)

    on_exit(fn ->
      Application.put_env(:muro_visor, MuroVisor.Endpoint, saved)
    end)

    explicit = MuroVisor.merge_endpoint(http: [ip: {10, 0, 0, 1}, port: 4040])
    assert get_in(explicit, [:http, :ip]) == {10, 0, 0, 1}
    assert get_in(explicit, [:http, :port]) == 4040

    for name <- ["config.exs", "test.exs"] do
      src = File.read!(Path.expand("../config/#{name}", __DIR__))
      assert src =~ "{127, 0, 0, 1}", "#{name} drops the loopback address"
    end

    # A later config file does Keyword.merge, so this is all that remains of :http.
    Application.put_env(:muro_visor, MuroVisor.Endpoint, http: [port: 0])
    assert :ok = Mix.Tasks.Muro.Ui.ensure_config!()

    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    assert get_in(config, [:http, :ip]) == {127, 0, 0, 1}
    assert get_in(config, [:http, :port]) == 0
    assert MuroVisor.url() == "http://127.0.0.1:0/"

    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(config, :server, true))
    restart!()

    assert {:ok, {{127, 0, 0, 1}, port}} =
             Bandit.PhoenixAdapter.server_info(MuroVisor.Endpoint, :http)

    assert is_integer(port) and port > 0
    assert {:ok, sock} = :gen_tcp.connect({127, 0, 0, 1}, port, [], 2_000)
    :gen_tcp.close(sock)
  end

  test "the url brackets an ipv6 address and keeps ipv4 and hostnames" do
    saved = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)

    on_exit(fn ->
      Application.put_env(:muro_visor, MuroVisor.Endpoint, saved)
    end)

    full = {0x2001, 0x0DB8, 0x85A3, 0x0000, 0x0000, 0x8A2E, 0x0370, 0x7334}

    for {ip, host, url} <- [
          {{0, 0, 0, 0, 0, 0, 0, 1}, "::1", "http://[::1]:4017/"},
          {full, "2001:db8:85a3::8a2e:370:7334", "http://[2001:db8:85a3::8a2e:370:7334]:4017/"},
          {{0, 0, 0, 0, 0, 0, 0, 0}, "::", "http://[::]:4017/"},
          {{127, 0, 0, 1}, "127.0.0.1", "http://127.0.0.1:4017/"},
          {:loopback, "127.0.0.1", "http://127.0.0.1:4017/"},
          {:any, "0.0.0.0", "http://0.0.0.0:4017/"},
          {"localhost", "localhost", "http://localhost:4017/"},
          {"visor.example", "visor.example", "http://visor.example:4017/"},
          {"::1", "::1", "http://[::1]:4017/"},
          {"[::1]", "::1", "http://[::1]:4017/"},
          {~c"::1", "::1", "http://[::1]:4017/"},
          {~c"localhost", "localhost", "http://localhost:4017/"}
        ] do
      Application.put_env(:muro_visor, MuroVisor.Endpoint, http: [ip: ip, port: 4017])

      assert MuroVisor.url() == url
      parsed = URI.parse(url)
      assert parsed.scheme == "http"
      assert parsed.host == host
      assert parsed.port == 4017

      if String.contains?(host, ":") do
        assert String.starts_with?(parsed.authority, "[#{host}]")
      else
        refute String.contains?(url, "[")
      end

      merged = MuroVisor.merge_endpoint(http: [ip: ip, port: 4017])
      assert "//#{authority_host(host)}" in merged[:check_origin]
    end

    kept =
      MuroVisor.merge_endpoint(
        http: [ip: {0, 0, 0, 0, 0, 0, 0, 1}, port: 4017],
        check_origin: ["//example.com"]
      )

    assert kept[:check_origin] == ["//example.com"]
  end

  defp authority_host(host) do
    if String.contains?(host, ":"), do: "[#{host}]", else: host
  end

  defp mix_ui(args) do
    System.cmd("mix", ["muro.ui" | args],
      cd: Path.expand("..", __DIR__),
      stderr_to_stdout: true,
      env: [{"MIX_ENV", "test"}]
    )
  end

  defp get(port) do
    {:ok, sock} =
      :gen_tcp.connect({127, 0, 0, 1}, port, [:binary, active: false], 2_000)

    :ok = :gen_tcp.send(sock, "GET / HTTP/1.0\r\nHost: 127.0.0.1\r\n\r\n")
    recv(sock, "")
  end

  defp recv(sock, acc) do
    case :gen_tcp.recv(sock, 0, 2_000) do
      {:ok, bin} -> recv(sock, acc <> bin)
      {:error, :closed} -> acc
      {:error, reason} -> flunk("recv #{inspect(reason)} after #{byte_size(acc)} bytes")
    end
  end

  defp restart! do
    :ok = Supervisor.terminate_child(MuroVisor.Supervisor, MuroVisor.Endpoint)
    {:ok, _pid} = Supervisor.restart_child(MuroVisor.Supervisor, MuroVisor.Endpoint)
  end

  defp silence do
    Application.delete_env(:muro_visor, :ui_hold)
    Application.delete_env(:muro_visor, :browser_open)
    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(config, :server, false))

    if Process.whereis(MuroVisor.Endpoint) do
      :ok = Supervisor.terminate_child(MuroVisor.Supervisor, MuroVisor.Endpoint)
      {:ok, _pid} = Supervisor.restart_child(MuroVisor.Supervisor, MuroVisor.Endpoint)
    end
  end

  defp refused do
    port =
      :muro_visor
      |> Application.fetch_env!(MuroVisor.Endpoint)
      |> Keyword.fetch!(:http)
      |> Keyword.fetch!(:port)

    match?({:error, :econnrefused}, :gen_tcp.connect({127, 0, 0, 1}, port, [], 200))
  end
end
