defmodule MuroVisor.SocketTest do
  use MuroVisor.ConnCase, async: false

  @moduletag timeout: 60_000

  setup do
    saved = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)

    on_exit(fn ->
      Application.put_env(:muro_visor, MuroVisor.Endpoint, saved)
      restart!()
      port = Process.get(:visor_port)

      if is_integer(port) do
        assert match?({:error, :econnrefused}, :gen_tcp.connect({127, 0, 0, 1}, port, [], 200))
      end
    end)

    :ok
  end

  test "the live socket joins with the layout token and refuses a join without it" do
    listen!()
    port = port!()
    Process.put(:visor_port, port)

    assert {:ok, _conn, %{status: 200, body: phoenix}} =
             request(port, "GET", "/assets/phoenix.min.js", [])

    assert phoenix =~ "Socket"

    assert {:ok, _conn, %{status: 200, body: live}} =
             request(port, "GET", "/assets/phoenix_live_view.min.js", [])

    assert live =~ "LiveSocket"

    assert {:ok, _conn, %{status: 200, body: html, headers: headers}} =
             request(port, "GET", "/", [])

    assert html =~ "_csrf_token"
    token = csrf!(html)
    {id, session, static} = live_root!(html)
    cookie = session_cookie!(headers)

    for origin <- ["http://127.0.0.1:#{port}", "http://localhost:#{port}"] do
      assert {:ok, "ok"} = join(port, id, session, static, token, cookie, origin)
    end

    assert {:ok, "error"} =
             join(port, id, session, static, nil, cookie, "http://127.0.0.1:#{port}")

    origins = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)[:check_origin]
    assert "//127.0.0.1" in origins
    assert "//localhost" in origins
  end

  defp listen! do
    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)

    http = config |> Keyword.fetch!(:http) |> Keyword.put(:port, 0)

    Application.put_env(
      :muro_visor,
      MuroVisor.Endpoint,
      Keyword.merge(config, http: http, server: true)
    )

    restart!()
  end

  defp restart! do
    :ok = Supervisor.terminate_child(MuroVisor.Supervisor, MuroVisor.Endpoint)
    {:ok, _pid} = Supervisor.restart_child(MuroVisor.Supervisor, MuroVisor.Endpoint)
  end

  defp port! do
    {:ok, {_ip, port}} = Bandit.PhoenixAdapter.server_info(MuroVisor.Endpoint, :http)
    port
  end

  defp request(port, method, path, headers) do
    {:ok, conn} = Mint.HTTP.connect(:http, "127.0.0.1", port, mode: :passive)
    {:ok, conn, ref} = Mint.HTTP.request(conn, method, path, headers, "")
    {:ok, conn, responses} = recv_all(conn, ref, [], 5_000)
    Mint.HTTP.close(conn)

    status =
      Enum.find_value(responses, fn
        {:status, ^ref, status} -> status
        _ -> nil
      end)

    headers =
      Enum.flat_map(responses, fn
        {:headers, ^ref, hs} -> hs
        _ -> []
      end)

    body =
      responses
      |> Enum.flat_map(fn
        {:data, ^ref, data} -> [data]
        _ -> []
      end)
      |> IO.iodata_to_binary()

    {:ok, conn, %{status: status, headers: headers, body: body}}
  end

  defp recv_all(conn, ref, acc, timeout) do
    case Mint.HTTP.recv(conn, 0, timeout) do
      {:ok, conn, responses} ->
        acc = acc ++ responses

        if Enum.any?(responses, &match?({:done, ^ref}, &1)) do
          {:ok, conn, acc}
        else
          recv_all(conn, ref, acc, timeout)
        end

      {:error, _conn, reason, responses} ->
        {:error, reason, acc ++ responses}
    end
  end

  defp csrf!(html) do
    [token] =
      html
      |> Floki.parse_document!()
      |> Floki.attribute("meta[name='csrf-token']", "content")

    token
  end

  defp live_root!(html) do
    [main] = html |> Floki.parse_document!() |> Floki.find("[data-phx-main]")
    [id] = Floki.attribute(main, "id")
    [session] = Floki.attribute(main, "data-phx-session")

    static =
      case Floki.attribute(main, "data-phx-static") do
        [""] -> nil
        [] -> nil
        [value] -> value
      end

    {id, session, static}
  end

  defp session_cookie!(headers) do
    headers
    |> Enum.find_value(fn
      {"set-cookie", value} ->
        if String.starts_with?(value, "_muro_visor_key="), do: value |> String.split(";") |> hd()

      _ ->
        nil
    end)
    |> tap(fn cookie -> assert is_binary(cookie) end)
  end

  defp join(port, id, session, static, token, cookie, origin) do
    query =
      case token do
        nil -> "vsn=2.0.0"
        token -> "_csrf_token=#{URI.encode_www_form(token)}&vsn=2.0.0"
      end

    headers = [{"cookie", cookie}, {"origin", origin}]
    {:ok, conn} = Mint.HTTP.connect(:http, "127.0.0.1", port, mode: :passive)

    {:ok, conn, ref} =
      Mint.WebSocket.upgrade(:ws, conn, "/live/websocket?#{query}", headers)

    {:ok, conn, responses} = recv_all(conn, ref, [], 5_000)

    status =
      Enum.find_value(responses, fn
        {:status, ^ref, status} -> status
        _ -> nil
      end)

    resp_headers =
      Enum.flat_map(responses, fn
        {:headers, ^ref, hs} -> hs
        _ -> []
      end)

    if status != 101 do
      Mint.HTTP.close(conn)
      {:ok, "upgrade #{status}"}
    else
      {:ok, conn, websocket} =
        Mint.WebSocket.new(conn, ref, status, resp_headers, mode: :passive)

      params = if token, do: %{"_csrf_token" => token, "_mounts" => 0}, else: %{"_mounts" => 0}

      frame =
        Jason.encode!([
          "1",
          "1",
          "lv:#{id}",
          "phx_join",
          %{
            "url" => "http://127.0.0.1:#{port}/",
            "params" => params,
            "session" => session,
            "static" => static,
            "sticky" => false
          }
        ])

      {:ok, websocket, data} = Mint.WebSocket.encode(websocket, {:text, frame})
      {:ok, conn} = Mint.WebSocket.stream_request_body(conn, ref, data)
      reply = read_reply(conn, ref, websocket)
      Mint.HTTP.close(conn)
      reply
    end
  end

  defp read_reply(conn, ref, websocket) do
    {:ok, _conn, responses} = Mint.WebSocket.recv(conn, 0, 5_000)

    frames =
      Enum.flat_map(responses, fn
        {:data, ^ref, data} ->
          {:ok, _websocket, frames} = Mint.WebSocket.decode(websocket, data)
          frames

        _ ->
          []
      end)

    text =
      Enum.find_value(frames, fn
        {:text, text} -> text
        _ -> nil
      end)

    case Jason.decode!(text) do
      [_join, _ref, _topic, "phx_reply", %{"status" => status}] -> {:ok, status}
      other -> {:ok, inspect(other)}
    end
  end
end
