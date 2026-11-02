defmodule MuroVisor.SocketTest do
  use MuroVisor.ConnCase, async: false

  @moduletag timeout: 60_000

  test "the live socket joins with the layout token and refuses a join without it" do
    saved = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)

    on_exit(fn ->
      assert {:ok, {_ip, port}} = Bandit.PhoenixAdapter.server_info(MuroVisor.Endpoint, :http)
      Application.put_env(:muro_visor, MuroVisor.Endpoint, saved)
      restart!()
      assert {:error, :econnrefused} = :gen_tcp.connect({127, 0, 0, 1}, port, [], 200)
    end)

    listen!()
    port = port!()

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

  test "a join reply split across reads waits for the whole frame" do
    payload = Jason.encode!(["4", "4", "lv:phx", "phx_reply", %{"status" => "ok"}])
    ws = %Mint.WebSocket{}
    {:ok, ws, binary} = Mint.WebSocket.encode(ws, {:text, payload})
    assert byte_size(binary) > 2
    at = div(byte_size(binary), 2)
    <<left::binary-size(at), right::binary>> = binary

    assert {:more, ws} = decode_chunks(ws, [left])
    assert {:ok, "ok", _ws} = decode_chunks(ws, [right])
    assert {:ok, "ok", _} = decode_chunks(%Mint.WebSocket{}, [left, right])
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
    case await_reply(conn, ref, websocket, []) do
      {:ok, status} -> {:ok, status}
      {:error, reason} -> {:error, reason}
    end
  end

  defp await_reply(conn, ref, websocket, frames) do
    case Mint.WebSocket.recv(conn, 0, 5_000) do
      {:ok, conn, responses} ->
        {websocket, frames} = take_frames(websocket, ref, responses, frames)

        case reply_status(frames) do
          {:ok, status} -> {:ok, status}
          :more -> await_reply(conn, ref, websocket, frames)
        end

      {:error, _conn, reason, _responses} ->
        {:error, reason}
    end
  end

  defp take_frames(websocket, ref, responses, frames) do
    Enum.reduce(responses, {websocket, frames}, fn
      {:data, ^ref, data}, {websocket, frames} ->
        {:ok, websocket, more} = Mint.WebSocket.decode(websocket, data)
        {websocket, frames ++ more}

      _, acc ->
        acc
    end)
  end

  defp decode_chunks(websocket, chunks) do
    {websocket, frames} =
      take_frames(websocket, :chunk, Enum.map(chunks, &{:data, :chunk, &1}), [])

    case reply_status(frames) do
      {:ok, status} -> {:ok, status, websocket}
      :more -> {:more, websocket}
    end
  end

  defp reply_status(frames) do
    case Enum.find_value(frames, fn
           {:text, text} -> text
           _ -> nil
         end) do
      nil ->
        :more

      text ->
        case Jason.decode(text) do
          {:ok, [_join, _ref, _topic, "phx_reply", %{"status" => status}]} -> {:ok, status}
          {:ok, other} -> {:ok, inspect(other)}
          _ -> :more
        end
    end
  end
end
