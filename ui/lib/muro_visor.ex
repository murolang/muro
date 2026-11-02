defmodule MuroVisor do
  @moduledoc """
  Open one checked book in the explorer.

  `open/1` loads the book and returns the local URL. It does not listen.
  `Mix.Tasks.Muro.Ui` is what starts the server.
  """

  @doc """
  Load `path` and return the URL the explorer will serve.

  `{:error, message}` when the file is missing or the book does not load.
  """
  def open(path) when is_binary(path) do
    case MuroVisor.Book.open(path) do
      {:ok, _stamp} -> {:ok, url()}
      {:error, _} = err -> err
    end
  end

  @default_origins ["//127.0.0.1", "//localhost"]

  @endpoint_defaults [
    url: [host: "127.0.0.1"],
    adapter: Bandit.PhoenixAdapter,
    http: [ip: {127, 0, 0, 1}, port: 4017],
    secret_key_base: String.duplicate("v", 64),
    render_errors: [formats: [html: MuroVisor.ErrorHTML], layout: false],
    pubsub_server: MuroVisor.PubSub,
    live_view: [signing_salt: "visorsalt"],
    check_origin: @default_origins,
    server: false
  ]

  @doc """
  Deep-merge endpoint options over the loopback defaults.

  A port-only `http:` list keeps `ip: {127, 0, 0, 1}` unless that
  list sets `ip`. Config files, `url/0`, and an installed package all
  use this merge before Bandit binds. The default origin list gains
  the bind address, with an IPv6 literal in brackets. An explicit
  `check_origin` is left as given.
  """
  def merge_endpoint(current) when is_list(current) do
    @endpoint_defaults
    |> Keyword.merge(current, &merge_opt/3)
    |> allow_bind_origin()
  end

  @doc false
  def install_endpoint! do
    current = Application.get_env(:muro_visor, MuroVisor.Endpoint, [])
    Application.put_env(:muro_visor, MuroVisor.Endpoint, merge_endpoint(current))
    :ok
  end

  @doc """
  The URL of the endpoint's http port, on the address it binds.

  An IPv6 address is written in brackets (`http://[::1]:4017/`).
  An IPv4 address (`http://127.0.0.1:4017/`) and a hostname
  (`http://localhost:4017/`) are not.
  """
  def url do
    http =
      :muro_visor
      |> Application.get_env(MuroVisor.Endpoint, [])
      |> merge_endpoint()
      |> Keyword.fetch!(:http)

    host = format_ip(Keyword.fetch!(http, :ip))
    "http://#{host}:#{Keyword.fetch!(http, :port)}/"
  end

  defp merge_opt(_key, left, right) do
    if keyword?(left) and keyword?(right) do
      Keyword.merge(left, right, &merge_opt/3)
    else
      right
    end
  end

  defp keyword?(value) when is_list(value), do: Keyword.keyword?(value)
  defp keyword?(_value), do: false

  defp allow_bind_origin(config) do
    case Keyword.get(config, :check_origin) do
      @default_origins = origins ->
        origin = "//" <> format_ip(config |> Keyword.fetch!(:http) |> Keyword.fetch!(:ip))

        if origin in origins do
          config
        else
          Keyword.put(config, :check_origin, origins ++ [origin])
        end

      _other ->
        config
    end
  end

  defp format_ip(:loopback), do: "127.0.0.1"
  defp format_ip(:any), do: "0.0.0.0"

  defp format_ip(ip) when is_tuple(ip) do
    case :inet.ntoa(ip) do
      chars when is_list(chars) -> chars |> List.to_string() |> bracket_ipv6()
      {:error, :einval} -> raise ArgumentError, "not an ip address: #{inspect(ip)}"
    end
  end

  defp format_ip(host) when is_binary(host) do
    literal =
      case unwrap_brackets(host) do
        {:ok, inner} -> inner
        :none -> host
      end

    case :inet.parse_address(String.to_charlist(literal)) do
      {:ok, ip} -> format_ip(ip)
      {:error, :einval} -> host
    end
  end

  defp format_ip(host) when is_list(host) do
    case :inet.parse_address(host) do
      {:ok, ip} -> format_ip(ip)
      {:error, :einval} -> format_ip(List.to_string(host))
    end
  end

  # :inet.ntoa/1 prints an IPv6 literal without brackets. A URL authority
  # needs them, or the host is missing and the task opens nothing.
  defp bracket_ipv6(host) do
    if String.contains?(host, ":"), do: "[#{host}]", else: host
  end

  defp unwrap_brackets("[" <> rest) do
    case String.replace_suffix(rest, "]", "") do
      ^rest -> :none
      inner -> {:ok, inner}
    end
  end

  defp unwrap_brackets(_host), do: :none
end
