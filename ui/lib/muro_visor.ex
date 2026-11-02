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

  @endpoint_defaults [
    url: [host: "127.0.0.1"],
    adapter: Bandit.PhoenixAdapter,
    http: [ip: {127, 0, 0, 1}, port: 4017],
    secret_key_base: String.duplicate("v", 64),
    render_errors: [formats: [html: MuroVisor.ErrorHTML], layout: false],
    pubsub_server: MuroVisor.PubSub,
    live_view: [signing_salt: "visorsalt"],
    check_origin: ["//127.0.0.1", "//localhost"],
    server: false
  ]

  @doc """
  Deep-merge endpoint options over the loopback defaults.

  A port-only `http:` list keeps `ip: {127, 0, 0, 1}` unless that
  list sets `ip`. Config files, `url/0`, and an installed package all
  use this merge before Bandit binds.
  """
  def merge_endpoint(current) when is_list(current) do
    Keyword.merge(@endpoint_defaults, current, &merge_opt/3)
  end

  @doc false
  def install_endpoint! do
    current = Application.get_env(:muro_visor, MuroVisor.Endpoint, [])
    Application.put_env(:muro_visor, MuroVisor.Endpoint, merge_endpoint(current))
    :ok
  end

  @doc "The URL of the endpoint's http port, on the address it binds."
  def url do
    http =
      :muro_visor
      |> Application.get_env(MuroVisor.Endpoint, [])
      |> merge_endpoint()
      |> Keyword.fetch!(:http)

    "http://#{format_ip(Keyword.fetch!(http, :ip))}:#{Keyword.fetch!(http, :port)}/"
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

  defp format_ip(:loopback), do: "127.0.0.1"
  defp format_ip(:any), do: "0.0.0.0"
  defp format_ip(ip) when is_tuple(ip), do: ip |> :inet.ntoa() |> List.to_string()
end
