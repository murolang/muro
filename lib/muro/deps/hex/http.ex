defmodule Muro.Deps.Hex.Http do
  @moduledoc """
  Hex transport over `:httpc`.

  `HEX_API_URL` defaults to `https://hex.pm/api`. `HEX_MIRROR`
  defaults to `https://repo.hex.pm`. Requests send `accept` and
  `user-agent`. HTTPS uses `verify_peer`,
  `:public_key.cacerts_get/0`, and the hostname check. Redirects
  are followed only when the scheme, host, and port stay the same.
  `:inets`, `:ssl`, and `:public_key` are started here, not as
  extra applications of `:muro`. Mix removes other OTP applications
  from the code path, so this module calls `Mix.ensure_application!/1`
  for those three, plus `:crypto` and `:asn1`, before starting them
  when Mix is loaded. In the executable Mix records the code path
  before the boot script loads those applications, so a miss loads
  the copy that sits in the release library beside `:muro`.

  No authorization header is sent. A 401 is reported as an
  unsupported private repository.
  """

  @behaviour Muro.Deps.Hex.Transport

  @redirects [301, 302, 303, 307, 308]

  @impl true
  def releases(package) when is_binary(package) do
    url = trim_slash(api_base()) <> "/packages/" <> uri_segment(package)

    with :ok <- ensure_http(),
         {:ok, body} <- request(url, ~c"application/json", 5),
         {:ok, decoded} <- decode_json(body) do
      normalize_releases(decoded)
    end
  end

  @impl true
  def tarball(package, version) when is_binary(package) and is_binary(version) do
    url =
      trim_slash(mirror()) <>
        "/tarballs/" <> uri_segment(package) <> "-" <> uri_segment(version) <> ".tar"

    with :ok <- ensure_http() do
      request(url, ~c"application/octet-stream", 5)
    end
  end

  defp ensure_http do
    with :ok <- ensure_mix_apps([:asn1, :crypto, :public_key, :ssl, :inets]),
         {:ok, _} <- Application.ensure_all_started(:public_key),
         {:ok, _} <- Application.ensure_all_started(:ssl),
         {:ok, _} <- Application.ensure_all_started(:inets) do
      :ok
    else
      {:error, reason} -> {:error, "could not start http (#{inspect(reason)})"}
    end
  end

  # Mix (since 1.15) drops OTP applications that are not in
  # extra_applications. Put them back on the code path. A release
  # that does not load Mix already has the applications it shipped.
  #
  # In the executable, Mix.State records the code path when muro
  # starts, which is before the boot script reaches these `:load`
  # applications. Mix.ensure_application!/1 then cannot see them.
  # They sit in the release lib beside `:muro`, so load that copy.
  @doc false
  def ensure_otp(apps) when is_list(apps), do: ensure_mix_apps(apps)

  defp ensure_mix_apps(apps) do
    if Code.ensure_loaded?(Mix) and function_exported?(Mix, :ensure_application!, 1) do
      Enum.each(apps, &ensure_mix_app/1)
    end

    :ok
  rescue
    error -> {:error, Exception.message(error)}
  end

  defp ensure_mix_app(app) do
    Mix.ensure_application!(app)
  rescue
    error ->
      case release_ebin(app) do
        nil ->
          reraise(error, __STACKTRACE__)

        ebin ->
          Code.prepend_path(ebin)

          case Application.load(app) do
            :ok -> :ok
            {:error, {:already_loaded, _}} -> :ok
            {:error, reason} -> raise "could not load #{app} (#{inspect(reason)})"
          end
      end
  end

  defp release_ebin(app) do
    case :code.lib_dir(:muro) do
      path when is_list(path) ->
        lib = path |> List.to_string() |> Path.dirname()

        case Path.wildcard(Path.join(lib, "#{app}-*/ebin")) do
          [ebin | _] -> ebin
          [] -> nil
        end

      _ ->
        nil
    end
  end

  defp request(url, accept, left) do
    headers = [
      {~c"accept", accept},
      {~c"user-agent", user_agent()}
    ]

    case :httpc.request(
           :get,
           {String.to_charlist(url), headers},
           [
             autoredirect: false,
             timeout: 30_000,
             connect_timeout: 10_000,
             ssl: ssl_opts(URI.parse(url))
           ],
           body_format: :binary
         ) do
      {:ok, {{_version, 200, _reason}, _headers, body}} ->
        {:ok, body}

      {:ok, {{_version, status, _reason}, headers, _body}} when status in @redirects ->
        follow(url, accept, headers, left)

      {:ok, {{_version, 401, _reason}, _headers, _body}} ->
        {:error, "hex returned 401; private repositories are not supported"}

      {:ok, {{_version, status, _reason}, _headers, _body}} ->
        {:error, "hex returned HTTP #{status}"}

      {:error, reason} ->
        {:error, "hex request failed (#{inspect(reason)})"}
    end
  end

  defp follow(_url, _accept, _headers, left) when left <= 1 do
    {:error, "hex redirected too many times"}
  end

  defp follow(url, accept, headers, left) do
    case location_header(headers) do
      {:ok, location} ->
        next = URI.merge(url, location) |> URI.to_string()

        if same_origin?(url, next) do
          request(next, accept, left - 1)
        else
          {:error, "hex redirected to another host"}
        end

      :error ->
        {:error, "hex redirect had no location"}
    end
  end

  defp location_header(headers) do
    Enum.find_value(headers, :error, fn {name, value} ->
      if String.downcase(to_text(name)) == "location" do
        {:ok, to_text(value)}
      end
    end)
  end

  defp to_text(value) when is_binary(value), do: value
  defp to_text(value) when is_list(value), do: List.to_string(value)

  defp same_origin?(left, right) do
    left = URI.parse(left)
    right = URI.parse(right)

    String.downcase(left.scheme || "") == String.downcase(right.scheme || "") and
      String.downcase(left.host || "") == String.downcase(right.host || "") and
      port(left) == port(right)
  end

  defp port(%URI{scheme: "https", port: nil}), do: 443
  defp port(%URI{scheme: "http", port: nil}), do: 80
  defp port(%URI{port: port}), do: port

  defp ssl_opts(%URI{scheme: "https", host: host}) when is_binary(host) do
    host = String.to_charlist(host)

    [
      verify: :verify_peer,
      cacerts: apply(:public_key, :cacerts_get, []),
      depth: 4,
      server_name_indication: host,
      customize_hostname_check: [
        match_fun: apply(:public_key, :pkix_verify_hostname_match_fun, [:https])
      ]
    ]
  end

  defp ssl_opts(_uri), do: []

  defp decode_json(body) do
    if Code.ensure_loaded?(JSON) do
      case apply(JSON, :decode, [body]) do
        {:ok, term} -> {:ok, term}
        {:error, reason} -> {:error, "hex response was not JSON (#{inspect(reason)})"}
      end
    else
      Muro.Deps.Hex.JSON.decode(body)
    end
  end

  defp normalize_releases(%{"releases" => releases}) when is_list(releases) do
    {:ok, list} =
      Enum.reduce_while(releases, {:ok, []}, fn rel, {:ok, acc} ->
        case normalize_release(rel) do
          {:ok, one} -> {:cont, {:ok, [one | acc]}}
          :skip -> {:cont, {:ok, acc}}
        end
      end)

    {:ok, Enum.reverse(list)}
  end

  defp normalize_releases(_other), do: {:error, "hex response has no releases"}

  defp normalize_release(%{"version" => version} = rel) when is_binary(version) do
    {:ok, %{version: version, retired: retired?(Map.get(rel, "retirement"))}}
  end

  defp normalize_release(_other), do: :skip

  defp retired?(nil), do: false
  defp retired?(false), do: false
  defp retired?(map) when is_map(map), do: true
  defp retired?(_other), do: false

  defp api_base, do: System.get_env("HEX_API_URL") || "https://hex.pm/api"
  defp mirror, do: System.get_env("HEX_MIRROR") || "https://repo.hex.pm"
  defp trim_slash(url), do: String.trim_trailing(url, "/")
  defp uri_segment(segment), do: URI.encode(segment, &URI.char_unreserved?/1)

  defp user_agent do
    vsn =
      case Application.spec(:muro, :vsn) do
        nil -> "dev"
        list -> List.to_string(list)
      end

    String.to_charlist("muro/" <> vsn <> " (mix muro.deps.get)")
  end
end
