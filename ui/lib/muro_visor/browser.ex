defmodule MuroVisor.Browser do
  @moduledoc false

  @doc "Open `url` in a local browser. A missing opener is not an error."
  def open(url) when is_binary(url) do
    case Application.get_env(:muro_visor, :browser_open) do
      fun when is_function(fun, 1) ->
        fun.(url)
        :ok

      _ ->
        native(url)
    end
  end

  defp native(url) do
    case opener() do
      nil ->
        :ok

      cmd ->
        _ = System.cmd(cmd, [url], stderr_to_stdout: true)
        :ok
    end
  rescue
    _ -> :ok
  end

  defp opener do
    case :os.type() do
      {:unix, :darwin} -> "open"
      {:unix, :linux} -> "xdg-open"
      _ -> nil
    end
  end
end
