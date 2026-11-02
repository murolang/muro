defmodule MuroVisor.Browser do
  @moduledoc false

  @doc "Open `url` in a local browser. A missing opener is not an error."
  def open(url) when is_binary(url) do
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
