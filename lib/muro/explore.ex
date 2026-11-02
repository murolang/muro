defmodule Muro.Explore do
  @moduledoc false

  # A test listens by passing its pid. Production leaves the key unset,
  # and a check then does nothing here.
  @key {__MODULE__, :hook}

  @doc false
  def listen(pid) when is_pid(pid) do
    :persistent_term.put(@key, pid)
    :ok
  end

  @doc false
  def silence do
    :persistent_term.erase(@key)
    :ok
  end

  @doc false
  def note(kind, meeting) when is_atom(kind) do
    case :persistent_term.get(@key, nil) do
      pid when is_pid(pid) -> send(pid, {:muro_explore, kind, meeting})
      _ -> :ok
    end

    :ok
  end
end
