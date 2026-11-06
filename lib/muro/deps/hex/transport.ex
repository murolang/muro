defmodule Muro.Deps.Hex.Transport do
  @moduledoc """
  Test seam for `Muro.Deps.Hex`. Not a user option.

  Select it with `Application.put_env(:muro, :hex_transport, module)`.
  The default is `Muro.Deps.Hex.Http`.
  """

  @callback releases(package :: String.t()) :: {:ok, [map()]} | {:error, String.t()}
  @callback tarball(package :: String.t(), version :: String.t()) ::
              {:ok, binary()} | {:error, String.t()}
end
