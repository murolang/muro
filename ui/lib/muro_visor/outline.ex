defmodule MuroVisor.Outline do
  @moduledoc false

  @doc """
  The outline of `backend` for a book already loaded.

  This calls `Muro.Emit.outline/3` on `Muro.Prelude.for_emit/1`. It does
  not load the file again and it does not write source.
  """
  def render(nil, _path, _backend), do: ""

  def render(book, path, backend) when is_list(book) and is_binary(path) do
    emit = Muro.Prelude.for_emit(book)

    case fetch(emit, path, backend) do
      {:ok, outline} -> format(backend, outline)
      {:error, msg} when is_binary(msg) -> msg
      {:error, other} -> inspect(other)
    end
  end

  defp fetch(book, path, :fsm), do: Muro.Emit.outline(:fsm, book, path)

  defp fetch(book, path, backend) do
    stem =
      path
      |> Path.basename()
      |> String.trim_trailing(".muro")
      |> String.replace("-", "_")

    Muro.Emit.outline(backend, book, stem)
  end

  defp format(_backend, outline) do
    sigs =
      Enum.map_join(outline.signatures, "\n", fn sig ->
        params = sig |> Map.get(:params, []) |> Enum.map_join(", ", &param/1)
        lays = Map.get(sig, :param_layouts, [])
        "#{sig.name}(#{params}) #{inspect(sig.layout)} #{inspect(lays)}"
      end)

    layouts =
      Enum.map_join(outline.layouts, "\n", fn lay ->
        base = "#{Map.get(lay, :name)} #{inspect(Map.get(lay, :layout))}"

        case Map.get(lay, :constructors) do
          ctors when is_list(ctors) and ctors != [] ->
            extra =
              Enum.map_join(ctors, " ", fn c ->
                "#{c.name}##{c.tag}#{inspect(c.fields)}"
              end)

            base <> " " <> extra

          _ ->
            base
        end
      end)

    %{
      names: Enum.join(outline.names, ", "),
      signatures: sigs,
      layouts: layouts,
      clauses: Enum.join(outline.clauses, "\n")
    }
  end

  defp param(name) when is_binary(name), do: name
  defp param(other), do: inspect(other)
end
