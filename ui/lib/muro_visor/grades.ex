defmodule MuroVisor.Grades do
  @moduledoc false

  @doc """
  Grades the checker recorded, copied onto the picture the SVG is drawn from.

  A binder is marked only when its quantity is one `Muro.Grade` already
  stores: an erased, linear, or reuse mark, or a `(c, t)` pair.
  `Muro.Grade.kernel_qty/1` is that quantity. An unmarked binder is
  affine by default and stays unmarked. It is not treated as erased.
  """
  def paint(picture, book) when is_map(picture) and not is_list(book) do
    paint(picture, [])
  end

  def paint(picture, book) when is_map(picture) and is_list(book) do
    surveyed = survey(book)

    nodes =
      Enum.map(picture.nodes, fn node ->
        info = Map.get(surveyed, node.bare, empty())
        Map.merge(node, info)
      end)

    Map.put(picture, :nodes, nodes)
  end

  @doc """
  One entry per definition name. `grade` is `"erased"`, `"runtime"`, or
  `nil`. `binders` lists only binders that carry a recorded quantity.
  """
  def survey(book) when is_list(book) do
    Map.new(book, fn
      %{name: name} = defn when is_binary(name) ->
        {name, classify(defn)}

      _other ->
        {nil, empty()}
    end)
    |> Map.delete(nil)
  end

  defp classify(defn) do
    binders =
      []
      |> walk(Map.get(defn, :type))
      |> walk(Map.get(defn, :body))
      |> Enum.reverse()
      |> Enum.uniq_by(fn binder -> {binder.name, binder.qty, binder.c, binder.t} end)

    %{grade: grade(binders), binders: binders}
  end

  defp empty, do: %{grade: nil, binders: []}

  # Every recorded binder is erased: the definition is erased evidence.
  # A surviving quantity keeps the definition bright. Erased binders on
  # that definition stay erased on their own.
  defp grade(binders) do
    case Enum.filter(binders, & &1.recorded) do
      [] -> nil
      recorded -> if Enum.all?(recorded, &(&1.qty == "erased")), do: "erased", else: "runtime"
    end
  end

  defp walk(acc, {:pi, qty, type, name, body}) do
    acc |> walk(type) |> binder(qty, name) |> walk(body)
  end

  defp walk(acc, {:lam, qty, type, name, body}) do
    acc |> walk(type) |> binder(qty, name) |> walk(body)
  end

  defp walk(acc, tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.reduce(acc, &walk(&2, &1))
  end

  defp walk(acc, list) when is_list(list), do: Enum.reduce(list, acc, &walk(&2, &1))

  defp walk(acc, map) when is_map(map),
    do: Enum.reduce(map, acc, fn {_k, v}, acc -> walk(acc, v) end)

  defp walk(acc, _other), do: acc

  defp binder(acc, _qty, name) when not is_binary(name), do: acc

  defp binder(acc, {:grade, c, t} = qty, name) do
    [
      %{
        name: name,
        qty: qty_name(qty),
        c: Muro.Grade.show(c),
        t: Muro.Grade.show(t),
        recorded: true
      }
      | acc
    ]
  end

  defp binder(acc, qty, name) when qty in [:erased, :linear, :reuse] do
    [%{name: name, qty: qty_name(qty), c: nil, t: nil, recorded: true} | acc]
  end

  defp binder(acc, _qty, _name), do: acc

  defp qty_name(qty), do: qty |> Muro.Grade.kernel_qty() |> Atom.to_string()

  @doc false
  def opacity(true, "erased"), do: "0.35"
  def opacity(true, "runtime"), do: "1"
  def opacity(_on, _grade), do: nil

  @doc false
  def binder_opacity(true, "erased"), do: "0.35"
  def binder_opacity(true, qty) when is_binary(qty), do: "1"
  def binder_opacity(_on, _qty), do: nil
end
