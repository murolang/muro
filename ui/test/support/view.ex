defmodule MuroVisor.View do
  @moduledoc false

  import ExUnit.Assertions
  import ExUnit.Callbacks
  import Phoenix.ConnTest
  import Phoenix.LiveViewTest

  @endpoint MuroVisor.Endpoint

  def example(name) do
    path = Path.expand("../../../examples/#{name}", __DIR__)
    assert File.regular?(path)
    path
  end

  def open_book(conn, path) do
    assert {:ok, _stamp} = MuroVisor.Book.open(path)
    {:ok, view, _html} = live(conn, "/?view=all")
    view
  end

  def book do
    assert {:ok, open} = MuroVisor.Book.current()
    open.book
  end

  def write_book(src) do
    path = Path.join(System.tmp_dir!(), "muro-visor-#{System.unique_integer([:positive])}.muro")
    File.write!(path, src)
    on_exit(fn -> File.rm(path) end)
    path
  end

  def reported(book) do
    Enum.filter(book, fn d ->
      is_map(d) and is_binary(Map.get(d, :name)) and Map.get(d, :mode) in [:spec, :evidence, :run]
    end)
  end

  def parse(html), do: Floki.parse_fragment!(html)

  def text_of(html, selector) do
    html |> parse() |> Floki.find(selector) |> Floki.text()
  end

  def definition_nodes(html) do
    html |> parse() |> Floki.find("g[data-kind]") |> Enum.map(&fields/1)
  end

  def use_edges(html) do
    html |> parse() |> Floki.find("g[data-use]") |> Enum.map(&fields/1)
  end

  def meeting_groups(html) do
    html
    |> parse()
    |> Floki.find("g[data-meeting]")
    |> Enum.map(fn node ->
      %{
        id: attr(node, "id"),
        class: attr(node, "class") || "",
        meeting: attr(node, "data-meeting"),
        children: node |> Floki.find("g[data-state]") |> Enum.map(&fields/1),
        transitions:
          node
          |> Floki.find("g[data-label]")
          |> Enum.map(fn t ->
            Map.put(fields(t), :d, t |> Floki.find("path") |> List.first() |> attr("d"))
          end)
      }
    end)
  end

  def svg_source(html) do
    case Regex.run(~r/<svg\b.*?<\/svg>/s, html) do
      [svg] -> svg
      _ -> flunk("the page has no svg")
    end
  end

  def well_formed!(svg) when is_binary(svg) do
    ensure_xmerl()

    {doc, rest} =
      apply(:xmerl_scan, :string, [:binary.bin_to_list(svg), [{:encoding, ~c"utf-8"}]])

    assert rest == []
    doc
  end

  # Mix does not put every OTP library on the code path. xmerl is one of them.
  defp ensure_xmerl do
    case :code.ensure_loaded(:xmerl_scan) do
      {:module, :xmerl_scan} ->
        :ok

      {:error, _} ->
        [dir] =
          :code.root_dir()
          |> List.to_string()
          |> Path.join("lib/xmerl-*/ebin")
          |> Path.wildcard()

        true = :code.add_patha(String.to_charlist(dir))
        {:module, :xmerl_scan} = :code.ensure_loaded(:xmerl_scan)
        :ok
    end
  end

  def digest(dir) do
    dir
    |> files()
    |> Map.new(fn path -> {path, :crypto.hash(:sha256, File.read!(path))} end)
  end

  def session_name(book, party) do
    case Enum.find(book, &(&1.name == party)).session do
      name when is_binary(name) -> name
      {:sess, name, _} -> name
    end
  end

  def walked(book, meet) do
    left = Enum.find(book, &(&1.name == meet.left))
    right = Enum.find(book, &(&1.name == meet.right))
    spans = {Map.get(left, :steps), Map.get(right, :steps)}

    case Map.get(meet, :buffer) do
      n when is_integer(n) ->
        Muro.Async.graph(left.proc, right.proc, book, n, meet.left, meet.right, spans)

      _ ->
        {_verdict, graph} = Muro.Meet.graph(left.proc, right.proc, book, nil, spans)
        graph
    end
  end

  defp files(dir) do
    dir
    |> File.ls!()
    |> Enum.sort()
    |> Enum.flat_map(fn name ->
      path = Path.join(dir, name)

      cond do
        File.regular?(path) -> [path]
        File.dir?(path) -> files(path)
        true -> []
      end
    end)
  end

  defp fields(node) do
    %{
      id: attr(node, "id"),
      class: attr(node, "class") || "",
      kind: attr(node, "data-kind"),
      mode: attr(node, "data-mode"),
      name: attr(node, "data-name"),
      from: attr(node, "data-from"),
      to: attr(node, "data-to"),
      use: attr(node, "data-use"),
      state: attr(node, "data-state"),
      meeting: attr(node, "data-meeting"),
      label: attr(node, "data-label"),
      text: first_text(node)
    }
  end

  defp first_text(node) do
    case Floki.find(node, "text") do
      [first | _] -> Floki.text(first)
      [] -> ""
    end
  end

  defp attr(nil, _name), do: nil

  defp attr(node, name) do
    case Floki.attribute(node, name) do
      [value | _] -> value
      [] -> nil
    end
  end
end
