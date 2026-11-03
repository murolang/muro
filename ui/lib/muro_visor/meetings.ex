defmodule MuroVisor.Meetings do
  @moduledoc false

  alias Muro.Emit.Name

  # Meetings in source order, grouped under the base session. The rows
  # are `MuroVisor.Sequence` over the configuration graph stored on the
  # meeting. Evidence is an `{d ≤ w}` bound on that session.

  def catalog(book, graph, path \\ nil)

  def catalog(nil, _graph, _path), do: %{meetings: [], groups: []}

  def catalog(book, %{nodes: nodes}, path) when is_list(book) do
    meetings =
      book
      |> Enum.filter(&(Map.get(&1, :kind) == :meet))
      |> Enum.map(&meeting(&1, book, nodes, path))

    %{meetings: meetings, groups: groups(meetings)}
  end

  def catalog(_book, _graph, _path), do: %{meetings: [], groups: []}

  defp meeting(meet, book, nodes, path) do
    base = base_name(meet, book)
    proto = opened_proto(book, base)
    {spec, dual} = protocols(book, base, proto)
    rows = meet |> rows_for() |> MuroVisor.Sequence.annotate(proto)
    evidence = evidence(book, base)

    %{
      name: meet.name,
      dom: Name.encode(meet.name),
      left: meet.left,
      right: meet.right,
      left_dom: Name.encode(meet.left),
      right_dom: Name.encode(meet.right),
      base: base,
      left_session: lane_session(book, meet.left, base),
      right_session: lane_session(book, meet.right, base),
      steps: Enum.count(rows, &(&1.kind != :terminal)),
      evidence: evidence,
      spec: spec,
      dual: dual,
      dual_name: dual_name(book, base),
      checked: true,
      buffer: Map.get(meet, :buffer),
      left_loc: loc(find_name(book, meet.left), path),
      right_loc: loc(find_name(book, meet.right), path),
      left_select: select_id(nodes, meet.left),
      right_select: select_id(nodes, meet.right),
      base_select: select_id(nodes, base),
      rows: rows,
      href: "/?meet=" <> URI.encode_www_form(meet.name)
    }
  end

  defp groups(meetings) do
    meetings
    |> Enum.map(& &1.base)
    |> Enum.uniq()
    |> Enum.map(fn base ->
      rows = Enum.filter(meetings, &(&1.base == base))

      %{
        base: base,
        dom: Name.encode(base),
        spec: rows |> List.first() |> then(&(&1 && &1.spec)) || "",
        meetings: rows
      }
    end)
  end

  defp rows_for(meet) do
    case Map.get(meet, :graph) do
      %{states: states, transitions: transitions}
      when is_list(states) and is_list(transitions) ->
        MuroVisor.Sequence.rows(states, transitions, meet.left, meet.right)

      _ ->
        []
    end
  end

  defp base_name(meet, book) do
    case Map.get(meet, :session) do
      name when is_binary(name) -> name
      _ -> session_name(find_name(book, meet.left)) || meet.name
    end
  end

  defp lane_session(book, party, base) do
    sess_name = session_name(find_name(book, party))
    sess = sess_name && find_name(book, sess_name)

    case sess && Map.get(sess, :proto) do
      {:dual, target} -> "dual " <> (ref_name(target) || base)
      _ -> sess_name || base
    end
  end

  defp opened_proto(book, base) do
    case Muro.Check.open_session(book, base) do
      {:ok, %{proto: proto}} -> proto
      _ -> nil
    end
  end

  defp protocols(_book, _base, proto) when not is_nil(proto) do
    {Muro.Session.show_proto(proto), Muro.Session.show_proto(Muro.Session.dual(proto))}
  end

  defp protocols(book, base, _proto) do
    case find_name(book, base) do
      %{proto: proto} -> {declared(proto), declared(proto)}
      _ -> {"", ""}
    end
  end

  defp declared({:dual, target}), do: "dual " <> (ref_name(target) || "")
  defp declared(proto), do: Muro.Session.show_proto(proto)

  defp evidence(book, base) do
    proto =
      case Muro.Check.open_session(book, base) do
        {:ok, %{proto: proto}} -> proto
        _ -> declared_proto(book, base)
      end

    proto |> bounds() |> Enum.join(" ")
  end

  defp declared_proto(book, base) do
    case find_name(book, base) do
      %{proto: proto} -> proto
      _ -> nil
    end
  end

  defp dual_name(book, base) do
    case Enum.find(
           book,
           &(Map.get(&1, :kind) == :session and dual_of?(Map.get(&1, :proto), base))
         ) do
      %{name: name} -> name
      _ -> nil
    end
  end

  defp dual_of?({:dual, name}, base) when name == base, do: true
  defp dual_of?({:dual, {:sess, name, _}}, base) when name == base, do: true
  defp dual_of?(_proto, _base), do: false

  defp bounds(nil), do: []
  defp bounds({:esend, name, e, rest}), do: [bound(name, e) | bounds(rest)]
  defp bounds({:erecv, name, e, rest}), do: [bound(name, e) | bounds(rest)]
  defp bounds({:send, _, rest}), do: bounds(rest)
  defp bounds({:recv, _, rest}), do: bounds(rest)
  defp bounds({:dsend, _, _, rest}), do: bounds(rest)
  defp bounds({:drecv, _, _, rest}), do: bounds(rest)
  defp bounds({:isend, _, left, right}), do: bounds(left) ++ bounds(right)
  defp bounds({:irecv, _, left, right}), do: bounds(left) ++ bounds(right)
  defp bounds({:choose, left, right}), do: bounds(left) ++ bounds(right)
  defp bounds({:branch, left, right}), do: bounds(left) ++ bounds(right)
  defp bounds({:rec, _, rest}), do: bounds(rest)

  defp bounds({:case, _, arms}) when is_list(arms) do
    Enum.flat_map(arms, fn {_ctor, rest} -> bounds(rest) end)
  end

  defp bounds(_other), do: []

  defp bound(name, expr), do: "{#{show_name(name)} ≤ #{show_expr(expr)}}"

  defp show_name(name) when is_atom(name), do: Atom.to_string(name)
  defp show_name(name) when is_binary(name), do: name
  defp show_name(name), do: to_string(name)

  defp show_expr({:var, name}), do: show_name(name)
  defp show_expr({:lit, n}) when is_integer(n), do: Integer.to_string(n)
  defp show_expr(n) when is_integer(n), do: Integer.to_string(n)
  defp show_expr(name) when is_atom(name), do: Atom.to_string(name)
  defp show_expr(other), do: inspect(other)

  defp select_id(nodes, name) do
    case Enum.find(nodes, &(&1.name == name)) do
      %{id: id} -> MuroVisor.Detail.dom_id(:node, id)
      _ -> nil
    end
  end

  defp loc(%{file: file, loc: {line, col}}, path)
       when is_binary(file) and is_integer(line) and is_integer(col) do
    "#{relative_file(file, path)}:#{line}:#{col}"
  end

  defp loc(%{loc: {line, col}}, _path) when is_integer(line) and is_integer(col),
    do: "#{line}:#{col}"

  defp loc(_other, _path), do: ""

  defp relative_file(file, path) when is_binary(path) and path != "" do
    if String.contains?(file, ":") do
      Path.basename(file)
    else
      dir = path |> Path.expand() |> Path.dirname()
      file |> Path.expand() |> Path.relative_to(dir)
    end
  end

  defp relative_file(file, _path), do: Path.basename(file)

  defp session_name(%{session: name}) when is_binary(name), do: name
  defp session_name(%{session: {:sess, name, _}}) when is_binary(name), do: name
  defp session_name(_other), do: nil

  defp find_name(book, name) when is_binary(name),
    do: Enum.find(book, &(Map.get(&1, :name) == name))

  defp find_name(_book, _name), do: nil

  defp ref_name(name) when is_binary(name), do: name
  defp ref_name({:sess, name, _}) when is_binary(name), do: name
  defp ref_name(_other), do: nil
end
