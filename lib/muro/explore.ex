defmodule Muro.Explore do
  @moduledoc """
  The book as a graph, read from a book `Muro.Load.file/1` already checked.

  One node for each spec, evidence, and run. One edge for each use: a
  free name in a term, a step of a process, a party of a meeting, and a
  `dual`. A session node holds the configurations its meetings proved.
  Those configurations are the graph `Muro.Meet` or `Muro.Async` records
  while it decides the meeting, not a second search.

  Nothing here emits code or writes the book.
  """

  alias Muro.{Async, Ast, Meet, Session}

  @doc """
  Nodes, edges, and the configurations attached to each session.
  """
  def graph(book) when is_list(book) do
    nodes = nodes(book)
    by_name = Map.new(nodes, &{&1.name, &1.id})
    names = MapSet.new(Map.keys(by_name))
    edges = edges(book, by_name, names)
    nodes = Enum.map(nodes, &attach(&1, book, by_name))
    %{nodes: nodes, edges: edges}
  end

  @doc """
  The refusal for one edge.

  A step is re-checked with that step moved one place earlier.
  Any other use is `:not_a_step`, and the location is the use.
  """
  def out_of_order(book, %{use: :step, proc: proc, step: index} = edge)
      when is_binary(proc) and is_integer(index) do
    case party(book, proc) do
      nil ->
        not_step(edge)

      defn ->
        case session_proto(book, defn) do
          {:ok, proto} ->
            Session.out_of_order(defn.proc, proto, book, Map.get(defn, :steps), index)

          {:error, msg} ->
            %{
              kind: :error,
              loc: edge.loc,
              proc: nil,
              proto: nil,
              reason: msg,
              index: index
            }
        end
    end
  end

  def out_of_order(_book, edge) when is_map(edge) do
    not_step(edge)
  end

  def out_of_order(book, proc, index) when is_binary(proc) and is_integer(index) do
    out_of_order(book, %{use: :step, proc: proc, step: index, loc: nil})
  end

  defp not_step(edge) do
    %{
      kind: :not_a_step,
      loc: Map.get(edge, :loc),
      proc: nil,
      proto: nil,
      reason: nil,
      index: Map.get(edge, :step)
    }
  end

  defp nodes(book) do
    book
    |> Enum.filter(&node?(&1))
    |> Enum.with_index()
    |> Enum.map(fn {d, i} ->
      %{
        id: "d#{i}",
        name: d.name,
        mode: d.mode,
        kind: Map.get(d, :kind, :def),
        loc: Map.get(d, :loc),
        file: Map.get(d, :file),
        children: [],
        transitions: []
      }
    end)
  end

  defp node?(d) do
    is_map(d) and is_binary(Map.get(d, :name)) and Map.get(d, :mode) in [:spec, :evidence, :run]
  end

  defp edges(book, by_name, names) do
    book
    |> Enum.filter(&node?/1)
    |> Enum.reduce([], fn d, acc ->
      from = Map.fetch!(by_name, d.name)
      acc = term_edges(d, from, names, by_name, acc)
      acc = step_edges(d, from, by_name, acc)
      acc = meet_edges(d, from, by_name, acc)
      dual_edges(d, from, by_name, acc)
    end)
    |> Enum.reverse()
    |> Enum.with_index()
    |> Enum.map(fn {e, i} -> Map.put(e, :id, "e#{i}") end)
  end

  defp term_edges(d, from, names, by_name, acc) do
    acc =
      case Map.get(d, :type) do
        nil -> acc
        ty -> walk_term(ty, nil, MapSet.new(), names, by_name, from, acc)
      end

    case Map.get(d, :body) do
      nil -> acc
      body -> walk_term(body, Map.get(d, :body_span), MapSet.new(), names, by_name, from, acc)
    end
  end

  defp walk_term({:var, name}, span, bound, names, by_name, from, acc) do
    if is_binary(name) and name not in bound and MapSet.member?(names, name) do
      use_edge(acc, from, Map.fetch!(by_name, name), span_loc(span), nil, nil, :def)
    else
      acc
    end
  end

  defp walk_term({:lam, _, ty, x, body}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(ty, Enum.at(kids, 0), bound, names, by_name, from, acc)
    walk_term(body, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:pi, _, ty, x, body}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(ty, Enum.at(kids, 0), bound, names, by_name, from, acc)
    walk_term(body, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:mnat, e, x, p, z, y, s}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(e, Enum.at(kids, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)
    acc = walk_term(z, Enum.at(kids, 2), bound, names, by_name, from, acc)
    walk_term(s, Enum.at(kids, 3), bind(bound, y), names, by_name, from, acc)
  end

  defp walk_term({:mdata, e, x, p, branches}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(e, Enum.at(kids, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)

    branches
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {{_cname, binders, body}, i}, acc ->
      walk_term(body, Enum.at(kids, i + 2), bind_all(bound, binders), names, by_name, from, acc)
    end)
  end

  defp walk_term({:letp, e, a, b, t}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(e, Enum.at(kids, 0), bound, names, by_name, from, acc)
    walk_term(t, Enum.at(kids, 1), bind(bind(bound, a), b), names, by_name, from, acc)
  end

  defp walk_term({:nu, x, f}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    walk_term(f, Enum.at(kids, 0), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:rwt, e, x, p, t}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(e, Enum.at(kids, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)
    walk_term(t, Enum.at(kids, 2), bound, names, by_name, from, acc)
  end

  defp walk_term({:memp, e, x, p}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(e, Enum.at(kids, 0), bound, names, by_name, from, acc)
    walk_term(p, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:munit, e, x, p, u}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(e, Enum.at(kids, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)
    walk_term(u, Enum.at(kids, 2), bound, names, by_name, from, acc)
  end

  defp walk_term({:matom, e, x, p, branches}, span, bound, names, by_name, from, acc) do
    kids = span_kids(span)
    acc = walk_term(e, Enum.at(kids, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, Enum.at(kids, 1), bind(bound, x), names, by_name, from, acc)

    branches
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {{_name, body}, i}, acc ->
      walk_term(body, Enum.at(kids, i + 2), bound, names, by_name, from, acc)
    end)
  end

  defp walk_term(term, span, bound, names, by_name, from, acc) do
    kids = Ast.children(term)
    spans = span_kids(span)

    Enum.reduce(Enum.with_index(kids), acc, fn {kid, i}, acc ->
      walk_term(kid, Enum.at(spans, i), bound, names, by_name, from, acc)
    end)
  end

  defp step_edges(%{kind: kind, proc: proc} = d, from, by_name, acc)
       when kind in [:conform, :read] do
    case session_id(d, by_name) do
      nil ->
        acc

      to ->
        spine_edges(Session.spine(proc, Map.get(d, :steps)), from, to, d.name, acc)
    end
  end

  defp step_edges(_, _, _, acc), do: acc

  defp spine_edges(items, from, to, proc_name, acc) do
    Enum.reduce(Enum.with_index(items), acc, fn {item, i}, acc ->
      acc = use_edge(acc, from, to, item_loc(item), i, proc_name, :step)

      case item do
        {:put, _, val, _} -> val_uses(val, MapSet.new(), from, acc)
        {:rest, proc, span} -> nested_steps(proc, span, MapSet.new(), from, to, proc_name, acc)
        _ -> acc
      end
    end)
  end

  defp nested_steps({:put, _, val, cont}, span, bound, from, to, proc_name, acc) do
    acc = use_edge(acc, from, to, Session.step_at(span), nil, proc_name, :step)
    acc = val_uses(val, bound, from, acc)
    nested_steps(cont, Session.step_down(span, 0), bound, from, to, proc_name, acc)
  end

  defp nested_steps({:get, _, name, cont}, span, bound, from, to, proc_name, acc) do
    acc = use_edge(acc, from, to, Session.step_at(span), nil, proc_name, :step)
    nested_steps(cont, Session.step_down(span, 0), bind(bound, name), from, to, proc_name, acc)
  end

  defp nested_steps({:pick0, cont}, span, bound, from, to, proc_name, acc) do
    acc = use_edge(acc, from, to, Session.step_at(span), nil, proc_name, :step)
    nested_steps(cont, Session.step_down(span, 0), bound, from, to, proc_name, acc)
  end

  defp nested_steps({:pick1, cont}, span, bound, from, to, proc_name, acc) do
    acc = use_edge(acc, from, to, Session.step_at(span), nil, proc_name, :step)
    nested_steps(cont, Session.step_down(span, 0), bound, from, to, proc_name, acc)
  end

  defp nested_steps({:cover, p, q}, span, bound, from, to, proc_name, acc) do
    acc = use_edge(acc, from, to, Session.step_at(span), nil, proc_name, :step)
    acc = nested_steps(p, Session.step_down(span, 0), bound, from, to, proc_name, acc)
    nested_steps(q, Session.step_down(span, 1), bound, from, to, proc_name, acc)
  end

  defp nested_steps({:iget, name, p, q}, span, bound, from, to, proc_name, acc) do
    acc = use_edge(acc, from, to, Session.step_at(span), nil, proc_name, :step)
    bound = bind(bound, name)
    acc = nested_steps(p, Session.step_down(span, 0), bound, from, to, proc_name, acc)
    nested_steps(q, Session.step_down(span, 1), bound, from, to, proc_name, acc)
  end

  defp nested_steps({:match, _, arms}, span, bound, from, to, proc_name, acc) do
    acc = use_edge(acc, from, to, Session.step_at(span), nil, proc_name, :step)

    arms
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {arm, i}, acc ->
      nested_steps(
        Session.arm_body(arm),
        Session.step_down(span, i),
        bind_all(bound, Session.arm_binders(arm)),
        from,
        to,
        proc_name,
        acc
      )
    end)
  end

  defp nested_steps({:rec, _, body}, span, bound, from, to, proc_name, acc) do
    nested_steps(body, Session.step_down(span, 0), bound, from, to, proc_name, acc)
  end

  defp nested_steps(_, _, _, _, _, _, acc), do: acc

  # Values carried by a step. A bound name is the `get` that received it.
  # The linear spine's binders are not in scope for a later `put` of a
  # book definition: a free name is a use. Binders along the spine are
  # applied by `val_uses/4` only for the value at that step. Nested
  # steps thread the binder.
  defp val_uses(_val, _bound, _from, acc), do: acc

  defp meet_edges(%{kind: :meet, left: left, right: right, loc: loc}, from, by_name, acc) do
    acc = party_edge(acc, from, left, by_name, loc)
    party_edge(acc, from, right, by_name, loc)
  end

  defp meet_edges(_, _, _, acc), do: acc

  defp party_edge(acc, from, name, by_name, loc) do
    case Map.get(by_name, name) do
      nil -> acc
      to -> use_edge(acc, from, to, loc, nil, nil, :meet)
    end
  end

  defp dual_edges(%{kind: :session, proto: proto, loc: loc}, from, by_name, acc) do
    proto_refs(proto, from, by_name, loc, acc)
  end

  defp dual_edges(_, _, _, acc), do: acc

  defp proto_refs({:dual, ref}, from, by_name, loc, acc) do
    case ref_name(ref) do
      nil -> acc
      name -> party_use(acc, from, name, by_name, loc, :dual)
    end
  end

  defp proto_refs({:sess, name, _}, from, by_name, loc, acc) do
    party_use(acc, from, name, by_name, loc, :def)
  end

  defp proto_refs({:send, _, s}, from, by_name, loc, acc),
    do: proto_refs(s, from, by_name, loc, acc)

  defp proto_refs({:recv, _, s}, from, by_name, loc, acc),
    do: proto_refs(s, from, by_name, loc, acc)

  defp proto_refs({:dsend, _, _, s}, from, by_name, loc, acc),
    do: proto_refs(s, from, by_name, loc, acc)

  defp proto_refs({:drecv, _, _, s}, from, by_name, loc, acc),
    do: proto_refs(s, from, by_name, loc, acc)

  defp proto_refs({:esend, _, _, s}, from, by_name, loc, acc),
    do: proto_refs(s, from, by_name, loc, acc)

  defp proto_refs({:erecv, _, _, s}, from, by_name, loc, acc),
    do: proto_refs(s, from, by_name, loc, acc)

  defp proto_refs({:isend, _, s, t}, from, by_name, loc, acc) do
    acc = proto_refs(s, from, by_name, loc, acc)
    proto_refs(t, from, by_name, loc, acc)
  end

  defp proto_refs({:irecv, _, s, t}, from, by_name, loc, acc) do
    acc = proto_refs(s, from, by_name, loc, acc)
    proto_refs(t, from, by_name, loc, acc)
  end

  defp proto_refs({:choose, s, t}, from, by_name, loc, acc) do
    acc = proto_refs(s, from, by_name, loc, acc)
    proto_refs(t, from, by_name, loc, acc)
  end

  defp proto_refs({:branch, s, t}, from, by_name, loc, acc) do
    acc = proto_refs(s, from, by_name, loc, acc)
    proto_refs(t, from, by_name, loc, acc)
  end

  defp proto_refs({:rec, _, s}, from, by_name, loc, acc),
    do: proto_refs(s, from, by_name, loc, acc)

  defp proto_refs({:case, _, arms}, from, by_name, loc, acc) do
    Enum.reduce(arms, acc, fn {_c, s}, acc -> proto_refs(s, from, by_name, loc, acc) end)
  end

  defp proto_refs(_, _, _, _, acc), do: acc

  defp party_use(acc, from, name, by_name, loc, use) do
    case Map.get(by_name, name) do
      nil -> acc
      to -> use_edge(acc, from, to, loc, nil, nil, use)
    end
  end

  defp attach(%{kind: :session, name: name} = node, book, _by_name) do
    meetings =
      Enum.filter(book, fn d ->
        Map.get(d, :kind) == :meet and session_of_party(book, d.left) == name
      end)

    {children, transitions} =
      Enum.reduce(meetings, {[], []}, fn meet, {cs, ts} ->
        graph = meeting_graph(book, meet)
        prefix = "cfg-#{name}-#{meet.name}"

        cs = cs ++ Enum.map(graph.states, &child(&1, prefix, meet.name))

        ts =
          ts ++
            Enum.map(graph.transitions, fn t ->
              %{
                from: "#{prefix}-#{t.from}",
                to: "#{prefix}-#{t.to}",
                label: t.label,
                loc: t.loc,
                side: Map.get(t, :side),
                meeting: meet.name
              }
            end)

        {cs, ts}
      end)

    %{node | children: children, transitions: transitions}
  end

  defp attach(node, _book, _by_name), do: node

  defp child(st, prefix, meeting) do
    %{
      id: "#{prefix}-#{st.id}",
      left: st.left,
      right: st.right,
      l2r: Map.get(st, :l2r, []),
      r2l: Map.get(st, :r2l, []),
      loc: st.loc,
      meeting: meeting
    }
  end

  defp meeting_graph(book, meet) do
    left = party(book, meet.left)
    right = party(book, meet.right)

    if left && right && Map.get(left, :proc) && Map.get(right, :proc) do
      spans = {Map.get(left, :steps), Map.get(right, :steps)}

      case Map.get(meet, :buffer) do
        n when is_integer(n) ->
          Async.graph(left.proc, right.proc, book, n, meet.left, meet.right, spans)

        _ ->
          {_verdict, graph} = Meet.graph(left.proc, right.proc, book, nil, spans)
          graph
      end
    else
      %{states: [], transitions: []}
    end
  end

  defp session_of_party(book, name) do
    case party(book, name) do
      %{session: session} -> ref_name(session)
      _ -> nil
    end
  end

  defp session_id(d, by_name) do
    case Map.get(d, :session) do
      nil -> nil
      session -> Map.get(by_name, ref_name(session))
    end
  end

  defp session_proto(book, defn) do
    name = ref_name(Map.get(defn, :session))

    case Enum.find(book, &(Map.get(&1, :kind) == :session and &1.name == name)) do
      nil -> {:error, "unknown session #{name}"}
      sess -> Session.elaborate(sess, book)
    end
  end

  defp party(book, name) do
    Enum.find(book, &(Map.get(&1, :kind) in [:conform, :read] and &1.name == name))
  end

  defp ref_name(name) when is_binary(name), do: name
  defp ref_name({:sess, name, _}) when is_binary(name), do: name
  defp ref_name(_), do: nil

  defp use_edge(acc, from, to, loc, step, proc, use) do
    [%{from: from, to: to, loc: loc, step: step, proc: proc, use: use} | acc]
  end

  defp item_loc({:put, _, _, at}), do: at
  defp item_loc({:get, _, _, at}), do: at
  defp item_loc({:pick0, at}), do: at
  defp item_loc({:pick1, at}), do: at
  defp item_loc({:rest, _, span}), do: Session.step_at(span)

  defp span_loc({loc, _kids}) when is_tuple(loc), do: loc
  defp span_loc(%{at: at}), do: at
  defp span_loc(_), do: nil

  defp span_kids({_loc, kids}) when is_list(kids), do: kids
  defp span_kids(_), do: []

  defp bind(bound, name) when is_binary(name), do: MapSet.put(bound, name)
  defp bind(bound, name) when is_atom(name) and name != nil, do: MapSet.put(bound, name)
  defp bind(bound, _), do: bound

  defp bind_all(bound, names) when is_list(names), do: Enum.reduce(names, bound, &bind(&2, &1))
  defp bind_all(bound, _), do: bound
end
