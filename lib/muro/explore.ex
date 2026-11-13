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

  alias Muro.{Async, Ast, Check, Meet, Session}
  alias Muro.Emit.Name

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
      when is_binary(proc) and
             (is_integer(index) or
                (is_tuple(index) and tuple_size(index) == 3 and elem(index, 0) == :down)) do
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
    |> Enum.filter(&node?/1)
    |> Enum.map(fn d ->
      %{
        id: Name.encode(d.name),
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
      acc = step_edges(book, d, from, by_name, acc)
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
        nil ->
          acc

        ty ->
          span = Map.get(d, :type_span) || {Map.get(d, :loc), :fallback}
          walk_term(ty, span, MapSet.new(), names, by_name, from, acc)
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
    acc = walk_term(ty, kid(span, 0), bound, names, by_name, from, acc)
    walk_term(body, kid(span, 1), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:pi, _, ty, x, body}, span, bound, names, by_name, from, acc) do
    acc = walk_term(ty, kid(span, 0), bound, names, by_name, from, acc)
    walk_term(body, kid(span, 1), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:mnat, e, x, p, z, y, s}, span, bound, names, by_name, from, acc) do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, kid(span, 1), bind(bound, x), names, by_name, from, acc)
    acc = walk_term(z, kid(span, 2), bound, names, by_name, from, acc)
    walk_term(s, kid(span, 3), bind(bound, y), names, by_name, from, acc)
  end

  defp walk_term({tag, e, x, p, branches}, span, bound, names, by_name, from, acc)
       when tag in [:mwbool, :mopt] do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, kid(span, 1), bind(bound, x), names, by_name, from, acc)

    branches
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {{_cname, binders, body}, i}, acc ->
      bound1 = if is_list(binders), do: bind_all(bound, binders), else: bound
      walk_term(body, kid(span, i + 2), bound1, names, by_name, from, acc)
    end)
  end

  defp walk_term({:mdata, e, x, p, branches}, span, bound, names, by_name, from, acc) do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, kid(span, 1), bind(bound, x), names, by_name, from, acc)

    branches
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {{_cname, binders, body}, i}, acc ->
      walk_term(body, kid(span, i + 2), bind_all(bound, binders), names, by_name, from, acc)
    end)
  end

  defp walk_term({:letp, e, a, b, t}, span, bound, names, by_name, from, acc) do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    walk_term(t, kid(span, 1), bind(bind(bound, a), b), names, by_name, from, acc)
  end

  defp walk_term({:nu, x, f}, span, bound, names, by_name, from, acc) do
    walk_term(f, kid(span, 0), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:rwt, e, x, p, t}, span, bound, names, by_name, from, acc) do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, kid(span, 1), bind(bound, x), names, by_name, from, acc)
    walk_term(t, kid(span, 2), bound, names, by_name, from, acc)
  end

  defp walk_term({:memp, e, x, p}, span, bound, names, by_name, from, acc) do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    walk_term(p, kid(span, 1), bind(bound, x), names, by_name, from, acc)
  end

  defp walk_term({:munit, e, x, p, u}, span, bound, names, by_name, from, acc) do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, kid(span, 1), bind(bound, x), names, by_name, from, acc)
    walk_term(u, kid(span, 2), bound, names, by_name, from, acc)
  end

  defp walk_term({:matom, e, x, p, branches}, span, bound, names, by_name, from, acc) do
    acc = walk_term(e, kid(span, 0), bound, names, by_name, from, acc)
    acc = walk_term(p, kid(span, 1), bind(bound, x), names, by_name, from, acc)

    branches
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {{_name, body}, i}, acc ->
      walk_term(body, kid(span, i + 2), bound, names, by_name, from, acc)
    end)
  end

  defp walk_term(term, span, bound, names, by_name, from, acc) do
    kids = Ast.children(term)

    Enum.reduce(Enum.with_index(kids), acc, fn {kid_term, i}, acc ->
      walk_term(kid_term, kid(span, i), bound, names, by_name, from, acc)
    end)
  end

  defp step_edges(book, %{kind: kind, proc: proc} = d, from, by_name, acc)
       when kind in [:conform, :read] do
    case session_id(book, d, by_name) do
      nil ->
        acc

      to ->
        names = MapSet.new(Map.keys(by_name))

        spine_edges(
          Session.spine(proc, Map.get(d, :steps)),
          from,
          to,
          d.name,
          names,
          by_name,
          acc
        )
    end
  end

  defp step_edges(_book, _, _, _, acc), do: acc

  defp spine_edges(items, from, to, proc_name, names, by_name, acc) do
    {acc, _} =
      Enum.reduce(Enum.with_index(items), {acc, MapSet.new()}, fn {item, i}, {acc, bound} ->
        acc = use_edge(acc, from, to, item_loc(item), i, proc_name, :step)

        case item do
          {:put, _, val, _} ->
            {val_uses(val, bound, from, item_loc(item), names, by_name, acc), bound}

          {:get, _, name, _} ->
            {acc, bind(bound, name)}

          {:rest, proc, span} ->
            {descend(proc, span, i, bound, from, to, proc_name, names, by_name, acc), bound}

          _ ->
            {acc, bound}
        end
      end)

    acc
  end

  # The spine edge is the branch head. Children keep that index and do
  # not emit the head again.
  defp descend({:rec, _, body}, span, spine_i, bound, from, to, proc_name, names, by_name, acc) do
    descend(
      body,
      Session.step_down(span, 0),
      spine_i,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp descend({:cover, p, q}, span, spine_i, bound, from, to, proc_name, names, by_name, acc) do
    acc =
      seq(
        p,
        Session.step_down(span, 0),
        [0],
        spine_i,
        0,
        bound,
        from,
        to,
        proc_name,
        names,
        by_name,
        acc
      )

    seq(
      q,
      Session.step_down(span, 1),
      [1],
      spine_i,
      0,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp descend(
         {:iget, name, p, q},
         span,
         spine_i,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    bound = bind(bound, name)

    acc =
      seq(
        p,
        Session.step_down(span, 0),
        [0],
        spine_i,
        0,
        bound,
        from,
        to,
        proc_name,
        names,
        by_name,
        acc
      )

    seq(
      q,
      Session.step_down(span, 1),
      [1],
      spine_i,
      0,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp descend({:match, _, arms}, span, spine_i, bound, from, to, proc_name, names, by_name, acc) do
    arms
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {arm, i}, acc ->
      seq(
        Session.arm_body(arm),
        Session.step_down(span, i),
        [i],
        spine_i,
        0,
        bind_all(bound, Session.arm_binders(arm)),
        from,
        to,
        proc_name,
        names,
        by_name,
        acc
      )
    end)
  end

  defp descend(_, _, _, _, _, _, _, _, _, acc), do: acc

  defp seq(
         {:rec, _, body},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    seq(
      body,
      Session.step_down(span, 0),
      path,
      spine_i,
      local,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp seq(
         {:put, _, val, cont},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    at = Session.step_at(span)
    acc = use_edge(acc, from, to, at, {:down, spine_i, path ++ [local]}, proc_name, :step)
    acc = val_uses(val, bound, from, at, names, by_name, acc)

    seq(
      cont,
      Session.step_down(span, 0),
      path,
      spine_i,
      local + 1,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp seq(
         {:get, _, name, cont},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    at = Session.step_at(span)
    acc = use_edge(acc, from, to, at, {:down, spine_i, path ++ [local]}, proc_name, :step)

    seq(
      cont,
      Session.step_down(span, 0),
      path,
      spine_i,
      local + 1,
      bind(bound, name),
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp seq(
         {:pick0, cont},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    seq_act(cont, span, path, spine_i, local, bound, from, to, proc_name, names, by_name, acc)
  end

  defp seq(
         {:pick1, cont},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    seq_act(cont, span, path, spine_i, local, bound, from, to, proc_name, names, by_name, acc)
  end

  defp seq(
         {:cover, p, q},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    at = Session.step_at(span)
    acc = use_edge(acc, from, to, at, {:down, spine_i, path ++ [local]}, proc_name, :step)
    nested = path ++ [local]

    acc =
      seq(
        p,
        Session.step_down(span, 0),
        nested ++ [0],
        spine_i,
        0,
        bound,
        from,
        to,
        proc_name,
        names,
        by_name,
        acc
      )

    seq(
      q,
      Session.step_down(span, 1),
      nested ++ [1],
      spine_i,
      0,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp seq(
         {:iget, name, p, q},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    at = Session.step_at(span)
    acc = use_edge(acc, from, to, at, {:down, spine_i, path ++ [local]}, proc_name, :step)
    bound = bind(bound, name)
    nested = path ++ [local]

    acc =
      seq(
        p,
        Session.step_down(span, 0),
        nested ++ [0],
        spine_i,
        0,
        bound,
        from,
        to,
        proc_name,
        names,
        by_name,
        acc
      )

    seq(
      q,
      Session.step_down(span, 1),
      nested ++ [1],
      spine_i,
      0,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  defp seq(
         {:match, _, arms},
         span,
         path,
         spine_i,
         local,
         bound,
         from,
         to,
         proc_name,
         names,
         by_name,
         acc
       ) do
    at = Session.step_at(span)
    acc = use_edge(acc, from, to, at, {:down, spine_i, path ++ [local]}, proc_name, :step)
    nested = path ++ [local]

    arms
    |> Enum.with_index()
    |> Enum.reduce(acc, fn {arm, i}, acc ->
      seq(
        Session.arm_body(arm),
        Session.step_down(span, i),
        nested ++ [i],
        spine_i,
        0,
        bind_all(bound, Session.arm_binders(arm)),
        from,
        to,
        proc_name,
        names,
        by_name,
        acc
      )
    end)
  end

  defp seq(_, _, _, _, _, _, _, _, _, _, _, acc), do: acc

  defp seq_act(cont, span, path, spine_i, local, bound, from, to, proc_name, names, by_name, acc) do
    at = Session.step_at(span)
    acc = use_edge(acc, from, to, at, {:down, spine_i, path ++ [local]}, proc_name, :step)

    seq(
      cont,
      Session.step_down(span, 0),
      path,
      spine_i,
      local + 1,
      bound,
      from,
      to,
      proc_name,
      names,
      by_name,
      acc
    )
  end

  # A free name in a sent value is a use of that definition. A name bound
  # by an earlier `get` on this spine is the received value, not a definition.
  defp val_uses(val, bound, from, loc, names, by_name, acc) do
    walk_val(val, bound, from, loc, names, by_name, acc)
  end

  defp walk_val({:var, name}, bound, from, loc, names, by_name, acc) do
    case val_name(name) do
      bin when is_binary(bin) and bin not in [""] ->
        if blocked?(bound, bin) or not MapSet.member?(names, bin) do
          acc
        else
          use_edge(acc, from, Map.fetch!(by_name, bin), loc, nil, nil, :def)
        end

      _ ->
        acc
    end
  end

  defp walk_val(term, bound, from, loc, names, by_name, acc) when is_tuple(term) do
    term
    |> Tuple.to_list()
    |> Enum.reduce(acc, &walk_val(&1, bound, from, loc, names, by_name, &2))
  end

  defp walk_val(term, bound, from, loc, names, by_name, acc) when is_list(term) do
    Enum.reduce(term, acc, &walk_val(&1, bound, from, loc, names, by_name, &2))
  end

  defp walk_val(_, _, _, _, _, _, acc), do: acc

  defp val_name(name) when is_binary(name), do: name
  defp val_name(name) when is_atom(name) and not is_nil(name), do: Atom.to_string(name)
  defp val_name(_), do: nil

  defp blocked?(bound, name) do
    MapSet.member?(bound, name) or MapSet.member?(bound, atom_name(name))
  end

  defp atom_name(name) do
    String.to_existing_atom(name)
  rescue
    ArgumentError -> nil
  end

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
        Map.get(d, :kind) == :meet and meeting_session(book, d) == name
      end)

    {children, transitions} =
      Enum.reduce(meetings, {[], []}, fn meet, {cs, ts} ->
        graph = meeting_graph(book, meet)
        prefix = "cfg-" <> Name.encode(name) <> "-" <> Name.encode(meet.name)

        left = party(book, meet.left)
        right = party(book, meet.right)
        lf = party_file(left)
        rf = party_file(right)

        cs = cs ++ Enum.map(graph.states, &child(&1, prefix, meet.name, lf, rf))

        ts =
          ts ++
            Enum.map(Enum.with_index(graph.transitions), fn {t, i} ->
              from = "#{prefix}-#{t.from}"
              to = "#{prefix}-#{t.to}"

              %{
                id: "#{i}-#{from}-#{to}",
                from: from,
                to: to,
                label: t.label,
                loc: qualify(t.loc, lf, rf),
                side: Map.get(t, :side),
                meeting: meet.name
              }
            end)

        {cs, ts}
      end)

    %{node | children: children, transitions: transitions}
  end

  defp attach(node, _book, _by_name), do: node

  defp child(st, prefix, meeting, left_file, right_file) do
    %{
      id: prefix <> "-" <> Integer.to_string(st.id),
      left: st.left,
      right: st.right,
      l2r: Map.get(st, :l2r, []),
      r2l: Map.get(st, :r2l, []),
      loc: qualify(st.loc, left_file, right_file),
      meeting: meeting
    }
  end

  defp meeting_graph(_book, %{graph: %{states: states, transitions: transitions}})
       when is_list(states) and is_list(transitions) do
    %{states: states, transitions: transitions}
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

  defp meeting_session(_book, %{session: session}) when is_binary(session), do: session

  defp meeting_session(book, %{left: left}), do: session_of_party(book, left)

  defp session_of_party(book, name) do
    case party(book, name) do
      nil -> nil
      d -> session_name_of(book, d)
    end
  end

  defp session_id(book, d, by_name) do
    case session_name_of(book, d) do
      nil -> nil
      name -> Map.get(by_name, name)
    end
  end

  defp session_name_of(book, %{kind: :read, endpoint: ename}) do
    case Enum.find(book, &(Map.get(&1, :kind) == :endpoint and &1.name == ename)) do
      %{session: session} -> ref_name(session)
      _ -> nil
    end
  end

  defp session_name_of(_book, %{session: session}), do: ref_name(session)
  defp session_name_of(_book, _), do: nil

  defp session_ref(book, %{kind: :read, endpoint: ename}) do
    case Enum.find(book, &(Map.get(&1, :kind) == :endpoint and &1.name == ename)) do
      %{session: session} -> session
      _ -> nil
    end
  end

  defp session_ref(_book, %{session: session}), do: session
  defp session_ref(_book, _), do: nil

  defp session_proto(book, defn) do
    case session_ref(book, defn) do
      nil ->
        {:error, "unknown session"}

      ref ->
        case Check.open_session(book, ref) do
          {:ok, session} -> {:ok, session.proto}
          {:error, msg} -> {:error, msg}
        end
    end
  end

  defp party_file(%{file: file}) when is_binary(file), do: file
  defp party_file(_), do: nil

  defp qualify(%{left: left, right: right}, lf, rf) do
    %{left: with_file(lf, left), right: with_file(rf, right)}
  end

  defp qualify(other, _lf, _rf), do: other

  defp with_file(file, {line, col}) when is_binary(file) and is_integer(line) and is_integer(col),
    do: {file, line, col}

  defp with_file(_file, other), do: other

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

  defp kid({_loc, :fallback} = span, _i), do: span
  defp kid({_loc, kids}, i) when is_list(kids), do: Enum.at(kids, i)
  defp kid(_, _), do: nil

  defp bind(bound, name) when is_binary(name), do: MapSet.put(bound, name)
  defp bind(bound, name) when is_atom(name) and name != nil, do: MapSet.put(bound, name)
  defp bind(bound, _), do: bound

  defp bind_all(bound, names) when is_list(names), do: Enum.reduce(names, bound, &bind(&2, &1))
  defp bind_all(bound, _), do: bound

  # A test listens by passing its pid. Production leaves the key unset,
  # and a check then does nothing here. `:meeting` is the checker's one
  # walk, which records the source configuration graph. `:graph` is the
  # compiled configuration graph, explored once per meeting.
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
