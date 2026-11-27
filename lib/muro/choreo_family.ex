defmodule Muro.ChoreoFamily do
  @moduledoc """
  Checks a family that ranges over a choreography.

  `family rollout : plan per key` runs one instance of the global type
  `plan` per key, any number of keys at once, independent across keys.
  A role marked `shared` in `plan` is one party for every key. The
  messages between shared roles, and the choices of shared roles,
  written before any other step are the shared preamble: they happen
  once, before any key steps. Each key then runs the rest of the global
  type in its written order (`Muro.Choreo.advance/2`).

  A formula `forall (k : key)` is decided on one key and the preamble.
  The keys share nothing after the preamble, the preamble is finite, and
  the global type has no recursion, so the runs of one key with the
  preamble are the runs of any key of any number of keys: the check is
  exact. A run steps the key to the end of the global type. A key that
  is never stepped again is not a run, as there is no fairness between
  keys here. The atoms are `done k (a -> b : label)` and
  `done k (p chooses label)`: that interaction has happened in the run
  of key `k`, or in the preamble.
  """

  alias Muro.Choreo

  @atom_msg "a formula over a choreography family names done <key> (<interaction>)"

  @doc """
  `:ok` when the family names a choreography that checks, writes no kind
  and no hold rule, and has at least one role that is not shared.
  `{:error, message}` otherwise. The message has no location and no
  declaration name.
  """
  def check(book, %{meeting: name} = family) when is_list(book) do
    chor = choreography(book, name)

    cond do
      meeting?(book, name) ->
        {:error, "#{name} is a meeting: a family of a meeting names its kind, per key of <Kind>"}

      chor == nil ->
        {:error, "unknown choreography #{name}"}

      Map.get(family, :rules, []) != [] ->
        {:error, "a family of a choreography has no hold rules"}

      Map.get(family, :redeliver, false) ->
        {:error, "may redeliver is a mark on a family of a meeting"}

      true ->
        case Choreo.check_decl(chor, book) do
          {:ok, _} -> per_key_role(chor)
          {:error, _} -> {:error, "skipped because #{name} does not check"}
        end
    end
  end

  @doc """
  The refusal of `family f : plan per key of Kind` when `plan` is a
  choreography and no meeting has that name. `:ok` otherwise.
  """
  def not_choreography(book, name) when is_list(book) do
    if choreography(book, name) != nil and not meeting?(book, name) do
      {:error,
       "#{name} is a choreography: a family of a choreography is per key, with no kind and no hold rules"}
    else
      :ok
    end
  end

  @doc "The success line `family <name>: <choreography> per key`."
  def line(%{name: name, meeting: meeting}), do: "family #{name}: #{meeting} per key"

  @doc """
  `{:ok, states, transitions}` when the formula holds on the runs of one
  key with the shared preamble. `states` is the nodes of the global type
  and `transitions` its interactions, plus one self-loop at each end.
  `{:error, message}` when a binder or an atom is not, or the formula
  fails. An `always` failure is the breadth-first path to the state and
  that state. An `eventually` or `leads_to` failure is the path to an
  end, then `then forever: the key has finished: end`.
  """
  def judge_formula(book, %{name: fam, meeting: name}, formula) when is_list(book) do
    chor = choreography(book, name)

    with {:ok, key, body} <- peel(formula, nil),
         :ok <- walk_formula(chor, key, body) do
      graph = graph(chor)
      decide(graph, fam, body)
    end
  end

  defp choreography(book, name) do
    Enum.find(book, &match?(%{kind: :choreography, name: ^name}, &1))
  end

  defp meeting?(book, name), do: Enum.any?(book, &match?(%{kind: :meet, name: ^name}, &1))

  defp per_key_role(%{name: name, roles: roles} = chor) do
    shared = Map.get(chor, :shared, [])

    if Enum.all?(roles, &(&1 in shared)) do
      {:error, "every role of #{name} is shared, so no step runs per key"}
    else
      :ok
    end
  end

  # ---- the formula ---------------------------------------------------------

  defp peel({:forall, x, {:dat, "key", []}, body}, nil), do: peel(body, x)

  defp peel({:forall, _x, {:dat, "key", []}, _body}, _key),
    do: {:error, "a formula over a choreography family binds one key"}

  defp peel({:forall, _x, ty, _body}, _key),
    do: {:error, "forall over #{forall_ty(ty)} is not a key"}

  defp peel(body, key), do: {:ok, key, body}

  defp forall_ty(:bit), do: "Bit"
  defp forall_ty(:nat), do: "Nat"
  defp forall_ty({:dat, name, _}), do: name
  defp forall_ty(:unit), do: "Unit"
  defp forall_ty({:vec, _, _}), do: "Vec"
  defp forall_ty({:pair, _, _}), do: "a pair"
  defp forall_ty({:rec, _}), do: "a record"
  defp forall_ty(other), do: inspect(other)

  defp walk_formula(chor, key, {:always, p}), do: walk_prop(chor, key, p)
  defp walk_formula(chor, key, {:eventually, p}), do: walk_prop(chor, key, p)

  defp walk_formula(chor, key, {:leads_to, p, q}) do
    with :ok <- walk_prop(chor, key, p), do: walk_prop(chor, key, q)
  end

  defp walk_formula(_chor, _key, _other), do: {:error, @atom_msg}

  defp walk_prop(_chor, _key, b) when is_boolean(b), do: :ok
  defp walk_prop(chor, key, {:not, p}), do: walk_prop(chor, key, p)

  defp walk_prop(chor, key, {op, p, q}) when op in [:and, :or, :imp] do
    with :ok <- walk_prop(chor, key, p), do: walk_prop(chor, key, q)
  end

  defp walk_prop(chor, key, {:did, k, move}) do
    cond do
      k != key -> {:error, "unbound key #{k}"}
      move in moves(chor.body) -> :ok
      true -> {:error, "#{chor.name} has no #{kind_of(move)} #{show_move(move)}"}
    end
  end

  defp walk_prop(_chor, _key, _other), do: {:error, @atom_msg}

  defp kind_of({:msg, _, _, _, _}), do: "interaction"
  defp kind_of({:pick, _, _}), do: "choice"

  defp moves(:end), do: []
  defp moves({:comm, a, b, l, ty, g}), do: [{:msg, a, b, l, ty} | moves(g)]

  defp moves({:choice, p, branches}) do
    Enum.flat_map(branches, fn {l, g} -> [{:pick, p, l} | moves(g)] end)
  end

  defp show_move({:msg, a, b, l, ty}), do: Choreo.show_message(a, b, l, ty)
  defp show_move({:pick, p, l}), do: "#{p} chooses #{l}"

  # ---- the graph -------------------------------------------------------------

  # One node per position of the global type, numbered in breadth-first
  # order. A node keeps the interactions done on the way to it. An edge
  # is labelled with the interaction, marked `(shared)` in the preamble.
  defp graph(chor) do
    shared = Map.get(chor, :shared, [])
    root = %{id: 0, g: chor.body, done: [], path: [], phase: :preamble}
    bfs([root], 1, [], shared)
  end

  defp bfs([], _next, acc, _shared), do: Enum.reverse(acc)

  defp bfs([node | rest], next, acc, shared) do
    kids = children(node, shared)

    {kids, next} =
      Enum.map_reduce(kids, next, fn kid, n -> {Map.put(kid, :id, n), n + 1} end)

    node = Map.put(node, :kids, Enum.map(kids, & &1.id))
    bfs(rest ++ kids, next, [node | acc], shared)
  end

  defp children(%{g: :end}, _shared), do: []

  defp children(%{g: {:comm, a, b, l, ty, cont} = g} = node, shared) do
    [child(node, g, cont, {:msg, a, b, l, ty}, shared)]
  end

  defp children(%{g: {:choice, p, branches} = g} = node, shared) do
    Enum.map(branches, fn {l, cont} -> child(node, g, cont, {:pick, p, l}, shared) end)
  end

  defp child(node, g, cont, move, shared) do
    global? = node.phase == :preamble and Choreo.shared_step?(g, shared)
    text = if global?, do: show_move(move) <> " (shared)", else: show_move(move)

    %{
      g: cont,
      done: [move | node.done],
      path: node.path ++ [text],
      phase: if(global?, do: :preamble, else: :per_key)
    }
  end

  defp decide(nodes, fam, body) do
    by_id = Map.new(nodes, &{&1.id, &1})
    states = length(nodes)
    transitions = Enum.sum(Enum.map(nodes, &max(length(&1.kids), 1)))

    case verdict(nodes, by_id, body) do
      :ok -> {:ok, states, transitions}
      {:always, node} -> {:error, safety_msg(fam, body, node)}
      {:live, leaf} -> {:error, live_msg(fam, body, leaf)}
    end
  end

  defp verdict(nodes, _by_id, {:always, p}) do
    case Enum.find(nodes, &(not holds?(p, &1))) do
      nil -> :ok
      node -> {:always, node}
    end
  end

  defp verdict(nodes, by_id, {:eventually, p}) do
    [root | _] = nodes

    case avoid(root, p, by_id) do
      nil -> :ok
      leaf -> {:live, leaf}
    end
  end

  defp verdict(nodes, by_id, {:leads_to, p, q}) do
    Enum.find_value(nodes, :ok, fn node ->
      if holds?(p, node) do
        case avoid(node, q, by_id) do
          nil -> nil
          leaf -> {:live, leaf}
        end
      end
    end)
  end

  # The first end, in written order, reached from `node` on a path where
  # `p` never holds, `node` included. nil when every path meets `p`.
  defp avoid(node, p, by_id) do
    cond do
      holds?(p, node) -> nil
      node.kids == [] -> node
      true -> Enum.find_value(node.kids, &avoid(Map.fetch!(by_id, &1), p, by_id))
    end
  end

  defp holds?(true, _node), do: true
  defp holds?(false, _node), do: false
  defp holds?({:not, p}, node), do: not holds?(p, node)
  defp holds?({:and, p, q}, node), do: holds?(p, node) and holds?(q, node)
  defp holds?({:or, p, q}, node), do: holds?(p, node) or holds?(q, node)
  defp holds?({:imp, p, q}, node), do: not holds?(p, node) or holds?(q, node)
  defp holds?({:did, _k, move}, node), do: move in node.done

  defp safety_msg(fam, body, node) do
    case node.path do
      [] -> "#{pp_form(body)} fails in #{fam}: #{dump(node)}"
      path -> "#{pp_form(body)} fails in #{fam} after #{Enum.join(path, ", ")}: #{dump(node)}"
    end
  end

  defp live_msg(fam, body, leaf) do
    forever = "then forever: the key has finished: #{dump(leaf)}"

    case leaf.path do
      [] -> "#{pp_form(body)} fails in #{fam}; #{forever}"
      path -> "#{pp_form(body)} fails in #{fam} after #{Enum.join(path, ", ")}; #{forever}"
    end
  end

  defp dump(%{g: :end}), do: "end"
  defp dump(%{g: g}), do: "next " <> Choreo.expected_text(g)

  defp pp_form({:always, p}), do: "always (#{pp(p)})"
  defp pp_form({:eventually, p}), do: "eventually (#{pp(p)})"
  defp pp_form({:leads_to, p, q}), do: "(#{pp(p)}) leads_to (#{pp(q)})"

  defp pp({:not, p}), do: "not #{pp(p)}"
  defp pp({:and, p, q}), do: "#{pp(p)} and #{pp(q)}"
  defp pp({:or, p, q}), do: "#{pp(p)} or #{pp(q)}"
  defp pp({:imp, p, q}), do: "(#{pp(p)}) implies (#{pp(q)})"
  defp pp({:did, k, move}), do: "done #{k} (#{show_move(move)})"
  defp pp(true), do: "true"
  defp pp(false), do: "false"
end
