defmodule MuroVisor.EnvGraph do
  @moduledoc false

  @doc """
  The environment's state graph, read from the checked book.

  States are the nullary constructors of `State`, in the order written.
  An edge is a branch of a match on those constructors whose body is a
  state, or a pair whose first component is a state. A nested match
  names the action. This does not run `step` and it does not search.
  """
  def build(book) when is_list(book) do
    states = constructors(book, "State")
    names = MapSet.new(states)

    edges =
      book
      |> Enum.reduce([], fn defn, acc ->
        acc
        |> walk(Map.get(defn, :body), names)
        |> walk(Map.get(defn, :type), names)
      end)
      |> Enum.reverse()
      |> Enum.uniq()

    %{states: states, edges: edges, environment?: states != []}
  end

  def build(_book), do: %{states: [], edges: [], environment?: false}

  defp constructors(book, data) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and Map.get(&1, :name) == data)) do
      %{ctors: ctors} when is_list(ctors) ->
        ctors
        |> Enum.filter(&nullary?/1)
        |> Enum.map(& &1.name)

      _ ->
        []
    end
  end

  defp nullary?(%{type: {:pi, _, _, _, _}}), do: false
  defp nullary?(%{name: name}) when is_binary(name), do: true
  defp nullary?(_ctor), do: false

  defp walk(acc, term, states) do
    case term do
      {:mdata, _scrut, _motive, branches} when is_list(branches) ->
        walk_match(acc, branches, states)

      {:mdata, _scrut, _name, _motive, branches} when is_list(branches) ->
        walk_match(acc, branches, states)

      tuple when is_tuple(tuple) ->
        tuple |> Tuple.to_list() |> Enum.reduce(acc, &walk(&2, &1, states))

      list when is_list(list) ->
        Enum.reduce(list, acc, &walk(&2, &1, states))

      _other ->
        acc
    end
  end

  defp walk_match(acc, branches, states) do
    if state_match?(branches, states) do
      Enum.reduce(branches, acc, fn {from, _binders, body}, acc ->
        case action_edges(from, body, states) do
          [] ->
            case dest(body, states) do
              nil -> walk(acc, body, states)
              to -> walk([%{from: from, action: nil, to: to} | acc], body, states)
            end

          edges ->
            Enum.reduce(edges, acc, fn edge, acc -> [edge | acc] end)
        end
      end)
    else
      Enum.reduce(branches, acc, fn {_name, _binders, body}, acc ->
        walk(acc, body, states)
      end)
    end
  end

  defp state_match?(branches, states) do
    branches != [] and
      Enum.all?(branches, fn
        {name, _binders, _body} when is_binary(name) -> MapSet.member?(states, name)
        _ -> false
      end)
  end

  defp action_edges(from, {:mdata, _scrut, _motive, branches}, states) do
    action_list(from, branches, states)
  end

  defp action_edges(from, {:mdata, _scrut, _name, _motive, branches}, states) do
    action_list(from, branches, states)
  end

  defp action_edges(_from, _body, _states), do: []

  defp action_list(from, branches, states) when is_list(branches) do
    if state_match?(branches, states) do
      []
    else
      Enum.flat_map(branches, fn
        {action, _binders, body} when is_binary(action) ->
          case dest(body, states) do
            nil -> []
            to -> [%{from: from, action: action, to: to}]
          end

        _ ->
          []
      end)
    end
  end

  defp action_list(_from, _branches, _states), do: []

  defp dest({:var, name}, states) when is_binary(name) do
    if MapSet.member?(states, name), do: name
  end

  defp dest({:pair, left, _right}, states), do: dest(left, states)
  defp dest({:ann, term, _type}, states), do: dest(term, states)
  defp dest(_term, _states), do: nil
end
