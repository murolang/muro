defmodule Muro.Synth.Oracle do
  @moduledoc false

  @names ~w(trace successor coind-homo)
  # Not a reward. Emitted rewards are atoms, numbers, tuples, and field
  # maps. They do not carry this module as `__struct__`.
  @unordered %{__struct__: __MODULE__, muro: :unordered}

  def names, do: @names

  @doc """
  Observations for `oracle` on the cover, from `host.step`.

  Two actions are one predicate, "prefer the first", and the second
  action is the else branch. More than two actions are one predicate
  per action, chained in `all-actions` order, else the book's default.
  """
  def observe(host, oracle, blind \\ [])

  def observe(_host, oracle, _blind) when oracle not in @names do
    {:error, :usage, "unknown oracle #{oracle}"}
  end

  def observe(host, oracle, blind) do
    case blind -- host.actions do
      [] ->
        cover = cover(host)

        label = fn action, other, state ->
          compare(host, oracle, state, action, other, blind)
        end

        case tasks(host.actions, host.default, cover, label) do
          {:silent, state, action, other} ->
            {:silent,
             %{
               carrier: state,
               pair: {action, other},
               reason: reason(oracle)
             }}

          {:ok, tasks} ->
            {:ok, %{cover: cover, tasks: tasks, oracle: oracle}}
        end

      [unknown | _] ->
        {:error, :usage, "unknown action #{unknown}"}
    end
  end

  @doc """
  Labelling tasks from a pure comparison.

  `label.(action, other, state)` is `true`, `false`, or `:silent`.
  """
  def tasks([action, other], _default, cover, label) when is_function(label, 3) do
    case column(cover, fn state -> label.(action, other, state) end) do
      {:silent, state} ->
        {:silent, state, action, other}

      {:ok, obs} ->
        {:ok, [%{action: action, other: other, else: other, observations: obs}]}
    end
  end

  def tasks(actions, default, cover, label) when is_function(label, 3) do
    Enum.reduce_while(actions, {:ok, []}, fn action, {:ok, acc} ->
      others = Enum.reject(actions, &(&1 == action))

      case column(cover, fn state -> beats_all?(action, others, state, label) end) do
        {:silent, state, other} ->
          {:halt, {:silent, state, action, other}}

        {:ok, obs} ->
          task = %{action: action, other: nil, else: default, observations: obs}
          {:cont, {:ok, acc ++ [task]}}
      end
    end)
  end

  # A loss is not the end of the column. `top` can dominate both `p` and
  # `q` while `p` and `q` are unordered. Stopping at the loss would emit
  # a policy for a pair the oracle cannot label. `false` is the label so
  # far; a later `:silent` still stops the run.
  defp beats_all?(action, others, state, label) do
    Enum.reduce_while(others, true, fn other, acc ->
      case label.(action, other, state) do
        :silent -> {:halt, {:silent, state, other}}
        false -> {:cont, false}
        true -> {:cont, acc}
      end
    end)
  end

  defp column(cover, fun) do
    Enum.reduce_while(cover, {:ok, []}, fn state, {:ok, acc} ->
      case fun.(state) do
        {:silent, state, other} -> {:halt, {:silent, state, other}}
        :silent -> {:halt, {:silent, state}}
        bit when is_boolean(bit) -> {:cont, {:ok, acc ++ [{state, bit}]}}
      end
    end)
  end

  def cover(host) do
    if host.all_states, do: host.all_states, else: reachable(host, host.states)
  end

  defp reachable(host, seeds) do
    grow(host, seeds, seeds, MapSet.new(seeds))
  end

  defp grow(_host, order, [], _seen), do: order

  defp grow(host, order, [state | rest], seen) do
    fresh =
      Enum.flat_map(host.actions, fn action ->
        {next, _reward} = host.step.(state, action)

        if MapSet.member?(seen, next), do: [], else: [next]
      end)

    grow(host, order ++ fresh, rest ++ fresh, MapSet.union(seen, MapSet.new(fresh)))
  end

  defp compare(host, "trace", state, action, other, blind) do
    {left, memo} = trace(host, state, other, host.horizon, blind, %{})
    {right, _memo} = trace(host, state, action, host.horizon, blind, memo)

    # `trace_le` is false both when the right trace is strictly smaller
    # and when the first differing rewards are not ordered. The reverse
    # comparison separates those. An unordered pair is not a ranking.
    cond do
      trace_le(host, left, right) == true -> true
      trace_le(host, right, left) == true -> false
      true -> :silent
    end
  end

  defp compare(host, oracle, state, action, other, _blind) do
    n = max(host.horizon, max(length(host.states), 1))
    left = prefix(host, oracle, state, other, n)
    right = prefix(host, oracle, state, action, n)

    # Pointwise, not the Finder's lexicographic trace order. A first
    # reward that is smaller does not make the rest of the stream smaller.
    cond do
      pointwise_le(host, left, right) -> true
      pointwise_le(host, right, left) -> false
      true -> :silent
    end
  end

  defp pointwise_le(host, left, right) do
    left
    |> Enum.zip(right)
    |> Enum.all?(fn {a, b} ->
      not unordered?(a) and not unordered?(b) and host.leb.(a, b)
    end)
  end

  defp prefix(host, "coind-homo", state, action, n) do
    {next, reward} = host.step.(state, action)
    {rest, _memo} = values(host, next, max(n - 1, 0))
    [reward | rest]
  end

  defp prefix(host, "successor", state, action, n) do
    {next, _reward} = host.step.(state, action)
    {rest, _memo} = values(host, next, n)
    rest
  end

  defp values(_host, _state, n) when n <= 0, do: {[], %{}}

  defp values(host, state, n) do
    Enum.map_reduce(0..(n - 1), %{}, fn k, memo ->
      solve(host, state, k, memo)
    end)
  end

  defp solve(host, state, k, memo) do
    key = {state, k}

    case Map.fetch(memo, key) do
      {:ok, value} ->
        {value, memo}

      :error ->
        {rewards, memo} =
          Enum.map_reduce(host.actions, memo, fn action, memo ->
            {next, reward} = host.step.(state, action)

            if k == 0 do
              {reward, memo}
            else
              solve(host, next, k - 1, memo)
            end
          end)

        value = maximum(host, rewards)
        {value, Map.put(memo, key, value)}
    end
  end

  # An unordered pair has no maximum. Picking either reward would make a
  # state that offers both compare equal to a state that offers only one.
  defp maximum(host, [first | rest]) do
    Enum.reduce_while(rest, first, fn reward, acc ->
      case max_reward(host, acc, reward) do
        {:ok, value} -> {:cont, value}
        :incomparable -> {:halt, @unordered}
      end
    end)
  end

  defp max_reward(_host, left, right) when left == @unordered or right == @unordered do
    :incomparable
  end

  defp max_reward(host, left, right) do
    cond do
      host.leb.(left, right) -> {:ok, right}
      host.leb.(right, left) -> {:ok, left}
      true -> :incomparable
    end
  end

  defp unordered?(value), do: value == @unordered

  defp trace(host, state, action, k, blind, memo) do
    if is_list(blind) and action in blind do
      {:hidden, memo}
    else
      {next, reward} = host.step.(state, action)
      {rest, memo} = best_trace(host, next, k, blind, memo)

      case rest do
        :hidden -> {:hidden, memo}
        rewards -> {[reward | rewards], memo}
      end
    end
  end

  defp best_trace(_host, _state, 0, _blind, memo), do: {[], memo}

  defp best_trace(host, state, k, blind, memo) do
    key = {:best, state, k}

    case Map.fetch(memo, key) do
      {:ok, value} ->
        {value, memo}

      :error ->
        {traces, memo} =
          Enum.map_reduce(host.actions, memo, fn action, memo ->
            trace(host, state, action, k - 1, blind, memo)
          end)

        value = Enum.reduce(traces, &trace_max(host, &1, &2))
        {value, Map.put(memo, key, value)}
    end
  end

  defp trace_max(host, current, candidate) do
    if trace_le(host, current, candidate), do: candidate, else: current
  end

  def trace_le(_host, :hidden, :hidden), do: true
  def trace_le(_host, :hidden, _right), do: true
  def trace_le(_host, _left, :hidden), do: false
  def trace_le(_host, [], _right), do: true
  def trace_le(_host, _left, []), do: false

  def trace_le(host, [left | ls], [right | rs]) do
    cond do
      host.leb.(left, right) and host.leb.(right, left) -> trace_le(host, ls, rs)
      host.leb.(left, right) -> true
      true -> false
    end
  end

  defp reason("coind-homo"), do: "action-value streams are incomparable"
  defp reason("successor"), do: "successor-value streams are incomparable"
  defp reason("trace"), do: "traces are incomparable"
end
