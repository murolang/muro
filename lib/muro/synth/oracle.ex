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
    # Search memo only. One table of best traces, one of solved values,
    # and one of `step` results, for every comparison in this call.
    # `Loop.run/2` deletes the same keys. The checker does not read them.
    # A fresh table at each comparison ranks the same actions. The tables
    # are re-read after a recursive call stores its own entries.
    Process.put(:muro_oracle_best, %{})
    Process.put(:muro_oracle_solve, %{})
    Process.put(:muro_oracle_step, %{})

    try do
      observe_body(host, oracle, blind)
    after
      clear_shared()
    end
  end

  @doc false
  def observe_separated(host, oracle, blind \\ [])

  def observe_separated(_host, oracle, _blind) when oracle not in @names do
    {:error, :usage, "unknown oracle #{oracle}"}
  end

  # The per-comparison table. Tests use it to check that the shared
  # tables rank the same actions, including a tie and a silent pair.
  def observe_separated(host, oracle, blind) do
    clear_shared()
    observe_body(host, oracle, blind)
  end

  defp clear_shared do
    Process.delete(:muro_oracle_best)
    Process.delete(:muro_oracle_solve)
    Process.delete(:muro_oracle_step)
  end

  defp observe_body(host, oracle, blind) do
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

  # A nullary cover is finite by the constructors. A reachable cover of a
  # self-referential `State` is not: `step` can build a new term at every
  # state. 256 admits a term graph of a few dozen states, which the
  # certificate already ranks, and refuses a successor that would exceed
  # that count without building that certificate. Size 256 is accepted.
  # It is not the inhabitant cap of 32, and it is not the reachability-table
  # cap. The states already met are not returned.
  @reachable_cap 256

  def reachable_cap, do: @reachable_cap

  def reachable_bound_message do
    "reachable states are not finite within #{@reachable_cap}; declare all-states"
  end

  def step_not_state_message, do: "step has a value that is not a State"

  def step_left_message, do: "step left the reachable cover"

  def cover(host) do
    cond do
      host.all_states ->
        host.all_states

      nullary_cover?(host) ->
        reachable(host, host.states)

      true ->
        # A finite structured enumeration. `step` of a complete inhabitant
        # list stays inside it, so the unbounded walk is not this path.
        host.states
    end
  end

  @doc """
  The states reached from `seeds` under `step` of every action.

  `{:error, :bound}` is a fresh state that would exceed `reachable_cap/0`.
  A cover of exactly that many states is returned. `{:error, :not_state}`
  is a value `step` returns that does not decode as a `State`. `{:error,
  :left}` is a successor that is a state and is not in the set the walk
  closed. A set that does not close is not truncated to the states already
  met.
  """
  def close_under_step(host, seeds) when is_list(seeds) do
    seeds = Enum.uniq_by(seeds, &state_key/1)

    if length(seeds) > @reachable_cap do
      {:error, :bound}
    else
      seen = MapSet.new(Enum.map(seeds, &state_key/1))

      with {:ok, order} <- grow_bounded(host, seeds, seeds, seen, @reachable_cap),
           :ok <- stays_inside(host, order) do
        {:ok, order}
      end
    end
  end

  # Unbounded, and only for a nullary `State`. A self-referential cover is
  # installed into `all_states` before `cover/1` asks, and a finite
  # structured enumeration is `host.states`. This walk is not that closure,
  # and it is not bounded by `reachable_cap/0`.
  defp reachable(host, seeds) do
    true = nullary_cover?(host)
    grow(host, seeds, seeds, MapSet.new(seeds))
  end

  defp nullary_cover?(host), do: not Map.get(host, :structured, false)

  defp grow(_host, order, [], _seen), do: order

  # Nullary constructors only. See `reachable/2`.
  defp grow(host, order, [state | rest], seen) do
    fresh =
      Enum.flat_map(host.actions, fn action ->
        {next, _reward} = host.step.(state, action)

        if MapSet.member?(seen, next), do: [], else: [next]
      end)

    grow(host, order ++ fresh, rest ++ fresh, MapSet.union(seen, MapSet.new(fresh)))
  end

  defp grow_bounded(_host, order, [], _seen, _cap), do: {:ok, order}

  defp grow_bounded(host, order, [state | rest], seen, cap) do
    case fresh_states(host, state, seen) do
      {:error, reason} when reason in [:left, :not_state] ->
        {:error, reason}

      {:ok, fresh} ->
        cond do
          fresh == [] ->
            grow_bounded(host, order, rest, seen, cap)

          length(order) + length(fresh) > cap ->
            {:error, :bound}

          true ->
            seen = MapSet.union(seen, MapSet.new(Enum.map(fresh, &state_key/1)))
            grow_bounded(host, order ++ fresh, rest ++ fresh, seen, cap)
        end
    end
  end

  defp stays_inside(host, states) do
    seen = MapSet.new(Enum.map(states, &state_key/1))

    Enum.reduce_while(states, :ok, fn state, :ok ->
      case fresh_states(host, state, seen) do
        {:ok, []} -> {:cont, :ok}
        {:ok, _} -> {:halt, {:error, :left}}
        {:error, reason} when reason in [:left, :not_state] -> {:halt, {:error, reason}}
      end
    end)
  end

  defp fresh_states(host, state, seen) do
    Enum.reduce_while(host.actions, {:ok, []}, fn action, {:ok, acc} ->
      case one_step(host, state, action) do
        {:error, reason} when reason in [:left, :not_state] ->
          {:halt, {:error, reason}}

        {:ok, next} ->
          key = state_key(next)

          if MapSet.member?(seen, key) or Enum.any?(acc, &(state_key(&1) == key)) do
            {:cont, {:ok, acc}}
          else
            {:cont, {:ok, acc ++ [next]}}
          end
      end
    end)
  end

  defp one_step(host, state, action) do
    {next, _reward} = host.step.(state, action)
    {:ok, next}
  rescue
    e in ArgumentError ->
      if not_state_error?(e), do: {:error, :not_state}, else: {:error, :left}
  end

  # `Term.decode!/2` raises this when `step` returns a value that is not
  # a `State`. Any other `ArgumentError` is a successor that left the cover.
  defp not_state_error?(%ArgumentError{message: "not a value of this state" <> _}), do: true
  defp not_state_error?(_), do: false

  defp state_key(%Muro.Synth.Term{value: value}), do: value
  defp state_key(other), do: other

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
    {next, reward} = stepped(host, state, action)
    {rest, _memo} = values(host, next, max(n - 1, 0))
    [reward | rest]
  end

  defp prefix(host, "successor", state, action, n) do
    {next, _reward} = stepped(host, state, action)
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

    case shared_fetch(:muro_oracle_solve, key) do
      {:ok, value} ->
        {value, memo}

      :miss ->
        {value, memo} = solve_fold(host, state, k, memo)
        shared_put(:muro_oracle_solve, key, value)
        {value, memo}

      :off ->
        case Map.fetch(memo, key) do
          {:ok, value} ->
            {value, memo}

          :error ->
            {value, memo} = solve_fold(host, state, k, memo)
            {value, Map.put(memo, key, value)}
        end
    end
  end

  defp solve_fold(host, state, k, memo) do
    {rewards, memo} =
      Enum.map_reduce(host.actions, memo, fn action, memo ->
        {next, reward} = stepped(host, state, action)

        if k == 0 do
          {reward, memo}
        else
          solve(host, next, k - 1, memo)
        end
      end)

    {maximum(host, rewards), memo}
  end

  # An unordered pair has no maximum. Picking either reward would make a
  # state that offers both compare equal to a state that offers only one.
  #
  # A left-to-right fold is not that maximum. `p` and `q` may be unordered
  # while `top` is at least both of them. The fold `[p, q, top]` stops at
  # the pair and misses `top`; `[top, p, q]` keeps it. The maximum is an
  # element that is at least every reward. When none is, the set is
  # unordered in every order.
  @doc false
  def maximum_reward(leb, rewards) when is_function(leb, 2) and is_list(rewards) do
    case maximum(%{leb: leb}, rewards) do
      @unordered -> :unordered
      value -> value
    end
  end

  defp maximum(host, rewards) do
    case Enum.find(rewards, &dominates?(host, &1, rewards)) do
      nil -> @unordered
      winner -> winner
    end
  end

  defp dominates?(host, candidate, rewards) do
    not unordered?(candidate) and
      Enum.all?(rewards, fn other ->
        not unordered?(other) and host.leb.(other, candidate)
      end)
  end

  defp unordered?(value), do: value == @unordered

  defp trace(host, state, action, k, blind, memo) do
    if is_list(blind) and action in blind do
      {:hidden, memo}
    else
      {next, reward} = stepped(host, state, action)
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

    case shared_fetch(:muro_oracle_best, key) do
      {:ok, value} ->
        {value, memo}

      :miss ->
        {value, memo} = best_fold(host, state, k, blind, memo)
        shared_put(:muro_oracle_best, key, value)
        {value, memo}

      :off ->
        case Map.fetch(memo, key) do
          {:ok, value} ->
            {value, memo}

          :error ->
            {value, memo} = best_fold(host, state, k, blind, memo)
            {value, Map.put(memo, key, value)}
        end
    end
  end

  defp best_fold(host, state, k, blind, memo) do
    {traces, memo} =
      Enum.map_reduce(host.actions, memo, fn action, memo ->
        trace(host, state, action, k - 1, blind, memo)
      end)

    {Enum.reduce(traces, &trace_max(host, &1, &2)), memo}
  end

  # `step` is pure. The shared table stores the pair `step` returned.
  # The separated path calls `step` every time, as before.
  defp stepped(host, state, action) do
    key = {state, action}

    case shared_fetch(:muro_oracle_step, key) do
      {:ok, pair} ->
        pair

      :miss ->
        pair = host.step.(state, action)
        shared_put(:muro_oracle_step, key, pair)
        pair

      :off ->
        host.step.(state, action)
    end
  end

  defp shared_fetch(name, key) do
    case Process.get(name) do
      table when is_map(table) ->
        case Map.fetch(table, key) do
          {:ok, value} -> {:ok, value}
          :error -> :miss
        end

      _ ->
        :off
    end
  end

  defp shared_put(name, key, value) do
    table = Process.get(name, %{})
    Process.put(name, Map.put(table, key, value))
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
