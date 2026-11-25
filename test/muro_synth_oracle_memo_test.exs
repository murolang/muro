defmodule Muro.Synth.OracleMemoTest do
  use ExUnit.Case, async: true

  @books [
    "examples/cshrl/envs/queens4.muro",
    "examples/cshrl/envs/two_state.muro",
    "examples/cshrl/envs/binary_sacrifice.muro",
    "examples/cshrl/envs/skill_investment.muro"
  ]

  @oracles ~w(trace successor coind-homo)

  test "shared tables match a fresh table on the stock books" do
    for book <- @books do
      assert {:ok, host} = Muro.Synth.Host.open(book)

      for oracle <- @oracles do
        assert Muro.Synth.Oracle.observe(host, oracle) ==
                 Muro.Synth.Oracle.observe_separated(host, oracle),
               "#{book} #{oracle}"
      end
    end
  end

  test "shared tables match a fresh table on a small grid, including ties" do
    host = grid(4, 4, 2)

    for oracle <- @oracles do
      assert Muro.Synth.Oracle.observe(host, oracle) ==
               Muro.Synth.Oracle.observe_separated(host, oracle),
             oracle
    end

    tied = %{
      host
      | actions: ["a", "b", "c"],
        default: "c",
        step: fn state, _action -> {state, 0} end
    }

    assert {:ok, shared} = Muro.Synth.Oracle.observe(tied, "trace")
    assert {:ok, separated} = Muro.Synth.Oracle.observe_separated(tied, "trace")
    assert shared.tasks == separated.tasks

    assert Enum.all?(shared.tasks, fn task ->
             Enum.all?(task.observations, fn {_state, bit} -> bit == true end)
           end)

    hidden = Muro.Synth.Oracle.observe(tied, "trace", ["b"])
    assert hidden == Muro.Synth.Oracle.observe_separated(tied, "trace", ["b"])
  end

  # 64 states and 16 actions. A fresh table at every pair repeats the
  # horizon-4 trace often enough to miss this bound. The shared table
  # fills each state once per depth.
  test "a wide cover labels from one trace table within the bound" do
    host = grid(64, 16, 4)
    {us, result} = :timer.tc(fn -> Muro.Synth.Oracle.observe(host, "trace") end)

    assert {:ok, %{tasks: tasks, oracle: "trace"}} = result
    assert length(tasks) == 16
    assert us < 2_000_000, "shared trace took #{us} µs"
  end

  defp grid(states_n, actions_n, horizon) do
    actions = for i <- 0..(actions_n - 1), do: "a#{i}"
    states = Enum.to_list(0..(states_n - 1))

    %{
      actions: actions,
      default: List.last(actions),
      states: states,
      all_states: states,
      horizon: horizon,
      step: fn state, action ->
        idx = action |> String.trim_leading("a") |> String.to_integer()
        next = rem(state + idx + 1, states_n)
        reward = if idx == rem(state, actions_n), do: 1, else: 0
        {next, reward}
      end,
      leb: fn left, right -> left <= right end
    }
  end
end
