defmodule Muro.SynthFeatureTest do
  use ExUnit.Case, async: true

  alias Muro.Synth.Feature

  # A cover with no states makes every template trivial. `[]` is both
  # all-true and all-false, as in the Agda filter.
  test "an empty cover drops every template" do
    host = host(states: [], actions: ["go"], all_states: nil, step: fn _, _ -> raise "step" end)
    assert Feature.discover(host, []) == []
  end

  test "a constant reward and a constant loop are dropped" do
    host =
      host(
        states: ["a", "b"],
        actions: ["go"],
        step: fn state, "go" -> {state, {:suc, 0}} end
      )

    assert Feature.discover(host, []) == []
  end

  test "a reward that changes across the cover is kept" do
    host = pos_host()

    assert [%{name: "has-pos-reward-go", kind: :has_pos_reward, action: "go"}] =
             Feature.discover(host, [])
  end

  test "an integer reward is a closed Nat, and a token is not" do
    ints =
      host(
        states: ["a", "b"],
        actions: ["go"],
        step: fn
          "a", "go" -> {"a", 0}
          "b", "go" -> {"b", 2}
        end
      )

    assert [%{kind: :has_pos_reward}] = Feature.discover(ints, [])

    tokens =
      host(
        states: ["a", "b"],
        actions: ["go"],
        step: fn
          "a", "go" -> {"b", :coin}
          "b", "go" -> {"b", :coin}
        end
      )

    specs = Feature.discover(tokens, [])
    refute Enum.any?(specs, &(&1.kind == :has_pos_reward))
    assert Enum.any?(specs, &(&1.kind == :is_self_loop))
  end

  test "a second feature with the same truth vector is dropped" do
    # stay pays exactly when go does, so the later template is the same atom.
    host =
      host(
        states: ["a", "b"],
        actions: ["go", "stay"],
        step: fn
          "a", _action -> {"a", 0}
          "b", _action -> {"b", {:suc, 0}}
        end
      )

    assert [%{name: "has-pos-reward-go", kind: :has_pos_reward}] = Feature.discover(host, [])
  end

  test "a declared feature equivalent to a dynamics feature is dropped" do
    host = pos_host()

    bits = %{
      {"marked", "a"} => false,
      {"marked", "b"} => true,
      {"odd", "a"} => true,
      {"odd", "b"} => false,
      {"always", "a"} => true,
      {"always", "b"} => true
    }

    specs =
      Feature.discover(host |> Map.put(:eval_feature, hint_eval(bits)), [
        "marked",
        "odd",
        "always"
      ])

    assert Enum.map(specs, & &1.name) == ["has-pos-reward-go", "odd"]
    assert Enum.map(specs, & &1.kind) == [:has_pos_reward, :hint]
  end

  test "a state is terminal only when every action stays there" do
    host = graph()
    assert Feature.terminal?(host, "room")
    refute Feature.terminal?(host, "door")
    refute Feature.terminal?(host, "jump")

    names = Feature.discover(host, []) |> Enum.map(& &1.name)

    assert names == [
             "is-self-loop-go",
             "is-self-loop-stay",
             "leads-terminal-go",
             "leads-terminal-stay"
           ]
  end

  test "a taken spelling freshens the feature name" do
    taken = host(book: [%{name: "has_pos_reward_go"}], step: pos_step())
    assert [%{name: "has-pos-reward-go-2"}] = Feature.discover(taken, [])

    exact = host(book: [%{name: "has-pos-reward-go"}], step: pos_step())
    assert [%{name: "has-pos-reward-go-2"}] = Feature.discover(exact, [])
  end

  defp pos_host, do: host(step: pos_step())

  defp pos_step do
    fn
      "a", "go" -> {"a", 0}
      "b", "go" -> {"b", {:suc, 0}}
    end
  end

  # jump leaves toward an absorbing room. door loops on go and leaves on
  # stay. slip leaves toward door, which is not absorbing. The four
  # vectors differ, so neither self-loop subsumes leads-terminal.
  defp graph do
    host(
      states: ["jump", "door", "room", "slip"],
      actions: ["go", "stay"],
      step: fn
        "jump", "go" -> {"room", 0}
        "jump", "stay" -> {"jump", 0}
        "door", "go" -> {"door", 0}
        "door", "stay" -> {"jump", 0}
        "room", "go" -> {"room", 0}
        "room", "stay" -> {"room", 0}
        "slip", "go" -> {"door", 0}
        "slip", "stay" -> {"slip", 0}
      end
    )
  end

  defp hint_eval(bits) do
    fn name, state -> Map.fetch!(bits, {name, state}) end
  end

  defp host(opts) do
    states = Keyword.get(opts, :states, ["a", "b"])
    actions = Keyword.get(opts, :actions, ["go"])

    %{
      book: Keyword.get(opts, :book, []),
      states: states,
      actions: actions,
      all_states: Keyword.get(opts, :all_states, states),
      step: Keyword.get(opts, :step, fn state, _action -> {state, 0} end),
      eval_feature: Keyword.get(opts, :eval_feature, fn _name, _state -> false end)
    }
  end
end
