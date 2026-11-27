defmodule Muro.SynthBudgetTest do
  use ExUnit.Case, async: true

  @queens4 "examples/cshrl/envs/queens4.muro"

  test "the default bounds sit above the 4-queens walk" do
    assert Muro.Synth.considered_budget() == 1_000_000
    assert Muro.Synth.memory_budget() == 512 * 1_048_576
    assert Muro.Synth.considered_budget() > 8_138
  end

  test "a considered budget stops before the next program and names the reason" do
    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p", "q"], 4, fn _feature -> 1 end, 2, nil,
               considered_budget: 5
             )

    assert meta.considered == 5
    assert meta.size == 2
    refute Map.has_key?(meta, :bank)
  end

  test "a zero considered budget stops before any program" do
    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil,
               considered_budget: 0,
               memory_budget: -1
             )

    assert meta.considered == 0
    assert meta.size == 0
    assert meta.sizes == []
  end

  test "a budget that ends a size names that size" do
    # Size 1 is true, false, and one test per feature: four programs.
    # The budget is that count, so size 2 is not enumerated.
    assert {:empty, "considered budget", meta} =
             Muro.Synth.enumerate_sized(["p", "q"], 4, fn _feature -> 1 end, 2, nil,
               considered_budget: 4
             )

    assert meta.considered == 4
    assert [size, count] = List.last(meta.sizes)
    assert size == 1
    assert count > 0
    assert meta.size == size
    refute Enum.any?(meta.sizes, fn [row, _] -> row > meta.size end)
  end

  test "a finished walk reports the last size that counted a program" do
    assert {:ok, _index, meta} =
             Muro.Synth.enumerate_sized(["p", "q"], 2, fn _feature -> 1 end, 2)

    assert [size, count] = List.last(meta.sizes)
    assert size == 2
    assert count > 0
    assert meta.size == size
    assert meta.considered > 0
    assert meta.distinct > 0
    assert meta.truncated == false
  end

  test "a negative memory budget stops before any candidate" do
    assert {:empty, "memory budget", meta} =
             Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil, memory_budget: -1)

    assert meta.considered == 0
    assert meta.size == 0
    assert meta.sizes == []
  end

  test "a positive memory budget stops when this process grows past it" do
    # `memory_budget: -1` hits a special-case clause and never samples
    # `walk_memory/0`. A large binary would sit off-heap; a list stays
    # on this process and is rooted until the walk samples.
    budget = 64 * 1024
    hold_n = 200_000

    try do
      assert {:empty, "memory budget", meta} =
               Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil,
                 memory_budget: budget,
                 after_base: fn ->
                   {:memory, before} = Process.info(self(), :memory)
                   held = Enum.to_list(1..hold_n)
                   Process.put(:muro_synth_budget_hold, held)
                   {:memory, after_mem} = Process.info(self(), :memory)
                   assert after_mem - before > budget
                 end
               )

      assert meta.considered == 0
      assert meta.size == 0
      assert meta.sizes == []
    after
      Process.delete(:muro_synth_budget_hold)
    end
  end

  test "the memory budget ignores growth in other processes" do
    # The walk used to sample `:erlang.memory(:total)`. A parallel ExUnit
    # case could take the VM more than 512 MiB past the start of a walk
    # that itself considered only a few hundred programs, and the walk
    # would stop with `memory budget`. The sample is this process.
    # `after_base:` runs after `base_mem` is recorded and before the
    # first candidate is inserted, so the other process is already
    # holding the extra memory when later samples run.
    features = ["a", "b", "c", "d"]
    states = [:s0, :s1, :s2, :s3, :s4, :s5]

    feat = fn
      "a", state when state in [:s0, :s5] -> true
      "b", state when state in [:s1, :s5] -> true
      "c", :s2 -> true
      "d", :s3 -> true
      _feature, _state -> false
    end

    budget = 16 * 1_048_576
    hold = 64 * 1_048_576
    parent = self()

    holder =
      spawn(fn ->
        receive do
          {:go, from} ->
            blob = :binary.copy(<<1>>, hold)
            send(from, {:held, byte_size(blob)})

            receive do
              :drop -> byte_size(blob)
            end
        end
      end)

    try do
      assert {:ok, _index, meta} =
               Muro.Synth.enumerate_sized(
                 features,
                 Muro.Synth.pred_size_bound(),
                 &Muro.Synth.signature(&1, states, feat),
                 length(states),
                 nil,
                 memory_budget: budget,
                 after_base: fn ->
                   send(holder, {:go, parent})

                   receive do
                     {:held, ^hold} -> :ok
                   after
                     5_000 -> flunk("holder did not allocate")
                   end
                 end
               )

      assert meta.truncated == false
      assert meta.considered > 0
    after
      send(holder, :drop)
    end
  end

  test "a non-integer budget is a usage error" do
    assert {:error, :usage, considered} =
             Muro.Synth.Loop.run("examples/cshrl/envs/two_state.muro", considered_budget: 1.5)

    assert considered =~ "considered budget"

    assert {:error, :usage, memory} =
             Muro.Synth.Loop.run("examples/cshrl/envs/two_state.muro", memory_budget: "512")

    assert memory =~ "memory budget"
  end

  test "enumerate_sized rejects a non-integer budget" do
    assert_raise ArgumentError, ~r/considered_budget must be an integer/, fn ->
      Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil, considered_budget: :no)
    end

    assert_raise ArgumentError, ~r/memory_budget must be an integer/, fn ->
      Muro.Synth.enumerate_sized(["p"], 2, fn _feature -> 0 end, 1, nil, memory_budget: 1.0)
    end
  end

  @tag timeout: 180_000
  test "4-queens under a tiny considered budget reports an empty version space" do
    Process.put(:muro_synth_reaches, %{sentinel: true})

    assert {:exit, 1, "", lines} = Muro.CLI.Synth.run([@queens4], considered_budget: 3)
    report = Enum.join(lines, "\n")

    assert report =~ "muro synth: empty version space"
    assert report =~ "considered budget"
    assert report =~ "considered 3"
    refute report =~ "predicate size 18 exhausted"
    refute report =~ "\ndepth 18\n"
    refute report =~ "homomorphism checked"
    refute report =~ "exhausts memory"
    assert Process.get(:muro_synth_reaches) == nil
  end

  @tag timeout: 180_000
  test "--json names a considered-budget stop and the counts the walk reached" do
    assert {:exit, 1, "", [json]} =
             Muro.CLI.Synth.run([@queens4, "--json"], considered_budget: 5)

    decoded = JSON.decode!(json)
    assert decoded["status"] == "empty"
    assert decoded["stop"] == "considered budget"
    assert decoded["considered"] == 5
    assert is_integer(decoded["distinct"])
    assert is_integer(decoded["size"])
    assert [size, _count] = List.last(decoded["sizes"])
    assert decoded["size"] == size
    assert is_integer(decoded["enum_ms"])
    assert is_boolean(decoded["truncated"])
    assert decoded["note"] == "no predicate matches the observations"
  end

  @tag timeout: 180_000
  test "--json names a memory-budget stop and the counts the walk reached" do
    assert {:exit, 1, "", [json]} =
             Muro.CLI.Synth.run([@queens4, "--json"], memory_budget: -1)

    decoded = JSON.decode!(json)
    assert decoded["status"] == "empty"
    assert decoded["stop"] == "memory budget"
    assert decoded["considered"] == 0
    assert decoded["size"] == 0
    assert decoded["sizes"] == []
    assert is_integer(decoded["enum_ms"])
  end

  test "a failed run clears the search memo" do
    Process.put(:muro_synth_reaches, %{sentinel: true})

    assert {:error, :book, _message} =
             Muro.Synth.Loop.run("/no/such/queens-review-fix.muro")

    assert Process.get(:muro_synth_reaches) == nil
  end

  test "a finished run clears the search memo" do
    Process.put(:muro_synth_reaches, %{sentinel: true})

    assert {:ok, result} =
             Muro.Synth.Loop.run("examples/cshrl/envs/two_state.muro",
               depth: 0,
               max_depth: 0
             )

    assert result.status == :certified
    assert Process.get(:muro_synth_reaches) == nil
    refute Map.has_key?(result, :considered)
  end
end
