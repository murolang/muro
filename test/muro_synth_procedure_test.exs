defmodule Muro.SynthProcedureTest do
  use ExUnit.Case, async: false

  alias Muro.Synth
  alias Muro.Synth.Procedure
  alias Muro.Synth.Procedure.Traces

  @two "examples/cshrl/envs/two_state.muro"
  @bin "examples/cshrl/envs/binary_sacrifice.muro"

  test "traces is the only accepted procedure" do
    assert Procedure.accepted() == ["traces"]
    assert {:ok, Traces} = Procedure.fetch("traces")
    assert {:error, "unknown --on equations; accepted: traces"} = Procedure.fetch("equations")
  end

  test "generate is a stream in enumeration order" do
    stream = Traces.generate(%{features: [:a, :b, :c], depth: 0})
    refute is_list(stream)
    assert Enumerable.impl_for(stream)
    assert Enum.take(stream, 4) == [true, false, {:feat, :a}, {:feat, :b}]

    assert Enum.to_list(Traces.generate(%{features: [:bit], depth: 0})) ==
             Synth.enumerate([:bit], 0)

    assert Enum.to_list(Traces.generate(%{features: [:bit], depth: 1})) ==
             Synth.enumerate([:bit], 1)
  end

  # Depth 3 of eight features is not a list this test can build.
  @tag timeout: 5_000
  test "generate yields depth 0 before a later depth" do
    features = [:a, :b, :c, :d, :e, :f, :g, :h]
    stream = Traces.generate(%{features: features, depth: 3})
    refute is_list(stream)
    assert Enum.take(stream, 1) == [true]
  end

  test "evaluate reports out of fuel and agrees with eval inside the budget" do
    feat = fn
      :bit, state -> state
      :other, _state -> false
    end

    observations = [{true, true}, {false, false}]
    candidate = {:feat, :bit}
    context = %{observations: observations, feat: feat}

    assert {:out_of_fuel, %{candidate: ^candidate}} =
             Traces.evaluate(candidate, Map.put(context, :fuel, 0))

    assert {:out_of_fuel, %{candidate: ^candidate}} =
             Traces.evaluate(candidate, Map.put(context, :fuel, 1))

    assert {:ok, detail} = Traces.evaluate(candidate, context)
    assert detail.agrees == true
    assert detail.fuel_left == Muro.Check.default_fuel() - 2
    assert detail.score == 0

    nested = {:not, {:not, {:not, {:feat, :bit}}}}
    nested_obs = [{true, false}]

    assert {:out_of_fuel, %{candidate: ^nested}} =
             Traces.evaluate(nested, %{fuel: 3, observations: nested_obs, feat: feat})

    assert {:ok, %{agrees: true, fuel_left: 0}} =
             Traces.evaluate(nested, %{fuel: 4, observations: nested_obs, feat: feat})

    parent = self()

    short = fn feature, _state ->
      send(parent, {:feat, feature})
      true
    end

    assert {:ok, %{agrees: true}} =
             Traces.evaluate({:and, false, {:feat, :missing}}, %{
               fuel: 10,
               observations: [{true, false}],
               feat: short
             })

    refute_received {:feat, :missing}

    preds = [
      true,
      false,
      {:feat, :bit},
      {:not, {:feat, :bit}},
      {:and, {:feat, :bit}, true},
      {:or, false, {:feat, :bit}},
      {:and, false, {:feat, :bit}},
      {:self, :reaches, :go, :bit},
      {:self, :reaches, :go, nil},
      {:other, :reaches, :go, [:bit, :other]}
    ]

    for pred <- preds do
      assert {:ok, %{agrees: agrees}} =
               Traces.evaluate(pred, %{fuel: 50, observations: observations, feat: feat})

      assert agrees ==
               Enum.all?(observations, fn {state, bit} ->
                 Synth.eval(pred, feat, state) == bit
               end)
    end

    assert {:ok, %{agrees: true, fuel_left: 0}} =
             Traces.evaluate(true, %{fuel: 0, observations: []})
  end

  test "rank follows pick and drops an unfinished walk" do
    score = fn
      {:not, _} -> 100
      false -> 5
      _pred -> 0
    end

    big = {:ok, %{candidate: {:not, {:feat, :bit}}, score: 100, agrees: true}}
    small = {:ok, %{candidate: true, score: 0, agrees: true}}
    assert candidates(Traces.rank([big, small])) == [true, {:not, {:feat, :bit}}]

    low = {:ok, %{candidate: {:feat, :a}, score: 1, agrees: true}}
    high = {:ok, %{candidate: {:feat, :b}, score: 9, agrees: true}}
    assert candidates(Traces.rank([low, high])) == [{:feat, :b}, {:feat, :a}]

    first = {:ok, %{candidate: {:feat, :a}, score: 3, agrees: true}}
    second = {:ok, %{candidate: {:feat, :b}, score: 3, agrees: true}}
    assert candidates(Traces.rank([first, second])) == [{:feat, :a}, {:feat, :b}]

    miss = {:ok, %{candidate: false, score: 0, agrees: false}}
    unfinished = {:out_of_fuel, %{candidate: true}}
    assert Traces.rank([unfinished, miss]) == [miss]

    preds = [true, {:not, {:feat, :bit}}, false, {:feat, :bit}]

    ranked =
      preds
      |> Enum.map(&{:ok, %{candidate: &1, score: score.(&1), agrees: true}})
      |> Traces.rank()
      |> candidates()

    assert hd(ranked) == Synth.pick(preds, score)
    assert ranked == Enum.sort_by(preds, fn pred -> {Synth.size(pred), -score.(pred)} end)
  end

  test "a book with no step is refused and an unknown --on lists traces" do
    message = Procedure.no_step_message()
    assert message == "the book has no step and no observations to synthesize against"
    refute message =~ "--on"

    for path <- ["examples/sort.muro", "examples/half_ok.muro"] do
      assert {:error, :usage, ^message} = Procedure.select(path, Muro.Check.default_fuel())

      for args <- [[path], [path, "--on", "traces"]] do
        assert {:exit, 2, "", [^message]} = Muro.CLI.Synth.run(args)
      end
    end

    for name <- ["equations", "nope"] do
      message = "unknown --on #{name}; accepted: traces"

      assert {:exit, 2, "", [^message]} =
               Muro.CLI.Synth.run(["examples/sort.muro", "--on", name])
    end

    missing = "unknown --on equations; accepted: traces"

    assert {:exit, 2, "", [^missing]} =
             Muro.CLI.Synth.run(["/tmp/muro-synth-procs-missing.muro", "--on", "equations"])

    dir = tmp()
    bad = Path.join(dir, "bad.muro")
    File.write!(bad, "def one : run Nat := true\n")
    assert {:exit, 2, "", lines} = Muro.CLI.Synth.run([bad])
    text = Enum.join(lines, "\n")
    assert text =~ "refusing to synthesize from a book that does not check"
    refute text =~ "no step"
  end

  test "the help and the manual name traces, the default, and the refusal" do
    help = Muro.CLI.Synth.help()
    assert help =~ "--on"
    assert help =~ "traces"
    assert help =~ "does not name a flag"
    assert help =~ "accepted values"

    for line <- String.split(String.trim_trailing(help, "\n"), "\n") do
      assert String.length(line) <= 80, "longer than 80: #{line}"
    end

    {:docs_v1, _, _, _, %{"en" => doc}, _, _} = Code.fetch_docs(Mix.Tasks.Muro.Synth)
    assert doc =~ "mix muro.synth path.muro --on traces"
    assert doc =~ "does not name a flag"
    assert doc =~ "accepted values"

    page = File.read!("manual/synth.md")
    assert page =~ "--on traces"
    assert page =~ "does not name a flag"
    assert page =~ "no `step` and no observations"
    assert page =~ "only procedure"
  end

  @tag timeout: 180_000
  test "--on traces matches the default command on the synth fixtures" do
    books =
      "test/fixtures/synth_*.muro"
      |> Path.wildcard()
      |> Enum.sort()

    for path <- books ++ [@two] do
      assert_same([path], path)
    end

    assert_same([@two, "--json"], "two_state json")

    dir = tmp()
    plain = Path.join(dir, "plain.muro")
    flagged = Path.join(dir, "flagged.muro")

    left = Muro.CLI.Synth.run([@two, "--out", plain])
    right = Muro.CLI.Synth.run([@two, "--on", "traces", "--out", flagged])
    assert normalize(left) == normalize(right)
    assert File.read!(plain) == File.read!(flagged)

    assert_same([@bin, "--oracle", "coind-homo"], "binary coind-homo")
  end

  defp assert_same(args, label) do
    plain = Muro.CLI.Synth.run(args)
    flagged = Muro.CLI.Synth.run(args ++ ["--on", "traces"])
    assert normalize(plain) == normalize(flagged), label
  end

  defp normalize({:exit, code, book, report}) do
    {code, book, Enum.map(report, &normalize_line/1)}
  end

  defp normalize(other), do: other

  defp normalize_line(line) do
    trimmed = String.trim_trailing(line, "\n")

    case JSON.decode(trimmed) do
      {:ok, map} when is_map(map) ->
        map |> Map.delete("enum_ms") |> JSON.encode!()

      _ ->
        Regex.replace(~r/\d+ ms/, trimmed, "N ms")
    end
  end

  defp candidates(ranked) do
    Enum.map(ranked, fn {:ok, detail} -> detail.candidate end)
  end

  defp tmp do
    path =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_proc_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.rm_rf!(path)
    File.mkdir_p!(path)
    on_exit(fn -> File.rm_rf!(path) end)
    path
  end
end
