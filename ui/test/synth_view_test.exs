defmodule MuroVisor.SynthViewTest do
  use MuroVisor.ConnCase, async: false

  test "the state graph comes from the checked book, and a trace lights one round", %{conn: conn} do
    path = fixture("env_step.muro")
    assert {:ok, book} = Muro.Load.file(path)
    graph = MuroVisor.EnvGraph.build(book)
    assert graph.states == ["start", "goal"]
    assert %{from: "start", action: "go", to: "goal"} in graph.edges
    assert %{from: "start", action: "stay", to: "start"} in graph.edges
    assert %{from: "goal", action: nil, to: "goal"} in graph.edges

    assert {:ok, _stamp} = MuroVisor.Book.open(path)
    {:ok, view, _html} = live(conn, "/?view=synth")
    bare = render(view)
    assert bare =~ "id=\"synth-graph\""
    assert bare =~ "id=\"synth-trace-missing\""
    assert bare =~ "data-state=\"start\""
    assert bare =~ "data-action=\"go\""
    refute state_attr(bare, "start", "data-status")
    refute bare =~ "id=\"synth-program\""

    trace = fixture("synth_rounds.json")
    {:ok, loaded} = MuroVisor.SynthTrace.load(trace)
    assert loaded.program == "truep"
    assert loaded.certificate == "CoindHomo"
    assert Enum.map(loaded.rounds, & &1.versions) == [4, 2, 1]
    assert Enum.map(loaded.rounds, & &1.cex) == [["start"], ["goal"], []]
    assert hd(loaded.states).status == "ranked"

    {:ok, view, _html} = live(conn, "/?view=synth&trace=#{URI.encode_www_form(trace)}&round=1")
    html = render(view)
    assert text_of(html, "#synth-program") == "truep"
    assert text_of(html, "#synth-certificate") == "CoindHomo"
    assert text_of(html, "#synth-status") == "certified"
    assert size(html, 1) == "4"
    assert size(html, 2) == "2"
    assert size(html, 3) == "1"
    assert state_attr(html, "start", "data-status") == "ranked"
    assert state_attr(html, "start", "data-certificate") == "CoindHomo"
    assert state_attr(html, "goal", "data-status") == "unsettled"
    assert state_attr(html, "start", "data-lit") == "true"
    assert state_attr(html, "goal", "data-lit") == "false"
    assert html =~ "cex"

    view |> element("#synth-round-2 a") |> render_click()
    assert_patch(view, MuroVisor.SynthView.synth_href(Path.expand(trace), 2))
    next = render(view)
    assert state_attr(next, "goal", "data-lit") == "true"
    assert state_attr(next, "start", "data-lit") == "false"
    assert text_of(next, "#synth-program") == "truep"
  end

  test "a report without rounds still shows sizes, the survivor, and the last counterexample",
       %{conn: conn} do
    book = fixture("env_step.muro")

    trace =
      write_trace(%{
        "status" => "policy",
        "program" => "(notp (feat hot))",
        "versions" => [3, 1],
        "cex" => [%{"carrier" => "goal", "predicted" => true, "oracle" => false}],
        "note" => "homomorphism is not derivable",
        "certificate" => nil
      })

    assert {:ok, loaded} = MuroVisor.SynthTrace.load(trace)
    assert Enum.map(loaded.rounds, &{&1.n, &1.versions, &1.cex}) == [{1, 3, []}, {2, 1, ["goal"]}]
    assert loaded.states == nil

    assert {:ok, _stamp} = MuroVisor.Book.open(book)
    {:ok, view, _html} = live(conn, "/?view=synth&trace=#{URI.encode_www_form(trace)}&round=2")
    html = render(view)
    assert text_of(html, "#synth-program") == "(notp (feat hot))"
    assert text_of(html, "#synth-status") == "policy"
    assert state_attr(html, "start", "data-status") == "unsettled"
    assert state_attr(html, "goal", "data-status") == "unsettled"
    assert state_attr(html, "goal", "data-lit") == "true"
    assert state_attr(html, "start", "data-lit") == "false"
    assert size(html, 1) == "3"
    assert size(html, 2) == "1"
    refute html =~ "CoindHomo"
  end

  test "two_state and binary_sacrifice expose the same kind of state graph" do
    two = MuroVisor.EnvGraph.build(load_example("cshrl/envs/two_state.muro"))
    assert two.states == ["start", "goal"]
    assert %{from: "start", action: "go", to: "goal"} in two.edges
    assert %{from: "start", action: "stay", to: "start"} in two.edges

    sacrifice = MuroVisor.EnvGraph.build(load_example("cshrl/envs/binary_sacrifice.muro"))
    assert sacrifice.states == ["start", "paradise", "trap"]
    assert %{from: "start", action: "go-paradise", to: "paradise"} in sacrifice.edges
    assert %{from: "start", action: "go-trap", to: "trap"} in sacrifice.edges
  end

  defp fixture(name), do: Path.expand("fixtures/#{name}", __DIR__)

  defp load_example(name) do
    assert {:ok, book} = Muro.Load.file(example(name))
    book
  end

  defp write_trace(map) do
    path =
      Path.join(System.tmp_dir!(), "muro-visor-trace-#{System.unique_integer([:positive])}.json")

    File.write!(path, Jason.encode!(map))
    on_exit(fn -> File.rm(path) end)
    path
  end

  defp size(html, round) do
    html
    |> parse()
    |> Floki.find("#synth-round-#{round}")
    |> case do
      [node | _] -> List.first(Floki.attribute(node, "data-size"))
      [] -> nil
    end
  end

  defp state_attr(html, state, attr) do
    html
    |> parse()
    |> Floki.find("#synth-graph [data-state=\"#{state}\"]")
    |> case do
      [node | _] -> List.first(Floki.attribute(node, attr))
      [] -> nil
    end
  end
end
