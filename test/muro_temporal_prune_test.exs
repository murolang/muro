defmodule Muro.TemporalPruneTest do
  use ExUnit.Case, async: true

  alias Muro.{Ast, Parser, Temporal}

  @spin """
  data Frame : Type where
    bytes : Frame
    trailers : Frame
    headers : Frame
  session spin := rec X. send Frame X
  session hear :=
    rec Y. recv (f : Frame) (case f
      | bytes => Y
      | trailers => end
      | headers => end)
  conform spin-client : spin := rec X. put bytes X
  conform hear-server : hear := rec Y. get (f : Frame) (match f Y done done)
  meet spin-wire : spin-client with hear-server buffer 1
  """

  test "prune matches a rescanning worklist on random graphs" do
    Enum.each(1..40, fn seed ->
      :rand.seed(:exsss, {seed, 7, 11})
      n = :rand.uniform(30)
      nodes = Enum.to_list(0..(n - 1))

      succ =
        Map.new(nodes, fn i ->
          k = :rand.uniform(4) - 1
          outs = if k == 0, do: [], else: Enum.map(1..k, fn _ -> :rand.uniform(n) - 1 end)
          {i, outs}
        end)

      assert Temporal.prune(nodes, succ) == reference(nodes, succ)

      region = Enum.filter(nodes, fn _ -> :rand.uniform(3) > 1 end)
      assert Temporal.prune(region, succ) == reference(region, succ)
    end)
  end

  test "prune matches a rescanning worklist on shaped graphs" do
    assert Temporal.prune([0, 1, 2], %{0 => [1], 1 => [2], 2 => []}) == []
    assert Temporal.prune([0, 1], %{0 => [1], 1 => [0]}) == [0, 1]
    assert Temporal.prune([0, 1, 2], %{0 => [1], 1 => [2], 2 => [1]}) == [0, 1, 2]
    assert Temporal.prune([0, 1, 2, 3], %{0 => [1, 2], 1 => [3], 2 => [3], 3 => []}) == []

    assert Temporal.prune([0, 1, 2, 3], %{0 => [1, 2], 1 => [3], 2 => [3], 3 => [3]}) == [
             0,
             1,
             2,
             3
           ]

    assert Temporal.prune([0, 1], %{0 => [{:fin, 0}], 1 => [{:lside, 0}]}) == [0, 1]
    assert Temporal.prune([0, 1], %{0 => [], 1 => [{:lside, 0}]}) == []
    assert Temporal.prune([0, 1], %{0 => [1, 1], 1 => []}) == []

    for {nodes, succ} <- [
          {[0, 1, 2], %{0 => [1], 1 => [2], 2 => []}},
          {[0, 1], %{0 => [{:fin, 0}], 1 => [0]}},
          {[0, 1, 2, 3], %{0 => [1, 2], 1 => [3], 2 => [3], 3 => []}}
        ] do
      assert Temporal.prune(nodes, succ) == reference(nodes, succ)
    end
  end

  test "prune matches a rescanning worklist on the worked meetings" do
    book = book_file!("examples/temporal.muro")

    for name <- ["inflight", "echo-wire"] do
      assert_meeting(book, name)
    end

    assert_meeting(book_src!(@spin), "spin-wire")
  end

  # A linear chain pruned from the end is cubic in the rescanning
  # worklist: each pass rebuilds a membership set over the nodes still
  # left and walks all of them to find the single zero at the end.
  # Twenty thousand states finish here well inside a second.
  @tag timeout: 10_000
  test "long chains and wide graphs prune in linear time" do
    n = 20_000
    nodes = Enum.to_list(0..(n - 1))

    chain =
      Map.new(nodes, fn
        i when i == n - 1 -> {i, []}
        i -> {i, [i + 1]}
      end)

    {chain_us, chain_z} = :timer.tc(fn -> Temporal.prune(nodes, chain) end)
    assert chain_z == []
    assert chain_us < 2_000_000

    star_edges = Enum.to_list(1..(n - 1))

    star =
      Map.new(nodes, fn
        0 -> {0, star_edges}
        i -> {i, []}
      end)

    {star_us, star_z} = :timer.tc(fn -> Temporal.prune(nodes, star) end)
    assert star_z == []
    assert star_us < 2_000_000

    hub =
      Map.new(nodes, fn
        0 -> {0, [0]}
        i -> {i, [0]}
      end)

    {hub_us, hub_z} = :timer.tc(fn -> Temporal.prune(nodes, hub) end)
    assert hub_z == nodes
    assert hub_us < 2_000_000
  end

  defp assert_meeting(book, name) do
    assert {:ok, %{g: g, cs: cs, edges: edges}} = Temporal.prepare(book, name, :ok)
    assert cs != []

    for region <- [cs, Enum.drop(cs, 1), Enum.take(cs, 1), Enum.take_every(cs, 2)] do
      assert Temporal.prune(region, edges) == reference(region, edges)
      assert Temporal.worklist(g, region) == reference(region, edges)
    end
  end

  defp book_src!(src) when is_binary(src) do
    assert {:ok, named} = Parser.parse(src)
    assert {:ok, book} = Ast.book_to_db(named)
    book
  end

  defp book_file!(path), do: book_src!(File.read!(path))

  # `Live.firstZero`: the first node, in list order, whose successors in
  # the region are empty, then delete it and repeat.
  defp reference(region, succ), do: reference(region, region, succ)

  defp reference(region, [], _succ), do: region

  defp reference(region, [node | rest], succ) do
    if zero?(region, node, succ) do
      reference(List.delete(region, node), succ)
    else
      reference(region, rest, succ)
    end
  end

  defp zero?(region, node, succ) do
    succ
    |> Map.get(node, [])
    |> Enum.map(&dest/1)
    |> Enum.all?(fn target -> target not in region end)
  end

  defp dest({:lside, dest}), do: dest
  defp dest({:rside, dest}), do: dest
  defp dest({:fin, dest}), do: dest
  defp dest(dest), do: dest
end
