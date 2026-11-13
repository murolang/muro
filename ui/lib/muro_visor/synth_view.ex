defmodule MuroVisor.SynthView do
  @moduledoc false

  use Phoenix.Component

  @node_w 140
  @node_h 56
  @gap_x 96
  @gap_y 96
  @origin_x 36
  @origin_y 40
  @cols 4

  attr :env, :map, required: true
  attr :trace, :map, default: nil
  attr :trace_error, :string, default: nil
  attr :trace_path, :string, default: nil
  attr :round, :integer, required: true

  def panel(assigns) do
    rounds = rounds_of(assigns.trace)
    round = clamp(assigns.round, rounds)
    selected = Enum.find(rounds, List.first(rounds), &(&1.n == round))
    lit = if selected, do: selected.cex, else: []
    picture = layout(assigns.env.states, assigns.env.edges)
    states = overlay(assigns.env.states, assigns.trace)

    assigns =
      assigns
      |> assign(:rounds, rounds)
      |> assign(:selected, selected)
      |> assign(:lit, lit)
      |> assign(:picture, picture)
      |> assign(:states, states)
      |> assign(:max_size, max_size(rounds))

    ~H"""
    <div class="graph-pane synth-pane">
      <nav class="views">
        <.link id="view-meetings" patch="/">Meetings</.link>
        <.link id="view-all" patch="/?view=all">All definitions</.link>
        <.link
          id="view-synth"
          class="current"
          patch={synth_href(@trace_path, @selected && @selected.n)}
        >
          Synthesis
        </.link>
      </nav>
      <p :if={@trace_error} id="synth-trace-error">{@trace_error}</p>
      <p :if={is_nil(@trace) and is_nil(@trace_error)} id="synth-trace-missing">
        No synthesis trace is loaded. A report from <code>mix muro.synth --json</code>
        opens with <code>?trace=</code>.
      </p>
      <p :if={!@env.environment?} id="synth-empty">This book does not define State.</p>
      <div :if={@trace} id="synth-report">
        <p id="synth-status" data-status={@trace.status}>{status_text(@trace)}</p>
        <p :if={@trace.certificate} id="synth-certificate">{@trace.certificate}</p>
        <p :if={@trace.note} id="synth-note">{@trace.note}</p>
        <h2>Survivor</h2>
        <pre id="synth-program">{@trace.program || "no survivor"}</pre>
        <h2>Version space</h2>
        <ol id="synth-versions">
          <li
            :for={entry <- @rounds}
            id={"synth-round-#{entry.n}"}
            data-round={entry.n}
            data-size={entry.versions}
            data-cex={Enum.join(entry.cex, " ")}
            class={[@selected && @selected.n == entry.n && "current"]}
          >
            <.link patch={synth_href(@trace_path, entry.n)}>round {entry.n}</.link>
            <span class="bar" style={"width: #{bar_width(entry.versions, @max_size)}px"}></span>
            <span class="size">{size_text(entry.versions)}</span>
          </li>
        </ol>
      </div>
      <ul id="synth-legend">
        <li data-kind="ranked"><span class="swatch ranked"></span> ranked</li>
        <li data-kind="unsettled"><span class="swatch unsettled"></span> unsettled</li>
        <li data-kind="cex"><span class="swatch cex"></span> counterexample this round</li>
      </ul>
      <div :if={@picture.nodes != []} class="graph-scroll">
        <svg
          id="synth-graph"
          xmlns="http://www.w3.org/2000/svg"
          width={@picture.width}
          height={@picture.height}
          viewBox={"0 0 #{@picture.width} #{@picture.height}"}
          role="img"
        >
          <g
            :for={edge <- @picture.edges}
            class="synth-edge"
            data-from={edge.from}
            data-to={edge.to}
            data-action={edge.action}
          >
            <path d={edge.d} fill="none" stroke="#44403c" stroke-width="1.5" />
            <text :if={edge.action} class="edge-label" x={edge.lx} y={edge.ly}>{edge.action}</text>
          </g>
          <g
            :for={node <- @picture.nodes}
            id={"state-#{dom(node.name)}"}
            class={["state", status_of(@states, node.name), lit?(@lit, node.name) && "cex"]}
            data-state={node.name}
            data-status={status_of(@states, node.name)}
            data-certificate={certificate_of(@states, node.name)}
            data-lit={to_string(lit?(@lit, node.name))}
          >
            <rect
              x={node.x}
              y={node.y}
              width={node.w}
              height={node.h}
              rx="4"
              class={["state", status_of(@states, node.name), lit?(@lit, node.name) && "cex"]}
            />
            <text class="state-name" x={node.x + 12} y={node.y + 22}>{node.name}</text>
            <text
              :if={status_of(@states, node.name)}
              class="state-status"
              x={node.x + 12}
              y={node.y + 42}
            >
              {status_of(@states, node.name)}
            </text>
          </g>
        </svg>
      </div>
    </div>
    """
  end

  @doc false
  def layout(states, edges) when is_list(states) and is_list(edges) do
    cols = if states == [], do: 1, else: min(length(states), @cols)

    nodes =
      states
      |> Enum.with_index()
      |> Enum.map(fn {name, index} ->
        col = rem(index, cols)
        row = div(index, cols)

        %{
          name: name,
          x: @origin_x + col * (@node_w + @gap_x),
          y: @origin_y + row * (@node_h + @gap_y),
          w: @node_w,
          h: @node_h
        }
      end)

    by_name = Map.new(nodes, &{&1.name, &1})
    drawn = Enum.map(edges, &place_edge(&1, by_name))
    width = extent(nodes, cols, :x, @node_w)
    height = extent(nodes, max(div(max(length(nodes) - 1, 0), cols) + 1, 1), :y, @node_h)

    %{nodes: nodes, edges: drawn, width: width, height: height}
  end

  defp place_edge(%{from: from, to: to} = edge, by_name) do
    left = Map.get(by_name, from)
    right = Map.get(by_name, to)

    if left && right && from == to do
      loop(edge, left)
    else
      if left && right do
        span(edge, left, right)
      else
        Map.merge(edge, %{d: "", lx: 0, ly: 0})
      end
    end
  end

  defp loop(edge, node) do
    x = node.x + node.w
    y = node.y + 16
    d = "M #{x} #{y} C #{x + 36} #{y - 28}, #{x + 36} #{y + 36}, #{x} #{y + 20}"

    Map.merge(edge, %{d: d, lx: x + 8, ly: y - 8})
  end

  defp span(edge, left, right) do
    x1 = left.x + left.w
    y1 = left.y + div(left.h, 2)
    x2 = right.x
    y2 = right.y + div(right.h, 2)
    {x1, x2} = if x2 > x1, do: {x1, x2}, else: {left.x, right.x + right.w}
    mid = div(x1 + x2, 2)
    d = "M #{x1} #{y1} C #{mid} #{y1}, #{mid} #{y2}, #{x2} #{y2}"

    Map.merge(edge, %{d: d, lx: mid - 8, ly: min(y1, y2) - 6})
  end

  defp extent([], _count, _key, _size), do: @origin_x + @node_w + @origin_x

  defp extent(nodes, count, key, size) do
    (Enum.max(Enum.map(nodes, &Map.fetch!(&1, key))) + size + @origin_x)
    |> max(@origin_x + count * (size + @gap_x))
  end

  defp overlay(names, nil), do: Map.new(names, &{&1, %{status: nil, certificate: nil}})

  defp overlay(names, %{states: states}) when is_list(states) do
    by_name = Map.new(states, &{&1.name, &1})

    Map.new(names, fn name ->
      case Map.get(by_name, name) do
        nil -> {name, %{status: nil, certificate: nil}}
        state -> {name, %{status: state.status, certificate: state.certificate}}
      end
    end)
  end

  defp overlay(names, %{status: "certified", certificate: certificate}) do
    Map.new(names, &{&1, %{status: "ranked", certificate: certificate}})
  end

  defp overlay(names, _trace) do
    Map.new(names, &{&1, %{status: "unsettled", certificate: nil}})
  end

  defp rounds_of(nil), do: []
  defp rounds_of(%{rounds: rounds}), do: rounds

  defp clamp(_round, []), do: 1

  defp clamp(round, rounds) do
    known = Enum.map(rounds, & &1.n)
    if round in known, do: round, else: hd(known)
  end

  defp max_size(rounds) do
    rounds
    |> Enum.map(& &1.versions)
    |> Enum.filter(&is_integer/1)
    |> Enum.max(fn -> 1 end)
    |> max(1)
  end

  defp bar_width(nil, _max), do: 0
  defp bar_width(size, max_size), do: max(round(size / max_size * 160), 8)

  defp size_text(nil), do: ""
  defp size_text(size), do: Integer.to_string(size)

  defp status_text(%{status: nil}), do: ""
  defp status_text(%{status: status}), do: status

  defp status_of(states, name) do
    case Map.get(states, name) do
      %{status: status} -> status
      _ -> nil
    end
  end

  defp certificate_of(states, name) do
    case Map.get(states, name) do
      %{certificate: certificate} -> certificate
      _ -> nil
    end
  end

  defp lit?(lit, name), do: name in lit

  defp dom(name), do: Muro.Emit.Name.encode(name)

  @doc false
  def synth_href(nil, round) when is_integer(round) and round > 1 do
    "/?view=synth&round=#{round}"
  end

  def synth_href(nil, _round), do: "/?view=synth"

  def synth_href(path, round) when is_binary(path) do
    query = %{"view" => "synth", "trace" => path}

    query =
      if is_integer(round) and round > 1 do
        Map.put(query, "round", Integer.to_string(round))
      else
        query
      end

    "/?" <> URI.encode_query(query)
  end
end
