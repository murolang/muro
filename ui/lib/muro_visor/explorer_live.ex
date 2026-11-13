defmodule MuroVisor.ExplorerLive do
  @moduledoc false

  use Phoenix.LiveView, layout: false

  @impl true
  def mount(_params, _session, socket) do
    socket =
      case MuroVisor.Book.current() do
        {:ok, open} ->
          graph = Muro.Explore.graph(open.book)

          socket
          |> assign(:stamp, open.stamp)
          |> assign(:path, open.path)
          |> assign(:book, open.book)
          |> assign(:graph, graph)
          |> assign(
            :picture,
            graph |> MuroVisor.Draw.layout() |> MuroVisor.Grades.paint(open.book)
          )
          |> assign(:env, MuroVisor.EnvGraph.build(open.book))
          |> assign(:catalog, MuroVisor.Meetings.catalog(open.book, graph, open.path))
          |> assign(:backend, :otp)
          |> assign(:outline, MuroVisor.Outline.render(open.book, open.path, :otp))
          |> assign(:detail, MuroVisor.Detail.empty())
          |> assign(:selected, nil)
          |> assign(:error, nil)

        {:error, msg} ->
          empty = %{nodes: [], edges: []}

          assign(socket,
            stamp: nil,
            path: nil,
            book: nil,
            graph: empty,
            picture: empty |> MuroVisor.Draw.layout() |> MuroVisor.Grades.paint([]),
            env: MuroVisor.EnvGraph.build(nil),
            catalog: MuroVisor.Meetings.catalog(nil, empty),
            backend: :otp,
            outline: "",
            detail: MuroVisor.Detail.empty(),
            selected: nil,
            error: msg
          )
      end

    {:ok,
     assign(socket,
       screen: :picker,
       focus: nil,
       missing: false,
       grades_on: false,
       round: 1,
       trace: nil,
       trace_error: nil,
       trace_path: nil
     )}
  end

  @impl true
  def handle_params(params, _uri, socket) do
    {screen, name} = screen(params)

    focus =
      if screen == :meet do
        Enum.find(socket.assigns.catalog.meetings, &(&1.name == name))
      end

    {screen, missing} =
      if screen == :meet and is_nil(focus), do: {:picker, true}, else: {screen, false}

    {trace, trace_error, trace_path} = load_trace(params["trace"])

    {:noreply,
     assign(socket,
       screen: screen,
       focus: focus,
       missing: missing,
       grades_on: screen == :all and params["grades"] == "on",
       round: parse_round(params["round"]),
       trace: trace,
       trace_error: trace_error,
       trace_path: trace_path
     )}
  end

  @impl true
  def handle_event("backend", %{"backend" => name}, socket) do
    case backend(name) do
      nil ->
        {:noreply, socket}

      which ->
        outline = MuroVisor.Outline.render(socket.assigns.book, socket.assigns.path, which)
        {:noreply, assign(socket, backend: which, outline: outline)}
    end
  end

  def handle_event("select", %{"id" => id} = params, socket) do
    if activate?(params) do
      detail = MuroVisor.Detail.lookup(socket.assigns.graph, socket.assigns.book, id)
      {:noreply, assign(socket, detail: detail, selected: id)}
    else
      {:noreply, socket}
    end
  end

  def handle_event("open-meet", %{"name" => name} = params, socket) do
    if activate?(params) and is_binary(name) and name != "" do
      {:noreply, push_patch(socket, to: "/?meet=#{URI.encode_www_form(name)}")}
    else
      {:noreply, socket}
    end
  end

  @impl true
  def render(assigns) do
    assigns =
      assigns
      |> assign(:host, MuroVisor.HostLexer.for_backend(assigns.backend))
      |> assign(:grade_binders, grade_binders(assigns.picture))

    ~H"""
    <header>
      <strong>muro visor</strong>
      <span>{path_label(@path)}</span>
      <span id="book-stamp" hidden>{@stamp}</span>
      <button
        :for={name <- ~w(otp fsm c rust zig)}
        id={"backend-#{name}"}
        type="button"
        phx-click="backend"
        phx-value-backend={name}
      >
        {name}
      </button>
    </header>
    <p :if={@error} id="book-error">{@error}</p>
    <main id="workspace" phx-hook="SideWidth">
      <div :if={@screen == :all} class="graph-pane">
        <nav class="views">
          <.link id="view-meetings" patch="/">Meetings</.link>
          <.link id="view-all" class="current" patch={all_href(@grades_on)}>All definitions</.link>
          <.link id="view-synth" patch="/?view=synth">Synthesis</.link>
        </nav>
        <.link id="grade-toggle" patch={grade_href(@grades_on)} data-on={"#{@grades_on}"}>
          {if @grades_on, do: "grades on", else: "grades"}
        </.link>
        <ul :if={@grades_on} id="grade-legend">
          <li data-kind="runtime">
            <span class="swatch grade-runtime">run</span> runtime, full opacity
          </li>
          <li data-kind="erased">
            <span class="swatch grade-erased">erased</span> erased, grade 0, faded
          </li>
          <li :if={qty?(@grade_binders, "linear")} data-kind="linear">
            <span class="swatch">%1</span> linear, used once
          </li>
          <li :if={qty?(@grade_binders, "reuse")} data-kind="reuse">
            <span class="swatch">+</span> reuse, may be copied
          </li>
        </ul>
        <ul :if={@grades_on} id="grade-binders">
          <li
            :for={binder <- @grade_binders}
            data-def={binder.def}
            data-binder={binder.name}
            data-qty={binder.qty}
            data-grade-c={binder.c}
            data-grade-t={binder.t}
            class={binder_class(@grades_on, binder.qty)}
            style={binder_style(@grades_on, binder.qty)}
          >
            {binder.def} {binder.name} {binder_label(binder)}
          </li>
        </ul>
        <input type="radio" name="zoom" id="zoom-fit" checked />
        <label for="zoom-fit">fit</label>
        <input type="radio" name="zoom" id="zoom-100" />
        <label for="zoom-100">100%</label>
        <input type="radio" name="zoom" id="zoom-150" />
        <label for="zoom-150">150%</label>
        <ul :if={@picture.legend != []} id="edge-legend">
          <li :for={kind <- @picture.legend} data-kind={kind}>
            <svg width="28" height="10" aria-hidden="true">
              <line class={"edge edge-#{kind}"} x1="0" y1="5" x2="28" y2="5" />
            </svg>
            <span>{kind}</span>
          </li>
        </ul>
        <div class="graph-scroll">
          <svg
            id="book-graph"
            xmlns="http://www.w3.org/2000/svg"
            width={@picture.width}
            height={@picture.height}
            style={"--native-width: #{@picture.width}px; --native-height: #{@picture.height}px"}
            preserveAspectRatio="xMidYMid meet"
            viewBox={"0 0 #{@picture.width} #{@picture.height}"}
          >
            <g :for={cluster <- @picture.clusters} class="cluster" data-cluster={cluster.name}>
              <rect
                class="cluster-frame"
                x={cluster.x}
                y={cluster.y}
                width={cluster.w}
                height={cluster.h}
                rx="6"
              />
              <text class="cluster-title" x={cluster.x + 8} y={cluster.y + 14}>{cluster.name}</text>
            </g>
            <g
              :for={node <- @picture.nodes}
              id={control(:node, node.id)}
              class={[
                node.class,
                picked?(@selected, :node, node.id) && "selected",
                @grades_on && node.grade && "grade-#{node.grade}"
              ]}
              data-kind={node.kind}
              data-mode={node.mode}
              data-name={node.name}
              data-grade={node.grade}
              data-cluster={Map.get(node, :cluster)}
              opacity={MuroVisor.Grades.opacity(@grades_on, node.grade)}
              tabindex="0"
              role="button"
              phx-click={click_event(node)}
              phx-keydown={click_event(node)}
              phx-value-id={control(:node, node.id)}
              phx-value-name={node.bare}
            >
              <rect class={node.class} x={node.x} y={node.y} width={node.w} height={node.h} />
              <text class="node-label muro-code" x={node.x + 8} y={node.y + 18}>
                {MuroVisor.Code.svg(node.name)}
              </text>
              <g
                :for={binder <- node.binders}
                class={binder_class(@grades_on, binder.qty)}
                data-binder={binder.name}
                data-qty={binder.qty}
                data-grade-c={binder.c}
                data-grade-t={binder.t}
                opacity={MuroVisor.Grades.binder_opacity(@grades_on, binder.qty)}
              >
              </g>
              <g
                :for={meet <- node.meetings}
                id={"meeting-#{meet.id}"}
                class="compound"
                data-meeting={meet.name}
                tabindex="0"
                role="link"
                phx-click="open-meet"
                phx-keydown="open-meet"
                phx-value-name={meet.name}
              >
                <rect class="compound" x={meet.x} y={meet.y} width={meet.w} height={meet.h} />
                <text x={meet.x + 6} y={meet.y + 14}>{meet.name}</text>
                <g
                  :for={child <- meet.children}
                  id={control(:configuration, child.id)}
                  class={picked?(@selected, :configuration, child.id) && "selected"}
                  data-state={child.state}
                  tabindex="0"
                  role="button"
                  phx-click="select"
                  phx-keydown="select"
                  phx-value-id={control(:configuration, child.id)}
                >
                  <rect
                    x={child.x}
                    y={child.y}
                    width={child.w}
                    height={child.h}
                    class={["node", picked?(@selected, :configuration, child.id) && "selected"]}
                  />
                  <text x={child.x + 6} y={child.y + 16}>{child.label}</text>
                </g>
                <g
                  :for={t <- meet.transitions}
                  id={control(:transition, t.id)}
                  data-from={t.from}
                  data-to={t.to}
                  data-label={t.label}
                  tabindex="0"
                  role="button"
                  phx-click="select"
                  phx-keydown="select"
                  phx-value-id={control(:transition, t.id)}
                >
                  <path
                    class={["transition", picked?(@selected, :transition, t.id) && "selected"]}
                    d={t.d}
                    fill="none"
                    stroke="#78716c"
                    stroke-width="1.25"
                  />
                  <text :if={t.label != ""} class="edge-label muro-code" x={t.lx} y={t.ly}>
                    {MuroVisor.Code.svg(t.label)}
                  </text>
                </g>
              </g>
            </g>
            <g
              :for={edge <- @picture.edges}
              id={control(:edge, edge.id)}
              data-from={edge.from}
              data-to={edge.to}
              data-use={edge.use}
              data-count={edge.count}
              tabindex="0"
              role="button"
              phx-click="select"
              phx-keydown="select"
              phx-value-id={control(:edge, edge.id)}
            >
              <path d={edge.d} fill="none" stroke="#44403c" stroke-opacity="0" stroke-width="12" />
              <path
                class={["edge", "edge-#{edge.use}", picked?(@selected, :edge, edge.id) && "selected"]}
                d={edge.d}
                stroke-width="1.5"
              />
              <text :if={edge.label != ""} class="edge-label muro-code" x={edge.lx} y={edge.ly}>
                {MuroVisor.Code.svg(edge.label)}
              </text>
              <rect
                :if={edge.count > 1}
                class="count-badge"
                x={edge.bx}
                y={edge.by}
                width={edge.bw}
                height={edge.bh}
                rx="3"
              />
              <text
                :if={edge.count > 1}
                class="count-badge"
                x={edge.tx}
                y={edge.ty}
                text-anchor="middle"
              >
                {edge.count}
              </text>
            </g>
          </svg>
        </div>
      </div>
      <MuroVisor.SynthView.panel
        :if={@screen == :synth}
        env={@env}
        trace={@trace}
        trace_error={@trace_error}
        trace_path={@trace_path}
        round={@round}
      />
      <div :if={@screen in [:picker, :meet]} class="graph-pane meeting-pane">
        <nav class="views">
          <.link id="view-meetings" class="current" patch="/">Meetings</.link>
          <.link id="view-all" patch="/?view=all">All definitions</.link>
          <.link id="view-synth" patch="/?view=synth">Synthesis</.link>
        </nav>
        <p :if={@missing} id="meeting-missing">no such meeting</p>
        <MuroVisor.Sequence.sequence :if={@focus} meet={@focus} />
        <div :if={is_nil(@focus)} id="meeting-picker" class="picker">
          <p :if={@catalog.groups == []}>This book has no meetings.</p>
          <section
            :for={group <- @catalog.groups}
            id={"group-#{group.dom}"}
            class="group"
            data-session={group.base}
          >
            <h2 class="session-head">
              <span class="session-name">{group.base}</span>: {MuroVisor.Code.inline(group.spec)}
            </h2>
            <div class="sheet" role="table">
              <div class="sheet-head" role="row">
                <span>meeting</span>
                <span>parties</span>
                <span>steps</span>
                <span>evidence</span>
              </div>
              <.link
                :for={meet <- group.meetings}
                id={"meet-#{meet.dom}"}
                class="meet-row"
                role="row"
                patch={meet.href}
                data-meet={meet.name}
                data-left={meet.left}
                data-right={meet.right}
                data-base={meet.base}
                data-steps={meet.steps}
                data-evidence={meet.evidence}
              >
                <span class="name">{meet.name}</span>
                <span class="parties">{meet.left} ⇄ {meet.right}</span>
                <span class="steps">{meet.steps}</span>
                <span class="evidence">{MuroVisor.Code.inline(meet.evidence)}</span>
              </.link>
            </div>
          </section>
        </div>
      </div>
      <aside class="side">
        <div class="side-grip" role="separator" aria-orientation="vertical"></div>
        <section :if={@focus} id="context">
          <p id="meeting-checked" class="badge">checked</p>
          <h2>Session</h2>
          <p id="context-session">{@focus.base}</p>
          {MuroVisor.Code.pre(@focus.spec, id: "context-spec")}
          <h2>Dual</h2>
          <p :if={@focus.dual_name} id="context-dual-name">{@focus.dual_name}</p>
          {MuroVisor.Code.pre(@focus.dual, id: "context-dual")}
          <h2>Conforms</h2>
          {conform_button(@focus.left_select, @focus.left_dom, @focus.left, @focus.left_loc)}
          {conform_button(@focus.right_select, @focus.right_dom, @focus.right, @focus.right_loc)}
        </section>
        <p :if={@focus} id="outline-for">meeting: {@focus.name}</p>
        <section :if={@detail.title != ""} id="detail">
          <h2>Detail</h2>
          <p id="detail-title">{@detail.title}</p>
          <p id="detail-loc">{@detail.loc}</p>
          <p id="detail-refusal-kind">{@detail.kind}</p>
          {MuroVisor.Code.blocks(@detail.excerpts)}
        </section>
        <h2>Outline</h2>
        <pre :if={!is_map(@outline)} id="outline" class="muro-code">{MuroVisor.Code.html(@outline)}</pre>
        <section :if={is_map(@outline)} id="outline">
          <h2 id="outline-backend">{@backend}</h2>
          <details id="outline-names" open>
            <summary>names</summary>
            <pre class="muro-code">{MuroVisor.Code.html("names: #{@outline.names}")}</pre>
          </details>
          <details id="outline-signatures">
            <summary>signatures</summary>
            <pre class="muro-code">{MuroVisor.Code.html(@outline.signatures, lexer: @host)}</pre>
          </details>
          <details id="outline-layouts">
            <summary>layouts</summary>
            <pre class="muro-code">{MuroVisor.Code.html("layouts:\n#{@outline.layouts}")}</pre>
          </details>
          <details id="outline-clauses">
            <summary>clauses</summary>
            <pre class="muro-code">{MuroVisor.Code.html(@outline.clauses, lexer: @host)}</pre>
          </details>
        </section>
      </aside>
    </main>
    """
  end

  defp conform_button(nil, _dom, _name, _loc), do: nil

  defp conform_button(select, dom, name, loc) do
    {:safe,
     ~s(<button id="conform-#{escape(dom)}" type="button" phx-click="select" phx-value-id="#{escape(select)}">#{escape(name)}<span class="loc">#{escape(loc)}</span></button>)}
  end

  defp escape(value) do
    value
    |> to_string()
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
  end

  defp activate?(%{"key" => key}), do: key in ["Enter", " ", "Space", "Spacebar"]
  defp activate?(_params), do: true

  defp click_event(%{kind: "meet"}), do: "open-meet"
  defp click_event(_node), do: "select"

  defp control(kind, id), do: MuroVisor.Detail.dom_id(kind, id)
  defp picked?(selected, kind, id), do: selected == control(kind, id)

  defp path_label(nil), do: ""
  defp path_label(path), do: Path.basename(path)

  defp backend("otp"), do: :otp
  defp backend("fsm"), do: :fsm
  defp backend("c"), do: :c
  defp backend("rust"), do: :rust
  defp backend("zig"), do: :zig
  defp backend(_other), do: nil

  defp screen(%{"meet" => name}) when is_binary(name) and name != "", do: {:meet, name}
  defp screen(%{"view" => "synth"}), do: {:synth, nil}
  defp screen(%{"view" => "all"}), do: {:all, nil}
  defp screen(_params), do: {:picker, nil}

  defp all_href(true), do: "/?view=all&grades=on"
  defp all_href(false), do: "/?view=all"

  defp grade_href(true), do: "/?view=all"
  defp grade_href(false), do: "/?view=all&grades=on"

  defp grade_binders(picture) do
    Enum.flat_map(picture.nodes, fn node ->
      node
      |> Map.get(:binders, [])
      |> Enum.map(&Map.put(&1, :def, node.bare))
    end)
  end

  defp qty?(binders, qty), do: Enum.any?(binders, &(&1.qty == qty))

  defp binder_class(true, "erased"), do: "binder grade-erased"
  defp binder_class(true, qty) when is_binary(qty), do: "binder grade-runtime"
  defp binder_class(_on, _qty), do: "binder"

  defp binder_style(true, "erased"), do: "opacity: 0.35"
  defp binder_style(true, qty) when is_binary(qty), do: "opacity: 1"
  defp binder_style(_on, _qty), do: nil

  defp binder_label(%{c: c, t: t, qty: qty}) when is_binary(c) and is_binary(t) do
    "#{qty} (#{c}, #{t})"
  end

  defp binder_label(%{qty: qty}), do: qty

  defp load_trace(path) when is_binary(path) and path != "" do
    expanded = Path.expand(path)

    case MuroVisor.SynthTrace.load(expanded) do
      {:ok, trace} -> {trace, nil, expanded}
      {:error, msg} -> {nil, msg, expanded}
    end
  end

  defp load_trace(_path), do: {nil, nil, nil}

  defp parse_round(text) when is_binary(text) do
    case Integer.parse(text) do
      {n, ""} when n > 0 -> n
      _ -> 1
    end
  end

  defp parse_round(_text), do: 1
end
