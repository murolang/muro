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
          |> assign(:picture, MuroVisor.Draw.layout(graph))
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
            picture: MuroVisor.Draw.layout(empty),
            catalog: MuroVisor.Meetings.catalog(nil, empty),
            backend: :otp,
            outline: "",
            detail: MuroVisor.Detail.empty(),
            selected: nil,
            error: msg
          )
      end

    {:ok, assign(socket, screen: :picker, focus: nil, missing: false)}
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

    {:noreply, assign(socket, screen: screen, focus: focus, missing: missing)}
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
    <main>
      <div :if={@screen == :all} class="graph-pane">
        <nav class="views">
          <.link id="view-meetings" patch="/">Meetings</.link>
          <.link id="view-all" class="current" patch="/?view=all">All definitions</.link>
        </nav>
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
              class={[node.class, picked?(@selected, :node, node.id) && "selected"]}
              data-kind={node.kind}
              data-mode={node.mode}
              data-name={node.name}
              data-cluster={Map.get(node, :cluster)}
              tabindex="0"
              role="button"
              phx-click={click_event(node)}
              phx-keydown={click_event(node)}
              phx-value-id={control(:node, node.id)}
              phx-value-name={node.bare}
            >
              <rect class={node.class} x={node.x} y={node.y} width={node.w} height={node.h} />
              <text x={node.x + 8} y={node.y + 18}>{node.name}</text>
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
                  <text :if={t.label != ""} class="edge-label" x={t.lx} y={t.ly}>{t.label}</text>
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
              <text :if={edge.label != ""} class="edge-label" x={edge.lx} y={edge.ly}>
                {edge.label}
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
      <div :if={@screen != :all} class="graph-pane meeting-pane">
        <nav class="views">
          <.link id="view-meetings" class="current" patch="/">Meetings</.link>
          <.link id="view-all" patch="/?view=all">All definitions</.link>
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
              <span class="session-name">{group.base}</span>: <code>{group.spec}</code>
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
                <span class="evidence">{meet.evidence}</span>
              </.link>
            </div>
          </section>
        </div>
      </div>
      <aside class="side">
        <section :if={@focus} id="context">
          <p id="meeting-checked" class="badge">checked</p>
          <h2>Session</h2>
          <p id="context-session">{@focus.base}</p>
          <pre id="context-spec">{@focus.spec}</pre>
          <h2>Dual</h2>
          <p :if={@focus.dual_name} id="context-dual-name">{@focus.dual_name}</p>
          <pre id="context-dual">{@focus.dual}</pre>
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
        </section>
        <h2>Outline</h2>
        <pre :if={!is_map(@outline)} id="outline">{@outline}</pre>
        <section :if={is_map(@outline)} id="outline">
          <h2 id="outline-backend">{@backend}</h2>
          <details id="outline-names" open>
            <summary>names</summary>
            <pre>{"names: #{@outline.names}"}</pre>
          </details>
          <details id="outline-signatures">
            <summary>signatures</summary>
            <pre>{@outline.signatures}</pre>
          </details>
          <details id="outline-layouts">
            <summary>layouts</summary>
            <pre>{"layouts:\n#{@outline.layouts}"}</pre>
          </details>
          <details id="outline-clauses">
            <summary>clauses</summary>
            <pre>{@outline.clauses}</pre>
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
  defp screen(%{"view" => "all"}), do: {:all, nil}
  defp screen(_params), do: {:picker, nil}
end
