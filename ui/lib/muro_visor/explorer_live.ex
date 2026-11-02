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
          |> assign(:catalog, MuroVisor.Meetings.catalog(open.book, graph))
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
        <div class="graph-scroll">
          <svg
            id="book-graph"
            xmlns="http://www.w3.org/2000/svg"
            width={@picture.width}
            height={@picture.height}
            style={"--native-width: #{@picture.width}px"}
            viewBox={"0 0 #{@picture.width} #{@picture.height}"}
          >
            <g
              :for={node <- @picture.nodes}
              id={control(:node, node.id)}
              class={[node.class, picked?(@selected, :node, node.id) && "selected"]}
              data-kind={node.kind}
              data-mode={node.mode}
              data-name={node.name}
              tabindex="0"
              role="button"
              phx-click="select"
              phx-keydown="select"
              phx-value-id={control(:node, node.id)}
            >
              <rect class={node.class} x={node.x} y={node.y} width={node.w} height={node.h} />
              <text x={node.x + 8} y={node.y + 18}>{node.name}</text>
              <g
                :for={meet <- node.meetings}
                id={"meeting-#{meet.id}"}
                class="compound"
                data-meeting={meet.name}
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
                  <text x={t.lx} y={t.ly}>{t.label}</text>
                </g>
              </g>
            </g>
            <g
              :for={edge <- @picture.edges}
              id={control(:edge, edge.id)}
              data-from={edge.from}
              data-to={edge.to}
              data-use={edge.use}
              tabindex="0"
              role="button"
              phx-click="select"
              phx-keydown="select"
              phx-value-id={control(:edge, edge.id)}
            >
              <path d={edge.d} fill="none" stroke="#44403c" stroke-opacity="0" stroke-width="12" />
              <path
                class={["edge", picked?(@selected, :edge, edge.id) && "selected"]}
                d={edge.d}
                stroke-width="1.5"
              />
              <text x={edge.lx} y={edge.ly}>{edge.label}</text>
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
        <div :if={@focus} id="sequence" class="sequence" data-meet={@focus.name}>
          <div class="seq-grid seq-head">
            <div
              id="lane-left"
              class="lane"
              data-party={@focus.left}
              data-session={@focus.left_session}
            >
              <strong>{@focus.left}</strong>
              <span>{@focus.left_session}</span>
            </div>
            <div></div>
            <div
              id="lane-right"
              class="lane"
              data-party={@focus.right}
              data-session={@focus.right_session}
            >
              <strong>{@focus.right}</strong>
              <span>{@focus.right_session}</span>
            </div>
          </div>
          <div
            :for={row <- @focus.rows}
            id={"seq-#{row.index}"}
            class={["seq-row", row.kind == :terminal && "terminal", row.loop && "loop"]}
            data-kind={row.kind}
            data-from={row.from}
            data-to={row.to}
            data-label={row.label}
            data-branch={row.branch}
            data-loop={row.loop && "true"}
          >
            <div :if={row.kind == :terminal} class="terminal-label">{row.label}</div>
            <div :if={row.kind != :terminal} class="seq-grid">
              <div class="life"></div>
              <div class={[
                "msg",
                row.to_side == :left && "to-left",
                row.to_side == :right && "to-right"
              ]}>
                <span :if={row.to_side == :left} class="glyph">←</span>
                <span class="shaft"></span>
                <span class="label">{row.label}</span>
                <span :if={row.branch} class="branch">/ {row.branch}</span>
                <span :if={row.loop} class="loop">loop</span>
                <span :if={row.to_side == :right} class="glyph">→</span>
              </div>
              <div class="life"></div>
            </div>
          </div>
        </div>
        <div :if={is_nil(@focus)} id="meeting-picker" class="picker">
          <p :if={@catalog.groups == []}>This book has no meetings.</p>
          <section
            :for={group <- @catalog.groups}
            id={"group-#{group.dom}"}
            class="group"
            data-session={group.base}
          >
            <h2>{group.base}</h2>
            <.link
              :for={meet <- group.meetings}
              id={"meet-#{meet.dom}"}
              class="meet-row"
              patch={meet.href}
              data-meet={meet.name}
              data-left={meet.left}
              data-right={meet.right}
              data-base={meet.base}
              data-steps={meet.steps}
              data-evidence={meet.evidence}
            >
              <span class="name">{meet.name}</span>
              <span class="parties">{meet.left} with {meet.right}</span>
              <span class="base">{meet.base}</span>
              <span class="steps">{meet.steps}</span>
              <span :if={meet.buffer} class="buffer">buffer {meet.buffer}</span>
              <span :if={meet.evidence != ""} class="evidence">{meet.evidence}</span>
            </.link>
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
          <button
            :if={@focus.left_select}
            id={"conform-#{@focus.left_dom}"}
            type="button"
            phx-click="select"
            phx-value-id={@focus.left_select}
          >
            {@focus.left}<span class="loc">{@focus.left_loc}</span>
          </button>
          <button
            :if={@focus.right_select}
            id={"conform-#{@focus.right_dom}"}
            type="button"
            phx-click="select"
            phx-value-id={@focus.right_select}
          >
            {@focus.right}<span class="loc">{@focus.right_loc}</span>
          </button>
        </section>
        <p :if={@focus} id="outline-for">meeting: {@focus.name}</p>
        <h2>Detail</h2>
        <p id="detail-title">{@detail.title}</p>
        <p id="detail-loc">{@detail.loc}</p>
        <p id="detail-refusal-kind">{@detail.kind}</p>
        <h2>Outline</h2>
        <pre :if={!is_map(@outline)} id="outline">{@outline}</pre>
        <section :if={is_map(@outline)} id="outline">
          {"backend: #{@backend}\n"}
          <details id="outline-names" open>
            <summary>names</summary>
            <pre>{"names: #{@outline.names}\n"}</pre>
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

  defp activate?(%{"key" => key}), do: key in ["Enter", " ", "Space", "Spacebar"]
  defp activate?(_params), do: true

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
