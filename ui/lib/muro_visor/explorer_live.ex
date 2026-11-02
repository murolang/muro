defmodule MuroVisor.ExplorerLive do
  @moduledoc false

  use Phoenix.LiveView, layout: false

  @impl true
  def mount(_params, _session, socket) do
    case MuroVisor.Book.current() do
      {:ok, open} ->
        graph = Muro.Explore.graph(open.book)

        {:ok,
         socket
         |> assign(:stamp, open.stamp)
         |> assign(:path, open.path)
         |> assign(:book, open.book)
         |> assign(:graph, graph)
         |> assign(:picture, MuroVisor.Draw.layout(graph))
         |> assign(:backend, :otp)
         |> assign(:outline, MuroVisor.Outline.render(open.book, open.path, :otp))
         |> assign(:detail, MuroVisor.Detail.empty())
         |> assign(:selected, nil)
         |> assign(:error, nil)}

      {:error, msg} ->
        empty = %{nodes: [], edges: []}

        {:ok,
         assign(socket,
           stamp: nil,
           path: nil,
           book: nil,
           graph: empty,
           picture: MuroVisor.Draw.layout(empty),
           backend: :otp,
           outline: "",
           detail: MuroVisor.Detail.empty(),
           selected: nil,
           error: msg
         )}
    end
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
      <div class="graph-pane">
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
      <aside class="side">
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
end
