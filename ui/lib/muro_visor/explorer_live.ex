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

  def handle_event("select", %{"id" => id}, socket) do
    detail = MuroVisor.Detail.lookup(socket.assigns.graph, socket.assigns.book, id)
    {:noreply, assign(socket, :detail, detail)}
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
      <svg
        id="book-graph"
        xmlns="http://www.w3.org/2000/svg"
        width={@picture.width}
        height={@picture.height}
        viewBox={"0 0 #{@picture.width} #{@picture.height}"}
      >
        <g
          :for={edge <- @picture.edges}
          id={"edge-#{edge.id}"}
          data-from={edge.from}
          data-to={edge.to}
          data-use={edge.use}
          phx-click="select"
          phx-value-id={edge.id}
        >
          <line class="edge" x1={edge.x1} y1={edge.y1} x2={edge.x2} y2={edge.y2} stroke-width="1.5" />
        </g>
        <g
          :for={node <- @picture.nodes}
          id={"node-#{node.id}"}
          class={node.class}
          data-kind={node.kind}
          data-mode={node.mode}
          data-name={node.name}
          phx-click="select"
          phx-value-id={node.id}
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
              id={"node-#{child.id}"}
              data-state={child.state}
              phx-click="select"
              phx-value-id={child.id}
            >
              <rect x={child.x} y={child.y} width={child.w} height={child.h} class="node" />
              <text x={child.x + 6} y={child.y + 16}>{child.label}</text>
            </g>
            <g
              :for={t <- meet.transitions}
              id={"trans-#{t.id}"}
              data-from={t.from}
              data-to={t.to}
              data-label={t.label}
            >
              <path d={t.d} fill="none" stroke="#78716c" stroke-width="1.25" />
              <text x={t.lx} y={t.ly}>{t.label}</text>
            </g>
          </g>
        </g>
      </svg>
      <section>
        <h2>Detail</h2>
        <p id="detail-title">{@detail.title}</p>
        <p id="detail-loc">{@detail.loc}</p>
        <p id="detail-refusal-kind">{@detail.kind}</p>
        <h2>Outline</h2>
        <pre id="outline">{@outline}</pre>
      </section>
    </main>
    """
  end

  defp path_label(nil), do: ""
  defp path_label(path), do: Path.basename(path)

  defp backend("otp"), do: :otp
  defp backend("fsm"), do: :fsm
  defp backend("c"), do: :c
  defp backend("rust"), do: :rust
  defp backend("zig"), do: :zig
  defp backend(_other), do: nil
end
