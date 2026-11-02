defmodule MuroVisor.Layouts do
  @moduledoc false

  use Phoenix.Component

  def root(assigns) do
    ~H"""
    <!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="utf-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1" />
        <meta name="csrf-token" content={Plug.CSRFProtection.get_csrf_token()} />
        <title>muro visor</title>
        <script src="/assets/phoenix.min.js">
        </script>
        <script src="/assets/phoenix_live_view.min.js">
        </script>
        <script>
          window.addEventListener("DOMContentLoaded", function () {
            if (!window.Phoenix || !window.LiveView) return
            var token = document.querySelector("meta[name='csrf-token']").getAttribute("content")
            var socket = new window.LiveView.LiveSocket("/live", window.Phoenix.Socket, {params: {_csrf_token: token}})
            socket.connect()
          })
        </script>
        <style>
          html, body { max-width: 100%; }
          body { font: 14px/1.4 ui-sans-serif, sans-serif; margin: 0; color: #1c1917; background: #fafaf9; overflow-x: hidden; }
          header { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; padding: 12px 16px; border-bottom: 1px solid #e7e5e4; }
          main { display: grid; grid-template-columns: minmax(0, 1fr) minmax(240px, 320px); gap: 16px; padding: 16px; align-items: start; }
          .graph-pane { min-width: 0; }
          .zoom { display: flex; gap: 12px; align-items: center; margin-bottom: 8px; }
          .graph-scroll { overflow: auto; max-height: calc(100vh - 140px); border: 1px solid #e7e5e4; background: #fff; }
          #zoom-fit:checked ~ .graph-scroll svg { width: 100%; height: auto; }
          #zoom-100:checked ~ .graph-scroll svg { width: var(--native-width); height: auto; }
          #zoom-150:checked ~ .graph-scroll svg { width: calc(var(--native-width) * 1.5); height: auto; }
          aside.side { min-width: 0; }
          button { font: inherit; padding: 4px 10px; }
          #outline { white-space: pre-wrap; font: 12px/1.4 ui-monospace, monospace; }
          #outline, #outline pre { white-space: pre-wrap; overflow-wrap: anywhere; max-width: 100%; }
          #outline details { margin: 4px 0; }
          #outline summary { cursor: pointer; }
          svg .node { fill: #fff; stroke: #44403c; }
          svg .compound { fill: #f5f5f4; }
          svg .edge { stroke: #78716c; fill: none; }
          svg g.selected > rect.node,
          svg g.selected > rect.compound,
          svg rect.selected { stroke: #b45309; stroke-width: 2.5px; }
          svg path.edge.selected { stroke: #b45309; stroke-width: 2.5px; }
          svg text { font: 12px ui-sans-serif, sans-serif; }
          svg g:focus { outline: 2px solid #b45309; }
          @media (max-width: 800px) {
            main { grid-template-columns: 1fr; }
          }
        </style>
      </head>
      <body>
        {@inner_content}
      </body>
    </html>
    """
  end
end
