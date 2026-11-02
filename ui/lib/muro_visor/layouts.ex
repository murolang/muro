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
            var socket = new window.LiveView.LiveSocket("/live", window.Phoenix.Socket)
            socket.connect()
          })
        </script>
        <style>
          body { font: 14px/1.4 ui-sans-serif, sans-serif; margin: 0; color: #1c1917; background: #fafaf9; }
          header { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; padding: 12px 16px; border-bottom: 1px solid #e7e5e4; }
          main { display: grid; grid-template-columns: minmax(0, 1fr) 320px; gap: 16px; padding: 16px; }
          button { font: inherit; padding: 4px 10px; }
          #outline { white-space: pre-wrap; font: 12px/1.4 ui-monospace, monospace; }
          svg .node { fill: #fff; stroke: #44403c; }
          svg .compound { fill: #f5f5f4; }
          svg .edge { stroke: #78716c; }
          svg text { font: 12px ui-sans-serif, sans-serif; }
        </style>
      </head>
      <body>
        {@inner_content}
      </body>
    </html>
    """
  end
end
