defmodule MuroVisor.Layouts do
  @moduledoc false

  use Phoenix.Component

  # Makeup's own sheets. The class is the visor's code class, so a
  # second keyword list cannot drift from `Muro.MakeupLexer`.
  @light_css Makeup.stylesheet(:default_style, "muro-code")
  @dark_css Makeup.stylesheet(:one_dark_style, "theme-dark .muro-code")

  def root(assigns) do
    assigns =
      assign(assigns, :ink, {:safe, ["<style>", @light_css, "\n", @dark_css, "</style>"]})

    ~H"""
    <!DOCTYPE html>
    <html lang="en">
      <head>
        <meta charset="utf-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1" />
        <meta name="csrf-token" content={Plug.CSRFProtection.get_csrf_token()} />
        <title>muro visor</title>
        <script>
          (function () {
            try {
              var theme = new URLSearchParams(window.location.search).get("theme")
              var dark = theme === "dark" || (theme !== "light" && window.matchMedia("(prefers-color-scheme: dark)").matches)
              document.documentElement.classList.add(dark ? "theme-dark" : "theme-light")
            } catch (e) {}
          })()
        </script>
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
          .graph-scroll { container-type: size; overflow: auto; height: calc(100vh - 140px); border: 1px solid #e7e5e4; background: #fff; }
          #edge-legend { display: flex; gap: 14px; align-items: center; list-style: none; margin: 0 0 8px; padding: 0; font-size: 13px; }
          #edge-legend li { display: flex; align-items: center; gap: 6px; }
          #edge-legend svg { display: block; }
          #zoom-fit:checked ~ .graph-scroll svg#book-graph { width: max(calc(var(--native-width) * 11 / 12), min(calc(100cqw - 24px), calc((100cqh - 24px) * var(--native-width) / var(--native-height)))); height: auto; aspect-ratio: var(--native-width) / var(--native-height); }
          #zoom-100:checked ~ .graph-scroll svg#book-graph { width: var(--native-width); height: var(--native-height); max-width: none; max-height: none; aspect-ratio: auto; }
          #zoom-150:checked ~ .graph-scroll svg#book-graph { width: calc(var(--native-width) * 1.5); height: calc(var(--native-height) * 1.5); max-width: none; max-height: none; aspect-ratio: auto; }
          aside.side { min-width: 0; }
          button { font: inherit; padding: 4px 10px; }
          #outline { font: 12px/1.35 ui-monospace, monospace; max-width: 100%; }
          #outline h2 { margin: 0 0 8px; font: 600 14px/1.3 ui-sans-serif, sans-serif; }
          #outline pre { white-space: pre-wrap; overflow-wrap: normal; word-break: normal; max-width: 100%; margin: 0; }
          #outline details { margin: 0; }
          #outline summary { cursor: pointer; }
          svg .node { fill: #fff; stroke: #44403c; }
          svg .compound { fill: #f5f5f4; }
          svg .edge { stroke: #78716c; fill: none; }
          svg .edge-meet { stroke: #c2410c; stroke-width: 1.75px; }
          svg .edge-step { stroke: #57534e; stroke-width: 1.5px; }
          svg .edge-dual { stroke: #1e3a8a; stroke-width: 1.5px; stroke-dasharray: 8 5; }
          svg .edge-def { stroke: #a8a29e; stroke-width: 1.25px; stroke-dasharray: 1 4; }
          svg rect.cluster-frame { fill: #fafaf9; stroke: #d6d3d1; stroke-width: 1px; }
          svg text.cluster-title { font-weight: 600; fill: #44403c; }
          svg rect.count-badge { fill: #fff; stroke: #44403c; }
          svg text.count-badge { font-size: 12px; fill: #1c1917; }
          svg g.selected > rect.node,
          svg g.selected > rect.compound,
          svg rect.selected { stroke: #b45309; stroke-width: 2.5px; }
          svg path.edge.selected { stroke: #b45309; stroke-width: 2.5px; }
          svg path.edge.selected + text { fill: #b45309; }
          svg path.transition.selected { stroke: #b45309; stroke-width: 2.5px; }
          svg path.transition.selected + text { fill: #b45309; }
          svg text { font: 12px ui-sans-serif, sans-serif; fill: #1c1917; stroke: none; }
          svg text.edge-label { stroke: #fff; stroke-width: 4px; paint-order: stroke fill; stroke-linejoin: round; }
          svg g:focus, svg g:focus-visible { outline: none; }
          svg g:focus-visible > rect.node,
          svg g:focus-visible > rect.compound { stroke: #b45309; stroke-width: 2.5px; }
          svg g:focus-visible > path.edge,
          svg g:focus-visible > path.transition {
            stroke: #b45309;
            stroke-width: 2.5px;
            filter: drop-shadow(0 0 1px #b45309);
          }
          svg g:focus-visible > path.edge + text,
          svg g:focus-visible > path.transition + text { fill: #b45309; }
          .views { display: flex; gap: 12px; margin-bottom: 12px; flex-wrap: wrap; }
          .views a { color: inherit; }
          .views a.current { font-weight: 600; }
          .meeting-pane, .sequence-wrap, .picker { max-width: 100%; overflow-x: hidden; }
          .sequence-wrap { display: flex; justify-content: center; }
          .sequence { max-width: 100%; height: auto; }
          .sequence text { font-family: ui-sans-serif, sans-serif; fill: #1c1917; stroke: none; }
          .sequence .lane-name, .sequence .arrow-label, .sequence .choice-note, .sequence .term-label, .sequence .step-no { font-size: 14px; }
          .sequence .lane-session, .sequence .loop-note { font-size: 13px; fill: #44403c; }
          .sequence .step-no { fill: #1c1917; stroke: #fafaf9; stroke-width: 3px; paint-order: stroke fill; }
          .sequence .evidence-pill { fill: #fff; stroke: #44403c; stroke-width: 1px; }
          .sequence .evidence-badge { font-size: 12px; fill: #1c1917; }
          .group { margin: 0 0 20px; }
          .session-head { margin: 0 0 8px; font-size: 15px; font-weight: 600; }
          .session-head code { font: 13px/1.4 ui-monospace, monospace; font-weight: 500; }
          .sheet-head, .meet-row { display: grid; grid-template-columns: minmax(7em, 1.1fr) minmax(10em, 1.6fr) 4.5em minmax(6em, 1fr); gap: 12px; align-items: baseline; padding: 7px 8px; }
          .sheet-head { font-size: 12px; color: #57534e; border-bottom: 1px solid #e7e5e4; }
          .meet-row { color: inherit; text-decoration: none; border-bottom: 1px solid #f5f5f4; }
          .meet-row:hover { background: #f5f5f4; }
          .meet-row .name { text-decoration: underline; }
          #context { margin-bottom: 16px; }
          #context pre { white-space: pre-wrap; overflow-wrap: normal; word-break: normal; max-width: 100%; margin: 0 0 8px; font: 13px/1.4 ui-monospace, monospace; }
          #context button { display: block; text-align: left; margin: 4px 0; white-space: normal; max-width: 100%; }
          #context .loc { display: block; font: 12px/1.4 ui-monospace, monospace; white-space: nowrap; }
          #detail { margin-bottom: 16px; }
          #detail h2, #context h2, .side > h2 { margin: 12px 0 4px; font-size: 14px; }
          .badge { display: inline-block; border: 1px solid #44403c; padding: 0 6px; }
          @media (max-width: 800px) {
            main { grid-template-columns: 1fr; }
          }
        </style>
        {@ink}
        <style>
          .session-head code { white-space: pre-wrap; }
          pre.muro-code { background-color: #fff; border-radius: 4px; }
          code.muro-code { background-color: transparent; }
          svg text.muro-code { background-color: transparent; }
          .muro-code .k, svg .k { color: #6d28d9; fill: #6d28d9; font-weight: 600; }
          .muro-code .kt, svg .kt { color: #0f766e; fill: #0f766e; }
          .muro-code .n, svg .n { color: #1c1917; fill: #1c1917; }
          .muro-code .nb, svg .nb { color: #1d4ed8; fill: #1d4ed8; }
          .muro-code .mi, svg .mi, .muro-code .m, svg .m { color: #b45309; fill: #b45309; }
          .muro-code .o, svg .o { color: #c2410c; fill: #c2410c; }
          .muro-code .p, svg .p { color: #44403c; fill: #44403c; }
          .muro-code .c, svg .c, .muro-code .c1, svg .c1 { color: #78716c; fill: #78716c; font-style: italic; }
          .muro-code .w, svg .w { color: inherit; fill: inherit; }
          .muro-code .err, svg .err { color: #c2410c; fill: #c2410c; border: 0; background: none; font-style: normal; }
          .muro-source { margin: 4px 0 8px; max-width: 100%; overflow-x: auto; font: 12px/1.45 ui-monospace, monospace; }
          .muro-source .row { display: block; }
          .muro-source .ln { display: inline-block; min-width: 2.6em; padding-right: 0.8em; text-align: right; color: #a8a29e; user-select: none; }
          .muro-source .row.marked { background: #fef3c7; }
          .muro-source .here, .muro-code .here { background: #fde68a; border-radius: 2px; }
          html.theme-dark body { color: #e7e5e4; background: #1c1917; }
          html.theme-dark header { border-bottom-color: #44403c; }
          html.theme-dark .graph-scroll { background: #292524; border-color: #44403c; }
          html.theme-dark svg .node { fill: #292524; stroke: #a8a29e; }
          html.theme-dark svg .compound { fill: #44403c; }
          html.theme-dark svg rect.cluster-frame { fill: #1c1917; stroke: #57534e; }
          html.theme-dark svg text.cluster-title { fill: #d6d3d1; }
          html.theme-dark svg text { fill: #e7e5e4; }
          html.theme-dark svg rect.count-badge { fill: #292524; stroke: #a8a29e; }
          html.theme-dark svg text.count-badge { fill: #e7e5e4; }
          html.theme-dark .sequence text { fill: #e7e5e4; }
          html.theme-dark .sequence .lane-session, html.theme-dark .sequence .loop-note { fill: #d6d3d1; }
          html.theme-dark .sequence .step-no { fill: #e7e5e4; stroke: #1c1917; }
          html.theme-dark .sequence .evidence-pill { fill: #292524; stroke: #a8a29e; }
          html.theme-dark .sequence .evidence-badge { fill: #e7e5e4; }
          html.theme-dark .sequence rect, html.theme-dark .sequence .choice-diamond { fill: #292524; stroke: #a8a29e; }
          html.theme-dark .sequence .term-mark { fill: #e7e5e4; }
          html.theme-dark .sequence .lifeline, html.theme-dark .sequence .arrow { stroke: #a8a29e; }
          html.theme-dark #seq-arrow path { fill: #a8a29e; }
          html.theme-dark .sheet-head { color: #a8a29e; border-bottom-color: #44403c; }
          html.theme-dark .meet-row { border-bottom-color: #292524; }
          html.theme-dark .meet-row:hover { background: #292524; }
          html.theme-dark .views a { color: inherit; }
          html.theme-dark pre.muro-code { background-color: #292524; color: #e7e5e4; }
          html.theme-dark .muro-code .k, html.theme-dark svg .k { color: #c4b5fd; fill: #c4b5fd; }
          html.theme-dark .muro-code .kt, html.theme-dark svg .kt { color: #5eead4; fill: #5eead4; }
          html.theme-dark .muro-code .n, html.theme-dark svg .n { color: #e7e5e4; fill: #e7e5e4; }
          html.theme-dark .muro-code .nb, html.theme-dark svg .nb { color: #93c5fd; fill: #93c5fd; }
          html.theme-dark .muro-code .mi, html.theme-dark svg .mi, html.theme-dark .muro-code .m, html.theme-dark svg .m { color: #fdba74; fill: #fdba74; }
          html.theme-dark .muro-code .o, html.theme-dark svg .o { color: #fdba74; fill: #fdba74; }
          html.theme-dark .muro-code .p, html.theme-dark svg .p { color: #d6d3d1; fill: #d6d3d1; }
          html.theme-dark .muro-code .c, html.theme-dark svg .c, html.theme-dark .muro-code .c1, html.theme-dark svg .c1 { color: #a8a29e; fill: #a8a29e; }
          html.theme-dark .muro-code .err, html.theme-dark svg .err { color: #fdba74; fill: #fdba74; border: 0; background: none; }
          html.theme-dark .muro-source .ln { color: #a8a29e; }
          html.theme-dark .muro-source .row.marked { background: #44403c; }
          html.theme-dark .muro-source .here, html.theme-dark .muro-code .here { background: #78350f; }
        </style>
      </head>
      <body>
        {@inner_content}
      </body>
    </html>
    """
  end
end
