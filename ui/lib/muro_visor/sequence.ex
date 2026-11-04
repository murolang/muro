defmodule MuroVisor.Sequence do
  @moduledoc false

  use Phoenix.Component

  # One row per transition of the configuration graph the checker
  # recorded, then a terminal row for a halted state. The process head
  # in that state says who sends. A choice's branch count and a
  # refinement discharged by a step come from the session the checker
  # opened, walked in step with those transitions.

  @gap 420
  @pad 16
  @step_col 36
  @box_h 52
  @char 8
  @mark 10

  attr :meet, :map, required: true

  def sequence(assigns) do
    assigns = assign(assigns, :d, diagram(assigns.meet))

    ~H"""
    <div class="sequence-wrap">
      <svg
        id="sequence"
        class="sequence"
        xmlns="http://www.w3.org/2000/svg"
        width={@d.width}
        height={@d.height}
        viewBox={"0 0 #{@d.width} #{@d.height}"}
        data-meet={@meet.name}
        role="img"
      >
        <defs>
          <marker
            id="seq-arrow"
            markerUnits="strokeWidth"
            markerWidth="7"
            markerHeight="6"
            refX="7"
            refY="3"
            orient="auto"
          >
            <path d="M0,0 L7,3 L0,6 Z" fill="#44403c" />
          </marker>
        </defs>
        <g id="lane-left" data-party={@meet.left} data-session={@meet.left_session}>
          <.lane box={@d.left_head} />
        </g>
        <g id="lane-right" data-party={@meet.right} data-session={@meet.right_session}>
          <.lane box={@d.right_head} />
        </g>
        <line
          class="lifeline"
          x1={@d.left_x}
          y1={@d.life_top}
          x2={@d.left_x}
          y2={@d.life_bot}
          stroke="#44403c"
          stroke-width="1.5"
        />
        <line
          class="lifeline"
          x1={@d.right_x}
          y1={@d.life_top}
          x2={@d.right_x}
          y2={@d.life_bot}
          stroke="#44403c"
          stroke-width="1.5"
        />
        <g
          :for={step <- @d.steps}
          id={"seq-#{step.index}"}
          class={["seq-row", step.kind == :terminal && "terminal", step.loop && "loop"]}
          data-kind={step.kind}
          data-from={step.from}
          data-to={step.to}
          data-label={step.label}
          data-branch={step.branch}
          data-loop={step.loop && "true"}
          data-arity={step.arity}
          data-evidence={step.evidence}
        >
          {text_at(step.number,
            class: "step-no",
            x: @d.number_x,
            y: step.number_y,
            fill: "#1c1917"
          )}
          <line
            :if={step.kind != :terminal}
            class="arrow"
            x1={step.x1}
            y1={step.y1}
            x2={step.x2}
            y2={step.y2}
            stroke="#44403c"
            stroke-width="1.5"
            marker-end="url(#seq-arrow)"
          />
          {text_at(step.arrow_label,
            class: "arrow-label",
            x: step.label_x,
            y: step.label_y,
            "text-anchor": "middle",
            code: true
          )}
          <rect
            :for={badge <- badge_list(step.badge)}
            class="evidence-pill"
            x={badge.x}
            y={badge.y}
            width={badge.w}
            height={badge.h}
            rx="8"
          />
          {text_at(badge_text(step.badge),
            class: "evidence-badge",
            x: step.badge_x,
            y: step.badge_y,
            fill: "#1c1917",
            "text-anchor": "middle",
            code: true
          )}
          {text_at(step.loop && "loop", class: "loop-note", x: step.loop_x, y: step.loop_y)}
          <polygon
            :if={step.choice}
            class="choice-diamond"
            points={step.choice.diamond}
            fill="#fafaf9"
            stroke="#44403c"
            stroke-width="1.5"
          />
          {text_at(step.choice && step.choice.text,
            class: "choice-note",
            x: step.choice && step.choice.note_x,
            y: step.choice && step.choice.note_y,
            "text-anchor": step.choice && step.choice.anchor
          )}
          <rect
            :for={mark <- step.marks}
            class="term-mark"
            x={mark.x}
            y={mark.y}
            width={mark.w}
            height={mark.h}
            fill="#44403c"
          />
          {text_at(step.term_label,
            class: "term-label",
            x: step.label_x,
            y: step.label_y,
            "text-anchor": "middle",
            code: true
          )}
        </g>
        <.lane box={@d.left_foot} />
        <.lane box={@d.right_foot} />
      </svg>
    </div>
    """
  end

  # Built outside HEEx so the glyph string has no template whitespace.
  defp text_at(nil, _attrs), do: nil
  defp text_at(false, _attrs), do: nil

  defp text_at(text, attrs) do
    {code, attrs} = Keyword.pop(attrs, :code, false)

    attrs =
      if code do
        Keyword.update(attrs, :class, "muro-code", &"#{&1} muro-code")
      else
        attrs
      end

    rendered =
      attrs
      |> Enum.reject(fn {_key, value} -> is_nil(value) end)
      |> Enum.map_join(" ", fn {key, value} -> ~s(#{key}="#{escape(value)}") end)

    inner =
      if code do
        MuroVisor.Code.highlight(to_string(text), tag: "tspan")
      else
        escape(text)
      end

    {:safe, ["<text ", rendered, ">", inner, "</text>"]}
  end

  defp escape(value) do
    value
    |> to_string()
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
  end

  attr :box, :map, required: true

  defp lane(assigns) do
    ~H"""
    <g class="lane-box">
      <rect
        x={@box.x}
        y={@box.y}
        width={@box.w}
        height={@box.h}
        fill="#fff"
        stroke="#44403c"
        stroke-width="1.25"
      />
      {text_at(@box.name,
        class: "lane-name",
        x: @box.cx,
        y: @box.name_y,
        "text-anchor": "middle",
        "font-weight": "700",
        code: true
      )}
      {text_at(@box.session,
        class: "lane-session",
        x: @box.cx,
        y: @box.session_y,
        "text-anchor": "middle",
        code: true
      )}
    </g>
    """
  end

  def rows(states, transitions, left, right)
      when is_list(states) and is_list(transitions) and is_binary(left) and is_binary(right) do
    by_id = Map.new(states, &{&1.id, &1})

    steps =
      transitions
      |> Enum.with_index()
      |> Enum.map(fn {trans, index} ->
        step(trans, Map.get(by_id, trans.from), left, right, index)
      end)

    steps ++ terminal_rows(states, length(steps))
  end

  defp step(trans, state, left, right, index) do
    text = label_text(Map.get(trans, :label))
    {actor, dir, kind, label, branch} = classify(Map.get(trans, :side, :both), state, text)
    {from_side, to_side} = ends(actor, dir)

    %{
      index: index,
      kind: kind,
      from: party(from_side, left, right),
      to: party(to_side, left, right),
      to_side: to_side,
      label: label,
      branch: branch,
      evidence: nil,
      arity: nil,
      loop: Map.get(trans, :from) == Map.get(trans, :to)
    }
  end

  defp classify(side, state, text) do
    {actor, head} = actor(side, state)

    cond do
      choice = choice_of(head, text) ->
        {label, branch} = choice
        {actor, choice_dir(head, text), :choice, label, branch}

      value = put_value(head) ->
        {actor, :out, :send, value, nil}

      get?(head) or cover?(head) ->
        {actor, :in, :send, payload(text), nil}

      true ->
        {actor, text_dir(text), text_kind(text), payload(text), text_branch(text)}
    end
  end

  defp actor(:left, %{left: left}), do: {:left, unwrap(left)}
  defp actor(:right, %{right: right}), do: {:right, unwrap(right)}

  defp actor(:both, %{left: left, right: right}) do
    left = unwrap(left)
    right = unwrap(right)

    cond do
      put?(left) or pick?(left) -> {:left, left}
      put?(right) or pick?(right) -> {:right, right}
      true -> {:left, left}
    end
  end

  defp actor(side, _state) when side in [:left, :right], do: {side, nil}
  defp actor(_side, _state), do: {:left, nil}

  defp ends(actor, :out), do: {actor, other(actor)}
  defp ends(actor, :in), do: {other(actor), actor}

  defp other(:left), do: :right
  defp other(:right), do: :left
  defp other(_side), do: :right

  defp party(:left, left, _right), do: left
  defp party(:right, _left, right), do: right
  defp party(_side, _left, _right), do: nil

  defp choice_dir(head, text) do
    if pick?(head) or String.contains?(text, "pick"), do: :out, else: :in
  end

  defp choice_of({:pick0, _}, _text), do: {"pick0", "0"}
  defp choice_of({:pick1, _}, _text), do: {"pick1", "1"}

  defp choice_of(_head, text) do
    cond do
      String.contains?(text, "pick0") -> {"pick0", "0"}
      String.contains?(text, "pick1") -> {"pick1", "1"}
      String.contains?(text, "cover0") -> {"cover0", "0"}
      String.contains?(text, "cover1") -> {"cover1", "1"}
      true -> nil
    end
  end

  defp text_dir(text) do
    case verb(text) do
      v when v in [:put, :pick0, :pick1] -> :out
      _ -> :in
    end
  end

  defp text_kind(text) do
    if text_branch(text), do: :choice, else: :send
  end

  defp text_branch(text) do
    cond do
      String.contains?(text, "pick0") or String.contains?(text, "cover0") -> "0"
      String.contains?(text, "pick1") or String.contains?(text, "cover1") -> "1"
      true -> nil
    end
  end

  defp verb(text) do
    cond do
      String.contains?(text, "pick0") -> :pick0
      String.contains?(text, "pick1") -> :pick1
      String.contains?(text, "cover0") -> :cover0
      String.contains?(text, "cover1") -> :cover1
      word?(text, "put") -> :put
      word?(text, "arm") -> :arm
      word?(text, "get") -> :get
      word?(text, "cover") -> :cover
      true -> :step
    end
  end

  defp word?(text, word), do: Regex.match?(~r/(^|\s)#{word}(\s|$)/, text)

  defp payload(text) do
    cond do
      match = Regex.run(~r/(?:^|\s)put\s+(.+)$/, text) -> hd(tl(match))
      match = Regex.run(~r/(?:^|\s)arm\s+(.+)$/, text) -> hd(tl(match))
      match = Regex.run(~r/(?:^|\s)get\s+(.+)$/, text) -> hd(tl(match))
      text != "" -> text
      true -> "step"
    end
  end

  defp put_value({:put, _, val, _}), do: shown(val)
  defp put_value(_other), do: nil

  defp shown(val) do
    case Muro.Session.show_value(val) do
      text when is_binary(text) and text != "" -> text
      _ -> nil
    end
  rescue
    FunctionClauseError -> nil
  end

  defp put?({:put, _, _, _}), do: true
  defp put?(_other), do: false

  defp pick?({:pick0, _}), do: true
  defp pick?({:pick1, _}), do: true
  defp pick?(_other), do: false

  defp get?({:get, _, _, _}), do: true
  defp get?({:iget, _, _, _}), do: true
  defp get?(_other), do: false

  defp cover?({:cover, _, _}), do: true
  defp cover?(_other), do: false

  defp terminal_rows(states, offset) do
    states
    |> Enum.filter(&halted?/1)
    |> Enum.with_index(offset)
    |> Enum.map(fn {state, index} ->
      %{
        index: index,
        kind: :terminal,
        from: nil,
        to: nil,
        to_side: nil,
        label: term_label(state),
        branch: nil,
        evidence: nil,
        arity: nil,
        loop: false
      }
    end)
  end

  @doc false
  def annotate(rows, proto) when is_list(rows) do
    {annotated, _proto} =
      Enum.map_reduce(rows, proto, fn row, proto ->
        case row.kind do
          :terminal ->
            {row, proto}

          _ ->
            {decorate(row, head(proto)), step_proto(proto, row)}
        end
      end)

    annotated
  end

  def annotate(rows, _proto), do: rows

  @doc false
  def diagram(meet) when is_map(meet) do
    rows = number_rows(meet.rows || [])
    left_w = box_w(meet.left, meet.left_session)
    right_w = box_w(meet.right, meet.right_session)
    left_x = @pad + @step_col + div(left_w, 2)
    right_x = left_x + @gap
    life_top = @pad + @box_h

    {steps, life_bot} =
      Enum.map_reduce(rows, life_top, fn row, y ->
        place_row(row, y, left_x, right_x, meet.left)
      end)

    width = right_x + div(right_w, 2) + @pad
    height = life_bot + @box_h + @pad

    %{
      width: width,
      height: height,
      left_x: left_x,
      right_x: right_x,
      life_top: life_top,
      life_bot: life_bot,
      number_x: @pad + 4,
      left_head: lane_box(meet.left, meet.left_session, left_x, left_w, @pad),
      right_head: lane_box(meet.right, meet.right_session, right_x, right_w, @pad),
      left_foot: lane_box(meet.left, meet.left_session, left_x, left_w, life_bot),
      right_foot: lane_box(meet.right, meet.right_session, right_x, right_w, life_bot),
      steps: steps
    }
  end

  defp decorate(%{kind: :choice} = row, proto) do
    case arm_count(proto) do
      n when is_integer(n) -> %{row | arity: n}
      _ -> row
    end
  end

  defp decorate(row, {:esend, name, expr, _}) do
    %{row | evidence: badge(row.label, name, expr)}
  end

  defp decorate(row, {:erecv, name, expr, _}) do
    %{row | evidence: badge(row.label, name, expr)}
  end

  defp decorate(row, _proto), do: row

  defp head(proto) do
    case proto do
      {:rec, _, body} -> head(body)
      other -> other
    end
  end

  defp step_proto(proto, row) do
    case head(proto) do
      {:esend, _, _, rest} -> rest
      {:erecv, _, _, rest} -> rest
      {:send, _, rest} -> rest
      {:recv, _, rest} -> rest
      {:dsend, _, _, rest} -> rest
      {:drecv, _, _, rest} -> rest
      {:choose, left, right} -> arm(left, right, row.branch)
      {:branch, left, right} -> arm(left, right, row.branch)
      {:isend, _, left, right} -> bit_arm(left, right, row.label)
      {:irecv, _, left, right} -> bit_arm(left, right, row.label)
      {:case, _, arms} = proto -> case_arm(arms, row.label) || proto
      other -> other
    end
  end

  defp arm(left, _right, "0"), do: left
  defp arm(_left, right, "1"), do: right
  defp arm(left, _right, _), do: left

  defp bit_arm(left, _right, "b0"), do: left
  defp bit_arm(_left, right, "b1"), do: right

  defp bit_arm(left, right, label) when is_binary(label) do
    cond do
      String.contains?(label, "b1") -> right
      String.contains?(label, "b0") -> left
      true -> left
    end
  end

  defp bit_arm(left, _right, _label), do: left

  defp case_arm(arms, label) when is_list(arms) and is_binary(label) do
    Enum.find_value(arms, fn {ctor, proto} ->
      if show_name(ctor) == label, do: proto
    end)
  end

  defp case_arm(_arms, _label), do: nil

  defp arm_count({:choose, _, _}), do: 2
  defp arm_count({:branch, _, _}), do: 2
  defp arm_count({:case, _, arms}) when is_list(arms), do: length(arms)
  defp arm_count(_other), do: nil

  defp badge(value, name, expr) do
    witness = if is_binary(value) and value != "", do: value, else: show_name(name)
    witness <> " ⊢ " <> show_name(name) <> " ≤ " <> show_expr(expr)
  end

  defp show_name(name) when is_atom(name), do: Atom.to_string(name)
  defp show_name(name) when is_binary(name), do: name
  defp show_name(name), do: to_string(name)

  defp show_expr({:var, name}), do: show_name(name)
  defp show_expr({:lit, n}) when is_integer(n), do: Integer.to_string(n)
  defp show_expr({:suc, expr}), do: "suc " <> show_expr(expr)
  defp show_expr(n) when is_integer(n), do: Integer.to_string(n)
  defp show_expr(name) when is_atom(name), do: Atom.to_string(name)
  defp show_expr(other), do: inspect(other)

  defp number_rows(rows) do
    {numbered, _} =
      Enum.map_reduce(rows, 1, fn row, n ->
        if row.kind == :terminal do
          {Map.put(row, :number, nil), n}
        else
          {Map.put(row, :number, n), n + 1}
        end
      end)

    numbered
  end

  defp place_row(row, y, left_x, right_x, left_name) do
    mid = div(left_x + right_x, 2)
    h = row_height(row)
    arrow_y = y + h - 16
    label_y = arrow_y - 12
    from_left = row.from == left_name
    {x1, x2} = if from_left, do: {left_x, right_x}, else: {right_x, left_x}
    shown = arrow_label(row)
    badge = badge_geom(row.evidence, mid, label_y, text_w(shown))

    step = %{
      index: row.index,
      kind: row.kind,
      from: row.from,
      to: row.to,
      label: row.label,
      branch: row.branch,
      loop: row.loop,
      evidence: row.evidence,
      arity: row.arity,
      number: row.number,
      number_y: arrow_y + 4,
      h: h,
      x1: x1,
      y1: arrow_y,
      x2: x2,
      y2: arrow_y,
      label_x: mid,
      label_y: label_y,
      arrow_label: if(row.kind == :terminal, do: nil, else: shown),
      badge: badge,
      badge_x: if(badge, do: badge.tx, else: mid),
      badge_y: if(badge, do: badge.ty, else: label_y - 16),
      loop_x: loop_x(mid, text_w(shown), badge),
      loop_y: label_y,
      choice: choice_mark(row, from_left, left_x, right_x, arrow_y),
      marks: if(row.kind == :terminal, do: term_marks(left_x, right_x, arrow_y), else: []),
      term_label: if(row.kind == :terminal, do: row.label, else: nil)
    }

    {step, y + h}
  end

  defp arrow_label(%{kind: :choice, branch: branch}) when is_binary(branch), do: branch
  defp arrow_label(%{label: label}), do: label

  defp badge_geom(text, mid, label_y, label_w) when is_binary(text) and text != "" do
    w = text_w(text) + 16
    h = 20
    x = mid + div(label_w, 2) + 14
    y = label_y - 16

    %{text: text, x: x, y: y, w: w, h: h, tx: x + div(w, 2), ty: y + 14}
  end

  defp badge_geom(_text, _mid, _label_y, _label_w), do: nil

  defp badge_list(nil), do: []
  defp badge_list(badge), do: [badge]

  defp badge_text(nil), do: nil
  defp badge_text(badge), do: badge.text

  defp loop_x(mid, label_w, nil), do: mid + div(label_w, 2) + 8
  defp loop_x(_mid, _label_w, badge), do: badge.x + badge.w + 8

  defp choice_mark(%{kind: :choice, branch: branch, arity: arity}, from_left, left_x, right_x, y)
       when is_binary(branch) and is_integer(arity) do
    x = if from_left, do: left_x, else: right_x

    %{
      text: "chooses branch #{branch} of #{arity}",
      diamond: diamond(x, y, 6),
      note_x: if(from_left, do: x + 14, else: x - 14),
      note_y: y - 14,
      anchor: if(from_left, do: "start", else: "end")
    }
  end

  defp choice_mark(_row, _from_left, _left_x, _right_x, _y), do: nil

  defp diamond(x, y, s) do
    "#{x},#{y - s} #{x + s},#{y} #{x},#{y + s} #{x - s},#{y}"
  end

  defp term_marks(left_x, right_x, y) do
    [mark(left_x, y), mark(right_x, y)]
  end

  defp mark(cx, cy) do
    %{x: cx - div(@mark, 2), y: cy - div(@mark, 2), w: @mark, h: @mark}
  end

  defp row_height(%{kind: :choice, arity: n}) when is_integer(n), do: 72
  defp row_height(%{kind: :terminal}), do: 40
  defp row_height(%{evidence: evidence}) when is_binary(evidence) and evidence != "", do: 58
  defp row_height(_row), do: 44

  defp lane_box(name, session, cx, w, y) do
    %{
      name: name,
      session: session,
      x: cx - div(w, 2),
      y: y,
      w: w,
      h: @box_h,
      cx: cx,
      name_y: y + 22,
      session_y: y + 40
    }
  end

  defp box_w(name, session) do
    max(text_w(name), text_w(session)) + 28
  end

  defp text_w(nil), do: @char
  defp text_w(text), do: max(String.length(to_string(text)), 1) * @char

  defp halted?(%{left: left, right: right}), do: term?(unwrap(left)) and term?(unwrap(right))
  defp halted?(_other), do: false

  defp term?(proc) when proc in [:done, :stop, :end], do: true
  defp term?(_other), do: false

  defp term_label(%{left: left, right: right}) do
    [unwrap(left), unwrap(right)]
    |> Enum.map(&term_word/1)
    |> Enum.uniq()
    |> Enum.join(" ")
  end

  defp term_word(:done), do: "done"
  defp term_word(:stop), do: "stop"
  defp term_word(:end), do: "end"
  defp term_word(_other), do: "end"

  defp unwrap({:rec, _, body}), do: unwrap(body)
  defp unwrap(other), do: other

  defp label_text(label) when is_list(label), do: Enum.join(label, " ")
  defp label_text(label) when is_binary(label), do: label
  defp label_text(nil), do: ""
  defp label_text(other), do: to_string(other)
end
