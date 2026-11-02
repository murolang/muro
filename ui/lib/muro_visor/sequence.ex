defmodule MuroVisor.Sequence do
  @moduledoc false

  # One row per transition of the configuration graph the checker
  # recorded, then a terminal row for a halted state. The process head
  # in that state says who sends. This does not walk the protocol.

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
        loop: false
      }
    end)
  end

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
