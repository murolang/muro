defmodule Muro.CLI.Text do
  @moduledoc false

  @width 80

  @doc "Join blocks with one blank line and a trailing newline."
  def page(blocks) when is_list(blocks) do
    blocks
    |> Enum.map(&String.trim_trailing(&1, "\n"))
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
    |> Kernel.<>("\n")
  end

  def section(title, body) when is_binary(title) and is_binary(body) do
    title <> "\n" <> String.trim_trailing(body, "\n")
  end

  def prose(text, indent \\ 0) when is_binary(text) and is_integer(indent) do
    wrap(text, indent)
  end

  @doc "Indent each line by four spaces. The lines are not rewrapped."
  def pre(lines) when is_list(lines) do
    Enum.map_join(lines, "\n", &("    " <> &1))
  end

  @doc """
  A synopsis on its own line, then a description wrapped under it.

  `synopsis` is one line or a list of lines. The description is one
  paragraph.
  """
  def stack(rows) when is_list(rows) do
    Enum.map_join(rows, "\n", fn {synopsis, description} ->
      lines = if is_list(synopsis), do: synopsis, else: [synopsis]
      head = Enum.map_join(lines, "\n", &("    " <> &1))
      head <> "\n" <> wrap(description, 8)
    end)
  end

  @doc "Copy-pasteable command, then a short comment."
  def examples(rows, gap \\ "\n") when is_list(rows) and is_binary(gap) do
    Enum.map_join(rows, gap, fn {command, comment} ->
      "    " <> command <> "\n" <> wrap(comment, 8)
    end)
  end

  def arguments(rows) when is_list(rows), do: stack(rows)

  @doc "Aligned key and value. Both columns are plain text."
  def kv(rows) when is_list(rows) do
    width =
      rows
      |> Enum.map(fn {key, _value} -> String.length(key) end)
      |> Enum.max(fn -> 0 end)

    Enum.map_join(rows, "\n", fn {key, value} ->
      "    " <> String.pad_trailing(key, width) <> "  " <> value
    end)
  end

  @doc """
  One option from the same list the command's parser accepts.

  `name` is the OptionParser key. `value` is the metavar, or nil for
  a boolean flag. `default` is the text after `Default:`. `doc` is
  what the flag does. `lines` are extra preformatted rows, used when
  a flag's values need a line each.
  """
  def options(opts) when is_list(opts) do
    Enum.map_join(opts, "\n\n", &option/1)
  end

  def option(opt) do
    flag = "--" <> (opt.name |> to_string() |> String.replace("_", "-"))
    value = Map.get(opt, :value)
    head = "    " <> flag <> if(is_binary(value) and value != "", do: " " <> value, else: "")
    default = "        Default: " <> ensure_period(to_string(opt.default))
    body = wrap(opt.doc, 8)
    extra = Map.get(opt, :lines, [])

    extra =
      if extra == [] do
        ""
      else
        "\n" <> Enum.map_join(extra, "\n", &("        " <> &1))
      end

    head <> "\n" <> default <> "\n" <> body <> extra
  end

  def exits(rows) when is_list(rows) do
    Enum.map_join(rows, "\n", fn {code, doc} ->
      hanging("    #{code}  ", doc)
    end)
  end

  def wrap(text, indent \\ 0) when is_binary(text) and is_integer(indent) do
    prefix = String.duplicate(" ", indent)
    width = @width - indent

    text
    |> String.trim()
    |> String.split(~r/\n\s*\n/, trim: true)
    |> Enum.map(fn paragraph ->
      paragraph
      |> words()
      |> lines(width)
      |> Enum.map_join("\n", &(prefix <> &1))
    end)
    |> Enum.join("\n\n")
  end

  @doc "Bold and color section headings and command names."
  def paint(text, false) when is_binary(text), do: text

  def paint(text, true) when is_binary(text) do
    text
    |> String.split("\n")
    |> Enum.map(&paint_line/1)
    |> Enum.join("\n")
  end

  @doc "True when stdout is a terminal and `NO_COLOR` is unset."
  def color?(tty? \\ nil) do
    tty? = if is_nil(tty?), do: stdout_tty?(), else: tty?
    tty? and is_nil(System.get_env("NO_COLOR"))
  end

  def stdout_tty? do
    match?({:ok, n} when is_integer(n) and n > 0, :io.columns(:standard_io))
  end

  defp hanging(prefix, doc) do
    width = @width - String.length(prefix)

    case wrap_lines(doc, width) do
      [] ->
        prefix

      [first | rest] ->
        pad = String.duplicate(" ", String.length(prefix))
        prefix <> first <> Enum.map_join(rest, "", &("\n" <> pad <> &1))
    end
  end

  defp wrap_lines(text, width) do
    text |> words() |> lines(width)
  end

  defp words(text) do
    text
    |> String.replace("\n", " ")
    |> String.split(~r/\s+/, trim: true)
  end

  defp lines([], _width), do: []
  defp lines(words, width), do: lines(words, width, [])

  defp lines([], _width, acc), do: Enum.reverse(acc)

  defp lines([word | rest], width, acc) do
    {line, rest} = take(rest, width, word)
    lines(rest, width, [line | acc])
  end

  defp take([word | rest] = all, width, line) do
    if String.length(line) + 1 + String.length(word) <= width do
      take(rest, width, line <> " " <> word)
    else
      {line, all}
    end
  end

  defp take([], _width, line), do: {line, []}

  defp ensure_period(text) do
    if String.ends_with?(text, "."), do: text, else: text <> "."
  end

  defp paint_line(line) do
    if heading?(line) do
      cyan_bold(line)
    else
      paint_invocation(line)
    end
  end

  defp heading?(line) do
    line =~ ~r/\A[A-Z][A-Z ]{2,}\z/
  end

  @invocation ~r/^(\s*)(muro)(\s+)(skills add|deps\.get|check|emit|gen|init|mutate)(?![\w-])(.*)$/
  @synopsis ~r/^(\s*)(skills add|deps\.get|check|emit|gen|init|mutate)(?![\w-])(.*)$/

  defp paint_invocation(line) do
    cond do
      match = Regex.run(@invocation, line) ->
        [_, space, muro, gap, command, rest] = match
        space <> green_bold(muro) <> gap <> green_bold(command) <> rest

      match = Regex.run(@synopsis, line) ->
        [_, space, command, rest] = match
        space <> green_bold(command) <> rest

      true ->
        line
    end
  end

  defp cyan_bold(text) do
    IO.ANSI.cyan() <> IO.ANSI.bright() <> text <> IO.ANSI.reset()
  end

  defp green_bold(text) do
    IO.ANSI.green() <> IO.ANSI.bright() <> text <> IO.ANSI.reset()
  end
end
