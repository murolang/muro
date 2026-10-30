defmodule Muro.Skills do
  @moduledoc """
  Write the agent block into `AGENTS.md`.

  The wording comes from `manual/for-agents.md` between
  `<!-- muro:begin -->` and `<!-- muro:end -->`, read at compile
  time. A marker counts only when it is the whole line, with an
  optional trailing carriage return. A mention inside a sentence
  is left alone. A rerun replaces the text between those markers.
  The prefix, the suffix, and both marker lines stay byte for
  byte, including a closing marker with no final newline. The new
  body uses the block's line ending. `CLAUDE.md` is updated only
  when it already exists.
  """

  @source Path.expand("../../manual/for-agents.md", __DIR__)
  @external_resource @source
  @begin "<!-- muro:begin -->"
  @close "<!-- muro:end -->"

  @template (
              text = File.read!(@source)

              case String.split(text, @begin <> "\n", parts: 2) do
                [_, rest] ->
                  case String.split(rest, @close, parts: 2) do
                    [body, _] ->
                      String.trim_trailing(body, "\n")

                    _other ->
                      raise "manual/for-agents.md is missing #{@close}"
                  end

                _other ->
                  raise "manual/for-agents.md is missing #{@begin}"
              end
            )

  @doc "The block written into an agent file, including the markers."
  def block(backend) do
    body =
      @template
      |> String.replace("{{commands}}", commands(backend))
      |> String.replace("{{example}}", example(backend))
      |> String.trim_trailing("\n")

    @begin <> "\n" <> body <> "\n" <> @close <> "\n"
  end

  @doc """
  Update `AGENTS.md` under `root`, creating it when it is missing.

  `{:ok, lines}` names each file written. `{:error, message}` names
  the file and the line when a marker is unbalanced. Nothing is
  written in that case.
  """
  def add(root) when is_binary(root) do
    root = Path.expand(root)

    with {:ok, backend} <- backend_for(root) do
      wrapped = block(backend)
      agents = Path.join(root, "AGENTS.md")
      claude = Path.join(root, "CLAUDE.md")
      agents_existed = File.regular?(agents)
      claude? = File.regular?(claude)
      agents_text = if agents_existed, do: File.read!(agents), else: ""
      claude_text = if claude?, do: File.read!(claude), else: nil

      with {:ok, agents_next} <- splice("AGENTS.md", agents_text, wrapped),
           {:ok, claude_next} <- splice_optional(claude?, "CLAUDE.md", claude_text, wrapped) do
        File.write!(agents, agents_next)
        if claude?, do: File.write!(claude, claude_next)

        lines =
          [
            if(agents_existed, do: "updated AGENTS.md", else: "created AGENTS.md")
          ] ++ if claude?, do: ["updated CLAUDE.md"], else: []

        {:ok, lines}
      end
    end
  end

  defp commands(nil) do
    """
    muro check
    muro emit path.muro
    muro gen
    muro gen --check
    """
    |> String.trim_trailing("\n")
  end

  defp commands(backend) do
    """
    muro check
    muro emit path.muro --backend #{backend}
    muro gen
    muro gen --check
    """
    |> String.trim_trailing("\n")
  end

  defp example(:c), do: "natsmuro"
  defp example(:rust), do: "natsmuro"
  defp example(:asm), do: "half_okmuro"
  defp example(:fsm), do: "meetmuro"
  defp example(_backend), do: "half_okmuro"

  defp backend_for(root) do
    case Muro.Manifest.load(root) do
      {:ok, %{backend: backend}} when not is_nil(backend) ->
        {:ok, backend}

      {:ok, _manifest} ->
        {:ok, Muro.Init.detect_backend(root)}

      {:error, "no manifest:" <> _rest} ->
        {:ok, Muro.Init.detect_backend(root)}

      {:error, message} ->
        {:error, message}
    end
  end

  defp splice_optional(false, _name, _text, _wrapped), do: {:ok, nil}

  defp splice_optional(true, name, text, wrapped), do: splice(name, text, wrapped)

  defp splice(name, text, wrapped) do
    case markers(text) do
      :append ->
        {:ok, append(text, wrapped)}

      {:replace, begin_line, end_line} ->
        {:ok, replace(text, wrapped, begin_line, end_line)}

      {:error, line} ->
        {:error, "#{name}:#{line}: unbalanced muro marker"}
    end
  end

  defp markers(text) do
    begins = marker_lines(text, @begin)
    ends = marker_lines(text, @close)

    cond do
      begins == [] and ends == [] ->
        :append

      begins == [] ->
        {:error, hd(ends)}

      ends == [] ->
        {:error, hd(begins)}

      length(begins) > 1 ->
        {:error, Enum.at(begins, 1)}

      length(ends) > 1 ->
        {:error, Enum.at(ends, 1)}

      hd(begins) > hd(ends) ->
        {:error, hd(ends)}

      true ->
        {:replace, hd(begins), hd(ends)}
    end
  end

  defp marker_lines(text, marker) do
    text
    |> raw_lines()
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {{line, _ending}, number} ->
      if line == marker, do: [number], else: []
    end)
  end

  # Rejoining the file would rewrite every line with one ending.
  # An LF prose line before a CRLF block would become CRLF, and a
  # closing marker at EOF with no newline would gain one. Keep the
  # prefix, both marker lines, and the suffix as they were read.
  # Only the body between the markers is new, in the opening
  # marker's line ending.
  defp replace(text, wrapped, begin_line, end_line) do
    lines = raw_lines(text)
    prefix = Enum.take(lines, begin_line - 1)
    opener = Enum.at(lines, begin_line - 1)
    closer = Enum.at(lines, end_line - 1)
    suffix = Enum.drop(lines, end_line)

    [
      render_lines(prefix),
      render_line(opener),
      replacement_body(wrapped, block_ending(opener)),
      render_line(closer),
      render_lines(suffix)
    ]
    |> IO.iodata_to_binary()
  end

  defp replacement_body(wrapped, ending) do
    wrapped
    |> String.trim_trailing("\n")
    |> String.split("\n")
    |> Enum.drop(1)
    |> Enum.drop(-1)
    |> Enum.map(&[&1, ending])
  end

  defp block_ending({_line, "\r\n"}), do: "\r\n"
  defp block_ending({_line, _ending}), do: "\n"

  defp render_lines(lines), do: Enum.map(lines, &render_line/1)
  defp render_line({line, ending}), do: [line, ending]

  defp raw_lines(text), do: raw_lines(text, [])

  defp raw_lines(<<>>, acc), do: Enum.reverse(acc)

  defp raw_lines(text, acc) do
    case :binary.match(text, ["\r\n", "\n"]) do
      {pos, len} ->
        line = binary_part(text, 0, pos)
        ending = binary_part(text, pos, len)
        rest = binary_part(text, pos + len, byte_size(text) - pos - len)
        raw_lines(rest, [{line, ending} | acc])

      :nomatch ->
        Enum.reverse([{text, ""} | acc])
    end
  end

  defp append("", wrapped), do: wrapped

  defp append(text, wrapped) do
    ending = line_ending(text)
    wrapped = transcode(wrapped, ending)

    if String.ends_with?(text, "\n"), do: text <> wrapped, else: text <> ending <> wrapped
  end

  defp line_ending(text) do
    if String.contains?(text, "\r\n"), do: "\r\n", else: "\n"
  end

  defp transcode(text, "\n"), do: text
  defp transcode(text, "\r\n"), do: String.replace(text, "\n", "\r\n")
end
