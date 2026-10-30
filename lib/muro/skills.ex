defmodule Muro.Skills do
  @moduledoc """
  Write the agent block into `AGENTS.md`.

  The wording comes from `manual/for-agents.md` between
  `<!-- muro:begin -->` and `<!-- muro:end -->`, read at compile
  time. A marker counts only when it is the whole line, with an
  optional trailing carriage return. A mention inside a sentence
  is left alone. A rerun replaces the text between those markers
  and nothing else, and keeps the file's line endings. `CLAUDE.md`
  is updated only when it already exists.
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
    {lines, _trailing?} = logical_lines(text)

    lines
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {line, number} ->
      if line == marker, do: [number], else: []
    end)
  end

  defp replace(text, wrapped, begin_line, end_line) do
    ending = line_ending(text)
    {lines, trailing?} = logical_lines(text)
    prefix = Enum.take(lines, begin_line - 1)
    suffix = Enum.drop(lines, end_line)

    block_lines =
      wrapped
      |> String.trim_trailing("\n")
      |> String.split("\n")

    join_lines(prefix ++ block_lines ++ suffix, ending, trailing? or suffix == [])
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

  defp logical_lines(text) do
    trailing? = String.ends_with?(text, "\n")

    lines =
      text
      |> String.split("\n")
      |> Enum.map(&String.trim_trailing(&1, "\r"))

    lines =
      if trailing? and lines != [] and List.last(lines) == "" do
        Enum.drop(lines, -1)
      else
        lines
      end

    {lines, trailing?}
  end

  defp join_lines(lines, ending, trailing?) do
    body = Enum.join(lines, ending)
    if trailing?, do: body <> ending, else: body
  end
end
