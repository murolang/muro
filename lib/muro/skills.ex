defmodule Muro.Skills do
  @moduledoc """
  Write the agent block into `AGENTS.md`.

  The wording comes from `manual/for-agents.md` between
  `<!-- muro:begin -->` and `<!-- muro:end -->`, read at compile
  time. A rerun replaces the text between those markers and nothing
  else. `CLAUDE.md` is updated only when it already exists.
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

      {:replace, _begin_line, _end_line} ->
        {:ok, replace(text, wrapped)}

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
    |> String.split("\n")
    |> Enum.with_index(1)
    |> Enum.flat_map(fn {line, number} ->
      if line == marker, do: [number], else: []
    end)
  end

  defp replace(text, wrapped) do
    [before, rest] = String.split(text, @begin, parts: 2)
    [_old, after_] = String.split(rest, @close, parts: 2)
    after_ = String.replace_prefix(after_, "\n", "")
    before <> wrapped <> after_
  end

  defp append("", wrapped), do: wrapped

  defp append(text, wrapped) do
    if String.ends_with?(text, "\n"), do: text <> wrapped, else: text <> "\n" <> wrapped
  end
end
