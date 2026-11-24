defmodule Muro.Skills.Extract do
  @moduledoc false

  def marked(text, open, close) when is_binary(text) do
    case String.split(text, open <> "\n", parts: 2) do
      [_, rest] ->
        case String.split(rest, close, parts: 2) do
          [body, _] ->
            String.trim_trailing(body, "\n")

          _other ->
            raise "marked section is missing #{close}"
        end

      _other ->
        raise "marked section is missing #{open}"
    end
  end

  def skill(text, name) when is_binary(text) and is_binary(name) do
    marked(
      text,
      "<!-- muro-skill:#{name}:begin -->",
      "<!-- muro-skill:#{name}:end -->"
    )
  end
end

defmodule Muro.Skills do
  @moduledoc """
  Write the agent index into `AGENTS.md` and the skills under
  `.agents/skills/`.

  The index wording comes from `manual/for-agents.md` between
  `<!-- muro:begin -->` and `<!-- muro:end -->`, read at compile
  time. Each skill body is a marked section of a manual page
  (`<!-- muro-skill:NAME:begin -->` … `<!-- muro-skill:NAME:end -->`).
  A marker counts only when it is the whole line, with an
  optional trailing carriage return. A mention inside a sentence
  is left alone. A rerun replaces the text between those markers
  and overwrites the skill files. The prefix, the suffix, and both
  marker lines stay byte for byte, including a closing marker with
  no final newline. The new body uses the block's line ending.
  `CLAUDE.md` is updated only when it already exists. The command
  does not write `.cursor/skills` or `.claude/skills`.
  """

  @for_agents Path.expand("../../manual/for-agents.md", __DIR__)
  @gen_manual Path.expand("../../manual/gen.md", __DIR__)
  @synth_manual Path.expand("../../manual/synth.md", __DIR__)
  @half_ok Path.expand("../../examples/half_ok.muro", __DIR__)
  @nats Path.expand("../../examples/nats.muro", __DIR__)
  @meet Path.expand("../../examples/meet.muro", __DIR__)

  @external_resource @for_agents
  @external_resource @gen_manual
  @external_resource @synth_manual
  @external_resource @half_ok
  @external_resource @nats
  @external_resource @meet

  @begin "<!-- muro:begin -->"
  @close "<!-- muro:end -->"

  @backends ~w(elixir c rust zig asm otp js mbi fsm exunit pytest rust-test)

  @skill_order [:book, :check, :emit, :gen, :synth, :contracts]

  @skill_meta %{
    book: %{
      source: :for_agents,
      description:
        "Write and structure a Muro book: tags spec/evidence/run, typed binders, motives, prelude, holes, and axioms. Use when creating or editing .muro files."
    },
    check: %{
      source: :for_agents,
      description:
        "Check a Muro book, read checker errors, and fix common refusals. Use when mix muro.check or muro check fails, including out of fuel."
    },
    emit: %{
      source: :for_agents,
      description:
        "Emit a checked Muro book to elixir, c, rust, zig, asm, otp, js, mbi, fsm, exunit, pytest, or rust-test. Use when choosing a backend or an emit flag."
    },
    gen: %{
      source: :gen,
      description:
        "Commit generated modules from a Muro manifest, including version pins. Use when running muro gen, muro init, or editing muro.exs / muro.toml."
    },
    synth: %{
      source: :synth,
      description:
        "Synthesize, fill, or mutate a Muro book. The synthesized PredProg is itself the certified term; never treat the Finder's ranking as the certificate."
    },
    contracts: %{
      source: :for_agents,
      description:
        "External contracts, packages, host representations, and params in Muro. Use for fsm contracts, muro.lock, repr, or param libraries."
    }
  }

  @for_agents_text File.read!(@for_agents)
  @gen_text File.read!(@gen_manual)
  @synth_text File.read!(@synth_manual)

  @template Muro.Skills.Extract.marked(@for_agents_text, @begin, @close)

  @skill_bodies %{
    book: Muro.Skills.Extract.skill(@for_agents_text, "book"),
    check: Muro.Skills.Extract.skill(@for_agents_text, "check"),
    emit: Muro.Skills.Extract.skill(@for_agents_text, "emit"),
    gen: Muro.Skills.Extract.skill(@gen_text, "gen"),
    synth: Muro.Skills.Extract.skill(@synth_text, "synth"),
    contracts: Muro.Skills.Extract.skill(@for_agents_text, "contracts")
  }

  @example_bodies [
    {"half_ok.muro", File.read!(@half_ok)},
    {"nats.muro", File.read!(@nats)},
    {"meet.muro", File.read!(@meet)}
  ]

  @doc "Emit backends the installed skills must name."
  def backends, do: @backends

  @doc "Skill names installed under `.agents/skills/`."
  def skill_names, do: @skill_order

  @doc "The running Muro version written into the index and skills."
  def version do
    case Application.spec(:muro, :vsn) do
      vsn when is_list(vsn) -> List.to_string(vsn)
      other -> raise "could not read the muro version (#{inspect(other)})"
    end
  end

  @doc "The block written into an agent file, including the markers."
  def block(backend) do
    body =
      @template
      |> fill(backend)
      |> String.trim_trailing("\n")

    @begin <> "\n" <> body <> "\n" <> @close <> "\n"
  end

  @doc "A skill file, including YAML frontmatter."
  def skill(name, backend) when name in @skill_order do
    meta = Map.fetch!(@skill_meta, name)
    body = fill(Map.fetch!(@skill_bodies, name), backend)

    """
    ---
    name: #{yaml_double_quoted("muro-#{name}")}
    description: #{yaml_double_quoted(meta.description)}
    ---

    #{body}
    """
  end

  # Always a double-quoted YAML scalar, so a colon in the description
  # cannot be read as a mapping indicator.
  defp yaml_double_quoted(text) when is_binary(text) do
    [?", yaml_escape(text, []), ?"]
    |> IO.iodata_to_binary()
  end

  defp yaml_escape(<<>>, acc), do: Enum.reverse(acc)
  defp yaml_escape(<<?\\, rest::binary>>, acc), do: yaml_escape(rest, ["\\\\" | acc])
  defp yaml_escape(<<?", rest::binary>>, acc), do: yaml_escape(rest, ["\\\"" | acc])
  defp yaml_escape(<<?\n, rest::binary>>, acc), do: yaml_escape(rest, ["\\n" | acc])
  defp yaml_escape(<<?\r, rest::binary>>, acc), do: yaml_escape(rest, ["\\r" | acc])
  defp yaml_escape(<<?\t, rest::binary>>, acc), do: yaml_escape(rest, ["\\t" | acc])

  defp yaml_escape(<<c::utf8, rest::binary>>, acc) when c < 0x20 do
    yaml_escape(rest, ["\\u" <> yaml_hex4(c) | acc])
  end

  defp yaml_escape(<<c::utf8, rest::binary>>, acc) do
    yaml_escape(rest, [<<c::utf8>> | acc])
  end

  defp yaml_hex4(c) do
    c
    |> Integer.to_string(16)
    |> String.pad_leading(4, "0")
  end

  @doc """
  Paths written under `root`, relative to `root`, in stable order.
  The agent files are not included; only the skill tree is.
  """
  def skill_relpaths do
    skills =
      Enum.map(@skill_order, fn name ->
        Path.join([".agents", "skills", "muro-#{name}", "SKILL.md"])
      end)

    examples =
      Enum.map(@example_bodies, fn {name, _body} ->
        Path.join([".agents", "skills", "muro-book", "examples", name])
      end)

    skills ++ examples
  end

  @doc """
  Update `AGENTS.md` under `root`, creating it when it is missing,
  and write the skill files.

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
        skill_lines = write_skills(root, backend)

        lines =
          [
            if(agents_existed, do: "updated AGENTS.md", else: "created AGENTS.md")
          ] ++ if(claude?, do: ["updated CLAUDE.md"], else: []) ++ skill_lines

        {:ok, lines}
      end
    end
  end

  defp write_skills(root, backend) do
    Enum.map(@skill_order, fn name ->
      rel = Path.join([".agents", "skills", "muro-#{name}", "SKILL.md"])
      write_file(root, rel, skill(name, backend))
    end) ++
      Enum.map(@example_bodies, fn {name, body} ->
        rel = Path.join([".agents", "skills", "muro-book", "examples", name])
        write_file(root, rel, body)
      end)
  end

  defp write_file(root, rel, contents) do
    path = Path.join(root, rel)
    existed? = File.regular?(path)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, contents)
    if existed?, do: "updated #{rel}", else: "created #{rel}"
  end

  defp fill(text, backend) do
    text
    |> String.replace("{{commands}}", commands(backend))
    |> String.replace("{{example}}", example(backend))
    |> String.replace("{{version}}", version())
    |> String.replace("{{backends}}", Enum.join(@backends, ", "))
  end

  defp commands(nil) do
    """
    muro check
    muro check --fuel 20000 path.muro
    muro emit path.muro
    muro gen
    muro gen --check
    muro gen --skip-check
    muro synth path.muro
    muro fill path.muro --def name
    muro mutate path.muro
    muro deps.get
    """
    |> String.trim_trailing("\n")
  end

  defp commands(backend) do
    """
    muro check
    muro check --fuel 20000 path.muro
    muro emit path.muro --backend #{backend}
    muro gen
    muro gen --check
    muro gen --skip-check
    muro synth path.muro
    muro fill path.muro --def name
    muro mutate path.muro
    muro deps.get
    """
    |> String.trim_trailing("\n")
  end

  defp example(:c), do: "nats"
  defp example(:rust), do: "nats"
  defp example(:asm), do: "half_ok"
  defp example(:fsm), do: "meet"
  defp example(:otp), do: "meet"
  defp example(_backend), do: "half_ok"

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
