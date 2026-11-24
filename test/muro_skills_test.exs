defmodule Muro.SkillsTest do
  use ExUnit.Case, async: false

  test "skills add creates AGENTS.md and leaves CLAUDE.md absent" do
    dir = tmp()
    assert {:ok, lines} = Muro.Skills.add(dir)
    assert lines == created_lines(false, false)
    refute File.exists?(Path.join(dir, "CLAUDE.md"))
    refute File.exists?(Path.join(dir, ".cursor"))
    refute File.exists?(Path.join(dir, ".claude"))
    assert installed_relpaths(dir) == expected_tree([])

    text = File.read!(Path.join(dir, "AGENTS.md"))
    assert String.starts_with?(text, "<!-- muro:begin -->\n")
    assert String.ends_with?(text, "<!-- muro:end -->\n")
    assert byte_size(text) in 2000..4096
    assert text =~ "Muro has two jobs: spec and evidence. `run` is what is emitted."
    assert text =~ "The wall: a spec never becomes evidence. Evidence never becomes a run."
    assert text =~ "muro check\n"
    assert text =~ "muro emit path.muro\n"
    refute text =~ "muro emit path.muro --backend"
    assert text =~ "muro gen\n"
    assert text =~ "muro gen --check\n"
    assert text =~ "muro synth path.muro\n"
    assert text =~ "muro fill path.muro --def name\n"
    assert text =~ "muro mutate path.muro\n"
    assert text =~ "muro deps.get\n"
    assert text =~ "muro check --fuel 20000 path.muro\n"
    assert text =~ "Every binder is typed and every motive is written."
    assert text =~ "Generated files are not edited by hand."
    assert text =~ ".agents/skills/muro-book/examples/half_ok.muro"
    refute text =~ "manual/examples.md#"
    assert text =~ "The synthesized PredProg is itself the certified term."
    assert text =~ "It is not the Finder's ranking."
    assert text =~ "This project is pinned to Muro #{Mix.Project.config()[:version]}."

    first = snapshot(dir)
    again = Muro.Skills.add(dir)
    assert again == {:ok, updated_lines(false)}
    assert snapshot(dir) == first
  end

  test "an existing file is appended, then replaced between the markers" do
    dir = tmp()
    path = Path.join(dir, "AGENTS.md")
    File.write!(path, "Keep this.\n\nAnd this.")

    assert {:ok, _} = Muro.Skills.add(dir)
    text = File.read!(path)
    assert String.starts_with?(text, "Keep this.\n\nAnd this.\n<!-- muro:begin -->\n")

    File.write!(path, "before\n<!-- muro:begin -->\nold\n<!-- muro:end -->\nafter\n")
    assert {:ok, _} = Muro.Skills.add(dir)
    replaced = File.read!(path)
    assert String.starts_with?(replaced, "before\n<!-- muro:begin -->\n")
    assert String.ends_with?(replaced, "<!-- muro:end -->\nafter\n")
    refute replaced =~ "old\n"
    first = snapshot(dir)
    assert {:ok, _} = Muro.Skills.add(dir)
    assert snapshot(dir) == first
  end

  test "CLAUDE.md is updated only when it already exists" do
    dir = tmp()
    File.write!(Path.join(dir, "CLAUDE.md"), "notes\n")
    assert {:ok, lines} = Muro.Skills.add(dir)
    assert lines == created_lines(false, true)
    assert File.read!(Path.join(dir, "CLAUDE.md")) =~ "<!-- muro:begin -->"
    assert File.read!(Path.join(dir, "CLAUDE.md")) =~ "notes\n"
    refute File.exists?(Path.join(dir, ".cursor"))
    refute File.exists?(Path.join(dir, ".claude"))

    first = snapshot(dir)
    assert {:ok, updated_lines(true)} == Muro.Skills.add(dir)
    assert snapshot(dir) == first
  end

  test "an inline marker is prose, and CRLF markers stay whole lines" do
    dir = tmp()
    path = Path.join(dir, "AGENTS.md")

    File.write!(path, """
    See <!-- muro:begin --> in this sentence.
    <!-- muro:begin -->
    old instructions
    <!-- muro:end -->
    keep this
    """)

    assert {:ok, _} = Muro.Skills.add(dir)
    replaced = File.read!(path)
    assert String.starts_with?(replaced, "See <!-- muro:begin --> in this sentence.\n")
    assert replaced =~ "<!-- muro:begin -->\n"
    assert replaced =~ "<!-- muro:end -->\nkeep this\n"
    refute replaced =~ "old instructions"

    crlf =
      "notes\r\n<!-- muro:begin -->\r\nold\r\n<!-- muro:end -->\r\nkeep\r\n"

    File.write!(path, crlf)
    assert {:ok, _} = Muro.Skills.add(dir)
    updated = File.read!(path)
    assert String.starts_with?(updated, "notes\r\n<!-- muro:begin -->\r\n")
    assert updated =~ "<!-- muro:end -->\r\nkeep\r\n"
    refute updated =~ "old\r\n"
    refute String.replace(updated, "\r\n", "") =~ "\n"

    File.write!(path, "one\r\n<!-- muro:begin -->\r\nno end\r\n")
    assert {:error, "AGENTS.md:2: unbalanced muro marker"} = Muro.Skills.add(dir)
    assert File.read!(path) == "one\r\n<!-- muro:begin -->\r\nno end\r\n"

    File.write!(path, "Keep\r\nthis\r\n")
    assert {:ok, _} = Muro.Skills.add(dir)
    appended = File.read!(path)
    assert String.starts_with?(appended, "Keep\r\nthis\r\n<!-- muro:begin -->\r\n")
    refute String.replace(appended, "\r\n", "") =~ "\n"
    first = snapshot(dir)
    assert {:ok, _} = Muro.Skills.add(dir)
    assert snapshot(dir) == first
  end

  test "mixed line endings keep the bytes outside the block" do
    dir = tmp()
    path = Path.join(dir, "AGENTS.md")

    File.write!(
      path,
      "Keep this line.\n<!-- muro:begin -->\r\nold\r\n<!-- muro:end -->\r\nAfter.\n"
    )

    assert {:ok, _} = Muro.Skills.add(dir)
    updated = File.read!(path)
    assert String.starts_with?(updated, "Keep this line.\n<!-- muro:begin -->\r\n")
    assert String.ends_with?(updated, "<!-- muro:end -->\r\nAfter.\n")
    assert updated =~ "muro check\r\n"
    refute updated =~ "old\r\n"
    refute updated =~ "Keep this line.\r\n"
    refute updated =~ "After.\r\n"

    first = snapshot(dir)
    assert {:ok, _} = Muro.Skills.add(dir)
    assert snapshot(dir) == first
  end

  test "a closing marker at EOF without a newline is preserved" do
    dir = tmp()
    path = Path.join(dir, "AGENTS.md")
    File.write!(path, "<!-- muro:begin -->\nold\n<!-- muro:end -->")

    assert {:ok, _} = Muro.Skills.add(dir)
    updated = File.read!(path)
    assert String.starts_with?(updated, "<!-- muro:begin -->\n")
    assert String.ends_with?(updated, "\n<!-- muro:end -->")
    refute String.ends_with?(updated, "<!-- muro:end -->\n")
    refute updated =~ "old\n"

    first = snapshot(dir)
    assert {:ok, _} = Muro.Skills.add(dir)
    assert snapshot(dir) == first
  end

  test "unbalanced markers name the line and write nothing" do
    dir = tmp()
    agents = Path.join(dir, "AGENTS.md")
    File.write!(agents, "one\n<!-- muro:begin -->\nno end\n")
    assert {:error, message} = Muro.Skills.add(dir)
    assert message == "AGENTS.md:2: unbalanced muro marker"
    assert File.read!(agents) =~ "no end"
    refute File.exists?(Path.join(dir, ".agents"))

    File.write!(agents, "<!-- muro:end -->\n")
    assert {:error, "AGENTS.md:1: unbalanced muro marker"} = Muro.Skills.add(dir)

    File.write!(agents, """
    <!-- muro:begin -->
    a
    <!-- muro:end -->
    <!-- muro:begin -->
    b
    <!-- muro:end -->
    """)

    assert {:error, "AGENTS.md:4: unbalanced muro marker"} = Muro.Skills.add(dir)

    File.write!(Path.join(dir, "CLAUDE.md"), "<!-- muro:begin -->\n")
    File.write!(agents, "")
    assert {:error, "CLAUDE.md:1: unbalanced muro marker"} = Muro.Skills.add(dir)
    assert File.read!(agents) == ""
    refute File.exists?(Path.join(dir, ".agents"))
  end

  test "the hex package ships the manuals and examples the compiler reads" do
    files = Keyword.fetch!(Mix.Project.config()[:package], :files)
    assert "manual/for-agents.md" in files
    assert "manual/gen.md" in files
    assert "manual/synth.md" in files
    assert "examples/half_ok.muro" in files
    assert "examples/nats.muro" in files
    assert "examples/meet.muro" in files

    source = Path.expand("../../manual/for-agents.md", Path.join(File.cwd!(), "lib/muro"))
    assert File.regular?(source)
    assert File.read!(source) =~ "<!-- muro:begin -->"
    assert File.read!(source) =~ "<!-- muro-skill:book:begin -->"
    assert Muro.Skills.block(nil) =~ "<!-- muro:begin -->"
  end

  test "the commands follow the manifest backend" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "#{version}"
    backend = "rust"
    modules = []
    """)

    assert {:ok, _} = Muro.Skills.add(dir)
    text = File.read!(Path.join(dir, "AGENTS.md"))
    assert text =~ "muro emit path.muro --backend rust\n"
    assert text =~ ".agents/skills/muro-book/examples/nats.muro"

    File.write!(Path.join(dir, "mix.exs"), "defmodule X.MixProject do\nend\n")
    File.rm!(Path.join(dir, "muro.toml"))
    File.rm!(Path.join(dir, "AGENTS.md"))
    assert {:ok, _} = Muro.Skills.add(dir)
    elixir = File.read!(Path.join(dir, "AGENTS.md"))
    assert elixir =~ "muro emit path.muro --backend elixir\n"
    assert elixir =~ ".agents/skills/muro-book/examples/half_ok.muro"
  end

  test "installed skills name every backend, synth rules, and the mix.exs version" do
    dir = tmp()
    assert {:ok, _} = Muro.Skills.add(dir)
    text = installed_text(dir)
    version = Mix.Project.config()[:version]
    assert version == Mix.Tasks.Muro.version()

    for backend <- Muro.Skills.backends() do
      assert text =~ backend, "installed skills do not mention backend #{backend}"
    end

    assert text =~ "muro synth"
    assert text =~ "muro fill"
    assert text =~ "muro mutate"
    assert text =~ "deps.get"
    assert text =~ "--fuel"
    assert text =~ version

    synth = File.read!(Path.join(dir, ".agents/skills/muro-synth/SKILL.md"))
    assert synth =~ "name: muro-synth"
    assert synth =~ "The synthesized PredProg is itself the certified term."
    assert synth =~ "It is not the Finder's ranking."

    for {name, source} <- [
          {"half_ok.muro", "examples/half_ok.muro"},
          {"nats.muro", "examples/nats.muro"},
          {"meet.muro", "examples/meet.muro"}
        ] do
      installed = File.read!(Path.join(dir, ".agents/skills/muro-book/examples/#{name}"))
      assert installed == File.read!(source)
    end
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_skills_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp created_lines(agents_existed?, claude?) do
    agents = if agents_existed?, do: "updated AGENTS.md", else: "created AGENTS.md"
    claude = if claude?, do: ["updated CLAUDE.md"], else: []
    [agents] ++ claude ++ Enum.map(Muro.Skills.skill_relpaths(), &"created #{&1}")
  end

  defp updated_lines(claude?) do
    claude = if claude?, do: ["updated CLAUDE.md"], else: []
    ["updated AGENTS.md"] ++ claude ++ Enum.map(Muro.Skills.skill_relpaths(), &"updated #{&1}")
  end

  defp expected_tree(extra) do
    Enum.sort(["AGENTS.md" | extra ++ Muro.Skills.skill_relpaths()])
  end

  defp installed_relpaths(dir) do
    dir
    |> Path.join("**/*")
    |> Path.wildcard(match_dot: true)
    |> Enum.filter(&File.regular?/1)
    |> Enum.map(&Path.relative_to(&1, dir))
    |> Enum.sort()
  end

  defp installed_text(dir) do
    (["AGENTS.md"] ++ Muro.Skills.skill_relpaths())
    |> Enum.map(&File.read!(Path.join(dir, &1)))
    |> Enum.join("\n")
  end

  defp snapshot(dir) do
    Map.new(installed_relpaths(dir), fn rel ->
      {rel, File.read!(Path.join(dir, rel))}
    end)
  end
end
