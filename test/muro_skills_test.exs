defmodule Muro.SkillsTest do
  use ExUnit.Case, async: false

  test "skills add creates AGENTS.md and leaves CLAUDE.md absent" do
    dir = tmp()
    assert {:ok, ["created AGENTS.md"]} = Muro.Skills.add(dir)
    refute File.exists?(Path.join(dir, "CLAUDE.md"))

    text = File.read!(Path.join(dir, "AGENTS.md"))
    assert String.starts_with?(text, "<!-- muro:begin -->\n")
    assert String.ends_with?(text, "<!-- muro:end -->\n")
    assert text =~ "Muro has two jobs: spec and evidence. `run` is what is emitted."
    assert text =~ "The wall: a spec never becomes evidence. Evidence never becomes a run."
    assert text =~ "muro check\n"
    assert text =~ "muro emit path.muro\n"
    refute text =~ "--backend"
    assert text =~ "muro gen\n"
    assert text =~ "muro gen --check\n"
    assert text =~ "Every binder is typed and every motive is written."
    assert text =~ "Generated files are not edited by hand."
    assert text =~ "manual/examples.md#half_okmuro"

    again = Muro.Skills.add(dir)
    assert again == {:ok, ["updated AGENTS.md"]}
    assert File.read!(Path.join(dir, "AGENTS.md")) == text
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
    assert {:ok, _} = Muro.Skills.add(dir)
    assert File.read!(path) == replaced
  end

  test "CLAUDE.md is updated only when it already exists" do
    dir = tmp()
    File.write!(Path.join(dir, "CLAUDE.md"), "notes\n")
    assert {:ok, lines} = Muro.Skills.add(dir)
    assert lines == ["created AGENTS.md", "updated CLAUDE.md"]
    assert File.read!(Path.join(dir, "CLAUDE.md")) =~ "<!-- muro:begin -->"
    assert File.read!(Path.join(dir, "CLAUDE.md")) =~ "notes\n"

    agents = File.read!(Path.join(dir, "AGENTS.md"))
    claude = File.read!(Path.join(dir, "CLAUDE.md"))
    assert {:ok, ["updated AGENTS.md", "updated CLAUDE.md"]} = Muro.Skills.add(dir)
    assert File.read!(Path.join(dir, "AGENTS.md")) == agents
    assert File.read!(Path.join(dir, "CLAUDE.md")) == claude
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
    assert {:ok, _} = Muro.Skills.add(dir)
    assert File.read!(path) == appended
  end

  test "unbalanced markers name the line and write nothing" do
    dir = tmp()
    agents = Path.join(dir, "AGENTS.md")
    File.write!(agents, "one\n<!-- muro:begin -->\nno end\n")
    assert {:error, message} = Muro.Skills.add(dir)
    assert message == "AGENTS.md:2: unbalanced muro marker"
    assert File.read!(agents) =~ "no end"

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
  end

  test "the hex package ships the agent manual the compiler reads" do
    files = Keyword.fetch!(Mix.Project.config()[:package], :files)
    assert "manual/for-agents.md" in files

    source = Path.expand("../../manual/for-agents.md", Path.join(File.cwd!(), "lib/muro"))
    assert File.regular?(source)
    assert File.read!(source) =~ "<!-- muro:begin -->"
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
    assert text =~ "manual/examples.md#natsmuro"

    File.write!(Path.join(dir, "mix.exs"), "defmodule X.MixProject do\nend\n")
    File.rm!(Path.join(dir, "muro.toml"))
    File.rm!(Path.join(dir, "AGENTS.md"))
    assert {:ok, _} = Muro.Skills.add(dir)
    elixir = File.read!(Path.join(dir, "AGENTS.md"))
    assert elixir =~ "muro emit path.muro --backend elixir\n"
    assert elixir =~ "manual/examples.md#half_okmuro"
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_skills_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
