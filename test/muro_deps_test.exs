defmodule Muro.DepsTest.Git do
  @moduledoc false

  defmacro git_test(name, do: body) do
    extra =
      if is_nil(System.find_executable("git")) do
        quote do: @tag(skip: "git is not on PATH")
      else
        quote do: @tag(git: true)
      end

    quote do
      @tag :git
      unquote(extra)

      test unquote(name) do
        unquote(body)
      end
    end
  end
end

defmodule Muro.DepsTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO
  import Muro.DepsTest.Git

  @wire "def wire : run Nat := 0\n"
  @wire2 "def wire : run Nat := suc 0\n"
  @banner "# muro.lock: written by mix muro.deps.get. Do not edit."

  test "the lock printer is stable and the reader refuses code" do
    sha = String.duplicate("ab", 32)
    other = String.duplicate("cd", 32)
    git_sha = String.duplicate("a", 40)
    tarball = String.duplicate("ef", 32)

    packages = %{
      "pricing" => %{
        files: %{"rules.muro" => sha},
        resolved: {:hex, "2.1.0", tarball},
        source: {:hex, "pricing_rules", "~> 2.0"},
        version: "2.1.0"
      },
      "shared_wire" => %{
        files: %{"sub/wire.muro" => other, "wire.muro" => sha},
        resolved: {:git, git_sha},
        source: {:git, "https://github.com/acme/shared-wire", [tag: "v1.2.0", root: "priv/muro"]},
        version: "1.2.0"
      }
    }

    expected = """
    #{@banner}
    %{
      "pricing" => %{
        files: %{
          "rules.muro" => "#{sha}"
        },
        resolved: {:hex, "2.1.0", "#{tarball}"},
        source: {:hex, "pricing_rules", "~> 2.0"},
        version: "2.1.0"
      },
      "shared_wire" => %{
        files: %{
          "sub/wire.muro" => "#{other}",
          "wire.muro" => "#{sha}"
        },
        resolved: {:git, "#{git_sha}"},
        source: {:git, "https://github.com/acme/shared-wire", [tag: "v1.2.0", root: "priv/muro"]},
        version: "1.2.0"
      }
    }
    """

    assert Muro.Lock.encode(packages) == expected
    assert Muro.Lock.encode(packages) == Muro.Lock.encode(packages)
    assert {:ok, decoded} = Muro.Lock.decode(expected)
    assert decoded == packages

    weird = "caf\u00e9-\#{x.muro"
    escaped = %{"shared" => %{packages["shared_wire"] | files: %{weird => sha}}}
    encoded = Muro.Lock.encode(escaped)
    assert encoded =~ "\\u{E9}"
    assert encoded =~ "\\\#{"
    assert {:ok, round} = Muro.Lock.decode(encoded)
    assert round["shared"].files[weird] == sha

    sentinel = Path.join(tmp_dir(), "still-here")
    File.write!(sentinel, "ok")

    assert {:error, message} = Muro.Lock.decode(@banner <> "\nFile.rm_rf!(\"/\")\n")
    assert message =~ "muro.lock"
    assert message =~ "mix muro.deps.get"
    assert File.read!(sentinel) == "ok"

    assert {:error, message} = Muro.Lock.decode(@banner <> "\n%{ \"Nope\" => 1 }\n")
    assert message =~ "muro.lock"
    assert {:error, message} = Muro.Lock.decode(@banner <> "\n[]\n")
    assert message =~ "muro.lock"
    assert {:error, message} = Muro.Lock.decode("not a lock\n")
    assert message =~ "muro.lock"
  end

  test "version labels drop one leading v and shorten a commit ref" do
    sha = String.duplicate("a", 40)
    short = "aaaaaaa"
    assert Muro.Deps.Git.version_label(%{pin: {:tag, "v1.2.0"}}, sha) == "1.2.0"
    assert Muro.Deps.Git.version_label(%{pin: {:tag, "vlatest"}}, sha) == "vlatest"
    assert Muro.Deps.Git.version_label(%{pin: {:tag, "latest"}}, sha) == "latest"
    assert Muro.Deps.Git.version_label(%{pin: {:ref, "topic"}}, sha) == "topic@" <> short
    assert Muro.Deps.Git.version_label(%{pin: {:ref, sha}}, sha) == short
    assert Muro.Deps.Git.version_label(%{pin: {:ref, short}}, sha) == short
  end

  test "a missing git executable names PATH and says nothing was written" do
    assert Muro.Deps.Git.fetch(%{name: "shared"}, nil) ==
             {:error, "git is not on PATH; muro.lock and muro_deps/ are unchanged"}
  end

  test "mix muro.deps.get rejects arguments and options" do
    assert_raise Mix.Error, ~r/usage: mix muro.deps.get/, fn ->
      Mix.Tasks.Muro.Deps.Get.run(["--nope"])
    end

    assert_raise Mix.Error, ~r/usage: mix muro.deps.get/, fn ->
      Mix.Tasks.Muro.Deps.Get.run(["shared"])
    end
  end

  test "editing a locked file fails the check until the bytes are restored" do
    dir = tmp_dir()
    write_locked(dir, ["shared"], %{"muro_deps/shared/wire.muro" => @wire})

    book =
      write_file(dir, "book.muro", "import \"pkg:shared/wire.muro\"\ndef use : run Nat := wire\n")

    hash = Muro.Hash.sha256(@wire)

    assert Muro.check_file(book) == :ok
    {:ok, [line]} = Muro.conforms(book)

    assert line ==
             "conforms to shared 1.0.0 (sha256 #{Muro.Hash.files([{"shared/wire.muro", @wire}])})"

    File.write!(Path.join(dir, "muro_deps/shared/wire.muro"), @wire <> "-- edited\n")

    assert {:error, message} = Muro.check_file(book)

    assert message =~
             "muro_deps/shared/wire.muro changed since muro.lock (expected sha256 #{hash})"

    assert message =~ "found sha256"
    assert message =~ "run mix muro.deps.get to fetch it again"
    assert {:error, ^message} = Muro.emit_file(book, Muro.DepsHandEdit)

    out =
      capture_io(fn ->
        assert_raise Mix.Error, ~r/changed since muro.lock \(expected sha256 #{hash}\)/, fn ->
          Mix.Tasks.Muro.Check.run([book])
        end
      end)

    assert out =~ "Muro v#{Mix.Tasks.Muro.version()}\n"

    File.write!(Path.join(dir, "muro_deps/shared/wire.muro"), @wire)
    assert Muro.check_file(book) == :ok

    ok =
      capture_io(fn ->
        assert Mix.Tasks.Muro.Check.run([book]) == :ok
      end)

    assert ok ==
             "Muro v#{Mix.Tasks.Muro.version()}\nAll terms check. Evidence never becomes a run.\n#{line}\n"
  end

  test "a file the book does not import does not change the conforms line" do
    dir = tmp_dir()
    extra = "def extra : run Nat := 0\n"

    write_locked(dir, ["shared"], %{
      "muro_deps/shared/wire.muro" => @wire,
      "muro_deps/shared/extra.muro" => extra
    })

    book =
      write_file(dir, "book.muro", "import \"pkg:shared/wire.muro\"\ndef use : run Nat := wire\n")

    {:ok, [line]} = Muro.conforms(book)

    changed = extra <> "-- touch\n"
    File.write!(Path.join(dir, "muro_deps/shared/extra.muro"), changed)

    relock(dir, %{"muro_deps/shared/wire.muro" => @wire, "muro_deps/shared/extra.muro" => changed})

    assert Muro.conforms(book) == {:ok, [line]}

    File.write!(Path.join(dir, "muro_deps/shared/wire.muro"), @wire2)

    relock(dir, %{
      "muro_deps/shared/wire.muro" => @wire2,
      "muro_deps/shared/extra.muro" => changed
    })

    assert {:ok, [other]} = Muro.conforms(book)
    assert other != line
    assert other =~ "conforms to shared 1.0.0 (sha256 "
  end

  test "param works across a package boundary once per importing book" do
    dir = tmp_dir()

    lib = """
    param step : run Π (+ s : Nat) → Nat
    def once : run Nat := step 0
    """

    write_locked(dir, ["shared"], %{"muro_deps/shared/lib.muro" => lib})

    suc = """
    import "pkg:shared/lib.muro"
    def step : run Π (+ s : Nat) → Nat := λ (+ s : Nat) → suc s
    def got : run Nat := once
    """

    same = """
    import "pkg:shared/lib.muro"
    def step : run Π (+ s : Nat) → Nat := λ (+ s : Nat) → s
    def got : run Nat := once
    """

    suc_book = write_file(dir, "suc.muro", suc)
    same_book = write_file(dir, "same.muro", same)
    assert Muro.check_file(suc_book) == :ok
    assert Muro.check_file(same_book) == :ok

    assert {:ok, suc_src} = Muro.emit_file(suc_book, Muro.DepsParamSuc)
    assert {:ok, same_src} = Muro.emit_file(same_book, Muro.DepsParamSame)
    assert suc_src =~ "def once do"
    assert suc_src =~ "def step"
    Code.eval_string(suc_src)
    Code.eval_string(same_src)
    assert apply(Muro.DepsParamSuc, :got, []) == {:suc, 0}
    assert apply(Muro.DepsParamSame, :got, []) == 0

    bare = write_file(dir, "bare.muro", "import \"pkg:shared/lib.muro\"\n")
    assert {:error, message} = Muro.check_file(bare)
    assert message =~ "muro_deps/shared/lib.muro"
    assert message =~ "param step is supplied by a file that imports this one"
    assert message =~ "in package shared"

    wrong =
      write_file(dir, "wrong.muro", """
      import "pkg:shared/lib.muro"
      def step : spec Π (+ s : Nat) → Nat := λ (+ s : Nat) → s
      def got : run Nat := once
      """)

    assert {:error, message} = Muro.check_file(wrong)
    assert message =~ "step is spec; the param it supplies is run"
    assert message =~ "muro_deps/shared/lib.muro"
    assert message =~ "in package shared"
  end

  test "diamonds load one package path, and two packages clash on the same name" do
    dir = tmp_dir()
    common = "def c : run Nat := 0\n"
    left = "import \"pkg:common/c.muro\"\ndef a : run Nat := c\n"
    right = "import \"pkg:common/c.muro\"\ndef b : run Nat := suc c\n"

    write_locked(dir, ["common", "left", "right"], %{
      "muro_deps/common/c.muro" => common,
      "muro_deps/left/a.muro" => left,
      "muro_deps/right/b.muro" => right
    })

    book =
      write_file(dir, "book.muro", """
      import "pkg:left/a.muro"
      import "pkg:right/b.muro"
      def top : run Nat := b
      """)

    assert Muro.check_file(book) == :ok
    assert {:ok, src} = Muro.emit_file(book, Muro.DepsDiamond)
    assert length(Regex.scan(~r/^  def c do$/m, src)) == 1

    use = "import \"c.muro\"\ndef use : run Nat := c\n"

    write_locked(dir, ["shared"], %{
      "muro_deps/shared/c.muro" => common,
      "muro_deps/shared/use.muro" => use
    })

    both =
      write_file(dir, "both.muro", """
      import "pkg:shared/c.muro"
      import "pkg:shared/use.muro"
      def top : run Nat := use
      """)

    assert Muro.check_file(both) == :ok
    assert {:ok, src} = Muro.emit_file(both, Muro.DepsDiamondRel)
    assert length(Regex.scan(~r/^  def c do$/m, src)) == 1

    own = "def c : run Nat := suc 0\n"

    write_locked(dir, ["alpha", "beta"], %{
      "muro_deps/alpha/c.muro" => common,
      "muro_deps/beta/c.muro" => own
    })

    clash =
      write_file(dir, "clash.muro", """
      import "pkg:alpha/c.muro"
      import "pkg:beta/c.muro"
      """)

    assert {:error, message} = Muro.check_file(clash)
    assert message =~ "duplicate name c"
    assert message =~ "muro_deps/alpha/c.muro"
    assert message =~ "muro_deps/beta/c.muro"
  end

  test "package imports name the package, the file, and the lock problem" do
    dir = tmp_dir()
    write_locked(dir, ["shared"], %{"muro_deps/shared/wire.muro" => @wire})

    book =
      write_file(dir, "book.muro", "import \"pkg:shared/wire.muro\"\ndef use : run Nat := wire\n")

    File.rm!(Path.join(dir, "muro.lock"))
    assert {:error, message} = Muro.check_file(book)
    assert message =~ "no muro.lock for package shared (muro_deps/shared/wire.muro)"
    assert message =~ "mix muro.deps.get"

    File.write!(Path.join(dir, "muro.lock"), Muro.Lock.encode(%{}))
    assert {:error, message} = Muro.check_file(book)
    assert message =~ "package shared (muro_deps/shared/wire.muro) is not in muro.lock"

    write_locked(dir, ["shared"], %{"muro_deps/shared/other.muro" => @wire})
    write_file(dir, "muro_deps/shared/wire.muro", @wire)
    assert {:error, message} = Muro.check_file(book)
    assert message =~ "muro_deps/shared/wire.muro is not in muro.lock"

    write_locked(dir, ["shared"], %{"muro_deps/shared/wire.muro" => @wire})
    File.rm!(Path.join(dir, "muro_deps/shared/wire.muro"))
    assert {:error, message} = Muro.check_file(book)
    assert message =~ "muro_deps/shared/wire.muro is missing"
    assert message =~ "mix muro.deps.get"

    write_file(dir, "muro_deps/shared/wire.muro", @wire)
    File.write!(Path.join(dir, "muro.exs"), manifest(["shared"], "v9.9.9"))
    assert {:error, message} = Muro.check_file(book)
    assert message =~ "muro.lock is out of date for shared:"
    assert message =~ "manifest says"
    assert message =~ "lock has"
    assert message =~ "mix muro.deps.get"

    unknown = write_file(dir, "unknown.muro", "import \"pkg:missing/wire.muro\"\n")
    assert {:error, message} = Muro.check_file(unknown)
    assert message =~ "package missing is not in muro_deps: (manifest muro.exs)"

    Enum.each(
      ["pkg:", "pkg:x", "pkg:x/../y.muro", "pkg:x/y.txt", "pkg:/abs.muro", "pkg:x//y.muro"],
      fn path ->
        bad = write_file(dir, "bad-#{:erlang.phash2(path)}.muro", "import \"#{path}\"\n")
        assert {:error, message} = Muro.check_file(bad)
        assert message =~ "bad package import \"#{path}\""
      end
    )

    lone = Path.join(tmp_dir(), "lone.muro")
    File.write!(lone, "import \"pkg:shared/wire.muro\"\n")
    assert {:error, message} = Muro.check_file(lone)
    assert message =~ "no manifest found"
    assert message =~ "muro.exs"

    escape = "import \"../outside.muro\"\ndef e : run Nat := 0\n"
    write_locked(dir, ["shared"], %{"muro_deps/shared/escape.muro" => escape})

    via =
      write_file(dir, "via.muro", "import \"pkg:shared/escape.muro\"\ndef use : run Nat := e\n")

    assert {:error, message} = Muro.check_file(via)
    assert message =~ "leaves the package"
    assert message =~ "muro_deps/shared/escape.muro"
    assert message =~ "outside.muro"

    nested = "import \"pkg:other/o.muro\"\ndef use : run Nat := o\n"
    write_locked(dir, ["shared"], %{"muro_deps/shared/nested.muro" => nested})

    nest_book =
      write_file(
        dir,
        "nest.muro",
        "import \"pkg:shared/nested.muro\"\ndef top : run Nat := use\n"
      )

    assert {:error, message} = Muro.check_file(nest_book)
    assert message =~ "package other is not in muro_deps:"
    assert message =~ "muro_deps/shared/nested.muro"
    assert message =~ "in package shared"

    parse = "!!!\n"
    write_locked(dir, ["shared"], %{"muro_deps/shared/bad.muro" => parse})
    parsed = write_file(dir, "parsed.muro", "import \"pkg:shared/bad.muro\"\n")
    assert {:error, message} = Muro.check_file(parsed)
    assert message =~ "in package shared"
    assert message =~ ~r/muro_deps\/shared\/bad\.muro:\d+:\d+:/

    broken = "def bad : run Nat := suc\n"
    write_locked(dir, ["shared"], %{"muro_deps/shared/broken.muro" => broken})

    checked =
      write_file(
        dir,
        "checked.muro",
        "import \"pkg:shared/broken.muro\"\ndef use : run Nat := bad\n"
      )

    assert {:error, message} = Muro.check_file(checked)
    assert message =~ "in package shared"
    assert message =~ ~r/muro_deps\/shared\/broken\.muro:\d+:\d+:/
  end

  git_test "two projects share a lock and a conforms line until one refetches" do
    repo = init_repo(%{"wire.muro" => @wire})
    git!(repo, ["tag", "v1.0.0"])
    url = file_url(repo)

    dir_a = tmp_dir()
    dir_b = tmp_dir()
    write_git_manifest(dir_a, "shared_wire", url, tag: "v1.0.0")
    write_git_manifest(dir_b, "shared_wire", url, tag: "v1.0.0")

    book = "import \"pkg:shared_wire/wire.muro\"\ndef use : run Nat := wire\n"
    book_a = write_file(dir_a, "book.muro", book)
    book_b = write_file(dir_b, "book.muro", book)

    task_get!(dir_a)
    task_get!(dir_b)

    lock_a = File.read!(Path.join(dir_a, "muro.lock"))
    lock_b = File.read!(Path.join(dir_b, "muro.lock"))
    assert lock_a == lock_b

    assert {:ok, lines_a} = Muro.conforms(book_a)
    assert {:ok, lines_b} = Muro.conforms(book_b)
    assert lines_a == lines_b
    assert hd(lines_a) =~ "conforms to shared_wire 1.0.0 (sha256 "

    File.write!(Path.join(repo, "wire.muro"), @wire2)
    git!(repo, ["add", "."])
    git!(repo, ["commit", "-m", "move"])
    git!(repo, ["tag", "-f", "v1.0.0"])

    out = task_get!(dir_a)
    assert out =~ "changed wire.muro"
    assert File.read!(Path.join(dir_b, "muro.lock")) == lock_b

    new_lock = File.read!(Path.join(dir_a, "muro.lock"))
    assert new_lock != lock_a
    assert wire_line(new_lock) != wire_line(lock_a)

    assert {:ok, new_lines} = Muro.conforms(book_a)
    assert {:ok, old_lines} = Muro.conforms(book_b)
    assert new_lines != old_lines
  end

  git_test "deps.get reports files, stays unchanged, and removes a dropped package" do
    repo = init_repo(%{"shared.muro" => @wire})
    git!(repo, ["tag", "v1.0.0"])
    dir = tmp_dir()
    write_git_manifest(dir, "shared", file_url(repo), tag: "v1.0.0")

    assert task_get!(dir) ==
             "fetched shared 1.0.0 (1 file)\n  added shared.muro\nwrote muro.lock\n"

    assert task_get!(dir) == "fetched shared 1.0.0 (1 file)\nmuro.lock unchanged\n"
    first = File.read!(Path.join(dir, "muro.lock"))
    task_get!(dir)
    assert File.read!(Path.join(dir, "muro.lock")) == first

    write_file(dir, "muro_deps/notes/keep.txt", "keep\n")
    File.write!(Path.join(dir, "muro.exs"), "[\n  fuel: 1\n]\n")
    assert task_get!(dir) == "nothing to fetch\nremoved shared\nremoved muro.lock\n"
    refute File.exists?(Path.join(dir, "muro_deps/shared"))
    assert File.read!(Path.join(dir, "muro_deps/notes/keep.txt")) == "keep\n"
    refute File.exists?(Path.join(dir, "muro.lock"))
  end

  git_test "a failed package leaves the lock and muro_deps unchanged" do
    good = init_repo(%{"wire.muro" => @wire})
    git!(good, ["tag", "v1.0.0"])
    bad = init_repo(%{"wire.muro" => @wire})
    dir = tmp_dir()
    write_git_manifest(dir, "alpha", file_url(good), tag: "v1.0.0")
    task_get!(dir)
    saved = File.read!(Path.join(dir, "muro.lock"))
    bytes = File.read!(Path.join(dir, "muro_deps/alpha/wire.muro"))

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro_deps: [
        alpha: {:git, #{inspect(file_url(good))}, tag: "v1.0.0"},
        zeta: {:git, #{inspect(file_url(bad))}, ref: "no-such-branch"}
      ]
    ]
    """)

    assert {:error, message} = Muro.Deps.get(dir)
    assert message =~ "zeta"
    assert message =~ "unchanged"
    assert File.read!(Path.join(dir, "muro.lock")) == saved
    assert File.read!(Path.join(dir, "muro_deps/alpha/wire.muro")) == bytes
    refute File.dir?(Path.join(dir, "muro_deps/zeta"))
  end

  git_test "root, a branch, a commit, an empty package, and a symlink" do
    rooted = init_repo(%{"priv/muro/wire.muro" => @wire, "other.muro" => @wire, "README" => "x"})
    git!(rooted, ["tag", "v1.2.0"])
    dir = tmp_dir()
    write_git_manifest(dir, "rooted", file_url(rooted), tag: "v1.2.0", root: "priv/muro")
    out = task_get!(dir)
    assert out =~ "fetched rooted 1.2.0 (1 file)"
    assert File.read!(Path.join(dir, "muro_deps/rooted/wire.muro")) == @wire
    refute File.exists?(Path.join(dir, "muro_deps/rooted/other.muro"))

    branched = init_repo(%{"wire.muro" => @wire})
    git!(branched, ["checkout", "-b", "topic"])
    sha = String.trim(git!(branched, ["rev-parse", "HEAD"]))
    short = String.slice(sha, 0, 7)
    branch_dir = tmp_dir()
    write_git_manifest(branch_dir, "branched", file_url(branched), ref: "topic")
    assert task_get!(branch_dir) =~ "fetched branched topic@#{short} (1 file)"
    {:ok, lock} = Muro.Lock.decode(File.read!(Path.join(branch_dir, "muro.lock")))
    assert lock["branched"].resolved == {:git, sha}
    assert lock["branched"].version == "topic@" <> short

    pinned = tmp_dir()
    write_git_manifest(pinned, "pinned", file_url(branched), ref: sha)
    assert task_get!(pinned) =~ "fetched pinned #{short} (1 file)"
    {:ok, lock} = Muro.Lock.decode(File.read!(Path.join(pinned, "muro.lock")))
    assert lock["pinned"].version == short
    assert lock["pinned"].resolved == {:git, sha}

    empty = init_repo(%{"README" => "x"})
    git!(empty, ["tag", "v1.0.0"])
    empty_dir = tmp_dir()
    write_git_manifest(empty_dir, "empty", file_url(empty), tag: "v1.0.0")
    assert {:error, message} = Muro.Deps.get(empty_dir)
    assert message =~ "no .muro file"
    refute File.exists?(Path.join(empty_dir, "muro.lock"))

    linked = init_repo(%{})
    File.write!(Path.join(linked, "real.txt"), @wire)
    File.ln_s!("real.txt", Path.join(linked, "wire.muro"))
    git!(linked, ["add", "."])
    git!(linked, ["commit", "-m", "link"])
    git!(linked, ["tag", "v1.0.0"])
    link_dir = tmp_dir()
    write_git_manifest(link_dir, "linked", file_url(linked), tag: "v1.0.0")
    assert {:error, message} = Muro.Deps.get(link_dir)
    assert message =~ "symlink"
    refute File.exists?(Path.join(link_dir, "muro.lock"))
  end

  defp wire_line(text) do
    text
    |> String.split("\n")
    |> Enum.find(&String.contains?(&1, "wire.muro"))
  end

  defp write_locked(dir, names, files) do
    File.write!(Path.join(dir, "muro.exs"), manifest(names, "v1.0.0"))
    Enum.each(files, fn {rel, bytes} -> write_file(dir, rel, bytes) end)
    relock(dir, files)
    dir
  end

  defp relock(dir, files) do
    {:ok, deps} = Muro.Manifest.load_deps(dir)

    packages =
      Map.new(deps, fn dep ->
        prefix = "muro_deps/" <> dep.name <> "/"

        hashed =
          files
          |> Enum.filter(fn {rel, _bytes} -> String.starts_with?(rel, prefix) end)
          |> Map.new(fn {rel, bytes} ->
            {String.replace_prefix(rel, prefix, ""), Muro.Hash.sha256(bytes)}
          end)

        {dep.name,
         %{
           files: hashed,
           resolved: {:git, String.duplicate("ab", 20)},
           source: dep.source,
           version: "1.0.0"
         }}
      end)

    File.write!(Path.join(dir, "muro.lock"), Muro.Lock.encode(packages))
  end

  defp manifest(names, tag) do
    entries =
      Enum.map_join(names, "\n", fn name ->
        "    #{name}: {:git, \"https://example.com/#{name}.git\", tag: \"#{tag}\"},"
      end)

    "[\n  muro_deps: [\n#{entries}\n  ]\n]\n"
  end

  defp write_git_manifest(dir, name, url, opts) do
    opt_text = Enum.map_join(opts, ", ", fn {key, value} -> "#{key}: #{inspect(value)}" end)

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro_deps: [
        #{name}: {:git, #{inspect(url)}, #{opt_text}}
      ]
    ]
    """)
  end

  defp write_file(dir, rel, bytes) do
    path = Path.join(dir, rel)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, bytes)
    path
  end

  defp task_get!(dir) do
    capture_io(fn ->
      File.cd!(dir, fn ->
        Mix.Tasks.Muro.Deps.Get.run([])
      end)
    end)
  end

  defp init_repo(files) do
    dir = tmp_dir()
    git!(dir, ["init"])
    git!(dir, ["config", "core.autocrlf", "false"])
    git!(dir, ["config", "uploadpack.allowReachableSHA1InWant", "true"])
    git!(dir, ["config", "uploadpack.allowAnySHA1InWant", "true"])

    if files == %{} do
      File.write!(Path.join(dir, ".keep"), "keep\n")
    else
      Enum.each(files, fn {rel, bytes} -> write_file(dir, rel, bytes) end)
    end

    git!(dir, ["add", "."])
    git!(dir, ["commit", "-m", "init"])
    dir
  end

  defp git!(dir, args) do
    git = System.find_executable("git")

    {out, status} =
      System.cmd(
        git,
        [
          "-c",
          "user.name=t",
          "-c",
          "user.email=t@t",
          "-c",
          "commit.gpgsign=false",
          "-c",
          "init.defaultBranch=main"
          | args
        ],
        cd: dir,
        stderr_to_stdout: true
      )

    if status != 0 do
      flunk("git #{inspect(args)} failed: #{String.slice(out, 0, 500)}")
    else
      out
    end
  end

  defp file_url(dir), do: "file://" <> Path.expand(dir)

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_deps_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
