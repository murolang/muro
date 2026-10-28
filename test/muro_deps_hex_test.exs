defmodule Muro.DepsHexTest.Transport do
  @moduledoc false
  @behaviour Muro.Deps.Hex.Transport

  @impl true
  def releases(package) do
    case Process.get({:hex_releases, package}) do
      nil -> {:error, "no fixture releases for #{package}"}
      releases -> {:ok, releases}
    end
  end

  @impl true
  def tarball(package, version) do
    case Process.get({:hex_tarball, package, version}) do
      nil -> {:error, "no fixture tarball for #{package} #{version}"}
      bin -> {:ok, bin}
    end
  end
end

defmodule Muro.DepsHexTest do
  use ExUnit.Case, async: false

  @wire "def wire : run Nat := 0\n"

  setup do
    previous = Application.get_env(:muro, :hex_transport)
    Application.put_env(:muro, :hex_transport, Muro.DepsHexTest.Transport)

    on_exit(fn ->
      if previous == nil do
        Application.delete_env(:muro, :hex_transport)
      else
        Application.put_env(:muro, :hex_transport, previous)
      end
    end)

    :ok
  end

  test "choose picks the highest release the requirement allows" do
    releases = [
      %{version: "1.9.0", retired: false},
      %{version: "2.0.0", retired: false},
      %{version: "2.1.0", retired: false},
      %{version: "2.2.0", retired: true},
      %{version: "2.3.0-rc.1", retired: false},
      %{version: "3.0.0", retired: false}
    ]

    assert Muro.Deps.Hex.choose(releases, "~> 2.0", "pricing_rules") == {:ok, "2.1.0"}
    assert Muro.Deps.Hex.choose(releases, ">= 2.0.0", "pricing_rules") == {:ok, "3.0.0"}

    assert Muro.Deps.Hex.choose(releases, ">= 1.0.0 and < 2.0.0", "pricing_rules") ==
             {:ok, "1.9.0"}

    assert Muro.Deps.Hex.choose(releases, "~> 2.3.0-rc", "pricing_rules") == {:ok, "2.3.0-rc.1"}

    only_retired = [
      %{version: "2.0.0", retired: true},
      %{version: "2.1.0", retired: true}
    ]

    assert Muro.Deps.Hex.choose(only_retired, "~> 2.0", "pricing_rules") == {:ok, "2.1.0"}

    assert {:error, message} = Muro.Deps.Hex.choose(releases, ">= 9.0.0", "pricing_rules")
    assert message =~ "no release of pricing_rules matches >= 9.0.0"
  end

  test "unpack keeps priv/muro books and records nothing else" do
    rules = @wire
    extra = "def extra : run Nat := suc 0\n"

    inner =
      inner_files([
        {"README", "notes"},
        {"lib/pricing.ex", "defmodule P do\nend\n"},
        {"priv/other.muro", rules},
        {"priv/muro/rules.muro", rules},
        {"priv/muro/sub/extra.muro", extra}
      ])

    outer = outer_tar(inner, checksum: :upper)
    assert {:ok, files} = Muro.Deps.Hex.unpack(outer)
    assert files == %{"rules.muro" => rules, "sub/extra.muro" => extra}

    assert {:ok, ^files} = Muro.Deps.Hex.unpack(outer_tar(inner, checksum: :lower))
    assert {:ok, ^files} = Muro.Deps.Hex.unpack(outer_tar(inner, checksum: :raw))
  end

  test "unpack refuses a bad checksum, a symlink, an absolute path, and .." do
    inner = inner_files([{"priv/muro/rules.muro", @wire}])
    assert {:error, message} = Muro.Deps.Hex.unpack(outer_tar(inner, checksum: :bad))
    assert message =~ "CHECKSUM does not match"

    assert {:error, message} =
             Muro.Deps.Hex.unpack(outer_tar(inner_with_symlink(), checksum: :upper))

    assert message =~ "symlink"

    absolute = inner_files([{"/etc/passwd.muro", @wire}, {"priv/muro/rules.muro", @wire}])
    assert {:error, message} = Muro.Deps.Hex.unpack(outer_tar(absolute, checksum: :upper))
    assert message =~ "absolute"

    escape = inner_files([{"../x.muro", @wire}, {"priv/muro/rules.muro", @wire}])
    assert {:error, message} = Muro.Deps.Hex.unpack(outer_tar(escape, checksum: :upper))
    assert message =~ "escapes"
  end

  test "fetch selects the release, keeps the books, and pins the tarball sha256" do
    rules = @wire
    inner = inner_files([{"priv/muro/rules.muro", rules}, {"mix.exs", "mix"}])
    outer = outer_tar(inner, version: "2.1.0", checksum: :upper)

    Process.put({:hex_releases, "pricing_rules"}, [
      %{version: "2.0.0", retired: false},
      %{version: "2.1.0", retired: false},
      %{version: "2.2.0-rc.1", retired: false},
      %{version: "3.0.0", retired: false}
    ])

    Process.put({:hex_tarball, "pricing_rules", "2.1.0"}, outer)

    assert {:ok, fetched} =
             Muro.Deps.Hex.fetch(%{
               kind: :hex,
               name: "pricing",
               package: "pricing_rules",
               requirement: "~> 2.0"
             })

    assert fetched.version == "2.1.0"
    assert fetched.files == %{"rules.muro" => rules}
    assert fetched.resolved == {:hex, "2.1.0", Muro.Hash.sha256(outer)}
  end

  test "fetch refuses an empty priv/muro and a bad tarball by package name" do
    empty = outer_tar(inner_files([{"README", "x"}]), checksum: :upper)
    Process.put({:hex_releases, "pricing_rules"}, [%{version: "2.1.0", retired: false}])
    Process.put({:hex_tarball, "pricing_rules", "2.1.0"}, empty)

    assert {:error, message} =
             Muro.Deps.Hex.fetch(%{
               kind: :hex,
               name: "pricing",
               package: "pricing_rules",
               requirement: "~> 2.0"
             })

    assert message =~ "pricing: no .muro file under priv/muro"

    bad = outer_tar(inner_files([{"priv/muro/rules.muro", @wire}]), checksum: :bad)
    Process.put({:hex_tarball, "pricing_rules", "2.1.0"}, bad)

    assert {:error, message} =
             Muro.Deps.Hex.fetch(%{
               kind: :hex,
               name: "pricing",
               package: "pricing_rules",
               requirement: "~> 2.0"
             })

    assert message =~ "pricing: tarball CHECKSUM does not match"
  end

  test "deps.get writes a hex package through the injected transport" do
    rules = @wire
    inner = inner_files([{"priv/muro/rules.muro", rules}])
    outer = outer_tar(inner, version: "2.1.0", checksum: :upper)

    Process.put({:hex_releases, "pricing_rules"}, [
      %{version: "2.1.0", retired: false},
      %{version: "2.2.0", retired: true}
    ])

    Process.put({:hex_tarball, "pricing_rules", "2.1.0"}, outer)

    dir = tmp_dir()

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro_deps: [
        pricing: {:hex, "pricing_rules", "~> 2.0"}
      ]
    ]
    """)

    assert {:ok, lines} = Muro.Deps.get(dir)
    assert lines == ["fetched pricing 2.1.0 (1 file)", "  added rules.muro", "wrote muro.lock"]
    assert File.read!(Path.join(dir, "muro_deps/pricing/rules.muro")) == rules

    {:ok, lock} = Muro.Lock.decode(File.read!(Path.join(dir, "muro.lock")))
    assert lock["pricing"].resolved == {:hex, "2.1.0", Muro.Hash.sha256(outer)}
    assert lock["pricing"].version == "2.1.0"
    assert lock["pricing"].source == {:hex, "pricing_rules", "~> 2.0"}
    assert lock["pricing"].files["rules.muro"] == Muro.Hash.sha256(rules)
  end

  test "the fallback JSON decoder reads a release list and refuses trailing input" do
    json = """
    {"releases":[{"version":"1.0.0","retirement":null},{"version":"1.1.0","retirement":{"reason":"security"}}]}
    """

    assert {:ok, %{"releases" => [first, second]}} = Muro.Deps.Hex.JSON.decode(json)
    assert first["version"] == "1.0.0"
    assert first["retirement"] == nil
    assert second["retirement"]["reason"] == "security"
    assert {:error, "trailing JSON"} = Muro.Deps.Hex.JSON.decode(String.trim(json) <> " 1")
    assert {:error, _message} = Muro.Deps.Hex.JSON.decode("{")
  end

  defp inner_files(files) do
    members = Enum.map(files, fn {name, bytes} -> {String.to_charlist(name), bytes} end)
    tar_bytes(members, [:compressed])
  end

  defp inner_with_symlink do
    dir = Path.join(System.tmp_dir!(), "muro_hex_link_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    File.write!(Path.join(dir, "real.muro"), @wire)
    File.ln_s!("real.muro", Path.join(dir, "link.muro"))

    tar = Path.join(dir, "inner.tar.gz")

    File.cd!(dir, fn ->
      :ok = :erl_tar.create(~c"inner.tar.gz", [~c"link.muro"], [:compressed])
    end)

    bin = File.read!(tar)
    File.rm_rf!(dir)
    bin
  end

  defp outer_tar(inner, opts) do
    version = Keyword.get(opts, :version, "2.1.0")
    metadata = "{}\n"
    digest = :crypto.hash(:sha256, version <> metadata <> inner)

    checksum =
      case Keyword.get(opts, :checksum, :upper) do
        :upper -> Base.encode16(digest, case: :upper)
        :lower -> Base.encode16(digest, case: :lower)
        :raw -> digest
        :bad -> "deadbeef"
      end

    tar_bytes(
      [
        {~c"VERSION", version},
        {~c"CHECKSUM", checksum},
        {~c"metadata.config", metadata},
        {~c"contents.tar.gz", inner}
      ],
      []
    )
  end

  defp tar_bytes(members, flags) do
    dir = Path.join(System.tmp_dir!(), "muro_hex_tar_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "archive.tar")
    :ok = :erl_tar.create(String.to_charlist(path), members, flags)
    bin = File.read!(path)
    File.rm_rf!(dir)
    bin
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_deps_hex_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
