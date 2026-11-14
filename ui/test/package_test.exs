defmodule MuroVisor.PackageTest do
  use ExUnit.Case, async: false

  test "publishing depends on muro by version, and a checkout overrides it" do
    assert MuroVisor.MixProject.muro_dependency(["hex.publish"], true, nil) ==
             {:muro, "~> 0.21.0"}

    assert MuroVisor.MixProject.muro_dependency(["hex.build"], true, "/tmp/muro-src") ==
             {:muro, "~> 0.21.0"}

    assert MuroVisor.MixProject.muro_dependency(["deps.get"], false, nil) ==
             {:muro, "~> 0.21.0"}

    {:muro, "~> 0.21.0", opts} =
      MuroVisor.MixProject.muro_dependency(["test"], true, nil)

    assert opts[:override] == true
    assert File.regular?(Path.join(opts[:path], "lib/muro.ex"))

    {:muro, "~> 0.21.0", opts} =
      MuroVisor.MixProject.muro_dependency(["deps.get"], false, "/tmp/muro-src")

    assert opts[:path] == "/tmp/muro-src"
    assert opts[:override] == true
  end

  test "a checkout drops a muro build whose version is not mix.exs" do
    root = Path.join(System.tmp_dir!(), "visor-stale-#{System.unique_integer([:positive])}")
    stale = Path.join(root, "dev/lib/muro/ebin/muro.app")
    fresh = Path.join(root, "test/lib/muro/ebin/muro.app")
    other = Path.join(root, "dev/lib/phoenix/ebin/phoenix.app")
    File.mkdir_p!(Path.dirname(stale))
    File.mkdir_p!(Path.dirname(fresh))
    File.mkdir_p!(Path.dirname(other))
    File.write!(stale, "{application,muro,[{vsn,\"0.20.5\"}]}.")
    File.write!(fresh, "{application,muro,[{vsn,\"0.20.7\"}]}.")
    File.write!(other, "{application,phoenix,[{vsn,\"1.7.14\"}]}.")
    on_exit(fn -> File.rm_rf(root) end)

    assert :ok = MuroVisor.MixProject.discard_stale_muro_build(root, "0.20.7")
    refute File.exists?(stale)
    assert File.exists?(fresh)
    assert File.exists?(other)
  end

  test "this checkout builds against the repository" do
    {:muro, "~> 0.21.0", opts} =
      Mix.Project.config()[:deps]
      |> Enum.find(&match?({:muro, _, _}, &1))

    assert opts[:override] == true
    assert File.regular?(Path.join(opts[:path], "lib/muro.ex"))
  end
end
