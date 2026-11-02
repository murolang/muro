defmodule MuroVisor.PackageTest do
  use ExUnit.Case, async: false

  test "publishing depends on muro by version, and a checkout overrides it" do
    assert MuroVisor.MixProject.muro_dependency(["hex.publish"], true, nil) ==
             {:muro, "~> 0.20.7"}

    assert MuroVisor.MixProject.muro_dependency(["hex.build"], true, "/tmp/muro-src") ==
             {:muro, "~> 0.20.7"}

    assert MuroVisor.MixProject.muro_dependency(["deps.get"], false, nil) ==
             {:muro, "~> 0.20.7"}

    {:muro, "~> 0.20.7", opts} =
      MuroVisor.MixProject.muro_dependency(["test"], true, nil)

    assert opts[:override] == true
    assert File.regular?(Path.join(opts[:path], "lib/muro.ex"))

    {:muro, "~> 0.20.7", opts} =
      MuroVisor.MixProject.muro_dependency(["deps.get"], false, "/tmp/muro-src")

    assert opts[:path] == "/tmp/muro-src"
    assert opts[:override] == true
  end

  test "this checkout builds against the repository" do
    {:muro, "~> 0.20.7", opts} =
      Mix.Project.config()[:deps]
      |> Enum.find(&match?({:muro, _, _}, &1))

    assert opts[:override] == true
    assert File.regular?(Path.join(opts[:path], "lib/muro.ex"))
  end
end
