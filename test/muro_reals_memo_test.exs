defmodule Muro.RealsMemoTest do
  use ExUnit.Case, async: true

  test "manual/reals.md exists and is linked from the index and the library" do
    assert File.exists?("manual/reals.md")
    manifest = File.read!("manual/manifest.yml")
    assert manifest =~ ~r/(?m)^  - file: reals\.md$/
    assert File.read!("manual/library.md") =~ "(reals.md)"
    assert File.read!("README.md") =~ "manual/reals.md"
    assert File.read!("AGENTS.md") =~ "manual/reals.md"
    assert File.read!("manual/index.md") =~ "(reals.md)"
  end
end
