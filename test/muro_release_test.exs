defmodule Muro.ReleaseTest do
  use ExUnit.Case, async: true

  test "the executable release loads the http applications and wraps a prod build" do
    text = File.read!("mix.exs")
    assert text =~ "extra_applications: [:logger]"

    for app <- ~w(mix asn1 crypto public_key ssl inets) do
      assert text =~ ~r/#{app}:\s*:load/, "the release does not load :#{app}"
    end

    refute text =~ "{:ssl"
    refute text =~ "{:inets"
    refute text =~ "{:public_key"
    refute text =~ "{:crypto"
    refute text =~ "{:asn1"
    assert text =~ ~s(if debug?, do: "0", else: "1")
    assert text =~ "&mark_muro_release/1"
  end

  test "the muro release marker is written into sys.config and leaves other apps" do
    dir = Path.join(System.tmp_dir!(), "muro_release_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "sys.config")

    File.write!(path, """
    %% coding: utf-8
    %% RUNTIME_CONFIG=false
    [{logger, [{level, info}]}].
    """)

    assert Muro.Application.write_release_marker(path) == :ok
    {:ok, [config]} = :file.consult(String.to_charlist(path))
    assert config[:muro][:release_cli] == true
    assert config[:logger][:level] == :info

    written = File.read!(path)
    assert written =~ "%% coding: utf-8\n"
    assert written =~ "%% RUNTIME_CONFIG=false\n"

    assert Muro.Application.write_release_marker(path) == :ok
    {:ok, [again]} = :file.consult(String.to_charlist(path))
    assert again == config
  end
end
