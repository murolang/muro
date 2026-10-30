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
  end
end
