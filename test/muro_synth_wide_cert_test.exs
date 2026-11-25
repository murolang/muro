defmodule Muro.Synth.WideCertTest do
  use ExUnit.Case, async: false

  @moduletag timeout: 180_000

  @wide "test/fixtures/wide_cover.muro"
  @queens4 "examples/cshrl/envs/queens4.muro"

  test "queens4 stays on the per-leaf certificate" do
    assert {:ok, host} = Muro.Synth.Host.open(@queens4)
    refute Muro.Synth.Cert.wide_host?(host)
  end

  test "a cyclic cover past 1500 cells shares one arm per winning action" do
    assert {:ok, host} = Muro.Synth.Host.open(@wide)
    assert Muro.Synth.Cert.wide_host?(host)

    {us, result} = :timer.tc(fn -> Muro.Synth.cegis_loop(@wide, depth: 0, max_depth: 0) end)
    assert us < 90_000_000, "wide cover took #{us} µs"
    assert {:ok, result} = result
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.book =~ "-- wide cover"
    assert result.book =~ "def cert-arm-action-"
    assert [_one] = Regex.scan(~r/^def cert-arm-action-/m, result.book)
    assert [_one] = Regex.scan(~r/^def le-stream /m, result.book)
    assert result.book =~ "def cert-miss-action"
    assert result.book =~ "def cert-same-action"
    refute result.book =~ "def cert-leaf-"
    refute result.book =~ "def hold-"
    assert result.book =~ "rewrite"
  end
end
