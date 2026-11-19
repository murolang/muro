defmodule Muro.EmitSortedMapsTest do
  # Since OTP 26 a small map with atom keys iterates in atom-table order,
  # which depends on what the VM loaded first. `mix muro.gen` in a fresh VM
  # and `mix muro.gen --check` inside a long test run then disagreed about
  # the same book. The emitted declarations print their keys sorted.
  use ExUnit.Case, async: true

  @book """
  data Report : Type where
    answered : Report
    unanswered : Report

  session wait := recv Report end
  session send-report := dual wait
  """

  test "the state machine prints a declaration's keys in sorted order" do
    {:ok, book} = Muro.Parser.parse(@book)
    assert {:ok, src} = Muro.Emit.Fsm.render(book, "report.muro", ReportFsm)
    assert_sorted(src)
  end

  test "the OTP image prints a declaration's keys in sorted order" do
    {:ok, book} = Muro.Parser.parse(@book)
    assert {:ok, src} = Muro.Emit.Otp.render(book, "report")
    assert_sorted(src)
  end

  defp assert_sorted(src) do
    assert src =~ ~r/%\{\s*ctors: %\{[^}]*\},\s*np: \d+,\s*order: \[[^\]]*\]\s*\}/s
  end
end
