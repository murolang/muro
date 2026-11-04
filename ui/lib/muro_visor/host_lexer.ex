defmodule MuroVisor.HostLexer do
  @moduledoc """
  Makeup lexers for outline signatures and clauses.

  OTP and FSM outlines are Elixir. Rust uses `makeup_rust` when that
  lexer is loaded. C and Zig stay plain. This module does not define
  a lexer of its own.
  """

  @doc "A Makeup lexer module, or `nil` when the outline stays plain."
  def for_backend(backend) when backend in [:otp, :fsm], do: elixir()
  def for_backend(:rust), do: rust()
  def for_backend(_backend), do: nil

  def elixir do
    if Code.ensure_loaded?(Makeup.Lexers.ElixirLexer), do: Makeup.Lexers.ElixirLexer, else: nil
  end

  def rust do
    mod = Module.concat(Makeup.Lexers, RustLexer)
    if Code.ensure_loaded?(mod) and function_exported?(mod, :lex, 2), do: mod, else: nil
  end
end
