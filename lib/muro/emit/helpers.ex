defmodule Muro.Emit.Helpers.Scan do
  @moduledoc false

  @deny MapSet.new(~w(
    moduledoc doc impl on_load callback behaviour behavior spec type
    derive optional_callbacks compile dialyzer after_compile before_compile
    deprecated vsn external_resource typedoc opaque enforce_keys
  ))

  @def_re ~r/^[ \t]*def(?:p|macro|macrop)?[ \t]+(?:unquote\([ \t]*:)?([A-Za-z_][A-Za-z0-9_]*[?!]?)/m
  @callback_re ~r/^[ \t]*@callback[ \t]+([A-Za-z_][A-Za-z0-9_]*[?!]?)/m
  @onload_re ~r/@on_load[ \t]+:([A-Za-z_][A-Za-z0-9_]*[?!]?)/
  @attr_re ~r/^[ \t]*@([A-Za-z_][A-Za-z0-9_]*[?!]?)(?![A-Za-z0-9_?!])/m

  @doc false
  def names_in(source) when is_binary(source) do
    defs = captures(@def_re, source)
    callbacks = captures(@callback_re, source)
    loads = captures(@onload_re, source)

    attrs =
      @attr_re
      |> captures(source)
      |> Enum.reject(&MapSet.member?(@deny, &1))

    MapSet.new(defs ++ callbacks ++ loads ++ attrs)
  end

  @doc false
  def load(mod) when is_atom(mod) do
    # Templates live beside this file. The Elixir emitter and the repr
    # helpers live in lib/muro.
    dir = __DIR__

    otp = scan(mod, Path.join(dir, "otp.ex"))
    exunit = scan(mod, Path.join(dir, "exunit.ex"))
    nif = scan(mod, Path.join(dir, "nif.ex"))
    node = scan(mod, Path.join(dir, "node.ex"))
    elixir = scan(mod, Path.expand("../emit.ex", dir))
    repr = scan(mod, Path.expand("../repr.ex", dir))
    {fsm_child, fsm} = fsm(mod, Path.join(dir, "fsm.ex"))

    runs =
      fsm
      |> MapSet.union(nif)
      |> MapSet.union(elixir)
      |> MapSet.union(repr)

    %{
      otp: otp,
      fsm: fsm,
      fsm_child: fsm_child,
      exunit: exunit,
      nif: nif,
      node: node,
      elixir: elixir,
      repr: repr,
      runs: runs
    }
  end

  defp scan(mod, path) do
    Module.put_attribute(mod, :external_resource, path)

    path
    |> File.read!()
    |> heredocs()
    |> Enum.reduce(MapSet.new(), fn body, acc -> MapSet.union(acc, names_in(body)) end)
  end

  # The child endpoint is a nested module. Its heredocs name `init` /
  # `send` / `recv` and do not define `muro_fsm_*`.
  defp fsm(mod, path) do
    Module.put_attribute(mod, :external_resource, path)

    {child, parent} =
      path
      |> File.read!()
      |> heredocs()
      |> Enum.split_with(&child_heredoc?/1)

    {bodies(child), bodies(parent)}
  end

  defp bodies(chunks) do
    Enum.reduce(chunks, MapSet.new(), fn body, acc -> MapSet.union(acc, names_in(body)) end)
  end

  defp child_heredoc?(body) do
    not Regex.match?(~r/^[ \t]*defp? muro_fsm_/m, body) and
      (String.contains?(body, "defmodule \#{camel}") or
         String.contains?(body, "def unquote(:send)") or
         Regex.match?(~r/^[ \t]*def (init|recv|expected|check_trace|done\?)\b/m, body))
  end

  defp heredocs(src) do
    src
    |> String.split(~s("""))
    |> Enum.drop(1)
    |> Enum.take_every(2)
  end

  defp captures(re, source) do
    Regex.scan(re, source)
    |> Enum.map(fn [_, name] -> name end)
  end
end

defmodule Muro.Emit.Helpers do
  @moduledoc false

  # Names an Elixir-facing template defines itself: `def`, `defp`,
  # `defmacro`, a callback, `@on_load`, or a module attribute. The set is
  # read from the template text, so a new helper is reserved when the
  # template starts defining it.
  #
  # A run shares a module with the FSM interpreter, the NIF loader, the
  # Elixir `muro_nat_to_int` helper, and the repr helpers. It does not
  # share a module with an OTP meeting, a node call, an ExUnit suite, or
  # the FSM child endpoint (`init`, `send`, `recv`). Those stay out of
  # `runs/0`, so a run named `step` or `send` keeps that name.

  @sets Muro.Emit.Helpers.Scan.load(__MODULE__)

  def otp, do: @sets.otp
  def fsm, do: @sets.fsm
  def fsm_child, do: @sets.fsm_child
  def exunit, do: @sets.exunit
  def nif, do: @sets.nif
  def node, do: @sets.node
  def elixir, do: @sets.elixir
  def repr, do: @sets.repr
  def runs, do: @sets.runs

  @doc false
  def names_in(source) when is_binary(source) do
    Muro.Emit.Helpers.Scan.names_in(source)
  end
end
