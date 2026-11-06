defmodule Muro.Place do
  @moduledoc """
  The Elixir mirror of `decide`, `ground`, `conform`, and `bounds`
  in `agda/Muro/Place.agda`.

  A place is `:ambient` or `{:node, name}`. A scheme is `:any` or
  `{:fixed, place}`. Reading `any` stays. Reading a fixed place stays
  at that place and crosses once at any other. `bounds/1` is `:none`
  for `stay` and `:one` for `cross`.
  """

  @doc """
  `stay` when the places are the same, `cross` otherwise.
  Mirrors `decide`.
  """
  def decide(p, q) when p == q, do: :stay
  def decide(_p, _q), do: :cross

  @doc """
  The place a scheme denotes at the place where it is read.
  Mirrors `ground`.
  """
  def ground(:any, q), do: q
  def ground({:fixed, p}, _q), do: p

  @doc """
  The move that reads `scheme` at `place`. Mirrors `conform`.
  """
  def conform(:any, _q), do: :stay
  def conform({:fixed, p}, q), do: decide(p, q)

  @doc """
  `stay` has no boundary. `cross` has one. Mirrors `bounds`.
  """
  def bounds(:stay), do: :none
  def bounds(:cross), do: :one
end
