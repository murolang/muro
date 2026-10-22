defmodule Muro.Policies.Library do
  @moduledoc """
  Feature functions applied to a raw observation.

  A numeric reading accepts `eq0`, `gt0`, `gt1`, and `square` then
  `gt1`. A tag reading accepts equality with a tag that occurs in the
  observations. A feature is one function applied to one field.
  """

  @numeric [:uses, :arg_apps, :arg_size]
  @tags [:mark, :arg_head]
  @fns [:eq0, :gt0, :gt1, :square_gt1]

  @doc """
  Every application of the library to fields of `observations`.
  """
  def offered(observations) when is_list(observations) do
    numeric = for field <- @numeric, fun <- @fns, do: {fun, field}

    tags =
      for field <- @tags,
          ob <- observations,
          tag = Map.get(ob, field),
          tag not in [:missing, :absent],
          uniq: true,
          do: {:is, field, tag}

    numeric ++ Enum.sort(tags)
  end

  @doc """
  Apply one feature function to `observation`.
  """
  def apply({:eq0, field}, observation), do: Map.fetch!(observation, field) == 0
  def apply({:gt0, field}, observation), do: Map.fetch!(observation, field) > 0
  def apply({:gt1, field}, observation), do: Map.fetch!(observation, field) > 1

  def apply({:square_gt1, field}, observation) do
    n = Map.fetch!(observation, field)
    n * n > 1
  end

  def apply({:is, field, tag}, observation), do: Map.fetch!(observation, field) == tag
end
