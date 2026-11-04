defmodule Muro.Choreo do
  @moduledoc """
  The Elixir mirror of projection in `agda/Muro/Choreo.agda`.

  A choreography is a global type. `project/3` is the binary session
  one role has with another. A message from `a` to `b` is `send` for
  the pair `(a, b)` and `recv` for `(b, a)`. Any other pair keeps the
  continuation. A choice by `p` is `choose` on `p`'s side of a pair and
  `branch` on the other side. More than two branches nest to the right.
  A pair that is neither end of the choice has a session only when every
  branch projects to the same session. That is plain merge.
  """

  @doc """
  The session role `r` has with role `s` in the global type.
  `{:error, msg}` is a self-interaction, a choice with fewer than two
  branches, or a plain-merge refusal.
  """
  def project(:end, r, s) when r == s, do: {:error, "self-interaction #{r}"}
  def project(:end, _r, _s), do: {:ok, :end}

  def project({:comm, a, b, _label, ty, g}, r, s) do
    cond do
      a == b -> {:error, "self-interaction #{a}"}
      r == s -> {:error, "self-interaction #{r}"}
      r == a and s == b -> wrap({:send, ty}, project(g, r, s))
      r == b and s == a -> wrap({:recv, ty}, project(g, r, s))
      true -> project(g, r, s)
    end
  end

  def project({:choice, p, branches}, r, s) do
    if r == s do
      {:error, "self-interaction #{r}"}
    else
      case project_branches(branches, r, s) do
        {:error, _} = err ->
          err

        {:ok, protos} ->
          cond do
            r == p -> nest(:choose, protos)
            s == p -> nest(:branch, protos)
            true -> merge(branches, protos, r)
          end
      end
    end
  end

  @doc """
  Declaration check. Roles are unique. Every name in the global type is
  one of those roles. A message is between two distinct roles. A choice
  has two or more branches and the labels do not repeat. Each payload
  is a session payload. The result is one line per ordered pair of
  distinct roles, in role-list order.
  """
  def check(name, roles, body, book) do
    case Enum.uniq(role_errors(roles) ++ walk(roles, body, book)) do
      [] -> outline(name, roles, body)
      errs -> {:error, Enum.join(errs, "; ")}
    end
  end

  @doc """
  The session `r` has with `s` once the choreography is accepted.
  """
  def session(roles, body, r, s, book) do
    with :ok <- accepted(roles, body, book) do
      cond do
        r not in roles -> {:error, "unknown role #{r}"}
        s not in roles -> {:error, "unknown role #{s}"}
        r == s -> {:error, "self-interaction #{r}"}
        true -> project(body, r, s)
      end
    end
  end

  defp accepted(roles, body, book) do
    case Enum.uniq(role_errors(roles) ++ walk(roles, body, book)) do
      [] -> :ok
      errs -> {:error, Enum.join(errs, "; ")}
    end
  end

  defp role_errors(roles) do
    roles
    |> Enum.frequencies()
    |> Enum.flat_map(fn
      {name, n} when n > 1 -> ["duplicate role #{name}"]
      _ -> []
    end)
  end

  defp walk(_roles, :end, _book), do: []

  defp walk(roles, {:comm, a, b, _label, ty, g}, book) do
    unknown(roles, [a, b]) ++ self_msg(a, b) ++ payload(ty, book) ++ walk(roles, g, book)
  end

  defp walk(roles, {:choice, p, branches}, book) do
    unknown(roles, [p]) ++
      choice_shape(branches) ++
      Enum.flat_map(branches, fn {_label, g} -> walk(roles, g, book) end)
  end

  defp unknown(roles, names) do
    for name <- names, name not in roles, do: "unknown role #{name}"
  end

  defp self_msg(a, a), do: ["self-interaction #{a}"]
  defp self_msg(_a, _b), do: []

  defp choice_shape(branches) do
    labels = Enum.map(branches, fn {label, _} -> label end)

    short =
      if length(branches) < 2 do
        ["a choice has two branches"]
      else
        []
      end

    dups =
      labels
      |> Enum.frequencies()
      |> Enum.flat_map(fn
        {label, n} when n > 1 -> ["duplicate branch #{label}"]
        _ -> []
      end)

    short ++ dups
  end

  defp payload(ty, book) do
    case Muro.Session.proto_ok({:send, ty, :end}, book) do
      :ok -> []
      {:error, msg} -> [msg]
    end
  end

  defp outline(name, roles, body) do
    pairs = for r <- roles, s <- roles, r != s, do: {r, s}

    {lines, errs} =
      Enum.reduce(pairs, {[], []}, fn {r, s}, {lines, errs} ->
        case project(body, r, s) do
          {:ok, proto} ->
            line = "choreography #{name}: #{r} with #{s} = #{Muro.Session.show_proto(proto)}"
            {lines ++ [line], errs}

          {:error, msg} ->
            {lines, [msg | errs]}
        end
      end)

    case Enum.uniq(Enum.reverse(errs)) do
      [] -> {:ok, lines}
      msgs -> {:error, Enum.join(msgs, "; ")}
    end
  end

  defp project_branches([], _r, _s), do: {:ok, []}

  defp project_branches([{_label, g} | rest], r, s) do
    with {:ok, proto} <- project(g, r, s),
         {:ok, protos} <- project_branches(rest, r, s) do
      {:ok, [proto | protos]}
    end
  end

  defp wrap(_tag, {:error, _} = err), do: err
  defp wrap({:send, ty}, {:ok, cont}), do: {:ok, {:send, ty, cont}}
  defp wrap({:recv, ty}, {:ok, cont}), do: {:ok, {:recv, ty, cont}}

  defp nest(_ctor, protos) when length(protos) < 2, do: {:error, "a choice has two branches"}
  defp nest(ctor, [b, c]), do: {:ok, {ctor, b, c}}

  defp nest(ctor, [b | rest]) do
    with {:ok, inner} <- nest(ctor, rest) do
      {:ok, {ctor, b, inner}}
    end
  end

  defp merge(branches, [first | rest], role) do
    if length(branches) < 2 do
      {:error, "a choice has two branches"}
    else
      if Enum.all?(rest, &(&1 == first)) do
        {:ok, first}
      else
        {:error, disagree(role, branches)}
      end
    end
  end

  defp merge(_branches, _protos, _role), do: {:error, "a choice has two branches"}

  defp disagree(role, branches) do
    labels = Enum.map(branches, fn {label, _} -> label end)

    text =
      case labels do
        [a, b] -> "branches #{a} and #{b} disagree"
        many -> "branches #{Enum.join(many, ", ")} disagree"
      end

    "#{role}: #{text}"
  end
end
