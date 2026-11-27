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

  `prefix/3` is the legal-prefix judgment of the global type in its
  written order, the Elixir mirror of `accept` in
  `agda/Muro/ChoreoPrefix.agda`.

  A role marked `shared` is one party for every key of a family that
  ranges over the choreography. A message between two shared roles is
  global. Those messages, and the choices of shared roles, written
  before any other step form the shared preamble. A message between two
  shared roles after a per-key step is refused (`check_decl/2`).
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
  has two or more branches and the labels do not repeat. Two roles, or
  two labels of one choice, do not reach one host atom
  (`Muro.Emit.elixir_atom_name/1`). Each payload
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
  `check/4` on a declaration, then the shared order: a message between
  two shared roles is written before every per-key step.
  """
  def check_decl(%{name: name, roles: roles, body: body} = decl, book) do
    case check(name, roles, body, book) do
      {:ok, lines} ->
        case shared_errors(Map.get(decl, :shared, []), body) do
          [] -> {:ok, lines}
          errs -> {:error, Enum.join(errs, "; ")}
        end

      {:error, _} = err ->
        err
    end
  end

  @doc """
  True when the next interaction of `g` belongs to the shared preamble
  when it is reached through preamble steps only: a message between two
  shared roles, or a choice by a shared role.
  """
  def shared_step?({:comm, a, b, _label, _ty, _}, shared), do: a in shared and b in shared
  def shared_step?({:choice, p, _}, shared), do: p in shared
  def shared_step?(:end, _shared), do: false

  defp shared_errors([], _body), do: []
  defp shared_errors(shared, body), do: shared_walk(body, shared, :preamble) |> Enum.uniq()

  defp shared_walk(:end, _shared, _phase), do: []

  defp shared_walk({:comm, a, b, label, ty, g} = node, shared, phase) do
    global? = shared_step?(node, shared)

    cond do
      phase == :preamble and global? ->
        shared_walk(g, shared, :preamble)

      phase == :per_key and global? ->
        [
          "#{show_message(a, b, label, ty)} is between shared roles after a per-key step; " <>
            "a message between shared roles belongs in the shared preamble"
          | shared_walk(g, shared, :per_key)
        ]

      true ->
        shared_walk(g, shared, :per_key)
    end
  end

  # A choice by a shared role in the preamble is global. After a
  # per-key step it is that key's choice.
  defp shared_walk({:choice, p, branches}, shared, phase) do
    next = if phase == :preamble and p in shared, do: :preamble, else: :per_key
    Enum.flat_map(branches, fn {_label, g} -> shared_walk(g, shared, next) end)
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

  @doc """
  One message as it is written in the global type: `a -> b : label`,
  then the payload when it is not `Unit`.
  """
  def show_message(a, b, label, ty), do: "#{a} -> #{b} : #{label}#{show_pay(ty)}"

  @doc """
  The labels a choice offers, in written order: `p chooses commit or abort`.
  """
  def show_choice(p, branches) do
    labels = Enum.map(branches, fn {label, _} -> label end)
    "#{p} chooses #{join_or(labels)}"
  end

  defp join_or([one]), do: one
  defp join_or([a, b]), do: "#{a} or #{b}"
  defp join_or(many), do: Enum.join(Enum.drop(many, -1), ", ") <> ", or " <> List.last(many)

  defp show_pay(:unit), do: ""

  defp show_pay(ty) do
    " " <> String.replace_prefix(Muro.Session.step_proto({:send, ty, :end}), "send ", "")
  end

  @doc """
  The legal-prefix judgment of a global type in its written order. A
  move is `{:msg, a, b, label, ty}` or `{:pick, p, label}`. The first
  move is the next interaction written, or a label of the choice
  written next. Two interactions that share no role are still taken in
  the order they are written. Returns `:ok`, or `{:error, n, reason}`
  for the first move `n` (one-based) that is not enabled, with
  `reason` `{:not_enabled, expected, wrote}` or `{:unknown_role, name}`.
  """
  def prefix(roles, body, moves), do: prefix_walk(roles, body, moves, 1)

  defp prefix_walk(_roles, _g, [], _n), do: :ok

  defp prefix_walk(roles, g, [move | rest], n) do
    case unknown_in(roles, move) do
      nil ->
        case advance(g, move) do
          {:ok, next} -> prefix_walk(roles, next, rest, n + 1)
          :no -> {:error, n, {:not_enabled, expected_text(g), move}}
        end

      name ->
        {:error, n, {:unknown_role, name}}
    end
  end

  defp unknown_in(roles, {:msg, a, b, _label, _ty}) do
    Enum.find([a, b], &(&1 not in roles))
  end

  defp unknown_in(roles, {:pick, p, _label}), do: if(p in roles, do: nil, else: p)
  defp unknown_in(_roles, _move), do: nil

  @doc """
  The global type after one event, in the written order: `{:ok, next}`
  or `:no`.
  """
  def advance({:comm, a, b, label, ty, cont}, {:msg, a, b, label, ty}), do: {:ok, cont}

  def advance({:choice, p, branches}, {:pick, p, label}) do
    case List.keyfind(branches, label, 0) do
      {_, g} -> {:ok, g}
      nil -> :no
    end
  end

  def advance(_g, _move), do: :no

  @doc """
  The next interaction of a global type, as it is written.
  """
  def expected_text(:end), do: "end"
  def expected_text({:comm, a, b, label, ty, _}), do: show_message(a, b, label, ty)
  def expected_text({:choice, p, branches}), do: show_choice(p, branches)

  defp accepted(roles, body, book) do
    case Enum.uniq(role_errors(roles) ++ walk(roles, body, book)) do
      [] -> :ok
      errs -> {:error, Enum.join(errs, "; ")}
    end
  end

  defp role_errors(roles) do
    dups =
      roles
      |> Enum.frequencies()
      |> Enum.flat_map(fn
        {name, n} when n > 1 -> ["duplicate role #{name}"]
        _ -> []
      end)

    dups ++ spelling_clashes("roles", roles)
  end

  # A role and a choice label are atoms in the state machine, spelled
  # by `Muro.Emit.elixir_atom_name/1`. Two distinct source names that
  # reach one atom would be one role, or one branch, on the host, so
  # they are refused here and the message names both.
  defp spelling_clashes(kind, names) do
    names
    |> Enum.uniq()
    |> Enum.reduce({%{}, []}, fn name, {seen, errs} ->
      host = Muro.Emit.elixir_atom_name(name)

      case Map.fetch(seen, host) do
        {:ok, prev} -> {seen, ["#{kind} #{prev} and #{name} spell one Elixir atom" | errs]}
        :error -> {Map.put(seen, host, name), errs}
      end
    end)
    |> elem(1)
    |> Enum.reverse()
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

    short ++ dups ++ spelling_clashes("branches", labels)
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
