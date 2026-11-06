defmodule Muro.Temporal.Compile do
  @moduledoc """
  Block table of one process. Continuations are compiled before the block
  is recorded, and the block index is the smaller one, which is the
  preorder `Muro.AsyncRec.compile` uses.

  | Elixir | Agda |
  | --- | --- |
  | `compile/1` | `Muro.AsyncRec.compile` |
  | `compile_arms/5` | `Muro.AsyncRec.compileArms` |
  | `materialise/2` | `Muro.AsyncRec.materialise` |
  | `alphabet/2` | `Muro.AsyncRec.alphabet` |

  `actions` is the table `at <ordinal> <verb>` resolves against: one entry
  per source action, in block-index order. A jump allocates no block.
  """

  @doc """
  Transcribes `AsyncRec.compile` from an elaborated process.
  """
  def compile(proc) do
    case go(proc, [], [], [], 0, 0) do
      {:ok, entry, next, slots, blocks, binders} ->
        blocks = materialise(next, blocks)

        {:ok,
         %{
           entry: entry,
           slots: slots,
           blocks: blocks,
           actions: actions(blocks),
           binders: binders
         }}

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Transcribes `AsyncRec.materialise`.
  """
  def materialise(next, blocks) when is_integer(next) and next >= 0 do
    for i <- 0..(next - 1)//1 do
      Enum.find(blocks, %{k: :done, show: "done", at: i}, &(&1.at == i))
    end
  end

  @doc """
  Transcribes `AsyncRec.alphabet` for processes with no `suc` of a received
  nat. Literals are collected by `lits` and `addA` (a new atom is prepended).
  """
  def alphabet(left, right) do
    adds(lits(left), lits(right))
  end

  defp go({:mu, name, body}, pending, renv, venv, slot, n) do
    go(body, [name | pending], renv, venv, slot, n)
  end

  defp go({:var, name}, pending, renv, _venv, slot, n) do
    cond do
      name in pending ->
        {:error, "unguarded recursion"}

      true ->
        case lookup(name, renv) do
          nil -> {:error, "unbound process variable"}
          i -> {:ok, i, n, slot, [], []}
        end
    end
  end

  defp go(:done, _pending, _renv, _venv, slot, n) do
    {:ok, n, n + 1, slot, [%{k: :done, show: "done", at: n}], []}
  end

  defp go(:stop, _pending, _renv, _venv, slot, n) do
    {:ok, n, n + 1, slot, [%{k: :stop, show: "stop", at: n}], []}
  end

  defp go({:put, atom, show, body}, pending, renv, venv, slot, n) do
    case go(body, [], add_names(pending, n, renv), venv, slot, n + 1) do
      {:ok, e, next, slots, bs, binders} ->
        block = %{k: :put, atom: atom, cont: e, show: show, at: n}
        {:ok, n, next, slots, [block | bs], binders}

      {:error, _} = err ->
        err
    end
  end

  defp go({:echo, name, show, body}, pending, renv, venv, slot, n) do
    case lookup(name, venv) do
      nil ->
        {:error, "unbound process variable"}

      s ->
        case go(body, [], add_names(pending, n, renv), venv, slot, n + 1) do
          {:ok, e, next, slots, bs, binders} ->
            block = %{k: :echo, slot: s, cont: e, show: show, at: n}
            {:ok, n, next, slots, [block | bs], binders}

          {:error, _} = err ->
            err
        end
    end
  end

  defp go({:get, tag, name, ty, show, body}, pending, renv, venv, slot, n) do
    case go(body, [], add_names(pending, n, renv), [{name, slot} | venv], slot + 1, n + 1) do
      {:ok, e, next, slots, bs, binders} ->
        block = %{k: :get, tag: tag, slot: slot, cont: e, show: show, at: n}
        {:ok, n, next, slots, [block | bs], own(name, slot, ty) ++ binders}

      {:error, _} = err ->
        err
    end
  end

  defp go({:pick0, show, body}, pending, renv, venv, slot, n) do
    cont(body, pending, renv, venv, slot, n, fn e ->
      %{k: :pick0, cont: e, show: show, at: n}
    end)
  end

  defp go({:pick1, show, body}, pending, renv, venv, slot, n) do
    cont(body, pending, renv, venv, slot, n, fn e ->
      %{k: :pick1, cont: e, show: show, at: n}
    end)
  end

  defp go({:cover, show, p, q}, pending, renv, venv, slot, n) do
    renv1 = add_names(pending, n, renv)

    with {:ok, e1, next1, slot1, bs1, b1} <- go(p, [], renv1, venv, slot, n + 1),
         {:ok, e2, next2, slot2, bs2, b2} <- go(q, [], renv1, venv, slot1, next1) do
      block = %{k: :cover, c0: e1, c1: e2, show: show, at: n}
      {:ok, n, next2, slot2, [block | bs1 ++ bs2], b1 ++ b2}
    end
  end

  defp go({:iget, name, ty, show, p, q}, pending, renv, venv, slot, n) do
    renv1 = add_names(pending, n, renv)
    venv1 = [{name, slot} | venv]

    with {:ok, e1, next1, slot1, bs1, b1} <- go(p, [], renv1, venv1, slot + 1, n + 1),
         {:ok, e2, next2, slot2, bs2, b2} <- go(q, [], renv1, venv1, slot1, next1) do
      block = %{k: :iget, slot: slot, c0: e1, c1: e2, show: show, at: n}
      {:ok, n, next2, slot2, [block | bs1 ++ bs2], own(name, slot, ty) ++ b1 ++ b2}
    end
  end

  defp go({:mget, tag, name, ty, show, arms}, pending, renv, venv, slot, n) do
    renv1 = add_names(pending, n, renv)
    venv1 = [{name, slot} | venv]

    case compile_arms(arms, renv1, venv1, slot + 1, n + 1) do
      {:ok, next, slots, named, bs, binders} ->
        block = %{k: :mget, tag: tag, slot: slot, arms: named, show: show, at: n}
        {:ok, n, next, slots, [block | bs], own(name, slot, ty) ++ binders}

      {:error, _} = err ->
        err
    end
  end

  defp go(_other, _pending, _renv, _venv, _slot, _n) do
    {:error, "payload outside the temporal fragment"}
  end

  defp cont(body, pending, renv, venv, slot, n, block_of) do
    case go(body, [], add_names(pending, n, renv), venv, slot, n + 1) do
      {:ok, e, next, slots, bs, binders} ->
        {:ok, n, next, slots, [block_of.(e) | bs], binders}

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Transcribes `AsyncRec.compileArms`. Each arm starts from the same
  environment; the slot counter advances across arms.
  """
  def compile_arms(arms, renv, venv, slot, n) do
    go_arms(arms, renv, venv, slot, n)
  end

  defp go_arms([], _renv, _venv, slot, n), do: {:ok, n, slot, [], [], []}

  defp go_arms([{name, proc} | rest], renv, venv, slot, n) do
    with {:ok, e, next, slot1, bs1, b1} <- go(proc, [], renv, venv, slot, n),
         {:ok, next2, slot2, named, bs2, b2} <- go_arms(rest, renv, venv, slot1, next) do
      {:ok, next2, slot2, [{to_string(name), e} | named], bs1 ++ bs2, b1 ++ b2}
    end
  end

  defp own(:_, _slot, _ty), do: []

  defp own(name, slot, ty) do
    [%{name: to_string(name), slot: slot, type: ty}]
  end

  defp add_names([], _n, renv), do: renv
  defp add_names([x | xs], n, renv), do: [{x, n} | add_names(xs, n, renv)]

  defp lookup(_name, []), do: nil
  defp lookup(name, [{name, i} | _]), do: i
  defp lookup(name, [_ | rest]), do: lookup(name, rest)

  defp actions(blocks) do
    Enum.flat_map(blocks, fn block ->
      case verb_of(block) do
        nil -> []
        verb -> [%{index: block.at, verb: verb}]
      end
    end)
  end

  defp verb_of(%{k: k}) when k in [:put, :echo], do: :put
  defp verb_of(%{k: k}) when k in [:get, :iget, :mget], do: :get
  defp verb_of(%{k: :pick0}), do: :pick0
  defp verb_of(%{k: :pick1}), do: :pick1
  defp verb_of(%{k: :cover}), do: :cover
  defp verb_of(_), do: nil

  defp lits([]), do: []
  defp lits([%{k: :put, atom: atom} | rest]), do: add_a(atom, lits(rest))
  defp lits([_ | rest]), do: lits(rest)

  defp adds([], as), do: as
  defp adds([atom | rest], as), do: adds(rest, add_a(atom, as))

  defp add_a(atom, as) do
    if Enum.any?(as, &atom_eq?(&1, atom)), do: as, else: [atom | as]
  end

  defp atom_eq?({:nat, m}, {:nat, n}), do: m == n
  defp atom_eq?({:bit, a}, {:bit, b}), do: a == b
  defp atom_eq?({:con, a}, {:con, b}), do: a == b
  defp atom_eq?(_, _), do: false
end
