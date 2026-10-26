defmodule Muro.Async do
  @moduledoc """
  The Elixir mirror of `Muro.Async` and `Muro.AsyncRec`.

  A configuration is the two processes, one FIFO in each direction, and
  the value environments those processes have already received. A send
  enqueues on its own queue when that queue holds fewer than `k`
  messages. A full queue is not an error: that send waits. A receive
  dequeues the head of the other queue. The head must be the type, the
  label, or the arm the receiver names.

  Both ends finish only with both queues empty. Until then some step
  has to remain possible. A cycle of configurations that can still step
  is that meeting again. The search remembers configurations it has
  entered. Recursive processes are the same search: a loop that would
  enqueue a value built from a received name is refused before the
  search, and a constant or an echo stays inside the configurations
  already seen.

  Evidence is not queued. The sender has already discharged it, and the
  message is the payload. The queued value is resolved, so an echo
  selects the arm of the value that was received. The length index is
  the expression the sender wrote.

  Buffer 0 blocks every send. It is not the synchronous meeting.
  """

  @cover "match does not cover the received value"

  @doc """
  `:ok` when every reachable configuration is safe at bound `k`.
  Otherwise the first fault of a left-to-right search: a reception
  error, an orphan message, a deadlock, `unguarded recursion`,
  `free session variable`, or `unbounded recursive payload`.
  """
  def meets(p, q, book, k) when is_integer(k) and k >= 0 do
    meets(p, q, book, k, "left", "right")
  end

  def meets(p, q, book, k, left, right) when is_integer(k) and k >= 0 do
    if cyclic_grow?(p, book) or cyclic_grow?(q, book) do
      {:error, "unbounded recursive payload"}
    else
      conf = %{
        k: k,
        lp: p,
        rp: q,
        l2r: [],
        r2l: [],
        lv: %{},
        rv: %{},
        lt: %{},
        rt: %{},
        li: %{},
        ri: %{},
        le: %{},
        re: %{},
        book: book,
        left: left,
        right: right
      }

      explore(conf, MapSet.new(), [])
    end
  end

  defp explore(conf, seen, trace) do
    key = seen_key(conf)

    if MapSet.member?(seen, key) do
      :ok
    else
      case classify(conf) do
        :final ->
          :ok

        {:bad, reason} ->
          {:error, render(reason, conf, trace)}

        {:go, kids} ->
          walk(kids, MapSet.put(seen, key), trace)
      end
    end
  end

  defp walk([], _seen, _trace), do: :ok

  defp walk([{conf, label} | rest], seen, trace) do
    case explore(conf, seen, trace ++ [label]) do
      :ok -> walk(rest, seen, trace)
      {:error, _} = err -> err
    end
  end

  defp seen_key(conf) do
    {conf.lp, conf.rp, conf.l2r, conf.r2l, conf.lv, conf.rv, conf.lt, conf.rt, conf.li, conf.ri,
     conf.le, conf.re}
  end

  defp classify(conf), do: merge(react(conf, :left), react(conf, :right), conf)

  defp merge({:bad, reason}, _right, _conf), do: {:bad, reason}
  defp merge(_left, {:bad, reason}, _conf), do: {:bad, reason}

  defp merge({:go, c1, lab1}, {:go, c2, lab2}, _conf), do: {:go, [{c1, lab1}, {c2, lab2}]}

  defp merge({:go, c, lab}, :wait, _conf), do: {:go, [{c, lab}]}
  defp merge(:wait, {:go, c, lab}, _conf), do: {:go, [{c, lab}]}
  defp merge(:wait, :wait, conf), do: idle(conf)

  defp idle(conf) do
    if halted?(conf.lp, conf.le) and halted?(conf.rp, conf.re) do
      if conf.l2r == [] and conf.r2l == [] do
        :final
      else
        {:bad, :orphan}
      end
    else
      {:bad, :dead}
    end
  end

  defp halted?(proc, env) do
    case Muro.Session.unwind_proc(proc, env) do
      {:ok, :done, _} -> true
      {:ok, :stop, _} -> true
      _ -> false
    end
  end

  defp react(conf, side) do
    {proc, env} = pull(conf, side)

    case Muro.Session.unwind_proc(proc, env) do
      {:error, msg} ->
        {:bad, msg}

      {:ok, head, env2} ->
        case act(put_env(conf, side, env2), side, head) do
          :wait -> :wait
          other -> other
        end
    end
  end

  defp act(conf, side, {:put, ty, val, cont}) do
    if length(out_queue(conf, side)) >= conf.k do
      :wait
    else
      case prepare_send(conf, side, ty, val) do
        :no ->
          :wait

        {:ok, sty, orig, ready} ->
          label = "#{side_name(conf, side)} put #{Muro.Session.show_value(ready)}"
          {:go, enqueue(conf, side, cont, {:pay, sty, orig, ready}), label}
      end
    end
  end

  defp act(conf, side, {:get, ty, name, {:match, scrut, arms}}) do
    if scrut != name do
      {:bad, @cover}
    else
      case dequeue(conf, side) do
        :empty ->
          :wait

        {:msg, msg, rest} ->
          recv_match(conf, side, ty, name, arms, msg, rest)
      end
    end
  end

  defp act(conf, side, {:get, ty, name, cont}) do
    case dequeue(conf, side) do
      :empty ->
        :wait

      {:msg, msg, rest} ->
        case accept_pay(conf, side, ty, msg) do
          :bad ->
            {:bad, {:recv, side, msg}}

          {:ok, recv_ty, orig, ready} ->
            conf = commit_recv(conf, side, cont, rest, name, recv_ty, orig, ready)
            {:go, conf, "#{side_name(conf, side)} #{step_get(ty, name)}"}
        end
    end
  end

  defp act(conf, side, {:pick0, cont}), do: send_lab(conf, side, false, cont, "pick0")
  defp act(conf, side, {:pick1, cont}), do: send_lab(conf, side, true, cont, "pick1")

  defp act(conf, side, {:cover, p, q}) do
    case dequeue(conf, side) do
      :empty ->
        :wait

      {:msg, {:lab, false}, rest} ->
        {:go, take(conf, side, p, rest), "#{side_name(conf, side)} cover0"}

      {:msg, {:lab, true}, rest} ->
        {:go, take(conf, side, q, rest), "#{side_name(conf, side)} cover1"}

      {:msg, msg, _rest} ->
        {:bad, {:recv, side, msg}}
    end
  end

  defp act(conf, side, {:iget, name, p, q}) do
    case dequeue(conf, side) do
      :empty ->
        :wait

      {:msg, msg, rest} ->
        recv_iget(conf, side, name, p, q, msg, rest)
    end
  end

  defp act(_conf, _side, :done), do: :wait
  defp act(_conf, _side, :stop), do: :wait
  defp act(_conf, _side, {:match, _, _}), do: :wait

  defp recv_match(conf, side, ty, name, arms, msg, rest) do
    case accept_pay(conf, side, ty, msg) do
      :bad ->
        {:bad, {:recv, side, msg}}

      {:ok, recv_ty, orig, ready} ->
        case Muro.Session.arm(recv_ty, ready, arms, conf.book) do
          {:ok, arm} ->
            conf = commit_recv(conf, side, arm, rest, name, recv_ty, orig, ready)
            {:go, conf, "#{side_name(conf, side)} arm #{arm_label(ready)}"}

          :error ->
            {:bad, {:recv, side, msg}}
        end
    end
  end

  defp recv_iget(conf, side, name, p, q, {:pay, sty, orig, ready} = msg, rest) do
    wire = if sty == :unknown, do: :bit, else: sty

    cond do
      wire != :bit ->
        {:bad, {:recv, side, msg}}

      ready == :b0 ->
        conf = commit_recv(conf, side, p, rest, name, :bit, orig, ready)
        {:go, conf, "#{side_name(conf, side)} arm b0"}

      ready == :b1 ->
        conf = commit_recv(conf, side, q, rest, name, :bit, orig, ready)
        {:go, conf, "#{side_name(conf, side)} arm b1"}

      true ->
        {:bad, {:recv, side, msg}}
    end
  end

  defp recv_iget(_conf, side, _name, _p, _q, msg, _rest), do: {:bad, {:recv, side, msg}}

  defp send_lab(conf, side, bit, cont, label) do
    if length(out_queue(conf, side)) >= conf.k do
      :wait
    else
      {:go, enqueue(conf, side, cont, {:lab, bit}), "#{side_name(conf, side)} #{label}"}
    end
  end

  defp prepare_send(conf, side, ty, val) do
    idx = idx_of(conf, side)
    ctx = ctx_of(conf, side)
    venv = venv_of(conf, side)

    case ready_of(val, venv, ctx, idx, conf.book) do
      :no ->
        :no

      {:ok, ready} ->
        if ty == :unknown do
          {:ok, :unknown, val, ready}
        else
          applied = apply_ty(idx, ty)

          case inhabits?(val, applied, idx, ctx, conf.book) do
            :yes -> {:ok, applied, val, ready}
            _ -> :no
          end
        end
    end
  end

  defp ready_of({:var, name}, venv, ctx, idx, book) do
    case Map.get(venv, name) do
      nil -> form_ready({:var, name}, ctx, idx, book)
      ready -> {:ok, ready}
    end
  end

  defp ready_of(val, _venv, ctx, idx, book), do: form_ready(val, ctx, idx, book)

  defp form_ready(val, ctx, idx, book) do
    case Muro.Session.form(val, ground(ctx, idx), book) do
      {:ok, :miss} -> :no
      {:ok, v} -> {:ok, v}
      _ -> :no
    end
  end

  defp accept_pay(_conf, _side, _ty, {:lab, _}), do: :bad

  defp accept_pay(conf, side, ty, {:pay, sty, orig, ready}) do
    recv_ty = apply_ty(idx_of(conf, side), ty)

    cond do
      sty != :unknown and sty != recv_ty ->
        :bad

      sty == :unknown and Muro.Session.answer(ready, recv_ty, %{}, conf.book) != :yes ->
        :bad

      true ->
        {:ok, recv_ty, orig, ready}
    end
  end

  defp commit_recv(conf, side, proc, rest, name, ty, orig, ready) do
    conf
    |> take(side, proc, rest)
    |> bind_recv(side, name, ty, orig, ready)
  end

  defp take(conf, :left, proc, rest), do: %{conf | lp: proc, r2l: rest}
  defp take(conf, :right, proc, rest), do: %{conf | rp: proc, l2r: rest}

  defp bind_recv(conf, _side, :_, _ty, _orig, _ready), do: conf

  defp bind_recv(conf, :left, name, ty, orig, ready) do
    %{
      conf
      | lv: Map.put(conf.lv, name, ready),
        lt: Map.put(conf.lt, name, ty),
        li: ext(conf.li, name, orig, ty)
    }
  end

  defp bind_recv(conf, :right, name, ty, orig, ready) do
    %{
      conf
      | rv: Map.put(conf.rv, name, ready),
        rt: Map.put(conf.rt, name, ty),
        ri: ext(conf.ri, name, orig, ty)
    }
  end

  defp enqueue(conf, :left, cont, msg), do: %{conf | lp: cont, l2r: conf.l2r ++ [msg]}
  defp enqueue(conf, :right, cont, msg), do: %{conf | rp: cont, r2l: conf.r2l ++ [msg]}

  defp dequeue(conf, side) do
    case in_queue(conf, side) do
      [] -> :empty
      [msg | rest] -> {:msg, msg, rest}
    end
  end

  defp pull(conf, :left), do: {conf.lp, conf.le}
  defp pull(conf, :right), do: {conf.rp, conf.re}

  defp put_env(conf, :left, env), do: %{conf | le: env}
  defp put_env(conf, :right, env), do: %{conf | re: env}

  defp out_queue(conf, :left), do: conf.l2r
  defp out_queue(conf, :right), do: conf.r2l

  defp in_queue(conf, :left), do: conf.r2l
  defp in_queue(conf, :right), do: conf.l2r

  defp idx_of(conf, :left), do: conf.li
  defp idx_of(conf, :right), do: conf.ri

  defp ctx_of(conf, :left), do: conf.lt
  defp ctx_of(conf, :right), do: conf.rt

  defp venv_of(conf, :left), do: conf.lv
  defp venv_of(conf, :right), do: conf.rv

  defp side_name(conf, :left), do: conf.left
  defp side_name(conf, :right), do: conf.right

  defp step_get(ty, name), do: Muro.Session.step_proc({:get, ty, name, :done})

  defp arm_label(:b0), do: "b0"
  defp arm_label(:b1), do: "b1"
  defp arm_label({:con, name, _}), do: "#{name}"
  defp arm_label(other), do: Muro.Session.show_value(other)

  defp render(msg, _conf, _trace) when is_binary(msg), do: msg

  defp render(:orphan, conf, trace), do: prose("orphan message", conf, trace, nil)
  defp render(:dead, conf, trace), do: prose("deadlock", conf, trace, nil)

  defp render({:recv, side, msg}, conf, trace) do
    prose("reception error", conf, trace, "head #{side_name(conf, side)} is #{show_msg(msg)}")
  end

  defp prose(kind, conf, trace, extra) do
    where = if trace == [], do: "", else: " after " <> Enum.join(trace, ", ")

    msg =
      "#{kind}#{where}: #{conf.left}: #{step_of(conf, :left)}; #{conf.right}: #{step_of(conf, :right)}; l2r: #{show_q(conf.l2r)}; r2l: #{show_q(conf.r2l)}"

    case extra do
      nil -> msg
      clause -> msg <> "; " <> clause
    end
  end

  defp step_of(conf, side) do
    {proc, env} = pull(conf, side)

    case Muro.Session.unwind_proc(proc, env) do
      {:ok, head, _} -> Muro.Session.step_proc(head)
      {:error, msg} -> msg
    end
  end

  defp show_q(queue), do: "[" <> Enum.map_join(queue, ", ", &show_msg/1) <> "]"

  defp show_msg({:pay, _, _, ready}), do: Muro.Session.show_value(ready)
  defp show_msg({:lab, false}), do: "pick0"
  defp show_msg({:lab, true}), do: "pick1"

  # A put that builds a value from a received name and then jumps back
  # to its own `rec` has no finite alphabet. A bare name is an echo.
  # A closed literal stays in the alphabet. One step that does not jump
  # back is not this refusal.
  defp cyclic_grow?(proc, book), do: grow_puts(proc, MapSet.new(), book)

  defp grow_puts(:done, _active, _book), do: false
  defp grow_puts(:stop, _active, _book), do: false

  defp grow_puts({:put, _ty, val, cont}, active, book) do
    (grow_val?(val, false, book) and reaches?(cont, active)) or grow_puts(cont, active, book)
  end

  defp grow_puts({:get, _ty, _name, cont}, active, book), do: grow_puts(cont, active, book)
  defp grow_puts({:pick0, cont}, active, book), do: grow_puts(cont, active, book)
  defp grow_puts({:pick1, cont}, active, book), do: grow_puts(cont, active, book)

  defp grow_puts({:cover, p, q}, active, book) do
    grow_puts(p, active, book) or grow_puts(q, active, book)
  end

  defp grow_puts({:iget, _name, p, q}, active, book) do
    grow_puts(p, active, book) or grow_puts(q, active, book)
  end

  defp grow_puts({:match, _name, arms}, active, book) do
    Enum.any?(arms, &grow_puts(Muro.Session.arm_body(&1), active, book))
  end

  defp grow_puts({:rec, name, body}, active, book) do
    grow_puts(body, MapSet.put(active, name), book)
  end

  defp grow_puts({:call, _name}, _active, _book), do: false

  # A received name at the top of a put is an echo. Under a constructor it
  # builds a larger payload each turn. A nullary constructor still written
  # as a name is that constructor, not a received value. A run application
  # is not a wrapping constructor: its result is the declared codomain.
  defp grow_val?({:var, name}, under?, book) do
    under? and not Muro.Session.nullary_ctor_name?(book, name)
  end

  defp grow_val?({:con, name, args}, under?, book) do
    inner = if Muro.Session.run_name?(book, name), do: under?, else: true
    Enum.any?(args, &grow_val?(&1, inner, book))
  end

  defp grow_val?({:tup, a, b}, _under?, book) do
    grow_val?(a, true, book) or grow_val?(b, true, book)
  end

  defp grow_val?({:rec, fields}, _under?, book) when is_list(fields) do
    Enum.any?(fields, fn {_name, val} -> grow_val?(val, true, book) end)
  end

  defp grow_val?({:rep, ix, elem}, _under?, book) do
    grow_val?(ix, true, book) or grow_val?(elem, true, book)
  end

  defp grow_val?({:nat, _n}, _under?, _book), do: false
  defp grow_val?(:b0, _under?, _book), do: false
  defp grow_val?(:b1, _under?, _book), do: false
  defp grow_val?(:tt, _under?, _book), do: false

  defp reaches?(:done, _active), do: false
  defp reaches?(:stop, _active), do: false
  defp reaches?({:put, _ty, _val, cont}, active), do: reaches?(cont, active)
  defp reaches?({:get, _ty, _name, cont}, active), do: reaches?(cont, active)
  defp reaches?({:pick0, cont}, active), do: reaches?(cont, active)
  defp reaches?({:pick1, cont}, active), do: reaches?(cont, active)
  defp reaches?({:cover, p, q}, active), do: reaches?(p, active) or reaches?(q, active)
  defp reaches?({:iget, _name, p, q}, active), do: reaches?(p, active) or reaches?(q, active)

  defp reaches?({:match, _name, arms}, active) do
    Enum.any?(arms, &reaches?(Muro.Session.arm_body(&1), active))
  end

  defp reaches?({:rec, name, body}, active), do: reaches?(body, MapSet.delete(active, name))

  defp reaches?({:call, name}, active), do: MapSet.member?(active, name)

  defp inhabits?({:var, name}, ty, idx, ctx, _book) do
    if held(ctx, idx, name) == ty, do: :yes, else: :no
  end

  defp inhabits?({:con, _, _} = val, ty, idx, ctx, book) do
    Muro.Session.answer(val, ty, ground(ctx, idx), book)
  end

  defp inhabits?(_val, _ty, _idx, _ctx, _book), do: :yes

  defp held(ctx, idx, name) do
    case Map.get(ctx, name) do
      nil -> nil
      stored -> apply_ty(idx, stored)
    end
  end

  defp ground(ctx, idx), do: Map.new(ctx, fn {name, ty} -> {name, apply_ty(idx, ty)} end)

  defp ext(idx, name, val, :nat) do
    case nexp(val) do
      nil -> Map.delete(idx, name)
      e -> Map.put(idx, name, e)
    end
  end

  defp ext(idx, name, _val, _ty), do: Map.delete(idx, name)

  defp nexp({:nat, n}) when is_integer(n) and n >= 0, do: {:lit, n}
  defp nexp({:var, name}), do: {:var, name}
  defp nexp(_), do: nil

  defp apply_ty(_idx, ty) when ty in [:nat, :bit, :unit, :unknown], do: ty
  defp apply_ty(idx, {:pair, a, b}), do: {:pair, apply_ty(idx, a), apply_ty(idx, b)}

  defp apply_ty(idx, {:rec, fields}) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, apply_ty(idx, ty)} end)}
  end

  defp apply_ty(idx, {:vec, elem, e}), do: {:vec, apply_ty(idx, elem), apply_ix(idx, e)}

  defp apply_ty(idx, {:dat, name, args}) do
    {:dat, name, Enum.map(args, &apply_ty(idx, &1))}
  end

  defp apply_ix(_idx, {:lit, _} = e), do: e

  defp apply_ix(idx, {:var, name}) do
    case Map.get(idx, name) do
      nil -> {:var, name}
      e -> e
    end
  end
end
