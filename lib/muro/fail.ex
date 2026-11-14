defmodule Muro.Fail do
  @moduledoc """
  A party of a two-party meeting may stop before `end`.

  The mark is `may fail` on that party. Every receive from a marked
  party needs a failure arm. A receive from a party that may not fail
  refuses one. The arm is not a step of the protocol: the success
  continuation is. A reason, when the arm names one, is a payload type
  the book declares. It is not a slot of the temporal graph.
  """

  @only "may fail is only a mark on a party of a meet"

  @doc """
  The message for `may fail` written outside a two-party `meet`.
  """
  def only_message, do: @only

  @doc """
  `may fail` printed back on the party it marks. `buffer` stays last.
  """
  def show_meet(%{kind: :meet, name: name, left: left, right: right} = meet) do
    flags = Map.get(meet, :may_fail, %{})
    buf = buffer_suffix(meet)

    "meet #{name} : #{party(left, Map.get(flags, :left, false))} with #{party(right, Map.get(flags, :right, false))}#{buf}"
  end

  @doc """
  Every receive in `left_proc` waits for the right party, and the other
  way around. `need` is that party's mark.
  """
  def arms(book, meet, left_def, right_def) do
    flags = Map.get(meet, :may_fail, %{})

    with :ok <-
           walk(left_def.proc, Map.get(flags, :right, false), meet.right, left_def.name, book) do
      walk(right_def.proc, Map.get(flags, :left, false), meet.left, right_def.name, book)
    end
  end

  @doc """
  `{:error, "c:mayfail\\n..."}` when a meeting marks a party. `:ok` when
  none does. Backends that do not emit the mark call this. OTP and the
  state machine do not. The checker does not.
  """
  def refuse_emit(book) when is_list(book) do
    if Enum.any?(book, &marked?/1) do
      {:error, "c:mayfail\nmay fail is checked and not emitted"}
    else
      :ok
    end
  end

  def marked?(%{kind: :meet} = meet) do
    flags = Map.get(meet, :may_fail, %{})
    Map.get(flags, :left, false) or Map.get(flags, :right, false)
  end

  def marked?(_), do: false

  defp party(name, true), do: "#{name} may fail"
  defp party(name, false), do: name

  defp buffer_suffix(%{buffer: n}) when is_integer(n), do: " buffer #{n}"
  defp buffer_suffix(_), do: ""

  defp walk({:on_fail, recv, reason, arm}, need?, peer, who, book) do
    with :ok <- reason_ok(reason, book),
         :ok <- extra(need?, recv, peer, who),
         :ok <- walk_under(recv, need?, peer, who, book) do
      walk(arm, need?, peer, who, book)
    end
  end

  defp walk({:get, _, _, _} = recv, true, peer, who, _book) do
    {:error, "#{who}: #{Muro.Session.step_proc(recv)} does not handle failure of #{peer}"}
  end

  defp walk({:get, _, _, body}, false, peer, who, book),
    do: walk(body, false, peer, who, book)

  defp walk({:iget, _, _, _} = recv, true, peer, who, _book) do
    {:error, "#{who}: #{Muro.Session.step_proc(recv)} does not handle failure of #{peer}"}
  end

  defp walk({:iget, _, p, q}, false, peer, who, book) do
    with :ok <- walk(p, false, peer, who, book), do: walk(q, false, peer, who, book)
  end

  defp walk({:cover, _, _} = recv, true, peer, who, _book) do
    {:error, "#{who}: #{Muro.Session.step_proc(recv)} does not handle failure of #{peer}"}
  end

  defp walk({:cover, p, q}, false, peer, who, book) do
    with :ok <- walk(p, false, peer, who, book), do: walk(q, false, peer, who, book)
  end

  defp walk({:put, _, _, p}, need?, peer, who, book), do: walk(p, need?, peer, who, book)
  defp walk({:pick0, p}, need?, peer, who, book), do: walk(p, need?, peer, who, book)
  defp walk({:pick1, p}, need?, peer, who, book), do: walk(p, need?, peer, who, book)

  defp walk({:match, _, arms}, need?, peer, who, book) do
    Enum.reduce_while(arms, :ok, fn arm, :ok ->
      case walk(Muro.Session.arm_body(arm), need?, peer, who, book) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp walk({:rec, _, body}, need?, peer, who, book), do: walk(body, need?, peer, who, book)
  defp walk({:call, _}, _need?, _peer, _who, _book), do: :ok
  defp walk(:done, _need?, _peer, _who, _book), do: :ok
  defp walk(:stop, _need?, _peer, _who, _book), do: :ok

  defp walk(_other, _need?, _peer, who, _book) do
    {:error, "#{who}: unknown process"}
  end

  defp walk_under({:get, _, _, body}, need?, peer, who, book),
    do: walk(body, need?, peer, who, book)

  defp walk_under({:iget, _, p, q}, need?, peer, who, book) do
    with :ok <- walk(p, need?, peer, who, book), do: walk(q, need?, peer, who, book)
  end

  defp walk_under({:cover, p, q}, need?, peer, who, book) do
    with :ok <- walk(p, need?, peer, who, book), do: walk(q, need?, peer, who, book)
  end

  defp walk_under(other, need?, peer, who, book), do: walk(other, need?, peer, who, book)

  defp extra(true, _recv, _peer, _who), do: :ok

  defp extra(false, recv, peer, who) do
    {:error,
     "#{who}: #{Muro.Session.step_proc(recv)} has a failure arm, and #{peer} may not fail"}
  end

  defp reason_ok(nil, _book), do: :ok
  defp reason_ok({ty, _name}, book), do: pay_known(ty, book)

  defp pay_known(:nat, _book), do: :ok
  defp pay_known(:bit, _book), do: :ok
  defp pay_known(:unit, _book), do: :ok

  defp pay_known({:pair, a, b}, book) do
    with :ok <- pay_known(a, book), do: pay_known(b, book)
  end

  defp pay_known({:rec, fields}, book) when is_list(fields) do
    Enum.reduce_while(fields, :ok, fn {_, ty}, :ok ->
      case pay_known(ty, book) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp pay_known({:vec, elem, _}, book), do: pay_known(elem, book)

  defp pay_known({:dat, name, args}, book) do
    if Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
      Enum.reduce_while(args, :ok, fn arg, :ok ->
        case pay_known(arg, book) do
          :ok -> {:cont, :ok}
          err -> {:halt, err}
        end
      end)
    else
      {:error, "unknown payload #{name}"}
    end
  end

  defp pay_known(_, _), do: {:error, "expected a payload"}
end
