defmodule Muro.Emit.Otp do
  @moduledoc """
  Emit each conforming process as a GenServer.

  A `conform` is one process. A `read` is one process. The actions
  are `Muro.Session.skel/1`, Agda's `skel`. The server talks to one
  peer pid. The message carries the value. The place stays on the
  reading. A `meet` starts those
  two processes as each other's peer. `leave` stops with
  `{:shutdown, :abandon}`, which a monitor observes. `finish` stops
  with `:normal`.

  Value binding: When a process has `get (k : Type) continuation`, the
  received value is checked against the type, but variable substitution
  in the continuation is not yet implemented in the OTP backend. The
  skeleton uses a witness value.

  The BEAM runs this server. The proof stops at the conformance
  derivation. `run` is not emitted here.
  """

  alias Muro.Session

  @doc """
  Render `book` as one Elixir file. `stem` is the source stem (`ping`).
  The module is that stem plus `Otp` (`PingOtp`).
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    parent = module_name(stem)
    mods = modules(book)
    {:ok, source(parent, mods) |> with_meetings(meetings(book))}
  end

  defp modules(book) do
    {mods, _} =
      book
      |> Enum.filter(&process?/1)
      |> Enum.reduce({[], MapSet.new()}, fn %{name: name, proc: proc}, {acc, used} ->
        {mod, used} = claim(camel(name), used)
        {[{mod, Session.skel(proc)} | acc], used}
      end)

    Enum.reverse(mods)
  end

  defp process?(%{kind: :conform, proc: proc}) when not is_nil(proc), do: true
  defp process?(%{kind: :read, proc: proc}) when not is_nil(proc), do: true
  defp process?(_), do: false

  # A meeting names the peer. Both processes exist before either is told
  # to go, and each is monitored by the other from that moment.
  defp meetings(book) do
    {funs, _} =
      book
      |> Enum.filter(&match?(%{kind: :meet}, &1))
      |> Enum.reduce({[], MapSet.new()}, fn %{name: name, left: left, right: right},
                                            {acc, used} ->
        {fname, used} = claim(fun_base(name), used)
        {[{fname, skel_of(book, left), skel_of(book, right)} | acc], used}
      end)

    Enum.reverse(funs)
  end

  defp skel_of(book, name) do
    %{proc: proc} =
      Enum.find(book, fn
        %{kind: kind, name: ^name, proc: proc}
        when kind in [:conform, :read] and not is_nil(proc) ->
          true

        _ ->
          false
      end)

    Session.skel(proc)
  end

  # `end`, `do`, and the other reserved words are not function names.
  defp fun_base(name) do
    base = String.replace(name, "-", "_")

    if base in ~w(end do else catch rescue after fn when and or not in) do
      "muro_#{base}"
    else
      base
    end
  end

  defp with_meetings(src, []), do: src

  defp with_meetings(src, meets) do
    src
    |> splice(
      "  # A reading is this same process. The server talks to one peer.\n",
      "  # A reading is this same process. The server talks to one peer.\n  # A meeting starts the two processes as each other's peer.\n"
    )
    |> splice(
      "  @impl true\n  def init({skel, peer}) do\n",
      meeting_funs(meets) <>
        "\n  @impl true\n" <> open_init() <> "  def init({skel, peer}) do\n"
    )
    |> splice(
      "  @impl true\n  def handle_info(:muro_go",
      peer_call() <> "  @impl true\n  def handle_info(:muro_go"
    )
  end

  defp splice(src, anchor, replacement) do
    case String.split(src, anchor, parts: 2) do
      [pre, post] -> pre <> replacement <> post
      _ -> raise "otp template is missing an anchor"
    end
  end

  defp open_init do
    """
      def init({skel, :open}) do
        {:ok, %{peer: nil, mon: nil, skel: skel, wait: nil, queue: [], bindings: %{}}}
      end

    """
  end

  defp peer_call do
    """
      @impl true
      def handle_call({:muro_peer, peer}, _from, %{peer: nil} = st) when is_pid(peer) do
        {:reply, :ok, %{st | peer: peer, mon: Process.monitor(peer)}}
      end

    """
  end

  defp meeting_funs(meets) do
    funs = Enum.map_join(meets, "\n\n", &meeting_fun/1)

    funs <> "\n\n" <> exchange_fun() <> "\n"
  end

  defp meeting_fun({name, left, right}) do
    """
      def #{name} do
        exchange(#{inspect(left)}, #{inspect(right)})
      end
    """
    |> String.trim_trailing()
  end

  defp exchange_fun do
    """
      defp exchange(left_skel, right_skel) do
        with {:ok, left} <- GenServer.start(__MODULE__, {left_skel, :open}),
             {:ok, right} <- open_peer(right_skel, left) do
          :ok = GenServer.call(left, {:muro_peer, right})
          :ok = GenServer.call(right, {:muro_peer, left})
          ref_l = Process.monitor(left)
          ref_r = Process.monitor(right)
          send(left, :muro_go)
          send(right, :muro_go)
          {:ok, left, right, ref_l, ref_r}
        end
      end

      defp open_peer(skel, sibling) do
        case GenServer.start(__MODULE__, {skel, :open}) do
          {:ok, pid} ->
            {:ok, pid}

          {:error, reason} ->
            GenServer.stop(sibling)
            {:error, reason}
        end
      end
    """
    |> String.trim_trailing()
  end

  defp source(parent, mods) do
    children = Enum.map_join(mods, "\n\n", &child(parent, &1))

    """
    defmodule #{parent} do
      # Generated by Muro. The BEAM runs this process.
      # The proof stops at the conformance derivation.
      # A reading is this same process. The server talks to one peer.
      # The message carries the value.
      use GenServer

      def start(skel, peer) when is_pid(peer) do
        case GenServer.start(__MODULE__, {skel, peer}) do
          {:ok, pid} ->
            ref = Process.monitor(pid)
            send(pid, :muro_go)
            {:ok, pid, ref}

          other ->
            other
        end
      end

      @impl true
      def init({skel, peer}) do
        mon = Process.monitor(peer)
        {:ok, %{peer: peer, mon: mon, skel: skel, wait: nil, queue: [], bindings: %{}}}
      end

      @impl true
      def handle_info(:muro_go, %{skel: skel} = st) when not is_nil(skel) do
        drive(skel, %{st | skel: nil})
      end

      def handle_info({:DOWN, mon, :process, peer, _}, %{mon: mon, peer: peer} = st) do
        {:stop, {:shutdown, :abandon}, st}
      end

      def handle_info({:muro, from, _value} = msg, %{peer: peer} = st) when from == peer do
        arrived(msg, st)
      end

      def handle_info({:muro_pick, from, bit} = msg, %{peer: peer} = st)
          when from == peer and bit in [:b0, :b1] do
        arrived(msg, st)
      end

      def handle_info(_msg, st), do: {:noreply, st}

      # A payload that arrives before the server reaches its next receive is
      # kept, in order, and read there. The peer can send as soon as start returns.
      defp arrived(msg, %{wait: nil, queue: queue} = st) do
        {:noreply, %{st | queue: queue ++ [msg]}}
      end

      defp arrived(msg, %{wait: wait, bindings: bindings} = st) do
        case step(ready(wait, bindings), msg) do
          {:go, next} -> drive(next, %{st | wait: nil})
          {:bind, :_, _value, next} -> drive(next, %{st | wait: nil})
          {:bind, name, value, next} -> drive(next, %{st | wait: nil, bindings: Map.put(bindings, name, value)})
          {:unexpected, value} -> {:stop, {:shutdown, {:unexpected, value}}, st}
        end
      end

      defp drive(:finish, st), do: {:stop, :normal, st}
      defp drive(:leave, st), do: {:stop, {:shutdown, :abandon}, st}

      defp drive({:say, value, next}, %{peer: peer, bindings: bindings} = st) do
        resolved = substitute(value, bindings)
        send(peer, {:muro, self(), resolved})
        drive(next, st)
      end

      defp drive({:choose, bit, next}, %{peer: peer} = st) do
        send(peer, {:muro_pick, self(), bit})
        drive(next, st)
      end

      defp drive({:hear, ty, name, next}, st), do: park({:hear, ty, name, next}, st)
      defp drive({:offer, left, right}, st), do: park({:offer, left, right}, st)

      defp park(wait, %{queue: []} = st), do: {:noreply, %{st | wait: wait}}

      defp park(wait, %{queue: [msg | rest], bindings: bindings} = st) do
        case step(ready(wait, bindings), msg) do
          {:go, next} ->
            drive(next, %{st | wait: nil, queue: rest})

          {:bind, :_, _value, next} ->
            # Anonymous binder, don't store
            drive(next, %{st | wait: nil, queue: rest})

          {:bind, name, value, next} ->
            drive(next, %{st | wait: nil, queue: rest, bindings: Map.put(bindings, name, value)})

          {:unexpected, value} ->
            {:stop, {:shutdown, {:unexpected, value}}, st}
        end
      end

      defp step({:hear, ty, name, next}, {:muro, _, value}) do
        if payload?(ty, value) do
          {:bind, name, value, next}
        else
          {:unexpected, value}
        end
      end

      defp step({:offer, left, _}, {:muro_pick, _, :b0}), do: {:go, left}
      defp step({:offer, _, right}, {:muro_pick, _, :b1}), do: {:go, right}
      defp step(_wait, {:muro, _, value}), do: {:unexpected, value}
      defp step(_wait, {:muro_pick, _, bit}), do: {:unexpected, bit}

      defp payload?(:nat, n) when is_integer(n) and n >= 0, do: true
      defp payload?(:bit, bit) when bit in [:b0, :b1], do: true
      defp payload?(:unit, :tt), do: true
      defp payload?({:pair, a, b}, {x, y}), do: payload?(a, x) and payload?(b, y)

      defp payload?({:rec, fields}, map) when is_list(fields) and is_map(map) do
        names = Enum.map(fields, fn {name, _} -> name end)

        Enum.sort(Map.keys(map)) == Enum.sort(names) and
          Enum.all?(fields, fn {name, ty} -> payload?(ty, Map.get(map, name)) end)
      end

      defp payload?({:vec, elem, {:lit, n}}, list)
           when is_list(list) and is_integer(n) and n >= 0 do
        length(list) == n and Enum.all?(list, &payload?(elem, &1))
      end

      defp payload?(_, _), do: false

      defp ready({:hear, ty, name, next}, bindings) do
        {:hear, subst_ty(ty, bindings), name, next}
      end

      defp ready(wait, _bindings), do: wait

      defp subst_ty({:pair, a, b}, bindings), do: {:pair, subst_ty(a, bindings), subst_ty(b, bindings)}

      defp subst_ty({:rec, fields}, bindings) when is_list(fields) do
        {:rec, Enum.map(fields, fn {name, ty} -> {name, subst_ty(ty, bindings)} end)}
      end

      defp subst_ty({:vec, elem, e}, bindings) do
        {:vec, subst_ty(elem, bindings), subst_ix(e, bindings)}
      end

      defp subst_ty(ty, _bindings), do: ty

      defp subst_ix({:var, name}, bindings) do
        case Map.get(bindings, name) do
          n when is_integer(n) and n >= 0 -> {:lit, n}
          _ -> {:var, name}
        end
      end

      defp subst_ix(e, _bindings), do: e

      defp substitute({:var, name}, bindings) do
        Map.get(bindings, name, {:var, name})
      end

      defp substitute({:rep, {:var, name}, val}, bindings) do
        case Map.get(bindings, name) do
          n when is_integer(n) and n >= 0 ->
            List.duplicate(substitute(val, bindings), n)

          _ ->
            {:rep, {:var, name}, substitute(val, bindings)}
        end
      end

      defp substitute({:rep, n, val}, bindings) when is_integer(n) and n >= 0 do
        List.duplicate(substitute(val, bindings), n)
      end

      defp substitute({a, b}, bindings) do
        {substitute(a, bindings), substitute(b, bindings)}
      end

      defp substitute(map, bindings) when is_map(map) do
        Map.new(map, fn {k, v} -> {k, substitute(v, bindings)} end)
      end

      defp substitute(list, bindings) when is_list(list) do
        Enum.map(list, &substitute(&1, bindings))
      end

      defp substitute(value, _bindings), do: value

    #{indent(children, 2)}
    end
    """
  end

  defp child(parent, {name, skel}) do
    """
    defmodule #{name} do
      def start(peer) when is_pid(peer) do
        #{parent}.start(#{inspect(skel)}, peer)
      end
    end
    """
  end

  defp module_name(stem) do
    stem
    |> String.replace("-", "_")
    |> Macro.camelize()
    |> Kernel.<>("Otp")
  end

  defp camel(name) do
    name
    |> String.replace("-", "_")
    |> Macro.camelize()
  end

  defp claim(base, used) do
    name = if MapSet.member?(used, base), do: bump(base, 2, used), else: base
    {name, MapSet.put(used, name)}
  end

  defp bump(base, i, used) do
    name = "#{base}#{i}"

    if MapSet.member?(used, name), do: bump(base, i + 1, used), else: name
  end

  defp indent(code, n) do
    pad = String.duplicate(" ", n)

    code
    |> String.trim_trailing()
    |> String.split("\n")
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> pad <> line
    end)
  end
end
