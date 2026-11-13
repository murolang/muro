defmodule Muro.Emit.Otp do
  @moduledoc """
  Emit each conforming process as a GenServer.

  A `conform` is one process. A `read` is one process. The actions are
  `Muro.Session.carry/2`: Agda's `skel`, with an unbound constructor
  resolved to the value the message carries. The server talks to one
  peer pid. The message carries the value. The place stays on the
  reading. A `meet` starts those two processes as each other's peer.
  `leave` stops with `{:shutdown, :abandon}`, which a monitor observes.
  `start/2` stops with `:normal` at `finish`. A paired meeting stays up
  after `finish` until its sends are acked, its queue is empty, and the
  peer has sent `{:muro_settled, _}`. Both then stop `:normal`. A peer
  exit that is not `:normal` is abandon, and so is a `:normal` exit that
  arrives before this process has settled. A `:normal` exit after this
  process has settled, while an id is still unacked or a token is still
  queued, is `{:shutdown, :orphan}` even when the peer sent no settled
  message. The same orphan is the stop when the peer has settled and a
  token is still held. A data or choice tuple whose arity does not match
  this process's cap, and whose `from` is the peer, stops
  `{:shutdown, :incompatible_wire}`. Another pid, and any other term, is
  ignored.

  An integer `buffer N` on a paired meeting gives each direction N send
  credits. A payload and a choice spend one credit each and carry a fresh
  send id. The credit for that id returns when its ack is applied, not
  when the token is queued. The outstanding set is ids sent whose ack
  is not yet applied, so it can include a consumed token awaiting that
  ack. The same id does not return a second credit. Ids are not reused.
  The set drops a retired id, so its size stays at most N; the counter
  grows with the number of sends.
  The sender yields while none remain. That yield applies a peer failure
  already recorded, and a later ack or failure still runs if the process
  stays up. Buffer 0 blocks every send. It is not a rendezvous. A meeting
  with no buffer stays an unbounded 3-tuple mailbox, with no credit and
  no per-send id. Paired completion on that meeting still waits for a
  clear local state and the peer's settled mark. `start/2` does not
  carry a buffer.

  Value binding: When a process has `get (k : Type) continuation`, the
  received value is checked against the type, but variable substitution
  in the continuation is not yet implemented in the OTP backend. The
  skeleton uses a witness value.

  An evidence payload is a nat on the channel. The evidence is a premise
  of the conformance derivation, not part of the process, so `skel` has
  no evidence to carry and the message is the nat alone.

  A declared data value is an atom when the constructor has no fields,
  and a tagged tuple when it has fields. `skel/1` leaves the constructor
  name as a variable. `carry/2` resolves an unbound one.

  A bit index is that bit on the channel. The receiver's skeleton holds
  both arms. `b0` takes the first and `b1` takes the second. The message
  is `{:muro, from, bit}`. It is not a choice label.

  The BEAM runs this server. The proof stops at the conformance
  derivation. `run` is not emitted here.
  """

  alias Muro.Emit.Name
  alias Muro.Session

  @doc """
  Render `book` as one Elixir file. `stem` is the source stem (`ping`).
  The module is that stem plus `Otp` (`PingOtp`).
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    case Muro.Emit.refuse_may_fail(book) do
      {:error, _} = err -> err
      :ok -> render_book(book, stem)
    end
  end

  defp render_book(book, stem) do
    parent = module_name(stem)
    mods = modules(book)
    meets = meetings(book)
    fragment = Session.run_fragment(book, run_names_in(mods, meets))
    decls = Session.payload_decls(book)

    {:ok, source(parent, mods, decls, fragment, host_clauses(book)) |> with_meetings(meets)}
  end

  @doc """
  The GenServer outline `render/2` draws from: module names, skeletons,
  mailbox, and the `handle_info` / `handle_call` clauses. The names are
  `module_name/1`, `Muro.Emit.elixir_modules/1`, and `Name.claim/2` on
  `Muro.Emit.elixir_base/1`. No source is written.
  """
  def outline(book, stem) when is_list(book) and is_binary(stem) do
    case Muro.Emit.refuse_may_fail(book) do
      {:error, _} = err -> err
      :ok -> outline_book(book, stem)
    end
  end

  defp outline_book(book, stem) do
    parent = module_name(stem)
    mods = modules(book)
    meets = meetings(book)
    hosts = host_clauses(book)

    names =
      [parent | Enum.map(mods, &elem(&1, 0))] ++ Enum.map(meets, &elem(&1, 0))

    clauses =
      [
        "use GenServer",
        "def start(skel, peer) when is_pid(peer)",
        "def init({skel, peer})",
        "def handle_info(:muro_go, %{skel: skel} = st)",
        "def handle_info({:muro, from, _value} = msg, %{peer: peer} = st)",
        "queue: []"
      ] ++
        host_lines(hosts) ++
        Enum.flat_map(mods, fn {name, skel} ->
          ["defmodule #{name} do", "#{parent}.start(#{inspect(skel)}, peer)"]
        end) ++ meeting_clauses(meets)

    signatures =
      Enum.map(mods, fn {name, skel} ->
        %{
          source: name,
          name: name,
          layout: skel,
          param_layouts: [],
          params: ["peer"],
          ret: "skel",
          export: true
        }
      end)

    {:ok,
     %{
       names: Enum.uniq(names),
       elixir: Muro.Emit.elixir_names(book),
       signatures: signatures,
       layouts: Enum.map(mods, fn {name, skel} -> %{name: name, layout: skel} end),
       clauses: clauses
     }}
  end

  defp host_lines(hosts) do
    hosts
    |> String.split("\n")
    |> Enum.map(&String.trim/1)
    |> Enum.reject(&(&1 == ""))
  end

  defp meeting_clauses([]) do
    []
  end

  defp meeting_clauses(meets) do
    [
      "def handle_call({:muro_peer, peer}, _from, %{peer: nil} = st)",
      "def init({skel, :open})"
    ] ++
      Enum.flat_map(meets, fn {name, left, right, buffer} ->
        ["def #{name} do", exchange_call(left, right, buffer)]
      end)
  end

  defp modules(book) do
    procs = Enum.filter(book, &process?/1)
    aliases = Muro.Emit.elixir_modules(Enum.map(procs, & &1.name))

    Enum.map(procs, fn %{name: name, proc: proc} ->
      {Map.fetch!(aliases, name), Session.carry(proc, book)}
    end)
  end

  defp process?(%{kind: :conform, proc: proc}) when not is_nil(proc), do: true
  defp process?(%{kind: :read, proc: proc}) when not is_nil(proc), do: true
  defp process?(_), do: false

  # A meeting names the peer. Both processes exist before either is told
  # to go, and each is monitored by the other from that moment.
  defp meetings(book) do
    # A meeting is `def name/0` beside every function this template defines.
    taken0 = Muro.Emit.Helpers.otp()

    {funs, _} =
      book
      |> Enum.filter(&match?(%{kind: :meet}, &1))
      |> Enum.reduce({[], taken0}, fn %{name: name, left: left, right: right} = meet,
                                      {acc, used} ->
        {fname, used} = Name.claim(Muro.Emit.elixir_base(name), used)

        {[{fname, skel_of(book, left), skel_of(book, right), Map.get(meet, :buffer)} | acc], used}
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

    Session.carry(proc, book)
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
        {:ok, muro_fresh(skel, nil, nil, nil)}
      end

      def init({skel, :open, cap}) when is_integer(cap) and cap >= 0 do
        {:ok, muro_fresh(skel, nil, nil, cap)}
      end

    """
  end

  defp peer_call do
    """
      @impl true
      def handle_call({:muro_peer, peer}, _from, %{peer: nil} = st) when is_pid(peer) do
        {:reply, :ok, %{st | peer: peer, mon: Process.monitor(peer), paired: true}}
      end

    """
  end

  defp meeting_funs(meets) do
    funs = Enum.map_join(meets, "\n\n", &meeting_fun/1)

    funs <> "\n\n" <> exchange_fun(meets) <> "\n"
  end

  defp meeting_fun({name, left, right, buffer}) do
    """
      def #{name} do
        #{exchange_call(left, right, buffer)}
      end
    """
    |> String.trim_trailing()
  end

  # Nil is two skeletons and no credit: the unbounded 3-tuple image.
  # An integer is the bound. Cap 0 is that integer, not the nil path.
  defp integer_cap?(cap) when is_integer(cap) and cap >= 0, do: true
  defp integer_cap?(_cap), do: false

  defp exchange_call(left, right, cap) when is_integer(cap) and cap >= 0 do
    "exchange(#{inspect(left)}, #{inspect(right)}, #{cap})"
  end

  defp exchange_call(left, right, _cap) do
    "exchange(#{inspect(left)}, #{inspect(right)})"
  end

  defp exchange_fun(meets) do
    unlimited = Enum.any?(meets, fn {_, _, _, cap} -> not integer_cap?(cap) end)
    bounded = Enum.any?(meets, fn {_, _, _, cap} -> integer_cap?(cap) end)

    heads =
      [
        unlimited &&
          """
            defp exchange(left_skel, right_skel) do
              muro_open_pair(left_skel, right_skel, nil)
            end
          """,
        bounded &&
          """
            defp exchange(left_skel, right_skel, cap) when is_integer(cap) and cap >= 0 do
              muro_open_pair(left_skel, right_skel, cap)
            end
          """
      ]
      |> Enum.filter(&is_binary/1)
      |> Enum.map_join("\n", &String.trim_trailing/1)

    (heads <>
       """

           defp muro_open_pair(left_skel, right_skel, cap) do
           with {:ok, left} <- GenServer.start(__MODULE__, muro_open_arg(left_skel, cap)),
                {:ok, right} <- open_peer(right_skel, left, cap) do
             :ok = GenServer.call(left, {:muro_peer, right})
             :ok = GenServer.call(right, {:muro_peer, left})
             ref_l = Process.monitor(left)
             ref_r = Process.monitor(right)
             send(left, :muro_go)
             send(right, :muro_go)
             {:ok, left, right, ref_l, ref_r}
           end
         end

         defp muro_open_arg(skel, cap) when is_integer(cap) and cap >= 0, do: {skel, :open, cap}
         defp muro_open_arg(skel, _cap), do: {skel, :open}

         defp open_peer(skel, sibling, cap) do
           case GenServer.start(__MODULE__, muro_open_arg(skel, cap)) do
             {:ok, pid} ->
               {:ok, pid}

             {:error, reason} ->
               GenServer.stop(sibling)
               {:error, reason}
           end
         end
       """)
    |> String.trim_trailing()
  end

  defp run_names_in(mods, meets) do
    skels =
      Enum.map(mods, fn {_mod, skel} -> skel end) ++
        Enum.flat_map(meets, fn {_name, left, right, _buffer} -> [left, right] end)

    skels |> Enum.flat_map(&run_names/1) |> Enum.uniq()
  end

  defp run_names({:run, name, args}) when is_binary(name) and is_list(args) do
    [name | Enum.flat_map(args, &run_names/1)]
  end

  defp run_names(tuple) when is_tuple(tuple),
    do: tuple |> Tuple.to_list() |> Enum.flat_map(&run_names/1)

  defp run_names(list) when is_list(list), do: Enum.flat_map(list, &run_names/1)
  defp run_names(map) when is_map(map), do: map |> Map.values() |> Enum.flat_map(&run_names/1)
  defp run_names(_), do: []

  defp host_clauses(book) do
    names = Muro.Emit.elixir_names(book)

    clauses =
      Enum.map(Muro.Emit.run_defs(book), fn %{name: name} ->
        host = Map.fetch!(names, name)
        ~s|defp muro_host(#{inspect(name)}), do: #{inspect(String.to_atom(host))}|
      end)

    Enum.join(clauses ++ [host_fallback()], "\n")
  end

  defp host_fallback do
    """
    defp muro_host(_name), do: nil
    """
    |> String.trim()
  end

  defp source(parent, mods, decls, fragment, hosts) do
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
        {:ok, muro_fresh(skel, peer, mon, nil)}
      end

      defp muro_fresh(skel, peer, mon, cap) do
        %{
          peer: peer,
          mon: mon,
          skel: skel,
          wait: nil,
          queue: [],
          bindings: %{},
          loops: %{},
          cap: cap,
          credit: if(is_integer(cap), do: cap, else: nil),
          next_send: 0,
          unacked: MapSet.new(),
          send_wait: nil,
          paired: false,
          phase: :run,
          peer_settled: false,
          peer_down: nil,
          told: false
        }
      end

      @impl true
      def handle_info(:muro_go, %{skel: skel} = st) when not is_nil(skel) do
        drive(skel, %{st | skel: nil})
      end

      # A `:normal` DOWN waits until protocol messages already queued
      # are applied. Success then requires this process to be settled
      # and clear. Before that, the stop is abandon. A settled process
      # that still holds a token stops `{:shutdown, :orphan}`, including
      # when the peer exits `:normal` without `{:muro_settled, _}`.
      # The peer-settled arm is that same reason when the settled message
      # has arrived and a token is still held. Any other reason abandons
      # immediately, including while parked on credit or on the handshake.
      # A known-peer data or choice tuple of the other cap's arity stops
      # `{:shutdown, :incompatible_wire}`.
      def handle_info({:DOWN, mon, :process, peer, reason}, %{mon: mon, peer: peer} = st) do
        if reason == :normal do
          muro_idle(%{st | peer_down: :normal})
        else
          {:stop, {:shutdown, :abandon}, st}
        end
      end

      # Credit returns only for an id this process still has outstanding.
      # A replay of that id, a never-issued id, or a 2-tuple ack does not
      # free a different send. `from` is the payload peer, not an
      # authentication of the BEAM sender.
      def handle_info({:muro_ack, from, id}, %{peer: peer, cap: cap, unacked: unacked} = st)
          when from == peer and is_integer(cap) and is_integer(id) do
        if MapSet.member?(unacked, id) do
          unacked = MapSet.delete(unacked, id)
          st = %{st | unacked: unacked, credit: cap - MapSet.size(unacked)}

          case st.send_wait do
            nil ->
              muro_idle(st)

            action ->
              drive(action, %{st | send_wait: nil})
          end
        else
          muro_idle(st)
        end
      end

      def handle_info({:muro_ack, from, _id}, %{peer: peer} = st) when from == peer do
        muro_idle(st)
      end

      def handle_info({:muro_ack, from}, %{peer: peer} = st) when from == peer do
        muro_idle(st)
      end

      def handle_info({:muro_settled, from}, %{peer: peer} = st) when from == peer do
        muro_idle(%{st | peer_settled: true})
      end

      def handle_info({:muro, from, id, value}, %{peer: peer} = st)
          when from == peer and is_integer(st.cap) and is_integer(id) do
        arrived({:muro, from, value}, st, id)
      end

      def handle_info({:muro_pick, from, id, bit}, %{peer: peer} = st)
          when from == peer and is_integer(st.cap) and is_integer(id) and bit in [:b0, :b1] do
        arrived({:muro_pick, from, bit}, st, id)
      end

      def handle_info({:muro, from, _value} = msg, %{peer: peer} = st)
          when from == peer and not is_integer(st.cap) do
        arrived(msg, st, nil)
      end

      def handle_info({:muro_pick, from, bit} = msg, %{peer: peer} = st)
          when from == peer and not is_integer(st.cap) and bit in [:b0, :b1] do
        arrived(msg, st, nil)
      end

      # The other arity, from this peer, is the other wire. An integer cap
      # speaks 4-tuples. A nil cap, and `start/2`, speak 3-tuples. A
      # non-integer id on a 4-tuple integer cap still falls through, and so
      # does a message whose `from` is not the peer.
      def handle_info({:muro, from, _value}, %{peer: peer} = st)
          when from == peer and is_integer(st.cap) do
        {:stop, {:shutdown, :incompatible_wire}, st}
      end

      def handle_info({:muro_pick, from, _bit}, %{peer: peer} = st)
          when from == peer and is_integer(st.cap) do
        {:stop, {:shutdown, :incompatible_wire}, st}
      end

      def handle_info({:muro, from, _id, _value}, %{peer: peer} = st)
          when from == peer and not is_integer(st.cap) do
        {:stop, {:shutdown, :incompatible_wire}, st}
      end

      def handle_info({:muro_pick, from, _id, _bit}, %{peer: peer} = st)
          when from == peer and not is_integer(st.cap) do
        {:stop, {:shutdown, :incompatible_wire}, st}
      end

      def handle_info(_msg, st), do: muro_idle(st)

      # A payload that arrives before the server reaches its next receive is
      # kept, in order, and read there. The peer can send as soon as start returns.
      # The id stays with the queued token so the ack names that send.
      defp arrived(msg, %{wait: nil, queue: queue} = st, id) do
        muro_idle(%{st | queue: queue ++ [{msg, id}]})
      end

      defp arrived(msg, %{wait: wait, bindings: bindings} = st, id) do
        case step(ready(wait, bindings), msg) do
          {:go, next} -> muro_on_consume(%{st | wait: nil}, next, id)
          {:bind, :_, _value, next} -> muro_on_consume(%{st | wait: nil}, next, id)
          {:bind, name, value, next} ->
            muro_on_consume(%{st | wait: nil, bindings: Map.put(bindings, name, value)}, next, id)

          {:bind_fields, pairs, next} ->
            muro_on_consume(%{st | wait: nil, bindings: store_all(bindings, pairs)}, next, id)

          {:unexpected, value} -> {:stop, {:shutdown, {:unexpected, value}}, st}
        end
      end

      # `start/2` is not paired: finish is `:normal` immediately. A paired
      # process records source finish and stays up until `muro_idle` can
      # exit. `leave` is abandon, not a normal completion.
      defp drive(:finish, %{paired: false} = st), do: {:stop, :normal, st}
      defp drive(:finish, st), do: muro_idle(%{st | phase: :settled})
      defp drive(:leave, st), do: {:stop, {:shutdown, :abandon}, st}

      defp drive({:loop, name, body}, %{loops: loops} = st) do
        drive(body, %{st | loops: Map.put(loops, name, body)})
      end

      defp drive({:jump, name}, %{loops: loops} = st) do
        drive(Map.fetch!(loops, name), st)
      end

      defp drive({:say, value, next}, %{bindings: bindings} = st) do
        muro_emit_token(st, :muro, substitute(value, bindings), {:say, value, next}, next)
      end

      defp drive({:choose, bit, next}, st) do
        muro_emit_token(st, :muro_pick, bit, {:choose, bit, next}, next)
      end

      defp drive({:hear, ty, name, next}, st), do: park({:hear, ty, name, next}, st)
      defp drive({:offer, left, right}, st), do: park({:offer, left, right}, st)

      defp drive({:index, name, left, right}, st) do
        park({:index, name, left, right}, st)
      end

      # `cap` nil is the unbuffered and `start/2` path: a 3-tuple, no id, no ack.
      # An integer cap stamps a fresh id and spends one slot in `unacked`.
      # At the cap the callback returns through `muro_idle`, so a DOWN
      # already recorded is applied. A later ack or DOWN still runs if the
      # process stays up.
      # Free slots are `cap - size(unacked)`. Membership, not that count,
      # decides whether an ack names this send. Ids are never reused, so a
      # retired id cannot free a later send. The set drops retired ids.
      defp muro_emit_token(%{cap: cap, peer: peer} = st, tag, payload, parked, next) do
        cond do
          not is_integer(cap) ->
            send(peer, {tag, self(), payload})
            drive(next, st)

          MapSet.size(st.unacked) < cap ->
            id = st.next_send
            unacked = MapSet.put(st.unacked, id)
            send(peer, {tag, self(), id, payload})

            drive(
              next,
              %{st | next_send: id + 1, unacked: unacked, credit: cap - MapSet.size(unacked)}
            )

          true ->
            muro_idle(%{st | send_wait: parked})
        end
      end

      defp muro_on_consume(st, next, id) do
        drive(next, muro_grant(st, id))
      end

      defp muro_grant(%{cap: cap, peer: peer} = st, id) when is_integer(cap) and is_integer(id) do
        send(peer, {:muro_ack, self(), id})
        st
      end

      defp muro_grant(st, _id), do: st

      # Local obligations are an empty unacked set, an empty queue, and no
      # credit park. Mailbox protocol messages are not obligations yet;
      # they are applied before a normal exit. `peer_down` wins over the
      # settle handshake so a crash already queued is not reported as success.
      defp muro_idle(%{peer_down: :normal} = st) do
        if muro_mailbox_quiet(), do: muro_down_stop(st), else: {:noreply, st}
      end

      defp muro_idle(%{peer_down: reason} = st) when not is_nil(reason) do
        {:stop, {:shutdown, :abandon}, st}
      end

      defp muro_idle(%{phase: :settled} = st), do: muro_conclude(st)
      defp muro_idle(st), do: {:noreply, st}

      defp muro_down_stop(%{paired: true, phase: :settled} = st) do
        if muro_clear(st), do: {:stop, :normal, st}, else: {:stop, {:shutdown, :orphan}, st}
      end

      defp muro_down_stop(st), do: {:stop, {:shutdown, :abandon}, st}

      defp muro_conclude(st) do
        cond do
          not muro_mailbox_quiet() ->
            {:noreply, st}

          muro_clear(st) ->
            st = muro_tell(st)

            if st.peer_settled do
              {:stop, :normal, st}
            else
              {:noreply, st}
            end

          st.peer_settled ->
            {:stop, {:shutdown, :orphan}, st}

          true ->
            {:noreply, st}
        end
      end

      defp muro_tell(%{told: true} = st), do: st

      defp muro_tell(%{paired: true, phase: :settled, peer: peer} = st) when is_pid(peer) do
        if muro_clear(st) do
          send(peer, {:muro_settled, self()})
          %{st | told: true}
        else
          st
        end
      end

      defp muro_tell(st), do: st

      defp muro_clear(%{unacked: unacked, queue: queue, send_wait: send_wait}) do
        MapSet.size(unacked) == 0 and queue == [] and send_wait == nil
      end

      defp muro_mailbox_quiet do
        {:messages, msgs} = Process.info(self(), :messages)
        not Enum.any?(msgs, &muro_control/1)
      end

      defp muro_control({:muro, _, _}), do: true
      defp muro_control({:muro, _, _, _}), do: true
      defp muro_control({:muro_pick, _, _}), do: true
      defp muro_control({:muro_pick, _, _, _}), do: true
      defp muro_control({:muro_ack, _, _}), do: true
      defp muro_control({:muro_ack, _, _, _}), do: true
      defp muro_control({:muro_settled, _}), do: true
      defp muro_control(:muro_go), do: true
      defp muro_control({:DOWN, _, :process, _, _}), do: true
      defp muro_control(_msg), do: false

      defp park(wait, %{queue: []} = st), do: muro_idle(%{st | wait: wait})

      defp park(wait, %{queue: [{msg, id} | rest], bindings: bindings} = st) do
        case step(ready(wait, bindings), msg) do
          {:go, next} ->
            muro_on_consume(%{st | wait: nil, queue: rest}, next, id)

          {:bind, :_, _value, next} ->
            # Anonymous binder, don't store
            muro_on_consume(%{st | wait: nil, queue: rest}, next, id)

          {:bind, name, value, next} ->
            muro_on_consume(
              %{st | wait: nil, queue: rest, bindings: Map.put(bindings, name, value)},
              next,
              id
            )

          {:bind_fields, pairs, next} ->
            muro_on_consume(
              %{st | wait: nil, queue: rest, bindings: store_all(bindings, pairs)},
              next,
              id
            )

          {:unexpected, value} ->
            {:stop, {:shutdown, {:unexpected, value}}, st}
        end
      end

      defp store_all(bindings, pairs) do
        Enum.reduce(pairs, bindings, fn
          {:_, _value}, acc -> acc
          {name, value}, acc -> Map.put(acc, name, value)
        end)
      end

      defp step({:hear, ty, name, {:pick, arms}}, {:muro, _, value}) do
        if payload?(ty, value) do
          case pick_arm(ty, value, arms) do
            {:ok, next, extra} ->
              pairs = if name == :_, do: extra, else: [{name, value} | extra]
              {:bind_fields, pairs, next}

            :error ->
              {:unexpected, value}
          end
        else
          {:unexpected, value}
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
      defp step({:index, name, left, _}, {:muro, _, :b0}), do: {:bind, name, :b0, left}
      defp step({:index, name, _, right}, {:muro, _, :b1}), do: {:bind, name, :b1, right}
      defp step(_wait, {:muro, _, value}), do: {:unexpected, value}
      defp step(_wait, {:muro_pick, _, bit}), do: {:unexpected, bit}

      # `b0` is the first arm and `b1` the second. A declared data value
      # takes the arm of its constructor, in declaration order. The order
      # is a list: inspecting the constructor map sorts its keys.
      # A named arm binds that constructor's fields. A positional arm does not.
      # A pair is the tuple `{a, b}`. A record is the map, read by the
      # keys fixed in the type, in that order.
      defp pick_arm(:bit, :b0, [arm, _]), do: open_pick(arm, "b0", [])
      defp pick_arm(:bit, :b1, [_, arm]), do: open_pick(arm, "b1", [])

      defp pick_arm({:pair, _, _}, {a, b}, [{:prod, {:pair, [x, y]}, next}])
           when is_atom(x) and is_atom(y) do
        {:ok, next, [{x, a}, {y, b}]}
      end

      defp pick_arm({:rec, fields}, map, [{:prod, {:rec, bs}, next}])
           when is_list(fields) and is_map(map) and is_list(bs) do
        keys = Enum.map(fields, fn {name, _} -> name end)
        got = Enum.map(bs, fn {name, _} -> name end)

        if keys == got and Enum.sort(Map.keys(map)) == Enum.sort(keys) do
          pairs = Enum.map(bs, fn {field, binder} -> {binder, Map.fetch!(map, field)} end)
          {:ok, next, pairs}
        else
          :error
        end
      end

      defp pick_arm({:dat, name, _}, value, arms) do
        case Map.get(data_decls(), name) do
          %{order: order, ctors: ctors} ->
            tag = tag_of(ctors, value)

            case Enum.find_index(order, &(&1 == tag)) do
              i when is_integer(i) ->
                case Enum.at(arms, i) do
                  nil -> :error
                  arm -> open_pick(arm, tag, fields_of_runtime(value))
                end

              _ ->
                :error
            end

          _ ->
            :error
        end
      end

      defp pick_arm(_, _, _), do: :error

      defp open_pick({:arm, ctor, binders, {:split, name, arms}}, expected, fields)
           when is_binary(ctor) and is_list(binders) and is_list(fields) and is_list(arms) do
        cond do
          ctor != expected ->
            :error

          length(binders) != length(fields) ->
            :error

          true ->
            case List.keyfind(Enum.zip(binders, fields), name, 0) do
              {^name, value} ->
                case pick_split(value, arms) do
                  {:ok, next, extra} -> {:ok, next, Enum.zip(binders, fields) ++ extra}
                  :error -> :error
                end

              nil ->
                :error
            end
        end
      end

      defp open_pick({:arm, ctor, binders, body}, expected, fields)
           when is_binary(ctor) and is_list(binders) and is_list(fields) do
        cond do
          ctor != expected -> :error
          length(binders) != length(fields) -> :error
          true -> {:ok, body, Enum.zip(binders, fields)}
        end
      end

      defp open_pick(arm, _expected, _fields), do: {:ok, arm, []}

      # A named split names its own constructors. The host label is
      # decoded once against those names. A positional split does not
      # name a declaration, so it keeps the arity fallback.
      defp pick_split(value, arms) do
        if named_arms(arms) do
          pick_named(value, arms)
        else
          pick_positional_split(value, arms)
        end
      end

      defp named_arms([{:arm, ctor, _, _} | rest]) when is_binary(ctor), do: named_arms(rest)
      defp named_arms([]), do: true
      defp named_arms(_), do: false

      defp pick_named(value, arms) do
        names = for {:arm, ctor, _, _} <- arms, do: ctor
        fields = fields_of_runtime(value)

        case raw_tag(value) do
          raw when is_binary(raw) ->
            case Muro.Emit.source_ctor(names, raw) do
              {:ok, tag} ->
                case named_index(arms, tag, 0) do
                  i when is_integer(i) -> open_pick(Enum.at(arms, i), tag, fields)
                  _ -> :error
                end

              :error ->
                :error
            end

          _ ->
            :error
        end
      end

      defp pick_positional_split(value, arms) do
        tag = split_tag(value, length(arms))
        fields = fields_of_runtime(value)

        case named_index(arms, tag, 0) do
          i when is_integer(i) ->
            open_pick(Enum.at(arms, i), tag, fields)

          _ ->
            pick_positional(value, tag, fields, arms)
        end
      end

      defp named_index([{:arm, c, _, _} | _], tag, i) when c == tag, do: i
      defp named_index([_ | rest], tag, i), do: named_index(rest, tag, i + 1)
      defp named_index([], _tag, _i), do: nil

      defp pick_positional(:b0, _tag, _fields, [arm, _]), do: open_pick(arm, "b0", [])
      defp pick_positional(:b1, _tag, _fields, [_, arm]), do: open_pick(arm, "b1", [])

      defp pick_positional(_value, tag, fields, arms) do
        case order_for(tag, length(arms)) do
          order when is_list(order) ->
            case Enum.find_index(order, &(&1 == tag)) do
              i when is_integer(i) ->
                case Enum.at(arms, i) do
                  nil -> :error
                  arm -> open_pick(arm, tag, fields)
                end

              _ ->
                :error
            end

          _ ->
            :error
        end
      end

      defp order_for(tag, n) do
        Enum.find_value(Map.values(data_decls()), fn
          %{order: order} when is_list(order) ->
            if length(order) == n and tag in order, do: order, else: nil

          _ ->
            nil
        end)
      end

      # Positional fallback only. A named split does not reach this.
      # The declaration is not named, so the host label is resolved
      # against each declaration of this constructor count.
      defp split_tag(value, n) do
        raw = raw_tag(value)

        found =
          if is_binary(raw) do
            Enum.find_value(Map.values(data_decls()), fn
              %{order: order, ctors: ctors} when is_list(order) and is_map(ctors) ->
                case Muro.Emit.source_ctor(Map.keys(ctors), raw) do
                  {:ok, name} ->
                    if length(order) == n and name in order, do: name, else: nil

                  :error ->
                    nil
                end

              _ ->
                nil
            end)
          end

        found || raw || ""
      end

      defp raw_tag(value) when is_atom(value), do: Atom.to_string(value)

      defp raw_tag(value) when is_tuple(value) and tuple_size(value) >= 1 do
        tag = elem(value, 0)
        if is_atom(tag), do: Atom.to_string(tag)
      end

      defp raw_tag(_), do: nil

      defp fields_of_runtime(value) when is_atom(value), do: []

      defp fields_of_runtime(value) when is_tuple(value) and tuple_size(value) >= 1 do
        [_tag | fields] = Tuple.to_list(value)
        fields
      end

      defp fields_of_runtime(_), do: []

      defp tag_of(ctors, value) when is_atom(value), do: ctor_source(ctors, value)

      defp tag_of(ctors, value) when is_tuple(value) and tuple_size(value) >= 1 do
        tag = elem(value, 0)
        if is_atom(tag), do: ctor_source(ctors, tag), else: ""
      end

      defp tag_of(_ctors, _), do: ""

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

      defp payload?({:dat, name, args}, value) when is_list(args) do
        case Map.get(data_decls(), name) do
          %{np: n, ctors: ctors} when length(args) == n ->
            dat_payload?(ctors, name, args, value)

          _ ->
            false
        end
      end

      defp payload?(_, _), do: false

      # A nullary constructor is an atom. A constructor with fields is a
      # tagged tuple. `{:par, i}` is a parameter of this declaration.
      # `{:self, args}` is this declaration. `{:dat, name, args}` is another.
      defp data_decls, do: #{inspect(decls, limit: :infinity)}

      defp run_book, do: #{inspect(fragment, limit: :infinity, charlists: :as_lists)}

      # One decode of the host atom against this declaration's constructors.
      defp ctor_source(ctors, tag) when is_atom(tag) do
        names = if is_map(ctors), do: Map.keys(ctors), else: []

        case Muro.Emit.source_ctor(names, Atom.to_string(tag)) do
          {:ok, name} -> name
          :error -> Atom.to_string(tag)
        end
      end

      defp dat_payload?(ctors, _dname, _args, value) when is_atom(value) do
        case Map.get(ctors, ctor_source(ctors, value)) do
          [] -> true
          _ -> false
        end
      end

      defp dat_payload?(ctors, dname, args, value) when is_tuple(value) and tuple_size(value) >= 1 do
        [tag | fields] = Tuple.to_list(value)

        if is_atom(tag) do
          case Map.get(ctors, ctor_source(ctors, tag)) do
            tmpl when is_list(tmpl) and length(tmpl) == length(fields) ->
              Enum.zip(tmpl, fields)
              |> Enum.all?(fn {field, got} -> payload?(inst_pay(field, dname, args), got) end)

            _ ->
              false
          end
        else
          false
        end
      end

      defp dat_payload?(_, _, _, _), do: false

      defp inst_pay({:par, i}, _dname, args), do: Enum.at(args, i)

      defp inst_pay({:pair, a, b}, dname, args) do
        {:pair, inst_pay(a, dname, args), inst_pay(b, dname, args)}
      end

      defp inst_pay({:self, ts}, dname, args) do
        {:dat, dname, Enum.map(ts, &inst_pay(&1, dname, args))}
      end

      defp inst_pay({:dat, name, ts}, dname, args) do
        {:dat, name, Enum.map(ts, &inst_pay(&1, dname, args))}
      end

      defp inst_pay(ty, _dname, _args), do: ty

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

      defp subst_ty({:dat, name, args}, bindings) do
        {:dat, name, Enum.map(args, &subst_ty(&1, bindings))}
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

      defp substitute({:run, name, args}, bindings) when is_binary(name) and is_list(args) do
        args = Enum.map(args, &substitute(&1, bindings))
        _ = muro_host(name)
        Muro.Session.eval_run(name, args, run_book())
      end

      defp substitute(tuple, bindings) when is_tuple(tuple) do
        tuple |> Tuple.to_list() |> Enum.map(&substitute(&1, bindings)) |> List.to_tuple()
      end

      defp substitute(map, bindings) when is_map(map) do
        Map.new(map, fn {k, v} -> {k, substitute(v, bindings)} end)
      end

      defp substitute(list, bindings) when is_list(list) do
        Enum.map(list, &substitute(&1, bindings))
      end

      defp substitute(value, _bindings), do: value

    #{indent(hosts, 2)}

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
