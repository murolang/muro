defmodule Muro.Emit.Otp do
  @moduledoc """
  Emit each conforming process as a GenServer.

  A `conform` is one process. A `read` is one process. The actions are
  `Muro.Session.carry/2`: Agda's `skel`, with an unbound constructor
  resolved to the value the message carries. The server talks to one
  peer pid. The message carries the value. The place stays on the
  reading. A `meet` starts those two processes as each other's peer.
  `leave` stops with `{:shutdown, :abandon}`, which a monitor observes.
  `finish` stops with `:normal`.

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

  alias Muro.Session

  @doc """
  Render `book` as one Elixir file. `stem` is the source stem (`ping`).
  The module is that stem plus `Otp` (`PingOtp`).
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    parent = module_name(stem)
    mods = modules(book)
    meets = meetings(book)
    fragment = Session.run_fragment(book, run_names_in(mods, meets))
    {:ok, source(parent, mods, Session.payload_decls(book), fragment) |> with_meetings(meets)}
  end

  defp modules(book) do
    {mods, _} =
      book
      |> Enum.filter(&process?/1)
      |> Enum.reduce({[], MapSet.new()}, fn %{name: name, proc: proc}, {acc, used} ->
        {mod, used} = claim(camel(name), used)
        {[{mod, Session.carry(proc, book)} | acc], used}
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

    Session.carry(proc, book)
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
        {:ok, %{peer: nil, mon: nil, skel: skel, wait: nil, queue: [], bindings: %{}, loops: %{}}}
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

  defp run_names_in(mods, meets) do
    skels =
      Enum.map(mods, fn {_mod, skel} -> skel end) ++
        Enum.flat_map(meets, fn {_name, left, right} -> [left, right] end)

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

  defp source(parent, mods, decls, fragment) do
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
        {:ok, %{peer: peer, mon: mon, skel: skel, wait: nil, queue: [], bindings: %{}, loops: %{}}}
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
          {:bind_fields, pairs, next} -> drive(next, %{st | wait: nil, bindings: store_all(bindings, pairs)})
          {:unexpected, value} -> {:stop, {:shutdown, {:unexpected, value}}, st}
        end
      end

      defp drive(:finish, st), do: {:stop, :normal, st}
      defp drive(:leave, st), do: {:stop, {:shutdown, :abandon}, st}

      defp drive({:loop, name, body}, %{loops: loops} = st) do
        drive(body, %{st | loops: Map.put(loops, name, body)})
      end

      defp drive({:jump, name}, %{loops: loops} = st) do
        drive(Map.fetch!(loops, name), st)
      end

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

      defp drive({:index, name, left, right}, st) do
        park({:index, name, left, right}, st)
      end

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

          {:bind_fields, pairs, next} ->
            drive(next, %{st | wait: nil, queue: rest, bindings: store_all(bindings, pairs)})

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
      defp pick_arm(:bit, :b0, [arm, _]), do: open_pick(arm, "b0", [])
      defp pick_arm(:bit, :b1, [_, arm]), do: open_pick(arm, "b1", [])

      defp pick_arm({:dat, name, _}, value, arms) do
        case Map.get(data_decls(), name) do
          %{order: order} ->
            tag = tag_of(value)

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

      defp open_pick({:arm, ctor, binders, body}, expected, fields)
           when is_binary(ctor) and is_list(binders) and is_list(fields) do
        cond do
          ctor != expected -> :error
          length(binders) != length(fields) -> :error
          true -> {:ok, body, Enum.zip(binders, fields)}
        end
      end

      defp open_pick(arm, _expected, _fields), do: {:ok, arm, []}

      defp fields_of_runtime(value) when is_atom(value), do: []

      defp fields_of_runtime(value) when is_tuple(value) and tuple_size(value) >= 1 do
        [_tag | fields] = Tuple.to_list(value)
        fields
      end

      defp fields_of_runtime(_), do: []

      defp tag_of(value) when is_atom(value), do: Atom.to_string(value)

      defp tag_of(value) when is_tuple(value) and tuple_size(value) >= 1 do
        tag = elem(value, 0)
        if is_atom(tag), do: Atom.to_string(tag), else: ""
      end

      defp tag_of(_), do: ""

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

      defp dat_payload?(ctors, _dname, _args, value) when is_atom(value) do
        case Map.get(ctors, Atom.to_string(value)) do
          [] -> true
          _ -> false
        end
      end

      defp dat_payload?(ctors, dname, args, value) when is_tuple(value) and tuple_size(value) >= 1 do
        [tag | fields] = Tuple.to_list(value)

        if is_atom(tag) do
          case Map.get(ctors, Atom.to_string(tag)) do
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
