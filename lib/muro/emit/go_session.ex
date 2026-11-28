defmodule Muro.Emit.Go.Session do
  @moduledoc false

  alias Muro.Emit.Go.Match
  alias Muro.Emit.Name

  @action ~w(send recv dsend drecv esend erecv isend irecv choose branch)a

  @doc false
  def compile(sess, entry, ctx) do
    acc = %{
      next: 0,
      states: %{},
      by_step: %{},
      recs: %{},
      counts: %{},
      root: entry.proto,
      self: sess.name,
      error: nil,
      decls: ctx.decls,
      reprs: ctx.reprs,
      match: ctx.match,
      fails: if(ctx.marked, do: ctx.fails, else: %{})
    }

    case land(entry.proto, acc, [], []) do
      {{:error, msg}, _} ->
        {:error, msg}

      {start, acc} ->
        acc = attach_fails(acc)

        cond do
          acc.error != nil ->
            {:error, acc.error}

          true ->
            {:ok,
             %{
               name: sess.name,
               params: Enum.map(entry.params, &Match.source_name/1),
               start: normalize(start),
               states: ordered(acc),
               match: acc.match,
               down: ctx.marked
             }}
        end
    end
  end

  @doc false
  def render(image, go_name, mod, taken) when is_struct(taken, MapSet) do
    states = image.states
    labels = Map.new(states, &{&1.id, &1.label})
    done = go_name <> "StateDone"
    stop = go_name <> "StateStop"
    stuck = go_name <> "StateStuck"
    invalid = go_name <> "StateInvalid"
    has_stop = Enum.any?(states, &stop?(&1)) or image.start == :stop

    ctx = %{
      go: go_name,
      mod: mod,
      labels: labels,
      done: done,
      stop: stop,
      stuck: stuck,
      invalid: invalid,
      has_stop: has_stop,
      states: states,
      needs: MapSet.new()
    }

    {start_state, _start_env, needs} = start_code(image, ctx)
    ctx = %{ctx | needs: MapSet.union(ctx.needs, needs)}
    {methods, needs} = methods(image, ctx)
    ctx = %{ctx | needs: MapSet.union(ctx.needs, needs)}
    taken = MapSet.union(taken, session_defined(image, go_name, ctx))
    {ctor, taken} = constructor(image, go_name, start_state, taken)

    src = """
    // #{go_name} is one end of session #{image.name}.
    // The zero value is not started: Step and Down report an illegal transition.
    // #{go_name} is not safe for concurrent use.
    type #{go_name} struct {
    \tstate #{go_name}State
    \tready bool
    \tenv   map[string]Value
    }

    // #{go_name}State is the resting position of #{go_name}.
    type #{go_name}State uint8

    const (
    \t// #{invalid} is the zero #{go_name}.
    \t#{invalid} #{go_name}State = iota
    #{const_lines(states, go_name)}#{done_line(done, states)}\t// #{stuck} is a protocol position with no step.
    \t#{stuck}
    #{if has_stop, do: "\t// #{stop} is the failure arm stop.\n\t#{stop}\n", else: ""})

    // String returns the state name.
    func (s #{go_name}State) String() string {
    \tswitch s {
    \tcase #{invalid}:
    \t\treturn "invalid"
    #{string_lines(states, go_name)}\tcase #{done}:
    \t\treturn "done"
    \tcase #{stuck}:
    \t\treturn "stuck"
    #{if has_stop, do: "\tcase #{stop}:\n\t\treturn \"stop\"\n", else: ""}\tdefault:
    \t\treturn "state"
    \t}
    }

    // New#{go_name} starts #{go_name} at its first step.
    #{ctor}

    // State returns the resting position. The zero value is invalid.
    func (m *#{go_name}) State() #{go_name}State {
    \tif m == nil || !m.ready {
    \t\treturn #{invalid}
    \t}
    \treturn m.state
    }

    // Done reports whether the session has reached end.
    func (m *#{go_name}) Done() bool {
    \treturn m != nil && m.ready && m.state == #{done}
    }

    // Expected is the next event, "done", "stop", or "start".
    func (m *#{go_name}) Expected() string {
    \tif m == nil || !m.ready {
    \t\treturn "start"
    \t}
    \tswitch m.state {
    #{expect_lines(states, go_name)}\tcase #{done}:
    \t\treturn "done"
    \tcase #{stuck}:
    \t\treturn "done"
    #{if has_stop, do: "\tcase #{stop}:\n\t\treturn \"stop\"\n", else: ""}\tdefault:
    \t\treturn "done"
    \t}
    }

    // Step takes one send or receive. A refused step leaves the value unchanged.
    func (m *#{go_name}) Step(ev Event) error {
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{go_name}", "#{invalid_string()}", "start", muroEvent(ev))
    \t}
    \tswitch ev := ev.(type) {
    \tcase Send:
    \t\treturn m.stepSend(ev.Value)
    \tcase Recv:
    \t\treturn m.stepRecv(ev.Value)
    \tdefault:
    \t\treturn muroIllegal("#{go_name}", m.State().String(), m.Expected(), muroEvent(ev))
    \t}
    }

    #{methods}
    """

    {src, ctx.needs, image.match, taken}
  end

  defp invalid_string, do: "invalid"

  defp constructor(%{params: []}, go, start_state, taken) do
    {"""
     func New#{go}() #{go} {
     \treturn #{go}{state: #{start_state}, ready: true, env: map[string]Value{}}
     }
     """, taken}
  end

  defp constructor(%{params: params, name: session}, go, start_state, taken) do
    {spellings, taken} =
      Enum.map_reduce(params, taken, fn name, taken ->
        Name.claim(go_base(name), taken)
      end)

    args = Enum.map_join(spellings, ", ", &"#{&1} int")

    checks =
      spellings
      |> Enum.with_index(1)
      |> Enum.map_join("", fn {spelling, i} ->
        message = string_lit("session #{session}: argument #{i} is not a nat")

        """
        \tif #{spelling} < 0 {
        \t\treturn #{go}{}, &ArgumentError{Message: #{message}}
        \t}
        """
      end)

    binds =
      params
      |> Enum.zip(spellings)
      |> Enum.map_join(", ", fn {name, spelling} -> "#{Match.gq(name)}: Nat(#{spelling})" end)

    {"""
     func New#{go}(#{args}) (#{go}, error) {
     #{checks}\treturn #{go}{state: #{start_state}, ready: true, env: map[string]Value{#{binds}}}, nil
     }
     """, taken}
  end

  defp start_code(image, ctx) do
    case image.start do
      {:state, id} ->
        {const_name(ctx, id), "map[string]Value{}", MapSet.new()}

      :done ->
        {ctx.done, "map[string]Value{}", MapSet.new()}

      :stuck ->
        {ctx.stuck, "map[string]Value{}", MapSet.new()}

      :stop ->
        {ctx.stop, "map[string]Value{}", MapSet.new()}

      _ ->
        {ctx.stuck, "map[string]Value{}", MapSet.new()}
    end
  end

  defp methods(image, ctx) do
    {send, ns} = dir_method(image, ctx, :send, "stepSend", "send")
    {recv, nr} = dir_method(image, ctx, :recv, "stepRecv", "recv")
    {down, nd} = down_method(image, ctx)
    {send <> recv <> down, ns |> MapSet.union(nr) |> MapSet.union(nd)}
  end

  defp dir_method(image, ctx, dir, fun, word) do
    states = Enum.filter(image.states, &(dir_of(&1.kind) == dir))

    body =
      Enum.map_join(states, "", fn st ->
        {code, _needs} = arm(st, ctx, word)

        """
        \tcase #{const_name(ctx, st.id)}:
        #{code}
        """
      end)

    needs =
      Enum.reduce(states, MapSet.new(), fn st, acc ->
        {_, n} = arm(st, ctx, word)
        MapSet.union(acc, n)
      end)

    src = """
    func (m *#{ctx.go}) #{fun}(v Value) error {
    \tswitch m.state {
    #{body}\tdefault:
    \t\treturn muroIllegal("#{ctx.go}", m.State().String(), m.Expected(), "#{word} "+v.String())
    \t}
    }

    """

    {src, needs}
  end

  defp arm(st, ctx, word) do
    ind = 2
    event = "\"#{word} \"+v.String()"
    {pre, needs} = guard(st, ctx, event, ind)

    case st.kind do
      kind when kind in [:choose, :branch] ->
        {left, nl} = goto(st.left, ctx, nil, ind + 1, expect(st))
        {right, nr} = goto(st.right, ctx, nil, ind + 1, expect(st))

        {pre <> pick_switch(st, ctx, event, left, right, ind),
         MapSet.union(needs, MapSet.union(nl, nr))}

      kind when kind in [:isend, :irecv] ->
        {left, nl} = goto(st.left, ctx, st.binder, ind + 1, expect(st))
        {right, nr} = goto(st.right, ctx, st.binder, ind + 1, expect(st))

        {pre <> bit_switch(st, ctx, event, left, right, ind),
         MapSet.union(needs, MapSet.union(nl, nr))}

      _ ->
        {rest, nr} = after_value(st, ctx, ind, expect(st))
        {pre <> rest, MapSet.union(needs, nr)}
    end
  end

  defp pick_switch(st, ctx, event, left, right, ind) do
    line(ind, "switch v.k {") <>
      line(ind, "case valPick0:") <>
      left <>
      line(ind, "case valPick1:") <>
      right <>
      line(ind, "default:") <>
      line(ind + 1, illegal(ctx, expect(st), event)) <>
      line(ind, "}")
  end

  defp bit_switch(st, ctx, event, left, right, ind) do
    line(ind, "switch v.k {") <>
      line(ind, "case valBit0:") <>
      left <>
      line(ind, "case valBit1:") <>
      right <>
      line(ind, "default:") <>
      line(ind + 1, illegal(ctx, expect(st), event)) <>
      line(ind, "}")
  end

  defp guard(st, ctx, event, ind) do
    err = line(ind + 1, illegal(ctx, expect(st), event))

    {base, needs} =
      cond do
        st.kind in [:isend, :irecv] ->
          {line(ind, "if v.k != valBit0 && v.k != valBit1 {") <> err <> line(ind, "}"),
           MapSet.new()}

        st.kind in [:choose, :branch] ->
          {line(ind, "if v.k != valPick0 && v.k != valPick1 {") <> err <> line(ind, "}"),
           MapSet.new()}

        true ->
          {fname, _} = st.match

          {line(ind, "if !#{fname}(v, m.env) {") <> err <> line(ind, "}"), MapSet.new()}
      end

    case st.bound do
      nil ->
        {base, needs}

      ix ->
        {lines, n, ok, more} = Match.ix(ix, "m.env")
        checks = Enum.map_join(lines, "", &line(ind, &1))

        {base <> checks <> line(ind, "if !#{ok} || v.n > #{n} {") <> err <> line(ind, "}"),
         MapSet.union(needs, more)}
    end
  end

  defp after_value(st, ctx, ind, expected) do
    case st.dest do
      {:case, scrut, arms, jumps} ->
        if scrut_name(scrut) != st.binder do
          {line(ind, illegal(ctx, expected, "\"recv \"+v.String()")), MapSet.new()}
        else
          case_goto(st.binder, ctx, arms, jumps, ind, expected)
        end

      dest ->
        goto(dest, ctx, st.binder, ind, expected)
    end
  end

  defp case_goto(binder, ctx, arms, jumps, ind, expected) do
    {setup, jn} = env_setup(binder, jumps, ctx, ind)

    {arms_src, needs} =
      Enum.reduce(arms, {"", jn}, fn {tag, dest}, {src, needs} ->
        {g, n} = goto_have(dest, ctx, ind + 1)

        {src <> line(ind, "case #{Match.gq(tag)}:") <> g, MapSet.union(needs, n)}
      end)

    src =
      setup <>
        line(ind, "switch v.tag {") <>
        arms_src <>
        line(ind, "default:") <>
        line(ind + 1, illegal(ctx, expected, "\"recv \"+v.String()")) <>
        line(ind, "}")

    {src, needs}
  end

  defp goto({:case, scrut, arms, jumps}, ctx, binder, ind, expected) do
    if scrut_name(scrut) != binder do
      {line(ind, illegal(ctx, expected, "\"recv \"+v.String()")), MapSet.new()}
    else
      case_goto(binder, ctx, arms, jumps, ind, expected)
    end
  end

  defp goto({:at, id, jumps}, ctx, binder, ind, _expected),
    do: commit(const_name(ctx, id), jumps, ctx, binder, ind)

  defp goto({:done, jumps}, ctx, binder, ind, _expected),
    do: commit(ctx.done, jumps, ctx, binder, ind)

  defp goto({:stuck, jumps}, ctx, binder, ind, _expected),
    do: commit(ctx.stuck, jumps, ctx, binder, ind)

  defp goto(_other, ctx, _binder, ind, _expected), do: commit(ctx.stuck, [], ctx, nil, ind)

  defp goto_have({:at, id, jumps}, ctx, ind),
    do: commit_have(const_name(ctx, id), jumps, ctx, ind)

  defp goto_have({:done, jumps}, ctx, ind), do: commit_have(ctx.done, jumps, ctx, ind)
  defp goto_have({:stuck, jumps}, ctx, ind), do: commit_have(ctx.stuck, jumps, ctx, ind)

  defp goto_have({:case, _scrut, _arms, jumps}, ctx, ind),
    do: commit_have(ctx.stuck, jumps, ctx, ind)

  defp goto_have(_other, ctx, ind), do: commit_have(ctx.stuck, [], ctx, ind)

  defp commit(state, [], _ctx, nil, ind) do
    {line(ind, "m.state = #{state}") <> line(ind, "return nil"), MapSet.new()}
  end

  defp commit(state, jumps, ctx, binder, ind) do
    {setup, needs} = env_setup(binder, jumps, ctx, ind)

    {setup <>
       line(ind, "m.env = env") <> line(ind, "m.state = #{state}") <> line(ind, "return nil"),
     needs}
  end

  defp commit_have(state, jumps, ctx, ind) do
    {js, needs} = jumps_code(jumps, ctx, ind)

    {js <> line(ind, "m.env = env") <> line(ind, "m.state = #{state}") <> line(ind, "return nil"),
     needs}
  end

  defp env_setup(binder, jumps, ctx, ind) do
    {js, needs} = jumps_code(jumps, ctx, ind)
    bind = if is_binary(binder), do: line(ind, "env[#{Match.gq(binder)}] = v"), else: ""

    {line(ind, "env := muroClone(m.env)") <> bind <> js, MapSet.put(needs, :clone)}
  end

  defp jumps_code([], _ctx, _ind), do: {"", MapSet.new()}

  defp jumps_code(jumps, ctx, ind) do
    Enum.reduce(jumps, {"", MapSet.new()}, fn args, {acc, needs} ->
      {block, n} = jump_block(args, ctx, ind)
      {acc <> block, MapSet.union(needs, n)}
    end)
  end

  defp jump_block(args, ctx, ind) do
    params = ctx.mod.params

    {evals, needs} =
      args
      |> Enum.with_index()
      |> Enum.reduce({[], MapSet.new()}, fn {arg, i}, {lines, needs} ->
        {more, _n, _ok, nset} = Match.ix_lines(arg, "env", i, ind)
        {lines ++ more, MapSet.union(needs, nset)}
      end)

    n = length(args)
    # `0..-1` is `[0, -1]`. A jump with no actuals must not emit `jok-1`.
    indices = 0..(n - 1)//1

    pairs =
      params
      |> Enum.zip(indices)
      |> Enum.map_join(", ", fn {name, i} -> "#{Match.gq(name)}: Nat(j#{i})" end)

    checks =
      Enum.map_join(indices, "", fn i ->
        line(ind, "if !jok#{i} {") <>
          line(ind + 1, "m.env = env") <>
          line(ind + 1, "m.state = #{ctx.stuck}") <>
          line(ind + 1, "return nil") <>
          line(ind, "}")
      end)

    {IO.iodata_to_binary(evals) <> checks <> line(ind, "env = map[string]Value{#{pairs}}"), needs}
  end

  defp illegal(ctx, expected, event) do
    "return muroIllegal(\"#{ctx.go}\", m.State().String(), #{Match.gq(expected)}, #{event})"
  end

  defp line(n, text), do: String.duplicate("\t", n) <> text <> "\n"

  defp down_method(%{down: false}, _ctx), do: {"", MapSet.new()}

  defp down_method(image, ctx) do
    arms =
      image.states
      |> Enum.filter(& &1.fail)
      |> Enum.map_join("", fn st ->
        {code, _} = down_arm(st, ctx)

        """
        \tcase #{const_name(ctx, st.id)}:
        #{code}
        """
      end)

    needs = MapSet.new([:down])

    src = """
    // Down takes a failure arm. Nil is an arm that binds no reason.
    // A refused failure leaves the value unchanged.
    func (m *#{ctx.go}) Down(reason *Value) error {
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{ctx.go}", "invalid", "start", muroDown(reason))
    \t}
    \tswitch m.state {
    #{arms}\tdefault:
    \t\treturn muroIllegal("#{ctx.go}", m.State().String(), m.Expected(), muroDown(reason))
    \t}
    }

    """

    {src, needs}
  end

  defp down_arm(st, ctx) do
    to = if st.fail.to == :stop, do: ctx.stop, else: ctx.done

    check =
      case st.fail.reason do
        nil ->
          """
          \t\tif reason != nil {
          \t\t\treturn muroIllegal("#{ctx.go}", m.State().String(), #{Match.gq(expect(st))}, muroDown(reason))
          \t\t}
          """

        _ty ->
          {fname, _} = st.fail.match

          """
          \t\tif reason == nil || !#{fname}(*reason, m.env) {
          \t\t\treturn muroIllegal("#{ctx.go}", m.State().String(), #{Match.gq(expect(st))}, muroDown(reason))
          \t\t}
          """
      end

    {"#{check}\t\tm.state = #{to}\n\t\treturn nil\n", MapSet.new()}
  end

  defp const_lines(states, go) do
    Enum.map_join(states, "", fn st ->
      name = go <> "State" <> st.label
      "\t// #{name} is #{st.step}.\n\t#{name}\n"
    end)
  end

  defp done_line(done, _states) do
    "\t// #{done} is the end of the session.\n\t#{done}\n"
  end

  defp string_lines(states, go) do
    Enum.map_join(states, "", fn st ->
      "\tcase #{go}State#{st.label}:\n\t\treturn #{Match.gq(Macro.underscore(st.label))}\n"
    end)
  end

  defp expect_lines(states, go) do
    Enum.map_join(states, "", fn st ->
      "\tcase #{go}State#{st.label}:\n\t\treturn #{Match.gq(expect(st))}\n"
    end)
  end

  defp const_name(ctx, id), do: ctx.go <> "State" <> Map.fetch!(ctx.labels, id)

  defp expect(st) do
    case st.kind do
      :choose -> "send pick"
      :branch -> "recv pick"
      :isend -> "send bit"
      :irecv -> "recv bit"
      kind -> word(kind) <> " " <> Match.describe(st.ty)
    end
  end

  defp word(k) when k in [:send, :dsend, :esend], do: "send"
  defp word(_), do: "recv"

  defp dir_of(k) when k in [:send, :dsend, :esend, :isend, :choose], do: :send
  defp dir_of(_), do: :recv

  defp stop?(%{fail: %{to: :stop}}), do: true
  defp stop?(_), do: false

  defp session_defined(image, go, ctx) do
    consts =
      [ctx.invalid, ctx.done, ctx.stuck] ++
        if(ctx.has_stop, do: [ctx.stop], else: []) ++
        Enum.map(image.states, &(go <> "State" <> &1.label))

    match_names =
      Enum.map(image.match.order, fn key ->
        {name, _src} = image.match.fns[key]
        name
      end)

    MapSet.new([go, go <> "State", "New" <> go | consts ++ match_names])
  end

  defp go_base(name) do
    base =
      name
      |> String.replace(~r/[^0-9A-Za-z_]/, "_")
      |> String.replace(~r/_+/, "_")
      |> String.trim("_")

    if base == "" or base =~ ~r/^[0-9]/, do: "p_" <> base, else: base
  end

  @doc false
  def string_lit(s) when is_binary(s) do
    body = s |> String.to_charlist() |> Enum.map_join(&escape_cp/1)
    "\"" <> body <> "\""
  end

  defp escape_cp(?\\), do: "\\\\"
  defp escape_cp(?"), do: "\\\""
  defp escape_cp(?\n), do: "\\n"
  defp escape_cp(?\r), do: "\\r"
  defp escape_cp(?\t), do: "\\t"

  defp escape_cp(c) when c >= 0 and (c < 0x20 or c == 0x7F) do
    "\\x" <> Base.encode16(<<c>>, case: :lower)
  end

  defp escape_cp(c) when c in 0..0x10FFFF, do: <<c::utf8>>

  defp ordered(acc) do
    acc.states
    |> Map.values()
    |> Enum.sort_by(& &1.id)
  end

  defp normalize({:at, id, []}), do: {:state, id}
  defp normalize({:done, _}), do: :done
  defp normalize({:stuck, _}), do: :stuck
  defp normalize({:case, _, _, _}), do: :stuck
  defp normalize({:at, _id, _jumps}), do: :stuck
  defp normalize(_), do: :stuck

  defp attach_fails(acc) do
    Enum.reduce(acc.states, acc, fn {id, st}, acc ->
      case Map.fetch(acc.fails, st.step) do
        :error ->
          acc

        {:ok, {why, skel}} ->
          case fail_to(skel) do
            {:ok, to} ->
              case fail_reason(why, acc) do
                {:error, msg} ->
                  %{acc | error: msg}

                {:ok, reason, match, acc} ->
                  st = %{st | fail: %{to: to, reason: reason, match: match}}
                  put_in(acc.states[id], st)
              end

            :error ->
              %{acc | error: "go: failure arm continues the protocol"}
          end
      end
    end)
  end

  defp fail_reason(nil, acc), do: {:ok, nil, nil, acc}

  defp fail_reason({ty, _name}, acc) do
    case Match.ensure(ty, acc.decls, acc.reprs, acc.match) do
      {:ok, fun, match} -> {:ok, ty, {fun, match}, %{acc | match: match}}
      {:error, msg} -> {:error, msg}
    end
  end

  defp fail_reason(_other, acc), do: {:ok, nil, nil, acc}

  defp fail_to(:finish), do: {:ok, :done}
  defp fail_to(:leave), do: {:ok, :stop}
  defp fail_to(_), do: :error

  defp land({:rec, name, body}, acc, seen, jumps) do
    if {:rec, name} in seen do
      {{:stuck, jumps}, acc}
    else
      acc =
        if will_alloc?(body) do
          %{acc | recs: Map.put(acc.recs, name, {:pending, acc.next})}
        else
          acc
        end

      land(body, acc, [{:rec, name} | seen], jumps)
    end
  end

  defp land({:svar, name}, acc, seen, jumps) do
    cond do
      {:svar, name} in seen ->
        {{:stuck, jumps}, acc}

      true ->
        case Map.get(acc.recs, name) do
          {:pending, id} -> {{:at, id, jumps}, acc}
          {:state, id} -> {{:at, id, jumps}, acc}
          _ -> {{:stuck, jumps}, acc}
        end
    end
  end

  defp land({:sjump, {:dual, _}, _}, acc, _seen, _jumps) do
    {{:error, "go: dual jump"}, %{acc | error: "go: dual jump"}}
  end

  defp land({:sjump, name, args} = node, acc, seen, jumps) when is_binary(name) do
    cond do
      node in seen ->
        {{:stuck, jumps}, acc}

      name == acc.self ->
        land(acc.root, acc, [node | seen], jumps ++ [args])

      true ->
        {{:error, "go: unsupported protocol"}, %{acc | error: "go: unsupported protocol"}}
    end
  end

  defp land({:end, _}, acc, _seen, jumps), do: {{:done, jumps}, acc}

  defp land({:case, scrut, arms}, acc, _seen, jumps) do
    cond do
      run_scrut?(scrut) ->
        {{:error, "go: run case"}, %{acc | error: "go: run case"}}

      true ->
        {compiled, acc} =
          Enum.reduce(arms, {[], acc}, fn {tag, proto}, {got, acc} ->
            {dest, acc} = land(proto, acc, [], [])
            {got ++ [{to_string(tag), dest}], acc}
          end)

        {{:case, scrut, compiled, jumps}, acc}
    end
  end

  defp land({:send, step, ty, cont}, acc, _seen, jumps) do
    compile_payload(:send, step, ty, nil, nil, cont, acc, jumps)
  end

  defp land({:recv, step, ty, cont}, acc, _seen, jumps) do
    compile_payload(:recv, step, ty, nil, nil, cont, acc, jumps)
  end

  defp land({:dsend, step, name, ty, cont}, acc, _seen, jumps) do
    compile_payload(:dsend, step, ty, binder_name(name), nil, cont, acc, jumps)
  end

  defp land({:drecv, step, name, ty, cont}, acc, _seen, jumps) do
    compile_payload(:drecv, step, ty, binder_name(name), nil, cont, acc, jumps)
  end

  defp land({:esend, step, name, bound, cont}, acc, _seen, jumps) do
    compile_payload(:esend, step, :nat, binder_name(name), bound, cont, acc, jumps)
  end

  defp land({:erecv, step, name, bound, cont}, acc, _seen, jumps) do
    compile_payload(:erecv, step, :nat, binder_name(name), bound, cont, acc, jumps)
  end

  defp land({:isend, step, name, left, right}, acc, _seen, jumps) do
    compile_index(:isend, step, binder_name(name), left, right, acc, jumps)
  end

  defp land({:irecv, step, name, left, right}, acc, _seen, jumps) do
    compile_index(:irecv, step, binder_name(name), left, right, acc, jumps)
  end

  defp land({:choose, step, left, right}, acc, _seen, jumps) do
    compile_pick(:choose, step, left, right, acc, jumps)
  end

  defp land({:branch, step, left, right}, acc, _seen, jumps) do
    compile_pick(:branch, step, left, right, acc, jumps)
  end

  defp land(_other, acc, _seen, _jumps) do
    {{:error, "go: unsupported protocol"}, %{acc | error: "go: unsupported protocol"}}
  end

  defp compile_payload(kind, step, ty, binder, bound, cont, acc, jumps) do
    case acc.by_step[step] do
      id when is_integer(id) ->
        {{:at, id, jumps}, acc}

      nil ->
        case Match.ensure(ty, acc.decls, acc.reprs, acc.match) do
          {:error, msg} ->
            {{:error, msg}, %{acc | error: msg}}

          {:ok, fname, match} ->
            {id, label, acc} = alloc(kind, acc)
            acc = %{acc | by_step: Map.put(acc.by_step, step, id), match: match}
            {dest, acc} = land(cont, acc, [], [])

            case dest do
              {:error, msg} ->
                {{:error, msg}, %{acc | error: acc.error || msg}}

              _ ->
                state = %{
                  id: id,
                  label: label,
                  kind: kind,
                  step: step,
                  ty: ty,
                  binder: binder,
                  bound: bound,
                  dest: dest,
                  left: nil,
                  right: nil,
                  match: {fname, match},
                  fail: nil
                }

                acc = put_in(acc.states[id], state)
                {{:at, id, jumps}, acc}
            end
        end
    end
  end

  defp compile_index(kind, step, name, left, right, acc, jumps) do
    case acc.by_step[step] do
      id when is_integer(id) ->
        {{:at, id, jumps}, acc}

      nil ->
        {id, label, acc} = alloc(kind, acc)
        acc = %{acc | by_step: Map.put(acc.by_step, step, id)}
        {ld, acc} = land(left, acc, [], [])
        {rd, acc} = land(right, acc, [], [])

        state = %{
          id: id,
          label: label,
          kind: kind,
          step: step,
          ty: :bit,
          binder: name,
          bound: nil,
          dest: nil,
          left: ld,
          right: rd,
          match: {"muroBits", acc.match},
          fail: nil
        }

        {{:at, id, jumps}, put_in(acc.states[id], state)}
    end
  end

  defp compile_pick(kind, step, left, right, acc, jumps) do
    case acc.by_step[step] do
      id when is_integer(id) ->
        {{:at, id, jumps}, acc}

      nil ->
        {id, label, acc} = alloc(kind, acc)
        acc = %{acc | by_step: Map.put(acc.by_step, step, id)}
        {ld, acc} = land(left, acc, [], [])
        {rd, acc} = land(right, acc, [], [])

        state = %{
          id: id,
          label: label,
          kind: kind,
          step: step,
          ty: :pick,
          binder: nil,
          bound: nil,
          dest: nil,
          left: ld,
          right: rd,
          match: {"muroPicks", acc.match},
          fail: nil
        }

        {{:at, id, jumps}, put_in(acc.states[id], state)}
    end
  end

  defp alloc(kind, acc) do
    id = acc.next
    n = Map.get(acc.counts, kind, 0) + 1
    label = label_of(kind) <> Integer.to_string(n)

    recs =
      Map.new(acc.recs, fn
        {name, {:pending, ^id}} -> {name, {:state, id}}
        pair -> pair
      end)

    {id, label, %{acc | next: id + 1, counts: Map.put(acc.counts, kind, n), recs: recs}}
  end

  defp label_of(:send), do: "Send"
  defp label_of(:recv), do: "Recv"
  defp label_of(:dsend), do: "Send"
  defp label_of(:drecv), do: "Recv"
  defp label_of(:esend), do: "Send"
  defp label_of(:erecv), do: "Recv"
  defp label_of(:isend), do: "SendBit"
  defp label_of(:irecv), do: "RecvBit"
  defp label_of(:choose), do: "Choose"
  defp label_of(:branch), do: "Branch"

  defp will_alloc?({:rec, _, body}), do: will_alloc?(body)
  defp will_alloc?({:svar, _}), do: false
  defp will_alloc?({:sjump, _, _}), do: false
  defp will_alloc?({:end, _}), do: false
  defp will_alloc?({:case, _, _}), do: false

  defp will_alloc?(node) when is_tuple(node) and tuple_size(node) >= 1,
    do: elem(node, 0) in @action

  defp will_alloc?(_), do: false

  defp run_scrut?({:run, _, _, _}), do: true
  defp run_scrut?({:run, _, _}), do: true
  defp run_scrut?(_), do: false

  defp scrut_name({:name, n}) when is_binary(n) or is_atom(n), do: binder_name(n)
  defp scrut_name(_), do: nil

  defp binder_name(nil), do: nil
  defp binder_name(name) when is_binary(name) or is_atom(name), do: to_string(name)
end

defmodule Muro.Emit.Go.Match do
  @moduledoc false

  @doc false
  def empty, do: %{fns: %{}, order: []}

  @doc false
  def ensure(ty, decls, reprs, acc) do
    case reject(ty, reprs) do
      {:error, _} = err ->
        err

      :ok ->
        case known_data(ty, decls) do
          {:error, _} = err ->
            err

          :ok ->
            key = ty

            case acc.fns[key] do
              {name, _src} ->
                {:ok, name, acc}

              nil ->
                name = "muroMatch#{map_size(acc.fns)}"
                acc = %{acc | fns: Map.put(acc.fns, key, {name, :pending})}

                case body(ty, decls, reprs, acc) do
                  {:error, _} = err ->
                    err

                  {body, acc} ->
                    src = "func #{name}(v Value, env map[string]Value) bool {\n#{body}}\n"

                    acc = %{
                      acc
                      | fns: Map.put(acc.fns, key, {name, src}),
                        order: acc.order ++ [key]
                    }

                    {:ok, name, acc}
                end
            end
        end
    end
  end

  @doc false
  def source(acc) do
    Enum.map_join(acc.order, "\n", fn key ->
      {_name, src} = acc.fns[key]
      src
    end)
  end

  @doc false
  def describe(:nat), do: "nat"
  def describe(:bit), do: "bit"
  def describe(:unit), do: "unit"
  def describe(:pick), do: "pick"
  def describe({:pair, _, _}), do: "pair"
  def describe({:rec, _}), do: "record"
  def describe({:vec, _, _}), do: "vec"
  def describe({:dat, name, _}), do: name
  def describe({:bnat, _}), do: "nat"
  def describe(_), do: "value"

  # `to_string(nil)` is `""`. A parameter named `nil` is that atom, and the
  # source spelling is `nil`.
  @doc false
  def source_name(name) when is_atom(name), do: Atom.to_string(name)
  def source_name(name) when is_binary(name), do: name

  @doc false
  def gq(s) when is_binary(s) do
    "\"" <>
      (s
       |> String.replace("\\", "\\\\")
       |> String.replace("\"", "\\\"")
       |> String.replace("\n", "\\n")
       |> String.replace("\r", "\\r")
       |> String.replace("\t", "\\t")) <> "\""
  end

  @doc false
  def ix(ix, env) do
    {expr, ok, lines, needs} = ix_go(ix, env, 0)
    {lines, expr, ok, needs}
  end

  @doc false
  def ix_lines(ix, env, i, indent) do
    {expr, ok, lines, needs} = ix_go(ix, env, i * 10)
    lines = lines ++ ["j#{i}, jok#{i} := #{expr}, #{ok}"]
    pad = String.duplicate("\t", indent)
    {Enum.map(lines, &(pad <> &1 <> "\n")), expr, ok, needs}
  end

  defp ix_go({:lit, n}, _env, _i) when is_integer(n) and n >= 0 do
    {Integer.to_string(n), "true", [], MapSet.new()}
  end

  defp ix_go({:var, name}, env, i) when is_binary(name) or is_atom(name) do
    {"n#{i}", "ok#{i}", ["n#{i}, ok#{i} := muroNat(#{env}, #{gq(source_name(name))})"],
     MapSet.new([:nat])}
  end

  defp ix_go({:suc, inner}, env, i) do
    {expr, ok, lines, needs} = ix_go(inner, env, i + 1)
    {"s#{i}", "ok#{i}", lines ++ ["s#{i} := #{expr} + 1", "ok#{i} := #{ok}"], needs}
  end

  defp ix_go(_, _env, i) do
    {"0", "false", ["_ = #{i}"], MapSet.new()}
  end

  defp reject(:nat, reprs) do
    if "Nat" in reprs, do: {:error, "go: repr payload"}, else: :ok
  end

  defp reject({:dat, name, args}, reprs) when is_binary(name) and is_list(args) do
    if name in reprs do
      {:error, "go: repr payload"}
    else
      Enum.reduce_while(args, :ok, fn arg, :ok ->
        case reject(arg, reprs) do
          :ok -> {:cont, :ok}
          err -> {:halt, err}
        end
      end)
    end
  end

  defp reject({:pair, a, b}, reprs) do
    with :ok <- reject(a, reprs), do: reject(b, reprs)
  end

  defp reject({:rec, fields}, reprs) when is_list(fields) do
    Enum.reduce_while(fields, :ok, fn {_n, ty}, :ok ->
      case reject(ty, reprs) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp reject({:vec, elem, _ix}, reprs), do: reject(elem, reprs)
  defp reject(:bit, _), do: :ok
  defp reject(:unit, _), do: :ok
  defp reject(:pick, _), do: :ok
  defp reject({:bnat, n}, _) when is_integer(n) and n >= 0, do: :ok
  defp reject(_, _), do: {:error, "go: unsupported payload"}

  defp known_data({:dat, name, args}, decls) when is_binary(name) and is_list(args) do
    case Map.fetch(decls, name) do
      {:ok, %{np: np}} when length(args) == np -> :ok
      _ -> {:error, "go: unsupported payload"}
    end
  end

  defp known_data(_, _), do: :ok

  defp body(:nat, _decls, _reprs, acc) do
    {"\treturn v.k == valNat && v.n >= 0\n", acc}
  end

  defp body(:bit, _decls, _reprs, acc) do
    {"\treturn v.k == valBit0 || v.k == valBit1\n", acc}
  end

  defp body(:unit, _decls, _reprs, acc) do
    {"\treturn v.k == valUnit\n", acc}
  end

  defp body({:bnat, n}, _decls, _reprs, acc) when is_integer(n) do
    {"\treturn v.k == valNat && v.n >= 0 && v.n <= #{n}\n", acc}
  end

  defp body({:pair, a, b}, decls, reprs, acc) do
    with {:ok, fa, acc} <- ensure(a, decls, reprs, acc),
         {:ok, fb, acc} <- ensure(b, decls, reprs, acc) do
      {"\treturn v.k == valPair && len(v.fields) == 2 && #{fa}(v.fields[0], env) && #{fb}(v.fields[1], env)\n",
       acc}
    end
  end

  defp body({:rec, fields}, decls, reprs, acc) do
    fields = Enum.sort_by(fields, fn {name, _} -> name end)

    {checks, acc} =
      Enum.reduce_while(Enum.with_index(fields), {[], acc}, fn {{name, ty}, i}, {lines, acc} ->
        case ensure(ty, decls, reprs, acc) do
          {:ok, f, acc} ->
            {:cont, {lines ++ ["v.names[#{i}] == #{gq(name)} && #{f}(v.fields[#{i}], env)"], acc}}

          {:error, _} = err ->
            {:halt, err}
        end
      end)

    with {checks, acc} when is_list(checks) <- {checks, acc} do
      n = length(fields)

      cond =
        if checks == [] do
          "true"
        else
          Enum.join(checks, " && ")
        end

      {"\treturn v.k == valRecord && len(v.names) == #{n} && len(v.fields) == #{n} && #{cond}\n",
       acc}
    end
  end

  defp body({:vec, elem, ix}, decls, reprs, acc) do
    with {:ok, fe, acc} <- ensure(elem, decls, reprs, acc) do
      {expr, ok, lines, _needs} = ix_go(ix, "env", 0)
      setup = Enum.map_join(lines, "", fn line -> "\t" <> line <> "\n" end)

      {"""
       \tif v.k != valVec {
       \t\treturn false
       \t}
       #{setup}\tif !(#{ok}) || len(v.fields) != #{expr} {
       \t\treturn false
       \t}
       \tfor _, el := range v.fields {
       \t\tif !#{fe}(el, env) {
       \t\t\treturn false
       \t\t}
       \t}
       \treturn true
       """, acc}
    end
  end

  defp body({:dat, name, args}, decls, reprs, acc) do
    case Map.fetch(decls, name) do
      :error ->
        {"\treturn false\n", acc}

      {:ok, %{np: np, order: order, ctors: ctors}} when length(args) == np ->
        reduced =
          Enum.reduce_while(order, {[], acc}, fn ctor, {arms, acc} ->
            fields = Map.fetch!(ctors, ctor)

            case fields_pred(fields, name, args, decls, reprs, acc) do
              {:ok, pred, acc} ->
                {:cont, {arms ++ ["\tcase #{gq(ctor)}:\n\t\treturn #{pred}\n"], acc}}

              {:error, _} = err ->
                {:halt, err}
            end
          end)

        case reduced do
          {:error, _} = err ->
            err

          {arms, acc} ->
            {"""
             \tif v.k != valCon {
             \t\treturn false
             \t}
             \tswitch v.tag {
             #{IO.iodata_to_binary(arms)}\tdefault:
             \t\treturn false
             \t}
             """, acc}
        end

      _ ->
        {"\treturn false\n", acc}
    end
  end

  defp body(_ty, _decls, _reprs, acc) do
    {"\treturn false\n", acc}
  end

  defp fields_pred(fields, dname, args, decls, reprs, acc) do
    reduced =
      Enum.reduce_while(Enum.with_index(fields), {[], acc}, fn {field, i}, {preds, acc} ->
        case ensure(inst(field, dname, args), decls, reprs, acc) do
          {:ok, f, acc} -> {:cont, {preds ++ ["#{f}(v.fields[#{i}], env)"], acc}}
          {:error, _} = err -> {:halt, err}
        end
      end)

    case reduced do
      {:error, msg} ->
        {:error, msg}

      {preds, acc} ->
        n = length(preds)

        pred =
          if preds == [] do
            "len(v.fields) == 0"
          else
            "len(v.fields) == #{n} && " <> Enum.join(preds, " && ")
          end

        {:ok, pred, acc}
    end
  end

  defp inst({:par, i}, _name, args), do: Enum.at(args, i)
  defp inst({:self, ts}, name, args), do: {:dat, name, Enum.map(ts, &inst(&1, name, args))}
  defp inst({:dat, n, ts}, name, args), do: {:dat, n, Enum.map(ts, &inst(&1, name, args))}
  defp inst({:pair, a, b}, name, args), do: {:pair, inst(a, name, args), inst(b, name, args)}

  defp inst({:rec, fields}, name, args) do
    {:rec, Enum.map(fields, fn {field, ty} -> {field, inst(ty, name, args)} end)}
  end

  defp inst({:vec, elem, ix}, name, args), do: {:vec, inst(elem, name, args), ix}
  defp inst(ty, _name, _args), do: ty
end
