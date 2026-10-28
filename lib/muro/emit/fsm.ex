defmodule Muro.Emit.Fsm do
  @moduledoc """
  Emit each session as a pure state machine.

  The module is data and functions. It starts no process and names no
  transport. The host threads the state through `init`, `send`, and `recv`.
  """

  alias Muro.{Ast, Emit, Session}

  @doc """
  Elixir source for `module`, one child per session of `book`.

  `path` is the book that was loaded. `opts` accepts `book:` (the label
  printed in a step) and `root:` (how an imported session's file is
  shown). A relative `path` with no `book:` is that path, with `/`
  separators, so the text does not depend on the working directory.
  """
  def render(book, path, module, opts \\ []) when is_list(book) and is_atom(module) do
    label = book_label(path, opts)

    case Enum.filter(book, &(Map.get(&1, :kind) == :session)) do
      [] ->
        {:error, "#{label} has no session to emit"}

      sessions ->
        st = %{
          book: book,
          sessions: sessions,
          index: Map.new(Enum.with_index(sessions), fn {sess, i} -> {sess.name, {i, sess}} end),
          opened: %{},
          stack: [],
          runs: MapSet.new(),
          results: %{},
          path: path,
          root: Keyword.get(opts, :root, File.cwd!()),
          label: label
        }

        case open_all(sessions, st) do
          {:ok, st} -> {:ok, source(module, book, st)}
          {:error, _} = err -> err
        end
    end
  end

  defp book_label(path, opts) do
    case Keyword.get(opts, :book) do
      book when is_binary(book) ->
        String.replace(book, "\\", "/")

      _ ->
        norm = path |> to_string() |> String.replace("\\", "/")
        if String.starts_with?(norm, "/"), do: Path.basename(norm), else: norm
    end
  end

  defp open_all(sessions, st) do
    Enum.reduce_while(sessions, {:ok, st}, fn sess, {:ok, st} ->
      case ensure(sess.name, st) do
        {:ok, st} -> {:cont, {:ok, st}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp ensure(name, st) do
    cond do
      Map.has_key?(st.opened, name) ->
        {:ok, st}

      name in st.stack ->
        {:error, cycle_msg(name, st)}

      true ->
        case Map.fetch(st.index, name) do
          :error ->
            {:error, missing_msg(name, st)}

          {:ok, {_i, sess}} ->
            st = %{st | stack: [name | st.stack]}

            case open_session(sess, st) do
              {:ok, entry, st} ->
                st = %{st | stack: tl(st.stack), opened: Map.put(st.opened, name, entry)}
                {:ok, st}

              {:error, _} = err ->
                err
            end
        end
    end
  end

  defp cycle_msg(name, st) do
    {file, line} = place(name, st)
    "#{file}:#{line} session #{name}: dual cycle"
  end

  defp missing_msg(name, st) do
    "#{st.label}: session #{name}: unknown session #{name}"
  end

  defp open_session(sess, st) do
    file = session_file(sess, st)
    line = line_of(sess)
    params = Map.get(sess, :params, [])

    ctx = %{
      st: st,
      self: sess.name,
      index: session_index(sess.name, st),
      file: file,
      line: line,
      name: sess.name,
      guarded: false,
      subst: Map.new(params, &{&1, {:var, &1}}),
      bound: %{},
      counts: %{send: 0, recv: 0, choose: 0, branch: 0, other: 0}
    }

    case label(sess.proto, ctx) do
      {:ok, proto, ctx} ->
        entry = %{
          params: params,
          proto: proto,
          file: file,
          line: line,
          end_step: "#{file}:#{line} session #{sess.name}: end"
        }

        {:ok, entry, ctx.st}

      {:error, _} = err ->
        err
    end
  end

  defp session_index(name, st) do
    case Map.fetch(st.index, name) do
      {:ok, {i, _}} -> i
      :error -> nil
    end
  end

  defp session_file(sess, st) do
    if is_binary(Map.get(sess, :file)) do
      Emit.ExUnitSuite.display_for(sess, %{path: st.path, display: st.label, root: st.root})
    else
      st.label
    end
  end

  defp place(name, st) do
    case Map.fetch(st.index, name) do
      {:ok, {_i, sess}} -> {session_file(sess, st), line_of(sess)}
      :error -> {st.label, 0}
    end
  end

  defp line_of(%{loc: {line, _col}}) when is_integer(line), do: line
  defp line_of(_), do: 0

  defp label(:end, ctx) do
    {:ok, {:end, "#{ctx.file}:#{ctx.line} session #{ctx.name}: end"}, ctx}
  end

  defp label({:send, ty, cont}, ctx) do
    with :ok <- support(ty, ctx) do
      {step, ctx} = note(ctx, Session.step_proto({:send, ty, :end}))
      ctx = guard(ctx)

      with {:ok, cont, ctx} <- label(cont, ctx) do
        {:ok, {:send, step, ty, cont}, ctx}
      end
    end
  end

  defp label({:recv, ty, cont}, ctx) do
    with :ok <- support(ty, ctx) do
      {step, ctx} = note(ctx, Session.step_proto({:recv, ty, :end}))
      ctx = guard(ctx)

      with {:ok, cont, ctx} <- label(cont, ctx) do
        {:ok, {:recv, step, ty, cont}, ctx}
      end
    end
  end

  defp label({:dsend, name, ty, cont}, ctx) do
    bind_comm(:dsend, name, ty, cont, ctx)
  end

  defp label({:drecv, name, ty, cont}, ctx) do
    bind_comm(:drecv, name, ty, cont, ctx)
  end

  defp label({:esend, name, bound, cont}, ctx) do
    ev_comm(:esend, name, bound, cont, ctx)
  end

  defp label({:erecv, name, bound, cont}, ctx) do
    ev_comm(:erecv, name, bound, cont, ctx)
  end

  defp label({:isend, name, left, right}, ctx) do
    ix_comm(:isend, name, left, right, ctx)
  end

  defp label({:irecv, name, left, right}, ctx) do
    ix_comm(:irecv, name, left, right, ctx)
  end

  defp label({:choose, left, right}, ctx) do
    arm_comm(:choose, left, right, ctx)
  end

  defp label({:branch, left, right}, ctx) do
    arm_comm(:branch, left, right, ctx)
  end

  defp label({:rec, name, body}, ctx) do
    case label(body, ctx) do
      {:ok, body, ctx} ->
        if rec_guarded?(body, name) do
          {:ok, {:rec, name, body}, ctx}
        else
          {:error, blame(ctx, "unguarded rec")}
        end

      {:error, _} = err ->
        err
    end
  end

  defp label({:svar, name}, ctx), do: {:ok, {:svar, name}, ctx}

  defp label({:case, scrut, arms}, ctx) do
    with {:ok, ctx} <- call_ok(scrut, ctx),
         {:ok, arms, ctx} <- label_arms(arms, ctx) do
      {:ok, {:case, scrut, arms}, ctx}
    end
  end

  defp label({:sess, name, args}, ctx) do
    cond do
      name == ctx.self and not ctx.guarded ->
        {:error, blame(ctx, "unguarded session call")}

      name == ctx.self ->
        with {:ok, args, ctx} <- ev_args(args, ctx) do
          {:ok, {:sjump, name, args}, ctx}
        end

      name in ctx.st.stack ->
        {:error, blame(ctx, "dual cycle")}

      later?(name, ctx) ->
        {:error, blame(ctx, "session declared later")}

      true ->
        inline(name, args, ctx)
    end
  end

  defp label({:dual, ref}, ctx) do
    with {:ok, labeled, ctx} <- refer(ref, ctx) do
      {:ok, dualize(labeled, ctx), ctx}
    end
  end

  defp label({:seen, _, _, _}, ctx) do
    {:error, blame(ctx, "seen is not a state machine")}
  end

  defp label(_other, ctx), do: {:error, blame(ctx, "ill-formed protocol")}

  defp bind_comm(tag, name, ty, cont, ctx) do
    with :ok <- support(ty, ctx) do
      node = {tag, name, ty, :end}
      {step, ctx} = note(ctx, Session.step_proto(node))
      ctx = ctx |> guard() |> bind_name(name, ty)

      with {:ok, cont, ctx} <- label(cont, ctx) do
        {:ok, {tag, step, name, ty, cont}, ctx}
      end
    end
  end

  defp ev_comm(tag, name, bound, cont, ctx) do
    with :ok <- bound_ok(bound, ctx) do
      node = {tag, name, bound, :end}
      {step, ctx} = note(ctx, Session.step_proto(node))
      # The checker does not put an evidence name in scope for a later
      # length or jump. The runtime still stores the nat it checked.
      ctx = guard(ctx)
      ctx = %{ctx | bound: Map.put(ctx.bound, name, :nat)}

      with {:ok, cont, ctx} <- label(cont, ctx) do
        {:ok, {tag, step, name, bound, cont}, ctx}
      end
    end
  end

  defp ix_comm(tag, name, left, right, ctx) do
    node = {tag, name, :end, :end}
    {step, ctx} = note(ctx, Session.step_proto(node))
    ctx = ctx |> guard() |> bind_name(name, :bit)

    with {:ok, left, ctx} <- label(left, ctx),
         {:ok, right, ctx} <- label(right, ctx) do
      {:ok, {tag, step, name, left, right}, ctx}
    end
  end

  defp arm_comm(tag, left, right, ctx) do
    node = {tag, :end, :end}
    {step, ctx} = note(ctx, Session.step_proto(node))
    ctx = guard(ctx)

    with {:ok, left, ctx} <- label(left, ctx),
         {:ok, right, ctx} <- label(right, ctx) do
      {:ok, {tag, step, left, right}, ctx}
    end
  end

  defp label_arms(arms, ctx) do
    Enum.reduce_while(arms, {:ok, [], ctx}, fn {tag, proto}, {:ok, acc, ctx} ->
      case label(proto, ctx) do
        {:ok, proto, ctx} -> {:cont, {:ok, acc ++ [{tag, proto}], ctx}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp guard(ctx), do: %{ctx | guarded: true}

  defp bound_ok(bound, ctx) do
    case support_ix(bound, ctx, "bound #{show_ix(bound)}") do
      :ok -> :ok
      {:error, reason} -> {:error, blame(ctx, reason)}
    end
  end

  defp bind_name(ctx, name, ty) do
    subst =
      case ty do
        :nat -> Map.put(ctx.subst, name, {:var, name})
        _ -> Map.delete(ctx.subst, name)
      end

    %{ctx | subst: subst, bound: Map.put(ctx.bound, name, ty)}
  end

  defp note(ctx, action) do
    kind = action_kind(action)
    n = Map.fetch!(ctx.counts, kind) + 1
    ctx = %{ctx | counts: Map.put(ctx.counts, kind, n)}
    step = "#{ctx.file}:#{ctx.line} session #{ctx.name}: #{ordinal(n)} #{action}"
    {step, ctx}
  end

  defp action_kind("send" <> _), do: :send
  defp action_kind("recv" <> _), do: :recv
  defp action_kind("choose" <> _), do: :choose
  defp action_kind("branch" <> _), do: :branch
  defp action_kind(_), do: :other

  defp ordinal(1), do: "first"
  defp ordinal(2), do: "second"
  defp ordinal(3), do: "third"

  defp ordinal(n) when is_integer(n) and n > 3 do
    "#{n}#{ordinal_suffix(n)}"
  end

  defp ordinal_suffix(n) when is_integer(n) do
    mod100 = rem(n, 100)
    mod10 = rem(n, 10)

    cond do
      mod100 in 11..13 -> "th"
      mod10 == 1 -> "st"
      mod10 == 2 -> "nd"
      mod10 == 3 -> "rd"
      true -> "th"
    end
  end

  defp later?(name, ctx) do
    case Map.fetch(ctx.st.index, name) do
      {:ok, {i, _}} -> is_integer(ctx.index) and i > ctx.index
      :error -> false
    end
  end

  defp inline(name, args, ctx) do
    with {:ok, st} <- ensure(name, ctx.st),
         {:ok, args, ctx} <- ev_args(args, %{ctx | st: st}) do
      entry = Map.fetch!(ctx.st.opened, name)

      if length(entry.params) == length(args) do
        subst = Map.new(Enum.zip(entry.params, args))
        {:ok, subst_p(entry.proto, subst), ctx}
      else
        {:error, blame(ctx, "wrong number of session arguments")}
      end
    end
  end

  defp refer(name, ctx) when is_binary(name) do
    if name in ctx.st.stack or name == ctx.self do
      {:error, blame(ctx, "dual cycle")}
    else
      with {:ok, st} <- ensure(name, ctx.st) do
        entry = Map.fetch!(st.opened, name)
        {:ok, entry.proto, %{ctx | st: st}}
      end
    end
  end

  defp refer({:sess, name, args}, ctx) do
    if name in ctx.st.stack or name == ctx.self do
      {:error, blame(ctx, "dual cycle")}
    else
      with {:ok, st} <- ensure(name, ctx.st),
           {:ok, args, ctx} <- ev_args(args, %{ctx | st: st}) do
        entry = Map.fetch!(ctx.st.opened, name)

        if length(entry.params) == length(args) do
          subst = Map.new(Enum.zip(entry.params, args))
          {:ok, subst_p(entry.proto, subst), ctx}
        else
          {:error, blame(ctx, "wrong number of session arguments")}
        end
      end
    end
  end

  defp refer(_, ctx), do: {:error, blame(ctx, "unknown session")}

  defp dualize(labeled, ctx) do
    stripped = strip(labeled)
    dualed = Session.dual(stripped)
    zip_dual(dualed, labeled, %{file: ctx.file, line: ctx.line, name: ctx.name})
  end

  defp strip({:end, _}), do: :end
  defp strip({:send, _, ty, c}), do: {:send, ty, strip(c)}
  defp strip({:recv, _, ty, c}), do: {:recv, ty, strip(c)}
  defp strip({:dsend, _, name, ty, c}), do: {:dsend, name, ty, strip(c)}
  defp strip({:drecv, _, name, ty, c}), do: {:drecv, name, ty, strip(c)}
  defp strip({:esend, _, name, bound, c}), do: {:esend, name, bound, strip(c)}
  defp strip({:erecv, _, name, bound, c}), do: {:erecv, name, bound, strip(c)}
  defp strip({:isend, _, name, l, r}), do: {:isend, name, strip(l), strip(r)}
  defp strip({:irecv, _, name, l, r}), do: {:irecv, name, strip(l), strip(r)}
  defp strip({:choose, _, l, r}), do: {:choose, strip(l), strip(r)}
  defp strip({:branch, _, l, r}), do: {:branch, strip(l), strip(r)}
  defp strip({:rec, name, body}), do: {:rec, name, strip(body)}
  defp strip({:svar, name}), do: {:svar, name}
  defp strip({:sjump, target, args}), do: {:sjump, target, args}

  defp strip({:case, scrut, arms}) do
    {:case, scrut, Enum.map(arms, fn {tag, proto} -> {tag, strip(proto)} end)}
  end

  defp zip_dual(:end, {:end, step}, meta), do: {:end, rewrite_step(step, meta)}

  defp zip_dual({:recv, ty, c1}, {:send, step, _, c2}, meta) do
    {:recv, rewrite_step(step, meta), ty, zip_dual(c1, c2, meta)}
  end

  defp zip_dual({:send, ty, c1}, {:recv, step, _, c2}, meta) do
    {:send, rewrite_step(step, meta), ty, zip_dual(c1, c2, meta)}
  end

  defp zip_dual({:drecv, name, ty, c1}, {:dsend, step, _, _, c2}, meta) do
    {:drecv, rewrite_step(step, meta), name, ty, zip_dual(c1, c2, meta)}
  end

  defp zip_dual({:dsend, name, ty, c1}, {:drecv, step, _, _, c2}, meta) do
    {:dsend, rewrite_step(step, meta), name, ty, zip_dual(c1, c2, meta)}
  end

  defp zip_dual({:erecv, name, bound, c1}, {:esend, step, _, _, c2}, meta) do
    {:erecv, rewrite_step(step, meta), name, bound, zip_dual(c1, c2, meta)}
  end

  defp zip_dual({:esend, name, bound, c1}, {:erecv, step, _, _, c2}, meta) do
    {:esend, rewrite_step(step, meta), name, bound, zip_dual(c1, c2, meta)}
  end

  defp zip_dual({:irecv, name, l1, r1}, {:isend, step, _, l2, r2}, meta) do
    {:irecv, rewrite_step(step, meta), name, zip_dual(l1, l2, meta), zip_dual(r1, r2, meta)}
  end

  defp zip_dual({:isend, name, l1, r1}, {:irecv, step, _, l2, r2}, meta) do
    {:isend, rewrite_step(step, meta), name, zip_dual(l1, l2, meta), zip_dual(r1, r2, meta)}
  end

  defp zip_dual({:branch, l1, r1}, {:choose, step, l2, r2}, meta) do
    {:branch, rewrite_step(step, meta), zip_dual(l1, l2, meta), zip_dual(r1, r2, meta)}
  end

  defp zip_dual({:choose, l1, r1}, {:branch, step, l2, r2}, meta) do
    {:choose, rewrite_step(step, meta), zip_dual(l1, l2, meta), zip_dual(r1, r2, meta)}
  end

  defp zip_dual({:rec, name, b1}, {:rec, _, b2}, meta) do
    {:rec, name, zip_dual(b1, b2, meta)}
  end

  defp zip_dual({:svar, name}, {:svar, _}, _meta), do: {:svar, name}

  defp zip_dual({:sjump, target, args}, {:sjump, _, _}, _meta) do
    {:sjump, target, args}
  end

  defp zip_dual({:case, scrut, arms1}, {:case, _, arms2}, meta) do
    arms =
      Enum.zip(arms1, arms2)
      |> Enum.map(fn {{tag, p1}, {_tag, p2}} -> {tag, zip_dual(p1, p2, meta)} end)

    {:case, scrut, arms}
  end

  defp rewrite_step(step, %{file: file, line: line, name: name}) do
    action =
      case String.split(step, ": ", parts: 2) do
        [_prefix, action] -> flip_action(action)
        _ -> "end"
      end

    "#{file}:#{line} session #{name}: #{action}"
  end

  defp flip_action("end"), do: "end"

  defp flip_action(action) do
    case String.split(action, " ", parts: 3) do
      [ord, "send"] -> ord <> " recv"
      [ord, "recv"] -> ord <> " send"
      [ord, "send", rest] -> ord <> " recv " <> rest
      [ord, "recv", rest] -> ord <> " send " <> rest
      [ord, "choose"] -> ord <> " branch"
      [ord, "branch"] -> ord <> " choose"
      [ord, "choose", rest] -> ord <> " branch " <> rest
      [ord, "branch", rest] -> ord <> " choose " <> rest
      _ -> action
    end
  end

  # A `rec` whose body can reach its own variable without an action
  # would unfold forever. The refusal is at emit time.
  defp rec_guarded?(proto, name), do: rec_hits?(proto, name, false)

  defp rec_hits?({:svar, name}, name, guarded), do: guarded
  defp rec_hits?({:svar, _}, _name, _guarded), do: true
  defp rec_hits?({:rec, _, body}, name, guarded), do: rec_hits?(body, name, guarded)
  defp rec_hits?({:send, _, _, c}, name, _), do: rec_hits?(c, name, true)
  defp rec_hits?({:recv, _, _, c}, name, _), do: rec_hits?(c, name, true)
  defp rec_hits?({:dsend, _, _, _, c}, name, _), do: rec_hits?(c, name, true)
  defp rec_hits?({:drecv, _, _, _, c}, name, _), do: rec_hits?(c, name, true)
  defp rec_hits?({:esend, _, _, _, c}, name, _), do: rec_hits?(c, name, true)
  defp rec_hits?({:erecv, _, _, _, c}, name, _), do: rec_hits?(c, name, true)

  defp rec_hits?({:isend, _, _, l, r}, name, _),
    do: rec_hits?(l, name, true) and rec_hits?(r, name, true)

  defp rec_hits?({:irecv, _, _, l, r}, name, _),
    do: rec_hits?(l, name, true) and rec_hits?(r, name, true)

  defp rec_hits?({:choose, _, l, r}, name, _),
    do: rec_hits?(l, name, true) and rec_hits?(r, name, true)

  defp rec_hits?({:branch, _, l, r}, name, _),
    do: rec_hits?(l, name, true) and rec_hits?(r, name, true)

  defp rec_hits?({:sjump, _, _}, _name, guarded), do: guarded
  defp rec_hits?(:end, _name, _), do: true
  defp rec_hits?({:end, _}, _name, _), do: true

  defp rec_hits?({:case, _, arms}, name, guarded) do
    Enum.all?(arms, fn {_tag, proto} -> rec_hits?(proto, name, guarded) end)
  end

  defp rec_hits?(_, _, _), do: true

  defp call_ok({:run, fname, scrut}, ctx) do
    case Map.get(ctx.bound, scrut) do
      nil ->
        {:error, blame(ctx, "cannot call run #{fname}")}

      ty ->
        case run_shape(fname, ctx.st.book) do
          {:ok, dom, cod} ->
            if dom == ty do
              st = %{
                ctx.st
                | runs: MapSet.put(ctx.st.runs, fname),
                  results: Map.put(ctx.st.results, fname, cod)
              }

              {:ok, %{ctx | st: st}}
            else
              {:error, blame(ctx, "cannot call run #{fname}")}
            end

          :error ->
            {:error, blame(ctx, "cannot call run #{fname}")}
        end
    end
  end

  defp call_ok(_scrut, ctx), do: {:ok, ctx}

  defp run_shape(fname, book) do
    case Enum.find(Emit.run_defs(book), &(&1.name == fname)) do
      nil ->
        :error

      dfn ->
        with {:ok, ty} <- Ast.to_db(dfn.type),
             {:ok, dom, cod} <- live_one(ty),
             {:ok, dom} <- as_pay(dom, book),
             {:ok, cod} <- as_pay(cod, book),
             true <- tag_type?(cod, book) do
          {:ok, dom, cod}
        else
          _ -> :error
        end
    end
  end

  defp live_one({:pi, :erased, _, _, body}), do: live_one(body)

  defp live_one({:pi, _, dom, _, body}) do
    if more_live?(body), do: :error, else: {:ok, dom, drop_erased(body)}
  end

  defp live_one(_), do: :error

  defp more_live?({:pi, :erased, _, _, body}), do: more_live?(body)
  defp more_live?({:pi, _, _, _, _}), do: true
  defp more_live?(_), do: false

  defp drop_erased({:pi, :erased, _, _, body}), do: drop_erased(body)
  defp drop_erased(ty), do: ty

  defp as_pay(:nat, _book), do: {:ok, :nat}
  defp as_pay(:bit, _book), do: {:ok, :bit}
  defp as_pay(:unit, _book), do: {:ok, :unit}

  defp as_pay({:prod, a, b}, book) do
    with {:ok, a} <- as_pay(a, book), {:ok, b} <- as_pay(b, book) do
      {:ok, {:pair, a, b}}
    end
  end

  defp as_pay({:def, name}, book) do
    if data?(name, book), do: {:ok, {:dat, name, []}}, else: :error
  end

  defp as_pay({:app, _, _} = term, book) do
    {head, args} = spine(term, [])

    case head do
      {:def, name} ->
        if data?(name, book) do
          with {:ok, args} <- map_pay(args, book) do
            {:ok, {:dat, name, args}}
          end
        else
          :error
        end

      _ ->
        :error
    end
  end

  defp as_pay(_, _), do: :error

  defp map_pay(args, book) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case as_pay(arg, book) do
        {:ok, ty} -> {:cont, {:ok, acc ++ [ty]}}
        :error -> {:halt, :error}
      end
    end)
  end

  defp tag_type?(:bit, _book), do: true
  defp tag_type?({:dat, name, _}, book), do: data?(name, book)
  defp tag_type?(_, _), do: false

  defp data?(name, book) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(head, acc), do: {head, acc}

  defp support(ty, ctx) do
    case support_ty(ty, ctx) do
      :ok -> :ok
      {:error, reason} -> {:error, blame(ctx, reason)}
    end
  end

  defp support_ty(:nat, _ctx), do: :ok
  defp support_ty(:bit, _ctx), do: :ok
  defp support_ty(:unit, _ctx), do: :ok

  defp support_ty({:pair, a, b}, ctx) do
    with :ok <- support_ty(a, ctx), do: support_ty(b, ctx)
  end

  defp support_ty({:rec, fields}, ctx) when is_list(fields) do
    Enum.reduce_while(fields, :ok, fn {_name, ty}, :ok ->
      case support_ty(ty, ctx) do
        :ok -> {:cont, :ok}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp support_ty({:vec, elem, ix}, ctx) do
    with :ok <- support_ty(elem, ctx) do
      support_ix(ix, ctx, "vector length #{show_ix(ix)}")
    end
  end

  defp support_ty({:dat, name, args}, ctx) when is_binary(name) and is_list(args) do
    decls = Session.payload_decls(ctx.st.book)

    if Map.has_key?(decls, name) do
      Enum.reduce_while(args, :ok, fn ty, :ok ->
        case support_ty(ty, ctx) do
          :ok -> {:cont, :ok}
          {:error, _} = err -> {:halt, err}
        end
      end)
    else
      {:error, "payload #{name} is not supported"}
    end
  end

  defp support_ty(other, _ctx), do: {:error, "payload #{inspect(other)} is not supported"}

  defp support_ix({:lit, n}, _ctx, _what) when is_integer(n) and n >= 0, do: :ok

  defp support_ix({:var, name}, ctx, what) do
    if Map.has_key?(ctx.subst, name), do: :ok, else: {:error, "cannot evaluate #{what}"}
  end

  defp support_ix({:suc, inner}, ctx, what), do: support_ix(inner, ctx, what)
  defp support_ix(_other, _ctx, what), do: {:error, "cannot evaluate #{what}"}

  defp ev_args(args, ctx) do
    Enum.reduce_while(args, {:ok, [], ctx}, fn arg, {:ok, acc, ctx} ->
      case ev_arg(arg, ctx) do
        {:ok, exp} -> {:cont, {:ok, acc ++ [exp], ctx}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp ev_arg({:lit, n}, _ctx) when is_integer(n) and n >= 0, do: {:ok, {:lit, n}}
  defp ev_arg({:lit, n}, ctx), do: {:error, blame(ctx, "cannot evaluate argument #{n}")}

  defp ev_arg({:var, name}, ctx) do
    case Map.get(ctx.subst, name) do
      {:lit, n} ->
        {:ok, {:lit, n}}

      {:var, v} ->
        {:ok, {:var, v}}

      nil ->
        case Session.eval_run(to_string(name), [], ctx.st.book) do
          n when is_integer(n) and n >= 0 -> {:ok, {:lit, n}}
          _ -> {:error, blame(ctx, "cannot evaluate argument #{name}")}
        end
    end
  end

  defp ev_arg({:suc, inner}, ctx) do
    case ev_arg(inner, ctx) do
      {:ok, {:lit, n}} -> {:ok, {:lit, n + 1}}
      {:ok, other} -> {:ok, {:suc, other}}
      {:error, _} = err -> err
    end
  end

  defp ev_arg({:con, name, args} = arg, ctx) do
    with {:ok, args, _ctx} <- ev_args(args, ctx) do
      if Enum.all?(args, &match?({:lit, _}, &1)) do
        vals = Enum.map(args, fn {:lit, n} -> n end)

        case Session.eval_run(name, vals, ctx.st.book) do
          n when is_integer(n) and n >= 0 ->
            {:ok, {:lit, n}}

          _ ->
            {:error, blame(ctx, "cannot evaluate argument #{show_ix(arg)}")}
        end
      else
        {:error, blame(ctx, "cannot evaluate argument #{show_ix(arg)}")}
      end
    end
  end

  defp ev_arg(other, ctx), do: {:error, blame(ctx, "cannot evaluate argument #{show_ix(other)}")}

  defp show_ix({:lit, n}), do: "#{n}"
  defp show_ix({:var, name}), do: "#{name}"
  defp show_ix({:suc, inner}), do: "(suc #{show_ix(inner)})"
  defp show_ix({:con, name, []}), do: "#{name}"

  defp show_ix({:con, name, args}) do
    "(#{name} #{Enum.map_join(args, " ", &show_ix/1)})"
  end

  defp show_ix(other), do: inspect(other)

  defp blame(ctx, reason), do: "#{ctx.file}:#{ctx.line} session #{ctx.name}: #{reason}"

  defp subst_p({:end, step}, _sub), do: {:end, step}
  defp subst_p({:send, step, ty, c}, sub), do: {:send, step, subst_ty(ty, sub), subst_p(c, sub)}
  defp subst_p({:recv, step, ty, c}, sub), do: {:recv, step, subst_ty(ty, sub), subst_p(c, sub)}

  defp subst_p({:dsend, step, name, ty, c}, sub) do
    {:dsend, step, name, subst_ty(ty, sub), subst_p(c, sub)}
  end

  defp subst_p({:drecv, step, name, ty, c}, sub) do
    {:drecv, step, name, subst_ty(ty, sub), subst_p(c, sub)}
  end

  defp subst_p({:esend, step, name, bound, c}, sub) do
    {:esend, step, name, subst_ix(bound, sub), subst_p(c, sub)}
  end

  defp subst_p({:erecv, step, name, bound, c}, sub) do
    {:erecv, step, name, subst_ix(bound, sub), subst_p(c, sub)}
  end

  defp subst_p({:isend, step, name, l, r}, sub) do
    {:isend, step, name, subst_p(l, sub), subst_p(r, sub)}
  end

  defp subst_p({:irecv, step, name, l, r}, sub) do
    {:irecv, step, name, subst_p(l, sub), subst_p(r, sub)}
  end

  defp subst_p({:choose, step, l, r}, sub), do: {:choose, step, subst_p(l, sub), subst_p(r, sub)}
  defp subst_p({:branch, step, l, r}, sub), do: {:branch, step, subst_p(l, sub), subst_p(r, sub)}
  defp subst_p({:rec, name, body}, sub), do: {:rec, name, subst_p(body, sub)}
  defp subst_p({:svar, name}, _sub), do: {:svar, name}

  defp subst_p({:sjump, target, args}, sub),
    do: {:sjump, target, Enum.map(args, &subst_ix(&1, sub))}

  defp subst_p({:case, scrut, arms}, sub) do
    {:case, scrut, Enum.map(arms, fn {tag, proto} -> {tag, subst_p(proto, sub)} end)}
  end

  defp subst_p(other, _sub), do: other

  defp subst_ty({:pair, a, b}, sub), do: {:pair, subst_ty(a, sub), subst_ty(b, sub)}

  defp subst_ty({:rec, fields}, sub) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, subst_ty(ty, sub)} end)}
  end

  defp subst_ty({:vec, elem, ix}, sub), do: {:vec, subst_ty(elem, sub), subst_ix(ix, sub)}

  defp subst_ty({:dat, name, args}, sub) do
    {:dat, name, Enum.map(args, &subst_ty(&1, sub))}
  end

  defp subst_ty(ty, _sub), do: ty

  defp subst_ix({:lit, n}, _sub), do: {:lit, n}

  defp subst_ix({:var, name}, sub) do
    case Map.get(sub, name) do
      nil -> {:var, name}
      exp -> exp
    end
  end

  defp subst_ix({:suc, inner}, sub) do
    case subst_ix(inner, sub) do
      {:lit, n} -> {:lit, n + 1}
      other -> {:suc, other}
    end
  end

  defp subst_ix(other, _sub), do: other

  # ---- source --------------------------------------------------------------

  defp source(module, book, st) do
    runs = close_runs(st.runs, book)
    duals = dual_templates(st)
    names = Emit.elixir_names(book)
    run_src = Emit.emit_private_runs(book, MapSet.to_list(runs))
    codec = repr_source(book, names)
    reprs = repr_names(book)

    text =
      """
      defmodule #{inspect(module)} do
        @moduledoc false
        # Generated by Muro - a session endpoint is a state machine. The transport stays with the host.

      #{indent(run_src, 2)}

      #{indent(codec, 2)}

      #{indent(interpreter(module, st, names, reprs, duals), 2)}

      #{indent(children(module, st), 2)}
      end
      """

    text
    |> Code.format_string!()
    |> IO.iodata_to_binary()
    |> Kernel.<>("\n")
  end

  defp repr_source(book, names) do
    case Muro.Repr.elixir(book, names) do
      "" -> ""
      codec -> codec
    end
  end

  defp repr_names(book) do
    book
    |> Enum.filter(&(Map.get(&1, :kind) == :repr))
    |> Enum.map(& &1.name)
  end

  defp close_runs(seeds, book) do
    grow = fn names ->
      Enum.reduce(names, names, fn name, acc ->
        case Enum.find(Emit.run_defs(book), &(&1.name == name)) do
          nil ->
            acc

          dfn ->
            case Ast.to_db(dfn.body) do
              {:ok, body} -> run_refs(body, book, acc)
              _ -> acc
            end
        end
      end)
    end

    fix(seeds, grow)
  end

  defp fix(set, grow) do
    next = grow.(set)
    if MapSet.equal?(next, set), do: set, else: fix(next, grow)
  end

  defp run_refs({:app, _, _} = term, book, acc) do
    {head, args} = spine(term, [])

    acc =
      case head do
        {:def, name} ->
          if run_name?(name, book), do: MapSet.put(acc, name), else: acc

        _ ->
          acc
      end

    Enum.reduce([head | args], acc, &run_refs(&1, book, &2))
  end

  defp run_refs({:def, name}, book, acc) do
    if run_name?(name, book), do: MapSet.put(acc, name), else: acc
  end

  defp run_refs(term, book, acc) when is_tuple(term) do
    term |> Tuple.to_list() |> Enum.reduce(acc, &run_refs(&1, book, &2))
  end

  defp run_refs(term, book, acc) when is_list(term) do
    Enum.reduce(term, acc, &run_refs(&1, book, &2))
  end

  defp run_refs(_, _, acc), do: acc

  defp run_name?(name, book) do
    Emit.run_defs(book) |> Enum.any?(&(&1.name == name)) and
      not Enum.any?(book, fn
        %{kind: :data, ctors: ctors} -> Enum.any?(ctors, &(&1.name == name))
        _ -> false
      end)
  end

  defp dual_templates(st) do
    needed =
      st.opened
      |> Map.values()
      |> Enum.reduce(MapSet.new(), fn entry, acc -> dual_targets(entry.proto, acc) end)

    Map.new(needed, fn name ->
      entry = Map.fetch!(st.opened, name)
      meta = %{file: entry.file, line: entry.line, name: name}
      proto = zip_dual(Session.dual(strip(entry.proto)), entry.proto, meta)
      {name, {entry.params, proto}}
    end)
  end

  defp dual_targets({:sjump, {:dual, name}, _}, acc) when is_binary(name),
    do: MapSet.put(acc, name)

  defp dual_targets({:sjump, _, _}, acc), do: acc
  defp dual_targets({:end, _}, acc), do: acc
  defp dual_targets({:svar, _}, acc), do: acc
  defp dual_targets({:rec, _, body}, acc), do: dual_targets(body, acc)
  defp dual_targets({:send, _, _, c}, acc), do: dual_targets(c, acc)
  defp dual_targets({:recv, _, _, c}, acc), do: dual_targets(c, acc)
  defp dual_targets({:dsend, _, _, _, c}, acc), do: dual_targets(c, acc)
  defp dual_targets({:drecv, _, _, _, c}, acc), do: dual_targets(c, acc)
  defp dual_targets({:esend, _, _, _, c}, acc), do: dual_targets(c, acc)
  defp dual_targets({:erecv, _, _, _, c}, acc), do: dual_targets(c, acc)
  defp dual_targets({:isend, _, _, l, r}, acc), do: dual_targets(r, dual_targets(l, acc))
  defp dual_targets({:irecv, _, _, l, r}, acc), do: dual_targets(r, dual_targets(l, acc))
  defp dual_targets({:choose, _, l, r}, acc), do: dual_targets(r, dual_targets(l, acc))
  defp dual_targets({:branch, _, l, r}, acc), do: dual_targets(r, dual_targets(l, acc))

  defp dual_targets({:case, _, arms}, acc) do
    Enum.reduce(arms, acc, fn {_tag, proto}, acc -> dual_targets(proto, acc) end)
  end

  defp dual_targets(_, acc), do: acc

  defp interpreter(_module, st, names, reprs, duals) do
    sessions =
      Enum.map(st.sessions, fn sess ->
        entry = Map.fetch!(st.opened, sess.name)
        {sess.name, {entry.params, entry.proto}}
      end)

    ends =
      Map.new(st.sessions, fn sess ->
        entry = Map.fetch!(st.opened, sess.name)
        {sess.name, entry.end_step}
      end)

    decls = Session.payload_decls(st.book)
    safe = safe_maps(decls)

    """
    @muro_fsm_cap 100_000

    @doc false
    def muro_fsm_init(key, args) do
      case muro_fsm_nats(key, args) do
        :ok ->
          {params, proto} = Map.fetch!(muro_fsm_templates(), key)
          env = Map.new(Enum.zip(params, args))
          muro_fsm_expose(%{k: key, p: proto, e: env, r: %{}, s: muro_fsm_end(key)})

        {:error, msg} ->
          raise ArgumentError, msg
      end
    end

    @doc false
    def muro_fsm_step(key, dir, state, value) when dir in [:send, :recv] do
      case muro_fsm_prep(key, state) do
        {:ok, st} ->
          case muro_fsm_expose(st) do
            %{p: {:end, step}} -> {:error, {:unexpected, step, :done, value}}
            %{p: {:stuck, step}} -> {:error, {:unexpected, step, :done, value}}
            st -> muro_fsm_act(dir, st, value)
          end

        :bad ->
          {:error, {:unexpected, muro_fsm_end(key), :done, value}}
      end
    end

    def muro_fsm_step(key, _dir, _state, value) do
      {:error, {:unexpected, muro_fsm_end(key), :done, value}}
    end

    @doc false
    def muro_fsm_done?(key, state) do
      case muro_fsm_prep(key, state) do
        {:ok, st} -> match?(%{p: {:end, _}}, muro_fsm_expose(st))
        :bad -> false
      end
    end

    @doc false
    def muro_fsm_expected(key, state) do
      case muro_fsm_prep(key, state) do
        {:ok, st} -> muro_fsm_expect(muro_fsm_expose(st))
        :bad -> :done
      end
    end

    @doc false
    def muro_fsm_trace(key, args, trace, complete?) when is_list(trace) do
      case muro_fsm_nats(key, args) do
        :ok ->
          muro_fsm_walk(muro_fsm_init(key, args), trace, 0, key, complete?)

        {:error, msg} ->
          raise ArgumentError, msg
      end
    end

    defp muro_fsm_walk(state, [], index, key, true) do
      if muro_fsm_done?(key, state) do
        :ok
      else
        {:error, {index, {:incomplete, muro_fsm_at(state), muro_fsm_expected(key, state)}}}
      end
    end

    defp muro_fsm_walk(_state, [], _index, _key, false), do: :ok

    defp muro_fsm_walk(state, [{dir, value} | rest], index, key, complete?) when dir in [:send, :recv] do
      case muro_fsm_step(key, dir, state, value) do
        {:ok, next} -> muro_fsm_walk(next, rest, index + 1, key, complete?)
        {:error, reason} -> {:error, {index, reason}}
      end
    end

    defp muro_fsm_walk(state, [other | _rest], index, key, _complete?) do
      {:error, {index, {:unexpected, muro_fsm_at(state), muro_fsm_expected(key, state), other}}}
    end

    defp muro_fsm_at(state) do
      case muro_fsm_expose(state) do
        %{s: step} when is_binary(step) -> step
        _ -> muro_fsm_end(state.k)
      end
    end

    defp muro_fsm_nats(key, args) when is_list(args) do
      case Map.get(muro_fsm_templates(), key) do
        {params, _proto} when length(params) == length(args) ->
          muro_fsm_nat_args(key, args, 1)

        _ ->
          {:error, "session " <> key <> ": check_trace requires args: [...]"}
      end
    end

    defp muro_fsm_nats(key, _args) do
      {:error, "session " <> key <> ": check_trace requires args: [...]"}
    end

    defp muro_fsm_nat_args(_key, [], _i), do: :ok

    defp muro_fsm_nat_args(key, [arg | rest], i) do
      if is_integer(arg) and arg >= 0 do
        muro_fsm_nat_args(key, rest, i + 1)
      else
        {:error, "session " <> key <> ": argument " <> Integer.to_string(i) <> " is not a nat"}
      end
    end

    defp muro_fsm_prep(key, %{k: key, p: _, e: env, r: rec, s: step} = st)
         when is_map(env) and is_map(rec) and is_binary(step) do
      {:ok, st}
    end

    defp muro_fsm_prep(_key, _state), do: :bad

    defp muro_fsm_expose(st), do: muro_fsm_expose(st, [])

    defp muro_fsm_expose(%{p: {:rec, name, body}} = st, seen) do
      muro_fsm_expose(%{st | p: body, r: Map.put(st.r, name, body)}, seen)
    end

    defp muro_fsm_expose(%{p: {:svar, name}} = st, seen) do
      mark = {:svar, name}

      cond do
        mark in seen ->
          %{st | p: {:stuck, st.s}}

        true ->
          case Map.get(st.r, name) do
            nil -> %{st | p: {:stuck, st.s}}
            body -> muro_fsm_expose(%{st | p: body}, [mark | seen])
          end
      end
    end

    defp muro_fsm_expose(%{p: {:sjump, target, args}} = st, seen) do
      mark = {:jump, target, args}

      cond do
        mark in seen ->
          %{st | p: {:stuck, st.s}}

        true ->
          case muro_fsm_enter(target, args, st.e) do
            {:ok, proto, env} ->
              muro_fsm_expose(%{st | p: proto, e: env, r: %{}}, [mark | seen])

            :error ->
              %{st | p: {:stuck, st.s}}
          end
      end
    end

    defp muro_fsm_expose(%{p: {:case, _, _}} = st, _seen), do: %{st | p: {:stuck, st.s}}
    defp muro_fsm_expose(%{p: {:end, step}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:send, step, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:recv, step, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:dsend, step, _, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:drecv, step, _, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:esend, step, _, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:erecv, step, _, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:isend, step, _, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:irecv, step, _, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:choose, step, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:branch, step, _, _}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(%{p: {:stuck, step}} = st, _seen), do: %{st | s: step}
    defp muro_fsm_expose(st, _seen), do: st

    defp muro_fsm_enter(name, args, env) when is_binary(name) do
      muro_fsm_open(muro_fsm_templates(), name, args, env)
    end

    defp muro_fsm_enter({:dual, name}, args, env) when is_binary(name) do
      muro_fsm_open(muro_fsm_duals(), name, args, env)
    end

    defp muro_fsm_enter(_, _, _), do: :error

    defp muro_fsm_open(table, name, args, env) do
      case Map.get(table, name) do
        {params, proto} ->
          case muro_fsm_vals(args, env) do
            {:ok, vals} when length(vals) == length(params) ->
              {:ok, proto, Map.new(Enum.zip(params, vals))}

            _ ->
              :error
          end

        _ ->
          :error
      end
    end

    defp muro_fsm_vals(args, env) do
      Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
        case muro_fsm_ix(arg, env) do
          {:ok, n} -> {:cont, {:ok, acc ++ [n]}}
          :error -> {:halt, :error}
        end
      end)
    end

    defp muro_fsm_ix({:lit, n}, _env) when is_integer(n) and n >= 0, do: {:ok, n}

    defp muro_fsm_ix({:var, name}, env) do
      case Map.get(env, name) do
        n when is_integer(n) and n >= 0 -> {:ok, n}
        _ -> :error
      end
    end

    defp muro_fsm_ix({:suc, inner}, env) do
      case muro_fsm_ix(inner, env) do
        {:ok, n} -> {:ok, n + 1}
        :error -> :error
      end
    end

    defp muro_fsm_ix(_, _), do: :error

    defp muro_fsm_act(dir, %{p: proto, s: step} = st, value) do
      case {dir, proto} do
        {:send, {:send, ^step, ty, cont}} ->
          muro_fsm_payload_step(st, ty, cont, value, step, nil)

        {:recv, {:recv, ^step, ty, cont}} ->
          muro_fsm_payload_step(st, ty, cont, value, step, nil)

        {:send, {:dsend, ^step, name, ty, cont}} ->
          muro_fsm_payload_step(st, ty, cont, value, step, name)

        {:recv, {:drecv, ^step, name, ty, cont}} ->
          muro_fsm_payload_step(st, ty, cont, value, step, name)

        {:send, {:esend, ^step, name, bound, cont}} ->
          muro_fsm_evidence(st, name, bound, cont, value, step)

        {:recv, {:erecv, ^step, name, bound, cont}} ->
          muro_fsm_evidence(st, name, bound, cont, value, step)

        {:send, {:isend, ^step, name, left, right}} ->
          muro_fsm_index(st, name, left, right, value, step)

        {:recv, {:irecv, ^step, name, left, right}} ->
          muro_fsm_index(st, name, left, right, value, step)

        {:send, {:choose, ^step, left, right}} ->
          muro_fsm_pick(st, left, right, value, step, :send)

        {:recv, {:branch, ^step, left, right}} ->
          muro_fsm_pick(st, left, right, value, step, :recv)

        _ ->
          {:error, {:unexpected, step, muro_fsm_expect(st), value}}
      end
    end

    defp muro_fsm_payload_step(st, ty, cont, value, step, name) do
      case muro_fsm_take(ty, value, st.e) do
        {:ok, wire} ->
          dir = muro_fsm_comm_dir(st.p)
          st = if is_nil(name), do: st, else: %{st | e: Map.put(st.e, name, wire)}
          muro_fsm_continue(%{st | p: cont}, name, value, ty, dir)

        :error ->
          {:error, {:unexpected, step, muro_fsm_expect_ty(st, ty), value}}
      end
    end

    defp muro_fsm_comm_dir({:send, _, _, _}), do: :send
    defp muro_fsm_comm_dir({:dsend, _, _, _, _}), do: :send
    defp muro_fsm_comm_dir(_), do: :recv

    defp muro_fsm_continue(st, name, host_value, ty, dir) do
      case muro_fsm_quiet(st, []) do
        %{p: {:case, scrut, arms}} = st2 ->
          muro_fsm_arm(st2, name, host_value, ty, scrut, arms, dir)

        st2 ->
          {:ok, muro_fsm_expose(st2)}
      end
    end

    defp muro_fsm_quiet(%{p: {:rec, name, body}} = st, seen) do
      muro_fsm_quiet(%{st | p: body, r: Map.put(st.r, name, body)}, seen)
    end

    defp muro_fsm_quiet(%{p: {:svar, name}} = st, seen) do
      mark = {:svar, name}

      cond do
        mark in seen ->
          %{st | p: {:stuck, st.s}}

        true ->
          case Map.get(st.r, name) do
            nil -> %{st | p: {:stuck, st.s}}
            body -> muro_fsm_quiet(%{st | p: body}, [mark | seen])
          end
      end
    end

    defp muro_fsm_quiet(%{p: {:sjump, target, args}} = st, seen) do
      mark = {:jump, target, args}

      cond do
        mark in seen ->
          %{st | p: {:stuck, st.s}}

        true ->
          case muro_fsm_enter(target, args, st.e) do
            {:ok, proto, env} ->
              muro_fsm_quiet(%{st | p: proto, e: env, r: %{}}, [mark | seen])

            :error ->
              %{st | p: {:stuck, st.s}}
          end
      end
    end

    defp muro_fsm_quiet(st, _seen), do: st

    defp muro_fsm_arm(st, name, host_value, ty, scrut, arms, dir) do
      scrut_name =
        case scrut do
          {:name, n} -> n
          {:run, _, n} -> n
          _ -> nil
        end

      expected = muro_fsm_dir_ty(dir, ty, st.e)

      cond do
        scrut_name != name ->
          {:error, {:unexpected, st.s, expected, host_value}}

        true ->
          case muro_fsm_select(scrut, host_value, ty, arms, st) do
            {:ok, proto} -> {:ok, muro_fsm_expose(%{st | p: proto})}
            :cap -> {:error, {:unexpected, st.s, {:nat_at_most, @muro_fsm_cap}, host_value}}
            :error -> {:error, {:unexpected, st.s, expected, host_value}}
          end
      end
    end

    defp muro_fsm_dir_ty(:send, ty, env), do: {:send, muro_fsm_desc(muro_fsm_subst(ty, env))}
    defp muro_fsm_dir_ty(_dir, ty, env), do: {:recv, muro_fsm_desc(muro_fsm_subst(ty, env))}

    # The arm is the constructor of the wire value just stored under the
    # scrutinee, or of the run applied to that value.
    defp muro_fsm_select({:name, name}, _host, _ty, arms, st) do
      muro_fsm_by_tag(muro_fsm_tag(Map.get(st.e, name)), arms)
    end

    defp muro_fsm_select({:run, fname, name}, _host, ty, arms, st) do
      ty = muro_fsm_subst(ty, st.e)

      case muro_fsm_to_emitted(Map.get(st.e, name), ty) do
        {:ok, arg} ->
          muro_fsm_by_tag(muro_fsm_result_tag(muro_fsm_call(fname, arg)), arms)

        :cap ->
          :cap

        :error ->
          :error
      end
    end

    defp muro_fsm_select(_, _, _, _, _), do: :error

    defp muro_fsm_by_tag(nil, _arms), do: :error

    defp muro_fsm_by_tag(tag, arms) when is_binary(tag) do
      case Enum.find_value(arms, fn
             {^tag, proto} -> proto
             _ -> nil
           end) do
        nil -> :error
        proto -> {:ok, proto}
      end
    end

    defp muro_fsm_by_tag(_, _), do: :error

    defp muro_fsm_evidence(st, name, bound, cont, value, step) do
      desc = muro_fsm_bound_desc(bound, st.e)

      expected =
        case st.p do
          {:erecv, _, _, _, _} -> {:recv, desc}
          _ -> {:send, desc}
        end

      case muro_fsm_take(:nat, value, st.e) do
        {:ok, n} ->
          case muro_fsm_ix(bound, st.e) do
            {:ok, max} when is_integer(n) and n <= max ->
              {:ok, muro_fsm_expose(%{st | e: Map.put(st.e, name, n), p: cont})}

            _ ->
              {:error, {:unexpected, step, expected, value}}
          end

        _ ->
          {:error, {:unexpected, step, expected, value}}
      end
    end

    defp muro_fsm_index(st, name, left, right, value, step) do
      case value do
        :b0 ->
          {:ok, muro_fsm_expose(%{st | e: Map.put(st.e, name, :b0), p: left})}

        :b1 ->
          {:ok, muro_fsm_expose(%{st | e: Map.put(st.e, name, :b1), p: right})}

        _ ->
          {:error, {:unexpected, step, muro_fsm_expect(st), value}}
      end
    end

    defp muro_fsm_pick(st, left, right, {:pick, bit}, _step, _dir) when bit in [:b0, :b1] do
      cont = if bit == :b0, do: left, else: right
      {:ok, muro_fsm_expose(%{st | p: cont})}
    end

    defp muro_fsm_pick(st, _left, _right, value, step, _dir) do
      {:error, {:unexpected, step, muro_fsm_expect(st), value}}
    end

    defp muro_fsm_expect(%{p: {:end, _}}), do: :done
    defp muro_fsm_expect(%{p: {:stuck, _}}), do: :done

    defp muro_fsm_expect(%{p: {:send, _, ty, _}, e: env}) do
      {:send, muro_fsm_desc(muro_fsm_subst(ty, env))}
    end

    defp muro_fsm_expect(%{p: {:recv, _, ty, _}, e: env}) do
      {:recv, muro_fsm_desc(muro_fsm_subst(ty, env))}
    end

    defp muro_fsm_expect(%{p: {:dsend, _, _, ty, _}, e: env}) do
      {:send, muro_fsm_desc(muro_fsm_subst(ty, env))}
    end

    defp muro_fsm_expect(%{p: {:drecv, _, _, ty, _}, e: env}) do
      {:recv, muro_fsm_desc(muro_fsm_subst(ty, env))}
    end

    defp muro_fsm_expect(%{p: {:esend, _, _, bound, _}, e: env}) do
      {:send, muro_fsm_bound_desc(bound, env)}
    end

    defp muro_fsm_expect(%{p: {:erecv, _, _, bound, _}, e: env}) do
      {:recv, muro_fsm_bound_desc(bound, env)}
    end

    defp muro_fsm_expect(%{p: {:isend, _, _, _, _}}), do: {:send, :bit}
    defp muro_fsm_expect(%{p: {:irecv, _, _, _, _}}), do: {:recv, :bit}
    defp muro_fsm_expect(%{p: {:choose, _, _, _}}), do: {:send_pick, [:b0, :b1]}
    defp muro_fsm_expect(%{p: {:branch, _, _, _}}), do: {:recv_pick, [:b0, :b1]}
    defp muro_fsm_expect(_), do: :done

    defp muro_fsm_expect_ty(st, ty) do
      case st.p do
        {:send, _, _, _} -> {:send, muro_fsm_desc(muro_fsm_subst(ty, st.e))}
        {:dsend, _, _, _, _} -> {:send, muro_fsm_desc(muro_fsm_subst(ty, st.e))}
        {:esend, _, _, _, _} -> {:send, muro_fsm_desc(muro_fsm_subst(ty, st.e))}
        {:isend, _, _, _, _} -> {:send, :bit}
        _ -> {:recv, muro_fsm_desc(muro_fsm_subst(ty, st.e))}
      end
    end

    defp muro_fsm_bound_desc(bound, env) do
      n =
        case muro_fsm_ix(bound, env) do
          {:ok, n} -> n
          :error -> 0
        end

      inner = {:nat_at_most, n}
      if "Nat" in muro_fsm_reprs(), do: {:repr, inner, "Nat"}, else: inner
    end

    #{take_fun(reprs)}

    #{from_host(reprs)}

    defp muro_fsm_payload?(:nat, n) when is_integer(n) and n >= 0, do: true
    defp muro_fsm_payload?(:bit, bit) when bit in [:b0, :b1], do: true
    defp muro_fsm_payload?(:unit, :tt), do: true
    defp muro_fsm_payload?({:pair, a, b}, {x, y}), do: muro_fsm_payload?(a, x) and muro_fsm_payload?(b, y)

    defp muro_fsm_payload?({:rec, fields}, map) when is_list(fields) and is_map(map) do
      names = Enum.map(fields, fn {name, _} -> name end)

      Enum.sort(Map.keys(map)) == Enum.sort(names) and
        Enum.all?(fields, fn {name, ty} -> muro_fsm_payload?(ty, Map.get(map, name)) end)
    end

    defp muro_fsm_payload?({:vec, elem, {:lit, n}}, list)
         when is_list(list) and is_integer(n) and n >= 0 do
      length(list) == n and Enum.all?(list, &muro_fsm_payload?(elem, &1))
    end

    defp muro_fsm_payload?({:dat, name, args}, value) when is_list(args) do
      case Map.get(muro_fsm_decls(), name) do
        %{np: n, ctors: ctors} when length(args) == n ->
          muro_fsm_dat?(ctors, name, args, value)

        _ ->
          false
      end
    end

    defp muro_fsm_payload?(_, _), do: false

    defp muro_fsm_dat?(ctors, _name, _args, value) when is_atom(value) do
      case Map.get(ctors, Atom.to_string(value)) do
        [] -> true
        _ -> false
      end
    end

    defp muro_fsm_dat?(ctors, dname, args, value) when is_tuple(value) and tuple_size(value) >= 1 do
      [tag | fields] = Tuple.to_list(value)

      if is_atom(tag) do
        case Map.get(ctors, Atom.to_string(tag)) do
          tmpl when is_list(tmpl) and length(tmpl) == length(fields) ->
            Enum.zip(tmpl, fields)
            |> Enum.all?(fn {field, got} ->
              muro_fsm_payload?(muro_fsm_inst(field, dname, args), got)
            end)

          _ ->
            false
        end
      else
        false
      end
    end

    defp muro_fsm_dat?(_, _, _, _), do: false

    defp muro_fsm_inst({:par, i}, _name, args), do: Enum.at(args, i)

    defp muro_fsm_inst({:pair, a, b}, name, args) do
      {:pair, muro_fsm_inst(a, name, args), muro_fsm_inst(b, name, args)}
    end

    defp muro_fsm_inst({:rec, fields}, name, args) when is_list(fields) do
      {:rec, Enum.map(fields, fn {field, ty} -> {field, muro_fsm_inst(ty, name, args)} end)}
    end

    defp muro_fsm_inst({:vec, elem, ix}, name, args) do
      {:vec, muro_fsm_inst(elem, name, args), ix}
    end

    defp muro_fsm_inst({:self, ts}, name, args) do
      {:dat, name, Enum.map(ts, &muro_fsm_inst(&1, name, args))}
    end

    defp muro_fsm_inst({:dat, name, ts}, dname, args) do
      {:dat, name, Enum.map(ts, &muro_fsm_inst(&1, dname, args))}
    end

    defp muro_fsm_inst(ty, _name, _args), do: ty

    defp muro_fsm_subst({:pair, a, b}, env), do: {:pair, muro_fsm_subst(a, env), muro_fsm_subst(b, env)}

    defp muro_fsm_subst({:rec, fields}, env) when is_list(fields) do
      {:rec, Enum.map(fields, fn {name, ty} -> {name, muro_fsm_subst(ty, env)} end)}
    end

    defp muro_fsm_subst({:vec, elem, ix}, env) do
      {:vec, muro_fsm_subst(elem, env), muro_fsm_subst_ix(ix, env)}
    end

    defp muro_fsm_subst({:dat, name, args}, env) do
      {:dat, name, Enum.map(args, &muro_fsm_subst(&1, env))}
    end

    defp muro_fsm_subst(ty, _env), do: ty

    defp muro_fsm_subst_ix({:var, name}, env) do
      case Map.get(env, name) do
        n when is_integer(n) and n >= 0 -> {:lit, n}
        _ -> {:var, name}
      end
    end

    defp muro_fsm_subst_ix({:suc, inner}, env) do
      case muro_fsm_subst_ix(inner, env) do
        {:lit, n} -> {:lit, n + 1}
        other -> {:suc, other}
      end
    end

    defp muro_fsm_subst_ix(ix, _env), do: ix

    defp muro_fsm_desc(:nat) do
      if "Nat" in muro_fsm_reprs(), do: {:repr, :nat, "Nat"}, else: :nat
    end

    defp muro_fsm_desc(:bit), do: :bit
    defp muro_fsm_desc(:unit), do: :unit
    defp muro_fsm_desc({:pair, a, b}), do: {:pair, muro_fsm_desc(a), muro_fsm_desc(b)}

    defp muro_fsm_desc({:rec, fields}) when is_list(fields) do
      {:record, Enum.map(fields, fn {name, ty} -> {name, muro_fsm_desc(ty)} end)}
    end

    defp muro_fsm_desc({:vec, elem, {:lit, n}}) when is_integer(n) do
      {:vec, muro_fsm_desc(elem), n}
    end

    defp muro_fsm_desc({:vec, elem, _}), do: {:vec, muro_fsm_desc(elem), 0}

    defp muro_fsm_desc({:dat, name, []}) do
      shown = {:data, name, []}
      if name in muro_fsm_reprs(), do: {:repr, shown, name}, else: shown
    end

    defp muro_fsm_desc({:dat, name, args}) when is_list(args) do
      {:data, name, Enum.map(args, &muro_fsm_desc/1)}
    end

    defp muro_fsm_desc(other), do: other

    defp muro_fsm_to_emitted(n, :nat) when is_integer(n) and n >= 0 and n <= @muro_fsm_cap do
      {:ok, muro_fsm_peano(n, 0)}
    end

    defp muro_fsm_to_emitted(n, :nat) when is_integer(n) and n > @muro_fsm_cap, do: :cap
    defp muro_fsm_to_emitted(_, :nat), do: :error
    defp muro_fsm_to_emitted(bit, :bit) when bit in [:b0, :b1], do: {:ok, bit}
    defp muro_fsm_to_emitted(:tt, :unit), do: {:ok, :tt}

    defp muro_fsm_to_emitted({x, y}, {:pair, a, b}) do
      case muro_fsm_to_emitted(x, a) do
        {:ok, x} ->
          case muro_fsm_to_emitted(y, b) do
            {:ok, y} -> {:ok, {x, y}}
            other -> other
          end

        other ->
          other
      end
    end

    defp muro_fsm_to_emitted(map, {:rec, fields}) when is_list(fields) and is_map(map) do
      muro_fsm_emit_rec(fields, map, [])
    end

    defp muro_fsm_to_emitted(list, {:vec, elem, _ix}) when is_list(list) do
      muro_fsm_emit_list(list, elem, [])
    end

    defp muro_fsm_to_emitted(value, {:dat, name, args}) when is_list(args) do
      muro_fsm_emit_dat(value, name, args)
    end

    defp muro_fsm_to_emitted(_, _), do: :error

    defp muro_fsm_emit_dat(value, name, args) do
      case Map.get(muro_fsm_decls(), name) do
        %{ctors: ctors} ->
          tag = muro_fsm_tag(value)
          fields = muro_fsm_wire_fields(value)

          case tag && Map.get(ctors, tag) do
            tmpl when is_list(tmpl) and length(tmpl) == length(fields) ->
              muro_fsm_emit_fields(tmpl, fields, name, args, tag)

            _ ->
              :error
          end

        _ ->
          :error
      end
    end

    defp muro_fsm_emit_rec([], _map, acc), do: {:ok, Map.new(acc)}

    defp muro_fsm_emit_rec([{name, ty} | rest], map, acc) do
      case muro_fsm_to_emitted(Map.get(map, name), ty) do
        {:ok, conv} -> muro_fsm_emit_rec(rest, map, [{name, conv} | acc])
        other -> other
      end
    end

    defp muro_fsm_emit_list([], _elem, acc), do: {:ok, :lists.reverse(acc)}

    defp muro_fsm_emit_list([item | rest], elem, acc) do
      case muro_fsm_to_emitted(item, elem) do
        {:ok, conv} -> muro_fsm_emit_list(rest, elem, [conv | acc])
        other -> other
      end
    end

    defp muro_fsm_emit_fields(tmpl, fields, dname, args, tag) do
      zipped = Enum.zip(tmpl, fields)

      Enum.reduce_while(zipped, {:ok, []}, fn {field, got}, {:ok, acc} ->
        case muro_fsm_to_emitted(got, muro_fsm_inst(field, dname, args)) do
          {:ok, conv} -> {:cont, {:ok, acc ++ [conv]}}
          other -> {:halt, other}
        end
      end)
      |> case do
        {:ok, conv} -> {:ok, muro_fsm_pack(tag, conv, :emitted)}
        other -> other
      end
    end

    defp muro_fsm_peano(0, acc), do: acc

    defp muro_fsm_peano(n, acc) when is_integer(n) and n > 0 do
      muro_fsm_peano(n - 1, {:suc, acc})
    end

    #{from_emitted(reprs)}

    defp muro_fsm_tag(value) when is_atom(value), do: Atom.to_string(value)

    defp muro_fsm_tag(value) when is_tuple(value) and tuple_size(value) >= 1 do
      tag = elem(value, 0)
      if is_atom(tag), do: Atom.to_string(tag), else: nil
    end

    defp muro_fsm_tag(_), do: nil

    defp muro_fsm_wire_fields(value) when is_atom(value), do: []

    defp muro_fsm_wire_fields(value) when is_tuple(value) and tuple_size(value) >= 1 do
      [_tag | fields] = Tuple.to_list(value)
      fields
    end

    defp muro_fsm_wire_fields(_), do: []

    defp muro_fsm_result_tag(value) do
      case muro_fsm_tag(value) do
        nil -> nil
        raw -> Map.get(muro_fsm_safe_to_source(), raw, raw)
      end
    end

    defp muro_fsm_pack(tag, [], :emitted) do
      String.to_atom(Map.get(muro_fsm_source_to_safe(), tag, tag))
    end

    defp muro_fsm_pack(tag, fields, :emitted) do
      atom = String.to_atom(Map.get(muro_fsm_source_to_safe(), tag, tag))
      List.to_tuple([atom | fields])
    end

    #{wire_pack(reprs)}

    #{calls(st, names)}

    defp muro_fsm_templates, do: #{lit(sessions |> Map.new())}

    defp muro_fsm_duals, do: #{lit(duals)}

    defp muro_fsm_ends, do: #{lit(ends)}

    defp muro_fsm_end(key), do: Map.get(muro_fsm_ends(), key, "")

    # An empty literal map makes Map.get always return its default.
    defp muro_fsm_decls, do: :maps.from_list(#{lit(Map.to_list(decls))})

    defp muro_fsm_reprs, do: #{lit(reprs)}

    defp muro_fsm_source_to_safe, do: :maps.from_list(#{lit(Map.to_list(safe.to))})

    defp muro_fsm_safe_to_source, do: :maps.from_list(#{lit(Map.to_list(safe.from))})
    """
  end

  # A book with no repr makes `from_host` the identity, so `take` does not
  # match on `:error` (that clause would be unreachable). With a repr,
  # `from_host` can fail and `take` reports it.
  defp take_fun([]) do
    """
    defp muro_fsm_take(ty, value, env) do
      ty = muro_fsm_subst(ty, env)
      {:ok, wire} = muro_fsm_from_host(ty, value)
      if muro_fsm_payload?(ty, wire), do: {:ok, wire}, else: :error
    end
    """
  end

  defp take_fun(_reprs) do
    """
    defp muro_fsm_take(ty, value, env) do
      ty = muro_fsm_subst(ty, env)

      case muro_fsm_from_host(ty, value) do
        {:ok, wire} -> if muro_fsm_payload?(ty, wire), do: {:ok, wire}, else: :error
        _ -> :error
      end
    end
    """
  end

  defp wire_pack([]) do
    ""
  end

  defp wire_pack(_reprs) do
    """
    defp muro_fsm_pack(tag, [], :wire), do: String.to_atom(tag)

    defp muro_fsm_pack(tag, fields, :wire) do
      List.to_tuple([String.to_atom(tag) | fields])
    end
    """
  end

  # The only generated function that matches `{:ok, decoded}` is
  # `muro_fsm_from_host/2`. A book with no repr leaves that function as
  # the identity.
  defp from_host([]) do
    """
    # This is the only place that knows decode_<type>/1 returns {:ok, value}.
    defp muro_fsm_from_host(_type, value), do: {:ok, value}
    """
  end

  defp from_host(reprs) do
    clauses =
      Enum.map(reprs, fn name ->
        fun = "decode_" <> snake(name)

        cond do
          name == "Nat" ->
            """
            defp muro_fsm_from_host(:nat, value) do
              case #{fun}(value) do
                {:ok, decoded} ->
                  case muro_fsm_from_emitted(decoded, :nat) do
                    {:ok, wire} -> {:ok, wire}
                    _ -> :error
                  end

                _ ->
                  :error
              end
            end
            """

          true ->
            """
            defp muro_fsm_from_host({:dat, #{inspect(name)}, []}, value) do
              case #{fun}(value) do
                {:ok, decoded} ->
                  case muro_fsm_from_emitted(decoded, {:dat, #{inspect(name)}, []}) do
                    {:ok, wire} -> {:ok, wire}
                    _ -> :error
                  end

                _ ->
                  :error
              end
            end
            """
        end
      end)

    """
    # This is the only place that knows decode_<type>/1 returns {:ok, value}.
    #{Enum.join(clauses, "\n")}
    defp muro_fsm_from_host({:pair, a, b}, {x, y}) do
      case muro_fsm_from_host(a, x) do
        {:ok, x} ->
          case muro_fsm_from_host(b, y) do
            {:ok, y} -> {:ok, {x, y}}
            :error -> :error
          end

        :error ->
          :error
      end
    end

    defp muro_fsm_from_host({:rec, fields}, map) when is_list(fields) and is_map(map) do
      muro_fsm_host_rec(fields, map, [])
    end

    defp muro_fsm_from_host({:vec, elem, _ix}, list) when is_list(list) do
      muro_fsm_host_list(list, elem, [])
    end

    defp muro_fsm_from_host({:dat, name, args}, value) when is_binary(name) and is_list(args) do
      muro_fsm_host_dat(name, args, value)
    end

    defp muro_fsm_from_host(_type, value), do: {:ok, value}

    defp muro_fsm_host_list([], _elem, acc), do: {:ok, :lists.reverse(acc)}

    defp muro_fsm_host_list([item | rest], elem, acc) do
      case muro_fsm_from_host(elem, item) do
        {:ok, wire} -> muro_fsm_host_list(rest, elem, [wire | acc])
        :error -> :error
      end
    end

    defp muro_fsm_host_rec([], _map, acc), do: {:ok, Map.new(acc)}

    defp muro_fsm_host_rec([{name, ty} | rest], map, acc) do
      case muro_fsm_from_host(ty, Map.get(map, name)) do
        {:ok, wire} -> muro_fsm_host_rec(rest, map, [{name, wire} | acc])
        :error -> :error
      end
    end

    defp muro_fsm_host_dat(name, args, value) do
      case Map.get(muro_fsm_decls(), name) do
        %{ctors: ctors} ->
          tag = muro_fsm_tag(value)
          fields = muro_fsm_wire_fields(value)

          case tag && Map.get(ctors, tag) do
            tmpl when is_list(tmpl) and length(tmpl) == length(fields) ->
              muro_fsm_host_fields(tmpl, fields, name, args, tag, [])

            _ ->
              {:ok, value}
          end

        _ ->
          {:ok, value}
      end
    end

    defp muro_fsm_host_fields([], _fields, _dname, _args, tag, acc) do
      {:ok, muro_fsm_pack(tag, :lists.reverse(acc), :wire)}
    end

    defp muro_fsm_host_fields([field | tmpl], [got | fields], dname, args, tag, acc) do
      ty = muro_fsm_inst(field, dname, args)

      case muro_fsm_from_host(ty, got) do
        {:ok, wire} -> muro_fsm_host_fields(tmpl, fields, dname, args, tag, [wire | acc])
        :error -> :error
      end
    end
    """
  end

  defp from_emitted([]), do: ""

  defp from_emitted(_reprs) do
    """
    defp muro_fsm_from_emitted(value, ty), do: muro_fsm_from_emitted(value, ty, 0)

    defp muro_fsm_from_emitted(0, :nat, n) when is_integer(n) and n >= 0, do: {:ok, n}

    defp muro_fsm_from_emitted({:suc, rest}, :nat, n) when is_integer(n) and n < 1_000_000 do
      muro_fsm_from_emitted(rest, :nat, n + 1)
    end

    defp muro_fsm_from_emitted(_, :nat, _), do: :error
    defp muro_fsm_from_emitted(bit, :bit, _) when bit in [:b0, :b1], do: {:ok, bit}
    defp muro_fsm_from_emitted(:tt, :unit, _), do: {:ok, :tt}

    defp muro_fsm_from_emitted({x, y}, {:pair, a, b}, _) do
      case muro_fsm_from_emitted(x, a) do
        {:ok, x} ->
          case muro_fsm_from_emitted(y, b) do
            {:ok, y} -> {:ok, {x, y}}
            _ -> :error
          end

        _ ->
          :error
      end
    end

    defp muro_fsm_from_emitted(map, {:rec, fields}, _) when is_list(fields) and is_map(map) do
      muro_fsm_unemit_rec(fields, map, [])
    end

    defp muro_fsm_from_emitted(list, {:vec, elem, _ix}, _) when is_list(list) do
      muro_fsm_unemit_list(list, elem, [])
    end

    defp muro_fsm_from_emitted(value, {:dat, name, args}, _) when is_list(args) do
      case Map.get(muro_fsm_decls(), name) do
        %{ctors: ctors} ->
          raw = muro_fsm_tag(value)
          tag = raw && Map.get(muro_fsm_safe_to_source(), raw, raw)
          fields = muro_fsm_wire_fields(value)

          case tag && Map.get(ctors, tag) do
            tmpl when is_list(tmpl) and length(tmpl) == length(fields) ->
              muro_fsm_unemit(tmpl, fields, name, args, tag, [])

            _ ->
              :error
          end

        _ ->
          :error
      end
    end

    defp muro_fsm_from_emitted(_, _, _), do: :error

    defp muro_fsm_unemit_rec([], _map, acc), do: {:ok, Map.new(acc)}

    defp muro_fsm_unemit_rec([{name, ty} | rest], map, acc) do
      case muro_fsm_from_emitted(Map.get(map, name), ty) do
        {:ok, wire} -> muro_fsm_unemit_rec(rest, map, [{name, wire} | acc])
        _ -> :error
      end
    end

    defp muro_fsm_unemit_list([], _elem, acc), do: {:ok, :lists.reverse(acc)}

    defp muro_fsm_unemit_list([item | rest], elem, acc) do
      case muro_fsm_from_emitted(item, elem) do
        {:ok, wire} -> muro_fsm_unemit_list(rest, elem, [wire | acc])
        _ -> :error
      end
    end

    defp muro_fsm_unemit([], _fields, _dname, _args, tag, acc) do
      {:ok, muro_fsm_pack(tag, :lists.reverse(acc), :wire)}
    end

    defp muro_fsm_unemit([field | tmpl], [got | fields], dname, args, tag, acc) do
      ty = muro_fsm_inst(field, dname, args)

      case muro_fsm_from_emitted(got, ty) do
        {:ok, wire} -> muro_fsm_unemit(tmpl, fields, dname, args, tag, [wire | acc])
        _ -> :error
      end
    end
    """
  end

  defp calls(st, names) do
    clauses =
      st.results
      |> Enum.sort_by(fn {fname, _cod} -> fname end)
      |> Enum.map(fn {fname, _cod} ->
        fun = Map.fetch!(names, fname)
        "defp muro_fsm_call(#{inspect(fname)}, arg), do: #{fun}(arg)"
      end)

    Enum.join(clauses ++ ["defp muro_fsm_call(_fname, _arg), do: :error"], "\n")
  end

  defp safe_maps(decls) do
    pairs =
      Enum.flat_map(decls, fn {_name, %{ctors: ctors}} ->
        Enum.flat_map(ctors, fn {ctor, _fields} ->
          safe = ctor |> String.replace("-", "_") |> String.replace("'", "_")
          if safe == ctor, do: [], else: [{ctor, safe}]
        end)
      end)

    %{
      to: Map.new(pairs),
      from: Map.new(pairs, fn {ctor, safe} -> {safe, ctor} end)
    }
  end

  defp snake(name) do
    name
    |> String.replace("-", "_")
    |> String.replace("'", "_")
    |> String.replace(~r/([a-z0-9])([A-Z])/, "\\1_\\2")
    |> String.downcase()
  end

  defp lit(term) do
    inspect(term, limit: :infinity, printable_limit: :infinity, charlists: :as_lists)
  end

  defp children(module, st) do
    parent = inspect(module)

    {mods, _} =
      Enum.reduce(st.sessions, {[], MapSet.new()}, fn sess, {acc, used} ->
        base = sess.name |> String.replace("-", "_") |> Macro.camelize()
        {camel, used} = claim(base, used)
        entry = Map.fetch!(st.opened, sess.name)
        {acc ++ [child(parent, camel, sess.name, entry.params)], used}
      end)

    Enum.join(mods, "\n\n")
  end

  defp child(parent, camel, key, params) do
    """
    defmodule #{camel} do
      @moduledoc \"\"\"
      One end of session `#{key}`. The state is opaque: thread it, compare it
      with ==, and do not depend on its shape.
      \"\"\"

      #{init_fun(parent, key, params)}

      def unquote(:send)(state, value) do
        #{parent}.muro_fsm_step(#{inspect(key)}, :send, state, value)
      end

      def recv(state, value) do
        #{parent}.muro_fsm_step(#{inspect(key)}, :recv, state, value)
      end

      def done?(state), do: #{parent}.muro_fsm_done?(#{inspect(key)}, state)

      def expected(state), do: #{parent}.muro_fsm_expected(#{inspect(key)}, state)

      #{trace_fun(parent, key, params)}
    end
    """
  end

  defp init_fun(parent, key, []) do
    "def init, do: #{parent}.muro_fsm_init(#{inspect(key)}, [])"
  end

  defp init_fun(parent, key, params) do
    args = Enum.map(1..length(params), &"a#{&1}")
    guard = Enum.map_join(args, " and ", &"is_integer(#{&1}) and #{&1} >= 0")

    body =
      Enum.with_index(args, 1)
      |> Enum.map(fn {arg, i} ->
        msg = "session #{key}: argument #{i} is not a nat"
        "not (is_integer(#{arg}) and #{arg} >= 0) -> raise ArgumentError, #{inspect(msg)}"
      end)

    last = "session #{key}: argument #{length(args)} is not a nat"

    body = Enum.join(body ++ ["true -> raise ArgumentError, #{inspect(last)}"], "\n")

    """
    def init(#{Enum.join(args, ", ")}) when #{guard} do
      #{parent}.muro_fsm_init(#{inspect(key)}, [#{Enum.join(args, ", ")}])
    end

    def init(#{Enum.join(args, ", ")}) do
      cond do
        #{body}
      end
    end
    """
  end

  defp trace_fun(parent, key, []) do
    """
    def check_trace(trace) when is_list(trace) do
      #{parent}.muro_fsm_trace(#{inspect(key)}, [], trace, false)
    end

    def check_trace(trace, opts) when is_list(trace) and is_list(opts) do
      #{parent}.muro_fsm_trace(#{inspect(key)}, [], trace, Keyword.get(opts, :complete) == true)
    end
    """
  end

  defp trace_fun(parent, key, _params) do
    msg = "session #{key}: check_trace requires args: [...]"

    """
    def check_trace(trace, opts) when is_list(trace) and is_list(opts) do
      case Keyword.fetch(opts, :args) do
        {:ok, args} when is_list(args) ->
          #{parent}.muro_fsm_trace(#{inspect(key)}, args, trace, Keyword.get(opts, :complete) == true)

        _ ->
          raise ArgumentError, #{inspect(msg)}
      end
    end
    """
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
