defmodule Muro.EmitCSessionTest do
  use ExUnit.Case, async: false

  @moduletag timeout: 180_000

  @cap 100_000
  @max_states 14
  @max_depth 6

  # Books the state machine accepts and the C stepper must follow.
  @stepped [
    "examples/async-meetings.muro",
    "examples/computed.muro",
    "examples/dual.muro",
    "examples/field-bindings.muro",
    "examples/field-choice.muro",
    "examples/indexed.muro",
    "examples/linear.muro",
    "examples/located.muro",
    "examples/may-fail-control.muro",
    "examples/meet.muro",
    "examples/pair-bindings.muro",
    "examples/ping.muro",
    "examples/recursive.muro",
    "examples/session-calls.muro",
    "examples/temporal.muro",
    "examples/value-protocols.muro"
  ]

  @harness Path.expand("support/c_session_harness.c", __DIR__)

  test "a book with no session emits no stepper" do
    for path <- ~w(examples/half_ok.muro examples/pair.muro examples/bytes.muro) do
      assert {:ok, header, source, _} = prepare(path)
      refute header =~ "muro__sess_", path
      refute source =~ "muro__sess_", path
      assert {:error, reason} = Muro.emit_fsm(path, parent())
      assert reason =~ "has no session"
    end
  end

  test "a session the machine rejects is c:session, and may fail stays c:mayfail" do
    for path <-
          ~w(examples/talk.muro examples/seated.muro examples/two-phase-commit.muro examples/bounded-split.muro examples/bounded-fields.muro) do
      assert {:error, reason} = Muro.emit_fsm(path, parent())
      assert {:error, "c:session\n" <> ^reason} = prepare(path)
    end

    for path <- ~w(examples/may-fail-free.muro examples/may-fail-send.muro) do
      assert {:ok, _} = Muro.emit_fsm(path, parent())
      assert {:error, "c:mayfail\nmay fail is checked and not emitted"} = prepare(path)
    end
  end

  test "a repr payload and an unboxed payload are not a C stepper" do
    repr = """
    repr Nat := integer
    session s := send Nat end
    """

    assert {:error, msg} = prepare_text("repr-sess.muro", repr)
    assert msg =~ "c:session"
    assert msg =~ "repr Nat is not a C payload"

    unboxed = """
    unboxed data Flag : Type where
      on : Flag
      off : Flag
    session s := send Flag end
    """

    assert {:error, msg} = prepare_text("unboxed-sess.muro", unboxed)
    assert msg =~ "c:session"
    assert msg =~ "unboxed Flag is not a C payload"
  end

  test "an unboxed type nested under boxed data is not a C stepper" do
    text = """
    unboxed data Flag : Type where
      on : Flag
      off : Flag
    data Box : Type where
      box : Flag → Box
    data Wrap : Type where
      wrap : Box → Wrap
    session s := send Wrap end
    """

    assert {:error, msg} = prepare_text("nested-unboxed.muro", text)
    assert msg =~ "c:session"
    assert msg =~ "unboxed Flag is not a C payload"
  end

  test "an unboxed type named only by a dual is refused" do
    book = [%{kind: :data, name: "Flag", unboxed: true}]

    image = %{
      sessions: [
        %{name: "s", file: "gap.muro", line: 2, proto: {:end, "end"}}
      ],
      duals: %{
        "gone" => {[], {:send, "step", {:dat, "Flag", []}, {:end, "end"}}}
      },
      decls: %{}
    }

    assert {:error, msg} = Muro.Emit.C.Session.refuse_unboxed(image, book)
    assert msg == "c:session\nsession:0 session gone: unboxed Flag is not a C payload"
  end

  test "a case run whose result or argument is not a C payload is refused" do
    # Flag is returned by value, so it is not a payload tag the step can switch on.
    result = """
    unboxed data Flag : Type where
      on : Flag
      off : Flag
    data Bool : Type where
      true : Bool
      false : Bool
    def mark : run Π (b : Bool) → Flag :=
      λ (b : Bool) →
        match b motive (λ _ → Flag)
          | true => on
          | false => off
    session s := recv (b : Bool) (case (mark b) | on => end | off => end)
    """

    assert {:error, msg} = prepare_text("flag-result.muro", result)
    assert msg =~ "c:session"
    assert msg =~ "mark: result is not a C payload tag"

    # An erased argument is not a live payload, so the machine refuses the call.
    arg = """
    data Bool : Type where
      true : Bool
      false : Bool
    def see : run Π (- b : Bool) → Bool :=
      λ (- b : Bool) → true
    session s := recv (b : Bool) (case (see b) | true => end | false => end)
    """

    assert {:error, msg} = prepare_text("erased-arg.muro", arg)
    assert msg =~ "c:session"
    assert msg =~ "cannot call run see"

    wide = """
    data Bool : Type where
      true : Bool
      false : Bool
    def both : run Π (a : Bool) → Π (b : Bool) → Bool :=
      λ (a : Bool) → λ (b : Bool) → a
    session s := recv (a : Bool) (recv (b : Bool) (case (both a b) | true => end | false => end))
    """

    assert {:error, msg} = prepare_text("wide-case.muro", wide)
    assert msg =~ "c:session"
    assert msg =~ "cannot call run both"
  end

  test "a nat above the C run cap is refused there and the state stays" do
    text = """
    data Bool : Type where
      true : Bool
      false : Bool
    data Box : Type where
      box : Nat → Box
    def big : run Π (b : Box) → Bool :=
      λ (b : Box) → true
    session s := recv (b : Box) (case (big b) | true => end | false => end)
    """

    path = write_book("cap.muro", text)
    parent = parent()
    assert {:ok, src} = Muro.emit_fsm(path, parent)
    Code.compile_string(src)
    mod = child(parent, "s")
    state = mod.init()
    {bin, _dir} = compile_path!(path)

    over = {:wire, :data, "box", [{:wire, :nat, 100_001}]}

    # The Elixir machine passes the integer to the run. A C run still takes
    # a Peano Nat, so the C machine keeps its cap of 100_000.
    assert {:ok, _} = mod.recv(state, {:box, 100_001})

    capped =
      {:step, [], :recv, sexpr(over), 1, state.s, show({:nat_at_most, @cap}), state.s, false}

    {script, wants} = script("s", [], [capped])
    compare!("s", "s", [], wants, run_c!(bin, script))

    inside = {:wire, :data, "box", [{:wire, :nat, 3}]}
    assert {:ok, done} = mod.recv(state, {:box, 3})
    assert mod.done?(done)
    replay!(bin, mod, "s", [], state, [{:recv, inside}])
  end

  test "evidence followed by a numeral case sticks, as the state machine does" do
    text = """
    data Bool : Type where
      true : Bool
      false : Bool
    data Ctl : Type where
      rst : Ctl
    session direct :=
      recv (d : Nat) {d ≤ 2} (case d
        | 0 => send Ctl end
        | 1 => send Nat end
        | 2 => end)
    """

    path = write_book("stuck-case.muro", text)
    conform_path!(path)
  end

  test "a direct nat case refuses every nat, as the state machine does" do
    text = """
    session s := recv (n : Nat) (case n
      | 0 => send Nat end
      | 1 => end)
    """

    book = parsed(text)
    parent = parent()
    assert {:ok, src} = Muro.Emit.Fsm.render(book, "direct.muro", parent)
    Code.compile_string(src)
    mod = child(parent, "s")
    state = mod.init()
    {bin, _} = compile_book!(book, "direct")

    for n <- [0, 1, 2] do
      replay!(bin, mod, "s", [], state, [{:recv, {:wire, :nat, n}}])
    end
  end

  test "a foreign key, a bad position, and an unknown name are unexpected" do
    path = "examples/ping.muro"
    parent = parent()
    assert {:ok, src} = Muro.emit_fsm(path, parent)
    Code.compile_string(src)
    mod = child(parent, "ping")
    state = mod.init()

    assert {:error, {:unexpected, _, _, _}} =
             apply(parent, :muro_fsm_step, ["no-such", :recv, state, 0])

    {bin, _} = compile_path!(path)

    script = """
    init ping 0
    set key 99
    step recv nat 1
    init ping 0
    set at 40000
    step recv nat 1
    init ping 0
    name gone
    step recv nat 1
    """

    [init, foreign, init2, wild, init3, unknown] = run_c!(bin, script)
    assert elem(init, 0) == 0
    assert elem(init2, 0) == 0
    assert elem(init3, 0) == 0
    assert {1, step, "done", _, false} = foreign
    assert step =~ "end"
    assert {1, _, "done", _, false} = wild
    assert {1, "", "done", "", false} = unknown
  end

  test "a case run frees the value it built" do
    text = """
    data Bool : Type where
      true : Bool
      false : Bool
    data Pair : Type where
      mk : Nat → Nat → Pair
    def ok : run Π (p : Pair) → Bool :=
      λ (p : Pair) → true
    session s := recv (p : Pair) (case (ok p) | true => end | false => end)
    """

    path = write_book("pair-live.muro", text)
    assert {:ok, header, source, _} = prepare(path)
    assert source =~ "|| !out"
    assert source =~ "muro__DROP"
    assert source =~ "muro__sess_free_"
    assert count_live!(header, source, "pair-live") == 0
  end

  test "down is not a symbol of the stepper" do
    assert {:ok, header, source, _} = prepare("examples/ping.muro")
    refute header =~ ~r/(^|[^A-Za-z0-9_])down([^A-Za-z0-9_]|$)/
    refute source =~ ~r/(^|[^A-Za-z0-9_])down([^A-Za-z0-9_]|$)/m
  end

  test "a session error names the path render was given" do
    book = parsed(File.read!("examples/talk.muro"))
    assert {:error, bare} = Muro.Emit.C.render(book, "talk")
    assert bare =~ "talk.muro:"
    refute bare =~ "examples/talk.muro:"

    assert {:error, named} = Muro.Emit.C.render(book, "talk", path: "examples/talk.muro")
    assert named =~ "examples/talk.muro:"
  end

  test "session declarations sit in front of the file guard" do
    header =
      "#ifndef GUARD\n#define GUARD\n/* #endif\n */\n#ifndef muro__ALLOC\n#define muro__ALLOC(n) malloc(n)\n#endif\nint kept;\n#endif"

    sess = "void muro__sess_init(const char *name);"
    assert Muro.Emit.C.splice_session(header, "") == header

    placed = Muro.Emit.C.splice_session(header, sess)

    assert String.ends_with?(placed, "int kept;\n\n#{sess}\n#endif")
    assert String.contains?(placed, "#define muro__ALLOC(n) malloc(n)\n#endif\nint kept;")
    assert String.contains?(placed, "/* #endif\n */")
  end

  test "a bare lambda stays c:lambda in front of the stepper" do
    book = [
      %{
        name: "bad",
        mode: :run,
        type: :nat,
        body: {:lam, :affine, :nat, "n", :ze}
      },
      %{kind: :session, name: "s"}
    ]

    assert {:error, "c:lambda"} = Muro.Emit.C.prepare(book, "bare-lam", path: "bare-lam.muro")
  end

  test "emitted C for the session examples matches the goldens" do
    for path <- @stepped do
      stem = Path.basename(path, ".muro")
      assert {:ok, header, source, _} = prepare(path)
      dir = Path.join("test/fixtures/c-session", stem)
      assert File.read!(Path.join(dir, stem <> ".h")) == header
      assert File.read!(Path.join(dir, stem <> ".c")) == source
    end
  end

  test "every session example the state machine accepts steps the same in C" do
    oks =
      Enum.reduce(session_books(), 0, fn path, oks ->
        case Muro.emit_fsm(path, parent()) do
          {:error, reason} ->
            if not checked?(path) do
              oks
            else
              case prepare(path) do
                {:error, "c:session\n" <> ^reason} ->
                  oks

                {:error, "c:mayfail\n" <> _} ->
                  oks

                {:error, "c:" <> rest} ->
                  if prior_refusal?(rest), do: oks, else: flunk("#{path} refused #{rest}")

                {:error, other} ->
                  flunk("#{path}\nfsm #{reason}\nc #{other}")

                {:ok, _, _, _} ->
                  flunk("#{path} emitted C after the state machine rejected it: #{reason}")
              end
            end

          {:ok, _src} ->
            case prepare(path) do
              {:error, "c:mayfail\n" <> _} ->
                oks

              {:error, "c:" <> rest} ->
                if prior_refusal?(rest) do
                  oks
                else
                  flunk("#{path} refused a session the state machine accepts: #{rest}")
                end

              {:ok, _, _, _} ->
                oks + conform_path!(path)
            end
        end
      end)

    assert oks > 0
  end

  defp prior_refusal?(rest) do
    Enum.any?(~w(machine lambda stream unboxed erased unsupported mayfail), fn word ->
      rest == word or String.starts_with?(rest, word <> "\n")
    end)
  end

  defp session_books do
    Path.wildcard("examples/**/*.muro")
    |> Enum.filter(fn path ->
      String.contains?(File.read!(path), "session ") and not String.contains?(path, "/cshrl/")
    end)
    |> Enum.sort()
  end

  defp checked?(path) do
    match?({:ok, _}, Muro.Load.file(path))
  end

  defp conform_path!(path) do
    book = erased(path)
    parent = parent()
    {:ok, src} = Muro.emit_fsm(path, parent)
    Code.compile_string(src)
    decls = Muro.Session.payload_decls(book)
    {bin, _} = compile_path!(path)

    sessions =
      for %{kind: :session, name: name, params: params} <- book, do: {name, length(params)}

    Enum.reduce(sessions, 0, fn {name, n}, oks ->
      mod = child(parent, name)

      Enum.reduce(arg_sets(n), oks, fn args, oks ->
        state = apply(mod, :init, args)
        probes = probes(mod, state, decls, 0, MapSet.new([state]), 0)
        {script, wants} = script(name, args, probes)
        rows = run_c!(bin, script)
        compare!(path, name, args, wants, rows)
        oks + Enum.count(probes, &match?({:step, _, _, _, 0, _, _, _, _}, &1))
      end)
    end)
  end

  defp probes(mod, state, decls, depth, seen, nstates) do
    at = state.s
    init_row = {:init, show(mod.expected(state)), at, at, mod.done?(state)}

    {rows, kids, seen, _nstates} =
      Enum.reduce(events(mod.expected(state), decls), {[], [], seen, nstates}, fn
        {dir, wire}, {rows, kids, seen, nstates} ->
          row = step_row(mod, state, dir, wire, at)

          if row.ok and nstates < @max_states and depth < @max_depth and
               not MapSet.member?(seen, row.state) do
            ev = {dir, sexpr(wire)}

            {rows ++ [row.view], kids ++ [{row.state, ev}], MapSet.put(seen, row.state),
             nstates + 1}
          else
            {rows ++ [row.view], kids, seen, nstates}
          end
      end)

    nested =
      Enum.flat_map(kids, fn {st, ev} ->
        [_init | rest] = probes(mod, st, decls, depth + 1, seen, nstates)
        Enum.map(rest, &prefix(&1, ev))
      end)

    [init_row | rows] ++ nested
  end

  defp prefix({:step, old, dir, sexpr, status, step, expected, at, done}, ev) do
    {:step, [ev | old], dir, sexpr, status, step, expected, at, done}
  end

  defp step_row(mod, state, :bad, _wire, at) do
    parent = mod |> Module.split() |> Enum.drop(-1) |> Module.concat()

    case parent.muro_fsm_step(state.k, :other, state, nil) do
      {:error, {:unexpected, step, expected, _}} ->
        %{
          ok: false,
          state: state,
          view: {:step, [], :bad, "unit", 1, step, show(expected), at, mod.done?(state)}
        }
    end
  end

  defp step_row(mod, state, dir, wire, at) do
    case apply(mod, dir, [state, to_fsm(wire)]) do
      {:ok, nxt} ->
        %{
          ok: true,
          state: nxt,
          view:
            {:step, [], dir, sexpr(wire), 0, at, show(mod.expected(nxt)), nxt.s, mod.done?(nxt)}
        }

      {:error, {:unexpected, step, expected, _}} ->
        %{
          ok: false,
          state: state,
          view: {:step, [], dir, sexpr(wire), 1, step, show(expected), at, mod.done?(state)}
        }
    end
  end

  defp script(name, args, probes) do
    init = "init #{name} #{length(args)}#{arg_text(args)}\n"

    Enum.reduce(probes, {"", []}, fn
      {:init, expected, step, at, done}, {script, wants} ->
        {script <> init, wants ++ [{:init, 0, step, expected, at, done}]}

      {:step, prefix, dir, sexpr, status, step, expected, at, done}, {script, wants} ->
        pre = Enum.map(prefix, fn {pdir, psexpr} -> "step #{pdir} #{psexpr}\n" end)
        line = if dir == :bad, do: "step bad\n", else: "step #{dir} #{sexpr}\n"
        block = init <> Enum.join(pre) <> line

        {script <> block,
         wants ++ [{:skip, 1 + length(prefix)}, {:step, status, step, expected, at, done}]}
    end)
  end

  defp arg_text([]), do: ""
  defp arg_text(args), do: " " <> Enum.join(args, " ")

  defp compare!(path, name, args, wants, rows) do
    case zip_wants(wants, rows) do
      :ok ->
        :ok

      :count ->
        flunk("#{path} #{name} #{inspect(args)} reply count #{length(rows)}")

      {:diff, want, have} ->
        flunk("""
        #{path} session #{name} #{inspect(args)}
        want #{inspect(want)}
        have #{inspect(have)}
        """)
    end
  end

  defp zip_wants([], []), do: :ok
  defp zip_wants([], _), do: :count
  defp zip_wants(_, []), do: :count

  defp zip_wants([{:skip, n} | wants], rows) do
    if length(rows) < n, do: :count, else: zip_wants(wants, Enum.drop(rows, n))
  end

  defp zip_wants([{:init, 0, step, expected, at, done} | wants], rows) do
    case rows do
      [{0, ^step, ^expected, ^at, ^done} | rows] ->
        zip_wants(wants, rows)

      [have | _] ->
        {:diff, {:init, 0, step, expected, at, done}, have}

      [] ->
        :count
    end
  end

  defp zip_wants([{:step, status, step, expected, at, done} | wants], rows) do
    case rows do
      [{^status, ^step, ^expected, ^at, ^done} | rows] ->
        zip_wants(wants, rows)

      [have | _] ->
        {:diff, {:step, status, step, expected, at, done}, have}

      [] ->
        :count
    end
  end

  defp replay!(bin, mod, name, args, state, events) do
    probes = Enum.map(events, fn {dir, wire} -> step_row(mod, state, dir, wire, state.s).view end)
    {script, wants} = script(name, args, probes)
    compare!(name, name, args, wants, run_c!(bin, script))
  end

  defp events(:done, _),
    do: [{:send, {:wire, :nat, 0}}, {:recv, {:wire, :nat, 0}}, {:bad, {:wire, :unit, 0}}]

  defp events({:send_pick, _}, _),
    do: [
      {:send, {:wire, :pick, 0}},
      {:send, {:wire, :pick, 1}},
      {:recv, {:wire, :pick, 0}},
      {:bad, {:wire, :unit, 0}}
    ]

  defp events({:recv_pick, _}, _),
    do: [
      {:recv, {:wire, :pick, 0}},
      {:recv, {:wire, :pick, 1}},
      {:send, {:wire, :pick, 0}},
      {:bad, {:wire, :unit, 0}}
    ]

  defp events({dir, ty}, decls) when dir in [:send, :recv] do
    legal = samples(ty, decls, 4) |> Enum.take(4) |> Enum.map(&{dir, &1})
    other = if dir == :send, do: :recv, else: :send
    sample = samples(ty, decls, 2) |> List.first() || {:wire, :nat, 0}
    junk = if ty == :unit, do: {:wire, :nat, 0}, else: {:wire, :unit, 0}
    legal ++ [{other, sample}, {dir, junk}, {:bad, {:wire, :unit, 0}}]
  end

  defp events(_, _), do: [{:bad, {:wire, :unit, 0}}]

  defp samples(:nat, _, _), do: [{:wire, :nat, 0}, {:wire, :nat, 1}]
  defp samples(:bit, _, _), do: [{:wire, :bit, 0}, {:wire, :bit, 1}]
  defp samples(:unit, _, _), do: [{:wire, :unit, 0}]

  defp samples({:nat_at_most, n}, _, _) when is_integer(n) and n >= 0 do
    over = if n < @cap, do: [n + 1], else: []
    vals = Enum.uniq([0, min(n, 2), n | over])
    Enum.map(vals, &{:wire, :nat, &1})
  end

  defp samples({:pair, a, b}, decls, depth) do
    for x <- samples(a, decls, depth) |> Enum.take(2),
        y <- samples(b, decls, depth) |> Enum.take(1) do
      {:wire, :pair, x, y}
    end
  end

  defp samples({:record, fields}, decls, depth) do
    built =
      Enum.map(fields, fn {name, ty} ->
        case samples(ty, decls, depth) do
          [v | _] -> {to_string(name), v}
          [] -> nil
        end
      end)

    if Enum.any?(built, &is_nil/1), do: [], else: [{:wire, :rec, built}]
  end

  defp samples({:vec, elem, n}, decls, depth) when is_integer(n) and n >= 0 and n <= 4 do
    case samples(elem, decls, depth) do
      [v | _] -> [{:wire, :vec, List.duplicate(v, n)}]
      [] -> []
    end
  end

  defp samples({:vec, _, n}, _, _) when is_integer(n) and n > 4, do: []

  defp samples({:data, name, args}, decls, depth) when depth > 0 do
    case Map.get(decls, name) do
      %{ctors: ctors, order: order} ->
        Enum.flat_map(order, fn ctor ->
          fields = Map.get(ctors, ctor, [])

          lists =
            Enum.map(fields, &(inst(&1, name, args) |> samples(decls, depth - 1) |> Enum.take(2)))

          if Enum.any?(lists, &(&1 == [])) and fields != [] do
            []
          else
            lists |> product() |> Enum.take(3) |> Enum.map(&{:wire, :data, ctor, &1})
          end
        end)

      _ ->
        []
    end
  end

  defp samples(_, _, _), do: []

  defp product([]), do: [[]]
  defp product([hs | ts]), do: for(h <- hs, r <- product(ts), do: [h | r])

  defp inst(:nat, _, _), do: :nat
  defp inst(:bit, _, _), do: :bit
  defp inst(:unit, _, _), do: :unit
  defp inst({:bnat, w}, _, _) when is_integer(w), do: {:nat_at_most, w}
  defp inst({:par, i}, _, args), do: Enum.at(args, i) || :ill
  defp inst({:pair, a, b}, name, args), do: {:pair, inst(a, name, args), inst(b, name, args)}

  defp inst({:rec, fields}, name, args) when is_list(fields) do
    {:record, Enum.map(fields, fn {n, ty} -> {to_string(n), inst(ty, name, args)} end)}
  end

  defp inst({:vec, elem, {:lit, n}}, name, args) when is_integer(n) do
    {:vec, inst(elem, name, args), n}
  end

  defp inst({:vec, _, _}, _, _), do: :ill
  defp inst({:self, ts}, name, args), do: {:data, name, Enum.map(ts, &inst(&1, name, args))}

  defp inst({:dat, dname, ts}, name, args),
    do: {:data, dname, Enum.map(ts, &inst(&1, name, args))}

  defp inst(other, _, _), do: other

  defp sexpr({:wire, :nat, n}), do: "nat #{n}"
  defp sexpr({:wire, :bit, b}), do: "bit #{b}"
  defp sexpr({:wire, :unit, _}), do: "unit"
  defp sexpr({:wire, :pick, b}), do: "pick #{b}"
  defp sexpr({:wire, :pair, a, b}), do: "pair #{sexpr(a)} #{sexpr(b)}"

  defp sexpr({:wire, :rec, fields}) do
    inner = Enum.map_join(fields, " ", fn {n, v} -> "#{n} #{sexpr(v)}" end)
    pad = if fields == [], do: "", else: " " <> inner
    "rec #{length(fields)}#{pad}"
  end

  defp sexpr({:wire, :vec, vs}) do
    inner = Enum.map_join(vs, " ", &sexpr/1)
    pad = if vs == [], do: "", else: " " <> inner
    "vec #{length(vs)}#{pad}"
  end

  defp sexpr({:wire, :data, ctor, vs}) do
    inner = Enum.map_join(vs, " ", &sexpr/1)
    pad = if vs == [], do: "", else: " " <> inner
    "data #{ctor} #{length(vs)}#{pad}"
  end

  defp to_fsm({:wire, :nat, n}), do: n
  defp to_fsm({:wire, :bit, 0}), do: :b0
  defp to_fsm({:wire, :bit, 1}), do: :b1
  defp to_fsm({:wire, :unit, _}), do: :tt
  defp to_fsm({:wire, :pick, 0}), do: {:pick, :b0}
  defp to_fsm({:wire, :pick, 1}), do: {:pick, :b1}
  defp to_fsm({:wire, :pair, a, b}), do: {to_fsm(a), to_fsm(b)}
  defp to_fsm({:wire, :rec, fields}), do: Map.new(fields, fn {n, v} -> {n, to_fsm(v)} end)
  defp to_fsm({:wire, :vec, vs}), do: Enum.map(vs, &to_fsm/1)
  defp to_fsm({:wire, :data, ctor, []}), do: String.to_atom(ctor)

  defp to_fsm({:wire, :data, ctor, vs}),
    do: List.to_tuple([String.to_atom(ctor) | Enum.map(vs, &to_fsm/1)])

  defp show(:done), do: "done"
  defp show(:stop), do: "stop"
  defp show({:nat_at_most, n}), do: "nat_at_most #{n}"
  defp show({:send_pick, _}), do: "send_pick"
  defp show({:recv_pick, _}), do: "recv_pick"
  defp show({:send, ty}), do: "send " <> wrap(show_ty(ty))
  defp show({:recv, ty}), do: "recv " <> wrap(show_ty(ty))
  defp show(other), do: inspect(other)

  defp show_ty(:nat), do: "nat"
  defp show_ty(:bit), do: "bit"
  defp show_ty(:unit), do: "unit"
  defp show_ty({:nat_at_most, n}), do: "nat_at_most #{n}"
  defp show_ty({:pair, a, b}), do: "pair " <> wrap(show_ty(a)) <> " " <> wrap(show_ty(b))

  defp show_ty({:record, fields}) do
    "record" <>
      Enum.map_join(fields, "", fn {name, ty} ->
        " " <> to_string(name) <> " " <> wrap(show_ty(ty))
      end)
  end

  defp show_ty({:vec, elem, n}), do: "vec " <> wrap(show_ty(elem)) <> " " <> to_string(n)
  defp show_ty({:data, name, []}), do: "data " <> name

  defp show_ty({:data, name, args}) do
    "data " <> name <> Enum.map_join(args, "", fn arg -> " " <> wrap(show_ty(arg)) end)
  end

  defp show_ty(other), do: inspect(other)
  defp wrap(s) when s in ["nat", "bit", "unit"], do: s
  defp wrap(s), do: "(" <> s <> ")"

  defp arg_sets(0), do: [[]]

  defp arg_sets(n) do
    zeros = List.duplicate(0, n)
    [zeros, List.replace_at(zeros, 0, 1)] |> Enum.uniq()
  end

  defp prepare(path) do
    stem = Path.basename(path, ".muro")
    Muro.Emit.C.prepare(erased(path), stem, path: path)
  end

  defp prepare_text(name, text) do
    path = write_book(name, text)
    prepare(path)
  end

  defp erased(path) do
    {:ok, book} = Muro.Load.file(path)
    book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()
  end

  defp parsed(text) do
    assert {:ok, book} = Muro.Parser.parse(text)
    book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()
  end

  defp count_live!(header, source, stem) do
    dir = Path.join(System.tmp_dir!(), "muro_live_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    File.write!(Path.join(dir, stem <> ".h"), header)
    File.write!(Path.join(dir, stem <> ".c"), source)

    main = """
    #include <stdlib.h>
    #include <stdio.h>
    #include <string.h>
    #include <stdint.h>
    static int live;
    static void *count_alloc(size_t n) {
      void *p = malloc(n ? n : 1);
      if (p) live++;
      return p;
    }
    static void count_drop(void *p) {
      if (!p) return;
      live--;
      free(p);
    }
    #define muro__ALLOC(n) count_alloc(n)
    #define muro__DROP(p) count_drop(p)
    #include "#{stem}.c"
    static int step_data(const char *ctor, muro__sess_val *fields, uint64_t n) {
      muro__sess_val v;
      muro__sess_res init, res;
      memset(&v, 0, sizeof v);
      v.tag = MURO_SESS_DATA;
      v.ctor = ctor;
      v.n = n;
      v.a = fields;
      init = muro__sess_init("s", 0, 0);
      if (live != 0) return 10;
      res = muro__sess_step("s", init.state, MURO_SESS_RECV, &v);
      if (live != 0) return 11;
      return res.status;
    }
    int main(void) {
      muro__sess_val fields[2];
      muro__sess_val unit;
      int status;
      memset(fields, 0, sizeof fields);
      fields[0].tag = MURO_SESS_NAT;
      fields[0].nat = 1;
      fields[1].tag = MURO_SESS_NAT;
      fields[1].nat = 2;
      status = step_data("mk", fields, 2);
      if (status != 0 || live != 0) return 1;
      fields[1].tag = MURO_SESS_UNIT;
      status = step_data("mk", fields, 2);
      if (status != 1 || live != 0) return 2;
      memset(&unit, 0, sizeof unit);
      unit.tag = MURO_SESS_UNIT;
      status = step_data("nope", &unit, 1);
      if (status != 1 || live != 0) return 3;
      return 0;
    }
    """

    File.write!(Path.join(dir, "main.c"), main)
    bin = Path.join(dir, "live")

    {msg, status} =
      System.cmd(
        "cc",
        ~w(-Wall -Wextra -Werror -std=c11 -I) ++ [dir, Path.join(dir, "main.c"), "-o", bin],
        stderr_to_stdout: true
      )

    assert status == 0, msg
    {out, ran} = System.cmd(bin, [], stderr_to_stdout: true)
    assert ran == 0, out
    0
  end

  defp write_book(name, text) do
    dir = Path.join(System.tmp_dir!(), "muro_csess_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    path = Path.join(dir, name)
    File.write!(path, text)
    path
  end

  defp compile_path!(path) do
    assert {:ok, header, source, _} = prepare(path)
    compile_texts!(header, source, Path.basename(path, ".muro"))
  end

  defp compile_book!(book, stem) do
    assert {:ok, header, source, _} =
             Muro.Emit.C.prepare(book, stem, path: stem <> ".muro")

    compile_texts!(header, source, stem)
  end

  defp compile_texts!(header, source, stem) do
    dir = Path.join(System.tmp_dir!(), "muro_cc_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    File.write!(Path.join(dir, stem <> ".h"), header)
    File.write!(Path.join(dir, stem <> ".c"), source)
    bin = Path.join(dir, "step")

    {msg, status} =
      System.cmd(
        "cc",
        ~w(-Wall -Wextra -Werror -std=c11) ++
          [
            "-I",
            dir,
            "-include",
            Path.join(dir, stem <> ".h"),
            @harness,
            Path.join(dir, stem <> ".c"),
            "-o",
            bin
          ],
        stderr_to_stdout: true
      )

    assert status == 0, msg
    {bin, dir}
  end

  defp run_c!(bin, script) do
    input = bin <> ".in"
    File.write!(input, script)
    {out, status} = System.cmd("sh", ["-c", ~s("#{bin}" < "#{input}")], stderr_to_stdout: true)
    assert status == 0, out <> "\n" <> String.slice(script, 0, 400)
    parse_rows(out, [])
  end

  defp parse_rows(<<>>, acc), do: Enum.reverse(acc)

  defp parse_rows(bin, acc) do
    {status_s, bin} = line!(bin)
    {done_s, bin} = line!(bin)
    {step, bin} = field!(bin)
    {expected, bin} = field!(bin)
    {at, bin} = field!(bin)
    {dot, bin} = line!(bin)
    assert dot == "."
    ["status", code] = String.split(status_s, " ", parts: 2)
    ["done", flag] = String.split(done_s, " ", parts: 2)
    parse_rows(bin, [{String.to_integer(code), step, expected, at, flag == "1"} | acc])
  end

  defp line!(bin) do
    case :binary.split(bin, "\n") do
      [a, b] -> {a, b}
    end
  end

  defp field!(bin) do
    {len_s, bin} = line!(bin)
    len = String.to_integer(len_s)
    <<field::binary-size(len), "\n", rest::binary>> = bin
    {field, rest}
  end

  defp parent, do: Module.concat(["CSess", Integer.to_string(System.unique_integer([:positive]))])

  defp child(parent, name), do: Module.concat(parent, Muro.Emit.elixir_alias(name))
end
