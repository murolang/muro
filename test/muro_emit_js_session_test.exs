defmodule Muro.EmitJSSessionTest do
  use ExUnit.Case, async: false

  alias Muro.{Emit, Load, Prelude}

  @moduletag timeout: 120_000

  @node System.find_executable("node") ||
          if(File.regular?("/opt/homebrew/bin/node"), do: "/opt/homebrew/bin/node")

  @node_skip if(is_nil(@node), do: "node not on PATH", else: false)

  @corpus [
    "examples/meet.muro",
    "examples/indexed.muro",
    "examples/recursive.muro",
    "examples/computed.muro",
    "examples/field-bindings.muro",
    "examples/pair-bindings.muro",
    "examples/async-meetings.muro",
    "examples/session-calls.muro",
    "examples/value-protocols.muro",
    "examples/field-choice.muro"
  ]

  @success %{
    {"examples/meet.muro", "ping"} => :done,
    {"examples/meet.muro", "back"} => :done,
    {"examples/meet.muro", "box"} => :done,
    {"examples/meet.muro", "sized"} => :done,
    {"examples/meet.muro", "window"} => :done,
    {"examples/meet.muro", "choice"} => :done,
    {"examples/indexed.muro", "route"} => :done,
    {"examples/value-protocols.muro", "server"} => :done,
    {"examples/value-protocols.muro", "gate"} => :done,
    {"examples/field-choice.muro", "gate"} => :done,
    {"examples/computed.muro", "flag"} => :done,
    {"examples/recursive.muro", "loop"} => :open
  }

  test "a session the state machine refuses is omitted and the runs stay" do
    talk = book!("examples/talk.muro")

    assert {:error, reason} =
             Emit.Fsm.render(talk, "examples/talk.muro", Emit.fsm_module("talk.muro"))

    assert reason =~ "seen is not a state machine"
    assert {:ok, source, types} = Emit.JS.render(talk, "talk", path: "examples/talk.muro")
    assert source =~ "export function kept("
    refute source =~ "export const "
    refute types =~ "SessionStepper"

    seated = book!("examples/seated.muro")

    assert {:error, seated_reason} =
             Emit.Fsm.render(seated, "examples/seated.muro", Emit.fsm_module("seated.muro"))

    assert seated_reason =~ "seen is not a state machine"

    assert {:error, "c:host in home (place)"} =
             Emit.JS.render(seated, "seated", path: "examples/seated.muro")

    src = """
    def kept : run Nat := 0
    session s := rec X. X
    """

    book = parse!(src)
    assert {:error, reason} = Emit.Fsm.render(book, "loop.muro", Emit.fsm_module("loop.muro"))
    assert reason =~ "unguarded rec"
    assert {:ok, source, types} = Emit.JS.render(book, "loop", path: "loop.muro")
    assert source =~ "export function kept("
    refute source =~ "export const "
    refute types =~ "SessionStepper"
  end

  test "a sibling stepper stays when another session is unrepresentable" do
    src = """
    session bad := rec X. X
    session ping := recv Nat (send Nat end)
    def kept : run Nat := 0
    """

    book = parse!(src)
    assert {:error, reason} = Emit.Fsm.render(book, "mix.muro", Emit.fsm_module("mix.muro"))
    assert reason =~ "unguarded rec"
    assert {:ok, source, types} = Emit.JS.render(book, "mix", path: "mix.muro")
    assert source =~ "export function kept("
    assert source =~ "export const ping ="
    refute source =~ "export const bad ="
    assert types =~ "export const ping: SessionStepper;"
    refute types =~ "bad: SessionStepper"
  end

  test "a place is c:host and a repr payload is omitted" do
    located = book!("examples/located.muro")

    assert {:error, "c:host in home (place)"} =
             Emit.JS.render(located, "located", path: "examples/located.muro")

    pair = book!("examples/pair.muro")
    assert {:ok, source, _types} = Emit.JS.render(pair, "pair", path: "examples/pair.muro")
    assert source =~ "export function"
    refute source =~ "has no session"

    body = """
    data Bool : Type where
      true : Bool
      false : Bool
    data Box : Type where
      box : Nat → Box
    repr Nat := integer
    repr Box := map { "n" => integer }
    session give := recv Box end
    session num := recv Nat end
    session ping := recv Bool end
    def kept : run Nat := 0
    """

    book = parse!(body)
    assert {:ok, _fsm} = Emit.Fsm.render(book, "reprs.muro", Emit.fsm_module("reprs.muro"))
    assert {:ok, source, types} = Emit.JS.render(book, "reprs", path: "reprs.muro")
    assert source =~ "export function kept("
    assert source =~ "export const ping ="
    refute source =~ "export const give ="
    refute source =~ "export const num ="
    assert types =~ "export const ping: SessionStepper;"
    refute types =~ "give: SessionStepper"
    refute types =~ "num: SessionStepper"

    arm = """
    data Bool : Type where
      true : Bool
      false : Bool
    repr Nat := integer
    session s := choose (send Nat end) end
    session ping := recv Bool end
    def kept : run Nat := 0
    """

    book = parse!(arm)
    assert {:ok, _} = Emit.Fsm.render(book, "arm.muro", Emit.fsm_module("arm.muro"))
    assert {:ok, source, _types} = Emit.JS.render(book, "arm", path: "arm.muro")
    assert source =~ "export function kept("
    assert source =~ "export const ping ="
    refute source =~ "export const s ="
  end

  @tag skip: @node_skip
  test "a spec-only session stays beside the runs, and an importer emits those runs" do
    dir = tmp()
    write!(dir, "wire.muro", wire_src())
    user = write!(dir, "user.muro", user_src())

    assert {:ok, [wire_mjs, _]} = Muro.emit_js(Path.join(dir, "wire.muro"))
    assert {:ok, [user_mjs, _]} = Muro.emit_js(user)
    wire = File.read!(wire_mjs)
    user_js = File.read!(user_mjs)
    assert wire =~ "export function flip("
    assert wire =~ "export const ask ="
    assert user_js =~ "export function flip("
    assert user_js =~ "export function twice("
    assert user_js =~ "export const ask ="

    script = """
    import { flip, twice, muro__data } from "./user.mjs";
    function assert(cond, msg) { if (!cond) throw new Error(msg); }
    const t = muro__data("true");
    const f = muro__data("false");
    assert(flip(t).tag === "false", "flip true");
    assert(flip(f).tag === "true", "flip false");
    assert(twice(t).tag === "true", "twice true");
    assert(twice(f).tag === "false", "twice false");
    console.log("ok");
    """

    assert node!([write!(dir, "drive.mjs", script)], dir) =~ "ok"
  end

  test "a run that names a session is refused" do
    ask = """
    session ask := recv Nat end
    def use : run Nat := ask
    """

    assert {:error, "c:session in use (session)"} =
             Emit.JS.render(parse!(ask), "use", path: "use.muro")

    conform = """
    session ask := recv Nat end
    conform answer : ask := get (k : Nat) (put 0 done)
    def use : run Nat := answer
    """

    assert {:error, "c:session in use (conform)"} =
             Emit.JS.render(parse!(conform), "use", path: "use.muro")

    meet = """
    session ask := recv Nat end
    session back := dual ask
    conform answer : ask := get (k : Nat) (put 0 done)
    conform reply : back := put 0 (get (m : Nat) done)
    meet one : answer with reply
    def use : run Nat := one
    """

    assert {:error, "c:session in use (meet)"} =
             Emit.JS.render(parse!(meet), "use", path: "use.muro")
  end

  test "a binder may reuse a session name" do
    src = """
    session ask := recv Nat end
    data Box : Type where
      box : Nat → Box
    def f : run Π (b : Box) → Nat :=
      λ (b : Box) →
        match b motive (λ _ → Nat)
          | box ask => ask
    def g : run Π (ask : Nat) → Nat :=
      λ (ask : Nat) → ask
    """

    book = parse!(src)
    assert {:ok, source, _types} = Emit.JS.render(book, "shadow", path: "shadow.muro")
    assert source =~ "export function f("
    assert source =~ "export function g("
    assert source =~ "export const ask ="
  end

  test "an omitted session does not claim a JavaScript identifier" do
    omitted = """
    session function := rec X. X
    def function_k : run Nat := 0
    """

    assert {:ok, source, _types} = Emit.JS.render(parse!(omitted), "omit", path: "omit.muro")
    assert source =~ "export function function_k("
    refute source =~ "spell one JavaScript identifier"

    kept = """
    session function := recv Nat end
    def function_k : run Nat := 0
    """

    assert {:error, reason} = Emit.JS.render(parse!(kept), "clash", path: "clash.muro")
    assert reason =~ "function and function_k spell one JavaScript identifier"
  end

  @tag skip: @node_skip
  test "meet steppers follow the fsm trace and keep the run" do
    path = "examples/meet.muro"
    {source, types, dir} = emit_js!(path)

    assert source =~ "export const ping = {"
    assert source =~ "export const grant_end = {"
    assert source =~ "export function kept("
    assert source =~ "export const window_k = {"
    refute source =~ "export const window = {"
    refute source =~ "async function"
    refute source =~ "await "
    refute source =~ "done?("
    refute source =~ "export const done?"
    refute source =~ "GrantEnd"

    assert types =~ "export type SessionStepper = {"
    assert types =~ "export const ping: SessionStepper;"
    assert types =~ "export const grant_end: SessionStepper;"
    assert types =~ "export const window_k: SessionStepper;"
    assert types =~ "done(state: SessionState): boolean;"
    assert types =~ "check_trace(trace: readonly SessionStep[]"
    refute types =~ "done?"

    script = """
    import { ping, back, box, sized, window_k, grant_end, choice, kept } from "./meet.mjs";

    function assert(cond, msg) { if (!cond) throw new Error(msg); }
    function eq(a, b) { return JSON.stringify(a) === JSON.stringify(b); }

    assert(kept() === 0n, "kept");

    let state = ping.init();
    assert(eq(ping.expected(state), { k: "recv", type: "nat" }), "ping expected");
    const bad = ping.recv(state, -1n);
    assert(bad.error && bad.error.unexpected === true, "bad unexpected");
    assert(bad.error.step === "examples/meet.muro:4 session ping: first recv Nat", bad.error.step);
    assert(eq(bad.error.expected, { k: "recv", type: "nat" }), "bad expected");
    assert(bad.error.value === -1n, "bad value");
    assert(ping.send(state, 0n).error.step === bad.error.step, "wrong direction");

    state = ping.recv(state, 0n).ok;
    assert(eq(ping.expected(state), { k: "send", type: "nat" }), "after recv");
    state = ping.send(state, 1n).ok;
    assert(ping.done(state) === true, "ping done");
    assert(ping.expected(state) === "done", "ping end expected");
    const again = ping.recv(state, 0n);
    assert(again.error.step === "examples/meet.muro:4 session ping: end", again.error.step);
    assert(again.error.expected === "done", "end expected");

    assert(ping.check_trace([]).ok === true, "empty trace");
    assert(ping.check_trace([{ k: "recv", value: 0n }]).ok === true, "prefix");
    const full = [{ k: "recv", value: 0n }, { k: "send", value: 1n }];
    assert(ping.check_trace(full, { complete: true }).ok === true, "complete");
    const early = ping.check_trace([{ k: "recv", value: 0n }], { complete: true });
    assert(early.error.incomplete === true && early.error.index === 1, "incomplete");
    assert(early.error.step === "examples/meet.muro:4 session ping: first send Nat", early.error.step);
    const wrong = ping.check_trace([{ k: "recv", value: 0n }, { k: "recv", value: "b0" }]);
    assert(wrong.error.index === 1 && wrong.error.unexpected === true, "trace unexpected");

    const arity = ping.init(0n);
    assert(arity.error.message === "session ping: init requires 0 nat arguments", arity.error.message);
    const listed = ping.check_trace(null);
    assert(listed.error.message === "session ping: check_trace requires a list", listed.error.message);

    const junk = ping.send({ nope: true }, 1n);
    assert(junk.error.expected === "done", "junk expected");
    assert(junk.error.step === "examples/meet.muro:4 session ping: end", junk.error.step);
    assert(ping.done({ nope: true }) === false, "junk done");

    state = back.init();
    assert(eq(back.expected(state), { k: "send", type: "nat" }), "back expected");
    state = back.send(state, 1n).ok;
    state = back.recv(state, 1n).ok;
    assert(back.done(state) === true, "back done");
    const crossed = ping.send(back.init(), 1n);
    assert(crossed.error.expected === "done", "crossed");
    assert(ping.done(back.init()) === false, "crossed done");

    state = box.init();
    assert(box.expected(state).k === "send", "box dir");
    assert(box.expected(state).type.k === "pair", "box pair");
    assert(box.send(state, {}).error.unexpected === true, "box empty");
    state = box.send(state, ["b0", { x: 0n, y: 0n }]).ok;
    assert(box.done(state) === true, "box done");

    state = sized.init();
    state = sized.recv(state, 2n).ok;
    const vec = sized.expected(state);
    assert(vec.k === "send" && vec.type.k === "vec" && vec.type.len === 2, "sized vec");
    assert(sized.send(state, [0n]).error.unexpected === true, "sized short");
    state = sized.send(state, [0n, 0n]).ok;
    assert(sized.done(state) === true, "sized done");

    state = window_k.init();
    state = window_k.recv(state, 8n).ok;
    const bound = window_k.expected(state);
    assert(bound.k === "send" && bound.type.k === "nat_at_most" && bound.type.max === 8, "window bound");
    assert(window_k.send(state, 9n).error.unexpected === true, "window over");
    state = window_k.send(state, 8n).ok;
    assert(window_k.done(state) === true, "window done");
    assert(window_k.expected(window_k.init()).step === undefined, "expected is data");

    state = grant_end.init();
    assert(grant_end.expected(state).k === "send", "grant dir");
    state = grant_end.send(state, 8n).ok;
    assert(grant_end.expected(state).type.max === 8, "grant bound");
    state = grant_end.recv(state, 8n).ok;
    assert(grant_end.done(state) === true, "grant done");

    state = choice.init();
    assert(eq(choice.expected(state), { k: "send_pick", labels: ["b0", "b1"] }), "choice pick");
    assert(choice.done(choice.send(state, { k: "pick", label: "b0" }).ok) === true, "choice b0");
    state = choice.send(choice.init(), { k: "pick", label: "b1" }).ok;
    assert(eq(choice.expected(state), { k: "send", type: "nat" }), "choice b1");
    assert(choice.send(choice.init(), "b0").error.unexpected === true, "string is not a pick");

    console.log("ok");
    """

    assert node!([write!(dir, "drive.mjs", script)], dir) =~ "ok"
  end

  @tag skip: @node_skip
  test "session parameters and a run case agree with fsm" do
    path = "examples/session-calls.muro"

    assert {:error, "c:host in home (place)"} =
             Emit.JS.render(book!(path), "session-calls", path: path)

    {_source, _types, dir} = emit_book!(without_host!(path), path)

    script = """
    import { nums, stream, three } from "./session-calls.mjs";
    function assert(cond, msg) { if (!cond) throw new Error(msg); }

    const missing = nums.init();
    assert(missing.error.message === "session nums: init requires 1 nat argument", missing.error.message);
    const neg = nums.init(-1n);
    assert(neg.error.message === "session nums: argument 1 is not a nat", neg.error.message);
    const num = nums.init(1);
    assert(num.error.message === "session nums: argument 1 is not a nat", "number");
    let state = nums.init(1n);
    assert(nums.expected(state).k === "send" && nums.expected(state).type === "nat", "nums type");
    const noArgs = nums.check_trace([{ k: "send", value: 4n }]);
    assert(noArgs.error.message === "session nums: check_trace requires args: [...]", noArgs.error.message);
    const traced = nums.check_trace([{ k: "send", value: 4n }], { args: [1n], complete: true });
    assert(traced.ok === true, "nums trace");

    state = stream.init(0n);
    assert(stream.expected(state).type.k === "nat_at_most" && stream.expected(state).type.max === 0, "stream 0");
    assert(stream.send(state, 1n).error.unexpected === true, "stream over");
    state = stream.send(state, 0n).ok;
    assert(stream.expected(state).type.max === 1, "stream 1");

    state = three.init();
    assert(three.expected(state).type.k === "vec" && three.expected(state).type.len === 3, "three");
    state = three.send(state, [0n, 0n, 0n]).ok;
    assert(three.done(state) === true, "three done");
    console.log("ok");
    """

    assert node!([write!(dir, "drive.mjs", script)], dir) =~ "ok"

    cap = """
    data Bool : Type where
      true : Bool
      false : Bool
    data Box : Type where
      box : Nat → Box
    def big : run Π (b : Box) → Bool :=
      λ (b : Box) → true
    session s := recv (b : Box) (case (big b) | true => end | false => end)
    """

    book = parse!(cap)
    parent = compile_fsm!(book, "cap.muro")
    sess = child(parent, "s")
    over = {:box, 100_001}

    assert {:error, {:unexpected, step, {:nat_at_most, 100_000}, ^over}} =
             sess.recv(sess.init(), over)

    assert step =~ "first recv (b : Box)"

    {_source, _types, dir} = emit_book!(book, "cap.muro")

    script = """
    import { s } from "./cap.mjs";
    function assert(cond, msg) { if (!cond) throw new Error(msg); }
    const over = { tag: "box", fields: [100001n] };
    const bad = s.recv(s.init(), over);
    assert(bad.error.unexpected === true, "cap flag");
    assert(bad.error.expected.k === "nat_at_most" && bad.error.expected.max === 100000, "cap shape");
    assert(bad.error.value.tag === "box" && bad.error.value.fields[0] === 100001n, "cap value");
    assert(bad.error.step.includes("first recv (b : Box)"), bad.error.step);
    const ok = s.recv(s.init(), { tag: "box", fields: [3n] });
    assert(s.done(ok.ok) === true, "cap done");
    console.log("ok");
    """

    assert node!([write!(dir, "drive.mjs", script)], dir) =~ "ok"
  end

  @tag skip: @node_skip
  test "fsm corpus traces agree with the javascript stepper" do
    for path <- @corpus do
      if path == "examples/session-calls.muro" do
        assert {:error, "c:host in home (place)"} =
                 Emit.JS.render(book!(path), stem(path), path: path)

        differ_book!(without_host!(path), path)
      else
        differ!(path)
      end
    end
  end

  defp differ!(path), do: differ_book!(book!(path), path)

  defp differ_book!(book, path) do
    {:ok, image} = Emit.Fsm.image(book, path, [])
    parent = compile_fsm!(book, path)
    {source, _types, dir} = emit_book!(book, path)
    exports = session_exports(source)

    unless String.contains?(path, "async") do
      refute source =~ "async"
    end

    refute source =~ "async function"
    refute source =~ "await "
    refute source =~ "done?("

    probes =
      Enum.map(image.sessions, fn sess ->
        mod = child(parent, sess.name)
        export = Map.fetch!(exports, sess.name)
        args = List.duplicate(0, length(sess.params))
        state = apply(mod, :init, args)
        primary = probe(mod, state, image.decls, %{bit: :b0, ctor: 0})
        extra = alt_probes(mod, state, image.decls, primary.first)
        %{export: export, name: sess.name, args: args, runs: [primary | extra]}
      end)

    plan = %{
      "sessions" =>
        Enum.map(probes, fn probe ->
          %{
            "export" => probe.export,
            "runs" => Enum.map(probe.runs, & &1.plan)
          }
        end)
    }

    File.write!(Path.join(dir, "plan.json"), JSON.encode!(plan))
    File.write!(Path.join(dir, "drive.mjs"), driver())
    out = node!(["drive.mjs"], dir)
    got = JSON.decode!(out)

    Enum.zip(probes, got)
    |> Enum.each(fn {probe, runs} ->
      Enum.zip(probe.runs, runs)
      |> Enum.each(fn {want, have} ->
        compare!(path, probe.name, want.log, have)
      end)
    end)

    Enum.each(probes, fn probe ->
      case Map.get(@success, {path, probe.name}) do
        nil ->
          :ok

        :done ->
          assert hd(probe.runs).outcome == :done, "#{path} #{probe.name} did not finish"

        :open ->
          assert hd(probe.runs).outcome == {:open, 4}, "#{path} #{probe.name} did not loop"
      end
    end)
  end

  defp alt_probes(mod, state, decls, first) do
    alts =
      case first do
        {:bit, dir, ty} ->
          [probe(mod, fresh(mod, state), decls, %{bit: :b1, ctor: 0}, dir, ty)]

        {:pick, _dir} ->
          [probe(mod, fresh(mod, state), decls, %{bit: :b1, ctor: 0})]

        {:data, dir, name, args, n} when n > 1 ->
          [one_step(mod, fresh(mod, state), decls, dir, {:data, name, args}, n - 1)]

        _ ->
          []
      end

    Enum.filter(alts, & &1)
  end

  defp fresh(mod, _state) do
    n = mod.__info__(:functions) |> Keyword.get(:init)

    args =
      case n do
        0 -> []
        k -> List.duplicate(0, k)
      end

    apply(mod, :init, args)
  end

  defp probe(mod, state, decls, prefer, dir \\ nil, ty \\ nil) do
    first = classify(apply(mod, :expected, [state]), decls)
    {final, steps, outcome} = walk(mod, state, decls, prefer, 4, [])
    bad = bad_step(mod, apply(mod, :init, init_args(mod)), dir, ty)

    outcome =
      cond do
        outcome == :done or apply(mod, :done?, [final]) -> :done
        outcome == :error -> :error
        true -> {:open, length(Enum.reject(steps, &Map.has_key?(&1, :error)))}
      end

    %{
      plan: plan_of(init_args(mod), bad, steps),
      log: log_of(mod, bad, steps),
      outcome: outcome,
      first: first
    }
  end

  defp one_step(mod, state, decls, dir, ty, ctor) do
    sample = sample_ty(ty, decls, %{bit: :b0, ctor: ctor}, 0)

    case sample do
      :stop ->
        nil

      {:ok, value} ->
        result = apply(mod, dir, [state, value.elixir])

        step = %{
          "op" => "step",
          "dir" => Atom.to_string(dir),
          "value" => value.js
        }

        log =
          case result do
            {:ok, next} ->
              %{
                "op" => "step",
                "ok" => true,
                "expected" => conv(apply(mod, :expected, [next])),
                "done" => apply(mod, :done?, [next])
              }

            {:error, {:unexpected, step_s, expected, _value}} ->
              %{
                "op" => "step",
                "ok" => false,
                "error" => %{"step" => step_s, "expected" => conv(expected)}
              }
          end

        %{
          plan: %{
            "args" => Enum.map(init_args(mod), &%{"t" => "nat", "n" => Integer.to_string(&1)}),
            "steps" => [step]
          },
          log: [log],
          outcome: :alt,
          first: nil
        }
    end
  end

  defp walk(mod, state, _decls, _prefer, 0, steps) do
    outcome = if(apply(mod, :done?, [state]), do: :done, else: walk_outcome(steps))
    {state, steps, outcome}
  end

  defp walk(mod, state, decls, prefer, depth, steps) do
    if apply(mod, :done?, [state]) do
      {state, steps, :done}
    else
      expected = apply(mod, :expected, [state])

      case sample(expected, decls, prefer) do
        :stop ->
          {state, steps, walk_outcome(steps)}

        :none ->
          {state, steps, walk_outcome(steps)}

        {:ok, dir, value} ->
          case apply(mod, dir, [state, value.elixir]) do
            {:ok, next} ->
              step = %{dir: dir, value: value, next: next}
              walk(mod, next, decls, %{bit: :b0, ctor: 0}, depth - 1, steps ++ [step])

            {:error, {:unexpected, step_s, exp, _value}} ->
              step = %{dir: dir, value: value, error: %{step: step_s, expected: exp}}
              {state, steps ++ [step], :error}
          end
      end
    end
  end

  defp walk_outcome(steps) do
    cond do
      steps == [] -> :empty
      match?(%{error: _}, List.last(steps)) -> :error
      true -> {:open, length(steps)}
    end
  end

  defp bad_step(mod, state, dir, _ty) do
    expected = apply(mod, :expected, [state])

    dir =
      cond do
        dir in [:send, :recv] -> dir
        is_atom(dir_of(expected)) -> dir_of(expected)
      end

    value = %{elixir: -1, js: %{"t" => "nat", "n" => "-1"}}

    case apply(mod, dir, [state, -1]) do
      {:error, {:unexpected, step, exp, _value}} ->
        %{dir: dir, value: value, error: %{step: step, expected: exp}}

      other ->
        flunk("bad value was accepted by #{inspect(mod)}: #{inspect(other, limit: 5)}")
    end
  end

  defp plan_of(args, bad, steps) do
    items =
      for step <- steps,
          not Map.has_key?(step, :error) do
        %{"dir" => Atom.to_string(step.dir), "value" => step.value.js}
      end

    %{
      "args" => Enum.map(args, &%{"t" => "nat", "n" => Integer.to_string(&1)}),
      "bad" => %{"dir" => Atom.to_string(bad.dir), "value" => bad.value.js},
      "steps" =>
        Enum.map(steps, fn step ->
          %{"op" => "step", "dir" => Atom.to_string(step.dir), "value" => step.value.js}
        end),
      "trace" => items
    }
  end

  defp log_of(mod, bad, steps) do
    bad_log = %{
      "op" => "bad",
      "ok" => false,
      "error" => %{"step" => bad.error.step, "expected" => conv(bad.error.expected)}
    }

    step_logs =
      Enum.map(steps, fn
        %{error: err} ->
          %{
            "op" => "step",
            "ok" => false,
            "error" => %{"step" => err.step, "expected" => conv(err.expected)}
          }

        %{next: next} ->
          %{
            "op" => "step",
            "ok" => true,
            "expected" => conv(apply(mod, :expected, [next])),
            "done" => apply(mod, :done?, [next])
          }
      end)

    _ = mod
    [bad_log | step_logs]
  end

  defp classify(expected, decls) do
    case expected do
      {dir, :bit} when dir in [:send, :recv] ->
        {:bit, dir, :bit}

      {dir, {:data, name, args}} when dir in [:send, :recv] ->
        n =
          case Map.get(decls, name) do
            %{order: order} -> length(order)
            _ -> 0
          end

        {:data, dir, name, args, n}

      {:send_pick, _} ->
        {:pick, :send}

      {:recv_pick, _} ->
        {:pick, :recv}

      _ ->
        :plain
    end
  end

  defp sample(:done, _decls, _prefer), do: :none
  defp sample({:send_pick, _}, _decls, prefer), do: {:ok, :send, pick(prefer.bit)}
  defp sample({:recv_pick, _}, _decls, prefer), do: {:ok, :recv, pick(prefer.bit)}

  defp sample({dir, ty}, decls, prefer) when dir in [:send, :recv] do
    case sample_ty(ty, decls, prefer, 0) do
      :stop -> :stop
      {:ok, value} -> {:ok, dir, value}
    end
  end

  defp sample(_other, _decls, _prefer), do: :stop

  defp sample_ty(:nat, _decls, _prefer, _depth), do: {:ok, nat(0)}
  defp sample_ty(:bit, _decls, prefer, _depth), do: {:ok, bit(prefer.bit)}
  defp sample_ty(:unit, _decls, _prefer, _depth), do: {:ok, %{elixir: :tt, js: %{"t" => "unit"}}}

  defp sample_ty({:nat_at_most, n}, _decls, _prefer, _depth) when is_integer(n) and n >= 0 do
    {:ok, nat(0)}
  end

  defp sample_ty({:pair, a, b}, decls, prefer, depth) do
    with {:ok, left} <- sample_ty(a, decls, prefer, depth),
         {:ok, right} <- sample_ty(b, decls, prefer, depth) do
      {:ok,
       %{
         elixir: {left.elixir, right.elixir},
         js: %{"t" => "pair", "l" => left.js, "r" => right.js}
       }}
    else
      :stop -> :stop
    end
  end

  defp sample_ty({:record, fields}, decls, prefer, depth) do
    samples =
      Enum.reduce_while(fields, [], fn {name, ty}, acc ->
        case sample_ty(ty, decls, prefer, depth) do
          {:ok, value} -> {:cont, [{to_string(name), value} | acc]}
          :stop -> {:halt, :stop}
        end
      end)

    case samples do
      :stop ->
        :stop

      pairs ->
        pairs = Enum.reverse(pairs)

        {:ok,
         %{
           elixir: Map.new(pairs, fn {name, value} -> {name, value.elixir} end),
           js: %{
             "t" => "rec",
             "fs" => Enum.map(pairs, fn {name, value} -> %{"n" => name, "v" => value.js} end)
           }
         }}
    end
  end

  defp sample_ty({:vec, _elem, n}, _decls, _prefer, _depth) when is_integer(n) and n > 8,
    do: :stop

  defp sample_ty({:vec, elem, n}, decls, prefer, depth) when is_integer(n) and n >= 0 do
    samples =
      Enum.reduce_while(1..max(n, 0)//1, [], fn _, acc ->
        case sample_ty(elem, decls, prefer, depth) do
          {:ok, value} -> {:cont, [value | acc]}
          :stop -> {:halt, :stop}
        end
      end)

    case samples do
      :stop ->
        :stop

      items ->
        items = Enum.reverse(items)

        {:ok,
         %{
           elixir: Enum.map(items, & &1.elixir),
           js: %{"t" => "vec", "xs" => Enum.map(items, & &1.js)}
         }}
    end
  end

  defp sample_ty({:data, _name, _args}, _decls, _prefer, depth) when depth > 4, do: :stop

  defp sample_ty({:data, name, args}, decls, prefer, depth) do
    case Map.get(decls, name) do
      %{order: order, ctors: ctors} ->
        tag = Enum.at(order, min(prefer.ctor, length(order) - 1))
        fields = Map.fetch!(ctors, tag)
        sample_fields(name, tag, fields, args, decls, %{prefer | ctor: 0}, depth)

      _ ->
        :stop
    end
  end

  defp sample_ty(_other, _decls, _prefer, _depth), do: :stop

  defp sample_fields(_name, tag, [], _args, _decls, _prefer, _depth) do
    {:ok, %{elixir: String.to_atom(tag), js: %{"t" => "data", "tag" => tag, "fs" => []}}}
  end

  defp sample_fields(dname, tag, fields, args, decls, prefer, depth) do
    samples =
      Enum.reduce_while(fields, [], fn field, acc ->
        case sample_field(field, dname, args, decls, prefer, depth) do
          {:ok, value} -> {:cont, [value | acc]}
          :stop -> {:halt, :stop}
        end
      end)

    case samples do
      :stop ->
        :stop

      items ->
        items = Enum.reverse(items)

        elixir = List.to_tuple([String.to_atom(tag) | Enum.map(items, & &1.elixir)])

        {:ok,
         %{elixir: elixir, js: %{"t" => "data", "tag" => tag, "fs" => Enum.map(items, & &1.js)}}}
    end
  end

  defp sample_field(:nat, _name, _args, _decls, _prefer, _depth), do: {:ok, nat(0)}
  defp sample_field(:bit, _name, _args, _decls, prefer, _depth), do: {:ok, bit(prefer.bit)}

  defp sample_field(:unit, _name, _args, _decls, _prefer, _depth),
    do: {:ok, %{elixir: :tt, js: %{"t" => "unit"}}}

  defp sample_field({:bnat, _}, _name, _args, _decls, _prefer, _depth), do: {:ok, nat(0)}

  defp sample_field({:par, i}, _name, args, decls, prefer, depth) do
    sample_ty(Enum.at(args, i), decls, prefer, depth)
  end

  defp sample_field({:pair, a, b}, name, args, decls, prefer, depth) do
    with {:ok, left} <- sample_field(a, name, args, decls, prefer, depth),
         {:ok, right} <- sample_field(b, name, args, decls, prefer, depth) do
      {:ok,
       %{
         elixir: {left.elixir, right.elixir},
         js: %{"t" => "pair", "l" => left.js, "r" => right.js}
       }}
    else
      :stop -> :stop
    end
  end

  defp sample_field({:rec, fields}, _name, args, decls, prefer, depth) do
    sample_ty(
      {:record, Enum.map(fields, fn {n, ty} -> {n, template_desc(ty, args)} end)},
      decls,
      prefer,
      depth
    )
  end

  defp sample_field({:vec, elem, {:lit, n}}, _name, args, decls, prefer, depth) do
    sample_ty({:vec, template_desc(elem, args), n}, decls, prefer, depth)
  end

  defp sample_field({:vec, _elem, _ix}, _name, _args, _decls, _prefer, _depth), do: :stop

  defp sample_field({:self, ts}, name, args, decls, prefer, depth) do
    inner = Enum.map(ts, &template_desc(&1, args))
    sample_ty({:data, name, inner}, decls, %{prefer | ctor: 0}, depth + 1)
  end

  defp sample_field({:dat, other, ts}, _name, args, decls, prefer, depth) do
    inner = Enum.map(ts, &template_desc(&1, args))
    sample_ty({:data, other, inner}, decls, %{prefer | ctor: 0}, depth + 1)
  end

  defp sample_field(_other, _name, _args, _decls, _prefer, _depth), do: :stop

  defp template_desc(:nat, _args), do: :nat
  defp template_desc(:bit, _args), do: :bit
  defp template_desc(:unit, _args), do: :unit
  defp template_desc({:par, i}, args), do: Enum.at(args, i)

  defp template_desc({:pair, a, b}, args),
    do: {:pair, template_desc(a, args), template_desc(b, args)}

  defp template_desc({:rec, fields}, args) do
    {:record, Enum.map(fields, fn {n, ty} -> {n, template_desc(ty, args)} end)}
  end

  defp template_desc({:vec, elem, {:lit, n}}, args), do: {:vec, template_desc(elem, args), n}
  defp template_desc({:vec, elem, _}, args), do: {:vec, template_desc(elem, args), 0}

  defp template_desc({:dat, name, ts}, args),
    do: {:data, name, Enum.map(ts, &template_desc(&1, args))}

  defp template_desc({:bnat, _}, _args), do: :nat
  defp template_desc(other, _args), do: other

  defp nat(n), do: %{elixir: n, js: %{"t" => "nat", "n" => Integer.to_string(n)}}
  defp bit(:b0), do: %{elixir: :b0, js: %{"t" => "bit", "v" => "b0"}}
  defp bit(:b1), do: %{elixir: :b1, js: %{"t" => "bit", "v" => "b1"}}
  defp pick(:b0), do: %{elixir: {:pick, :b0}, js: %{"t" => "pick", "v" => "b0"}}
  defp pick(:b1), do: %{elixir: {:pick, :b1}, js: %{"t" => "pick", "v" => "b1"}}

  defp dir_of({:send, _}), do: :send
  defp dir_of({:recv, _}), do: :recv
  defp dir_of({:send_pick, _}), do: :send
  defp dir_of({:recv_pick, _}), do: :recv
  defp dir_of(:done), do: :send
  defp dir_of(_), do: :send

  defp conv(:done), do: "done"
  defp conv({:send, ty}), do: %{"k" => "send", "type" => conv_ty(ty)}
  defp conv({:recv, ty}), do: %{"k" => "recv", "type" => conv_ty(ty)}

  defp conv({:send_pick, labels}) do
    %{"k" => "send_pick", "labels" => Enum.map(labels, &to_string/1)}
  end

  defp conv({:recv_pick, labels}) do
    %{"k" => "recv_pick", "labels" => Enum.map(labels, &to_string/1)}
  end

  defp conv({:nat_at_most, n}), do: %{"k" => "nat_at_most", "max" => n}
  defp conv(other), do: conv_ty(other)

  defp conv_ty(:nat), do: "nat"
  defp conv_ty(:bit), do: "bit"
  defp conv_ty(:unit), do: "unit"
  defp conv_ty({:pair, a, b}), do: %{"k" => "pair", "left" => conv_ty(a), "right" => conv_ty(b)}

  defp conv_ty({:record, fields}) do
    %{
      "k" => "record",
      "fields" =>
        Enum.map(fields, fn {name, ty} ->
          %{"name" => to_string(name), "type" => conv_ty(ty)}
        end)
    }
  end

  defp conv_ty({:vec, elem, n}), do: %{"k" => "vec", "elem" => conv_ty(elem), "len" => n}

  defp conv_ty({:data, name, args}),
    do: %{"k" => "data", "name" => name, "args" => Enum.map(args, &conv_ty/1)}

  defp conv_ty({:nat_at_most, n}), do: %{"k" => "nat_at_most", "max" => n}

  defp conv_ty({:repr, inner, name}),
    do: %{"k" => "repr", "type" => conv_ty(inner), "name" => name}

  defp conv_ty(other), do: %{"opaque" => inspect(other, limit: 6)}

  defp compare!(path, name, want, have) do
    assert length(want) == length(have),
           "#{path} #{name} length #{length(want)} != #{length(have)}\n#{inspect(have, pretty: true, limit: 20)}"

    Enum.zip(want, have)
    |> Enum.with_index()
    |> Enum.each(fn {{want, have}, i} ->
      assert want["op"] == have["op"], "#{path} #{name} ##{i} op"

      cond do
        want["ok"] == false ->
          assert have["ok"] == false,
                 "#{path} #{name} ##{i} js accepted #{inspect(have, limit: 8)}"

          assert want["error"]["step"] == have["error"]["step"], "#{path} #{name} ##{i} step"

          assert want["error"]["expected"] == have["error"]["expected"],
                 "#{path} #{name} ##{i} expected\n#{inspect(want["error"]["expected"], limit: 12)}\n#{inspect(have["error"]["expected"], limit: 12)}"

        true ->
          assert have["ok"] == true, "#{path} #{name} ##{i} #{inspect(have["error"], limit: 12)}"

          assert want["expected"] == have["expected"],
                 "#{path} #{name} ##{i}\n#{inspect(want["expected"], limit: 12)}\n#{inspect(have["expected"], limit: 12)}"

          assert want["done"] == have["done"], "#{path} #{name} ##{i} done"
      end
    end)
  end

  defp driver do
    ~S"""
    import { readFileSync } from "node:fs";
    import * as book from "./book.mjs";

    function val(v) {
      if (!v || typeof v !== "object" || !v.t) return v;
      if (v.t === "nat") return BigInt(v.n);
      if (v.t === "bit" || v.t === "atom") return v.v;
      if (v.t === "unit") return null;
      if (v.t === "pair") return [val(v.l), val(v.r)];
      if (v.t === "rec") {
        const o = {};
        for (const f of v.fs) o[f.n] = val(f.v);
        return o;
      }
      if (v.t === "vec") return v.xs.map(val);
      if (v.t === "data") return { tag: v.tag, fields: v.fs.map(val) };
      if (v.t === "pick") return { k: "pick", label: v.v };
      throw new Error("bad value");
    }

    function norm(v) {
      if (typeof v === "bigint") return { bigint: v.toString() };
      if (Array.isArray(v)) return v.map(norm);
      if (v && typeof v === "object") {
        const o = {};
        for (const k of Object.keys(v).sort()) o[k] = norm(v[k]);
        return o;
      }
      return v;
    }

    function shape(err) {
      const out = { step: err.step, expected: norm(err.expected) };
      return out;
    }

    const plan = JSON.parse(readFileSync(new URL("./plan.json", import.meta.url), "utf8"));
    const all = [];

    for (const sess of plan.sessions) {
      const api = book[sess.export];
      const runs = [];
      for (const run of sess.runs) {
        const log = [];
        try {
          const args = (run.args || []).map(val);
          let state = api.init(...args);
          if (state && state.error) {
            log.push({ op: "init", ok: false, error: norm(state.error) });
            runs.push(log);
            continue;
          }
          if (run.bad) {
            const res = api[run.bad.dir](state, val(run.bad.value));
            if (res.error) log.push({ op: "bad", ok: false, error: shape(res.error) });
            else log.push({ op: "bad", ok: true, expected: norm(api.expected(res.ok)), done: api.done(res.ok) });
          }
          for (const step of run.steps || []) {
            const res = api[step.dir](state, val(step.value));
            if (res.error) {
              log.push({ op: "step", ok: false, error: shape(res.error) });
            } else {
              state = res.ok;
              log.push({ op: "step", ok: true, expected: norm(api.expected(state)), done: api.done(state) });
            }
          }
        } catch (err) {
          log.push({ thrown: String(err && err.stack || err) });
        }
        runs.push(log);
      }
      all.push(runs);
    }

    console.log(JSON.stringify(all));
    """
  end

  defp init_args(mod) do
    case mod.__info__(:functions) |> Keyword.get(:init) do
      0 -> []
      n -> List.duplicate(0, n)
    end
  end

  defp session_exports(source) do
    ~r/^\/\/ session (.+)\nexport const (\S+) = \{/m
    |> Regex.scan(source)
    |> Map.new(fn [_, name, ident] -> {name, ident} end)
  end

  defp emit_js!(path) do
    book = book!(path)
    emit_book!(book, path)
  end

  defp emit_book!(book, path) do
    stem = stem(path)
    assert {:ok, source, types} = Emit.JS.render(book, stem, path: path)
    dir = tmp()
    File.write!(Path.join(dir, "book.mjs"), source)
    File.write!(Path.join(dir, stem <> ".mjs"), source)
    File.write!(Path.join(dir, stem <> ".d.ts"), types)
    {source, types, dir}
  end

  defp compile_fsm!(book, path) do
    parent = Module.concat(Muro.JsSessProbe, "P#{System.unique_integer([:positive])}")
    assert {:ok, source} = Emit.Fsm.render(book, path, parent)
    mods = Code.compile_string(source)

    on_exit(fn ->
      Enum.each(mods, fn {mod, _bin} ->
        :code.delete(mod)
        :code.purge(mod)
      end)
    end)

    parent
  end

  defp child(parent, name) do
    aliases = Emit.elixir_modules([name])
    Module.concat(parent, Map.fetch!(aliases, name))
  end

  defp book!(path) do
    assert {:ok, book} = Load.file(path)
    Prelude.for_emit(book)
  end

  defp without_host!(path) do
    src =
      path
      |> File.read!()
      |> String.split("\n", trim: false)
      |> Enum.map_join("\n", fn line ->
        if Regex.match?(~r/^\s*(place|scheme|move|endpoint)\b/, line),
          do: "-- " <> line,
          else: line
      end)

    dir = tmp()
    file = Path.join(dir, Path.basename(path))
    File.write!(file, src)
    assert {:ok, book} = Load.file(file)
    Prelude.for_emit(book)
  end

  defp parse!(src) do
    assert {:ok, book} = Muro.Parser.parse(src)
    Prelude.for_emit(book)
  end

  defp wire_src do
    """
    data Bool : Type where
      true  : Bool
      false : Bool

    def flip : run Π (b : Bool) → Bool :=
      λ (b : Bool) →
        match b motive (λ _ → Bool)
          | true => false
          | false => true

    data Reply : Type where
      written : Reply
      invalid : Reply

    session ask := recv Bool (send Reply end)

    conform answer : ask :=
      get (b : Bool) (put written done)
    """
  end

  defp user_src do
    """
    import "wire.muro"

    def twice : run Π (b : Bool) → Bool :=
      λ (b : Bool) → flip (flip b)
    """
  end

  defp stem(path), do: path |> Path.basename() |> String.trim_trailing(".muro")

  defp node!(args, dir) do
    {out, status} = System.cmd(@node, args, cd: dir, stderr_to_stdout: true)
    assert status == 0, out
    out
  end

  defp write!(dir, name, src) do
    path = Path.join(dir, name)
    File.write!(path, src)
    path
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_js_sess_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)

    on_exit(fn ->
      File.rm_rf!(dir)
    end)

    dir
  end
end
