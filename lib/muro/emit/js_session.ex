defmodule Muro.Emit.JS.Session do
  @moduledoc false

  alias Muro.Emit.Fsm

  @doc false
  def prepare(book, path, opts) when is_list(book) do
    sessions = Enum.filter(book, &(Map.get(&1, :kind) == :session))

    cond do
      sessions == [] ->
        {:ok, nil}

      Enum.any?(sessions, &(not well_formed?(&1))) ->
        {:error, "ill-formed session"}

      true ->
        with {:ok, image} <- Fsm.image(book, path, opts) do
          refuse_repr(image)
        end
    end
  end

  @doc false
  def script(image, %{var: var, runs: runs, idents: idents}) do
    with {:ok, templates} <- enc(templates_of(image)),
         {:ok, duals} <- enc(image.duals),
         {:ok, ends} <- enc(ends_of(image)),
         {:ok, decls} <- enc(image.decls) do
      text =
        machine()
        |> String.replace("___MURO_TEMPLATES___", templates)
        |> String.replace("___MURO_DUALS___", duals)
        |> String.replace("___MURO_ENDS___", ends)
        |> String.replace("___MURO_DECLS___", decls)
        |> String.replace("___MURO_RUNS___", runs_js(runs))
        |> String.replace("___MURO_VAR___", var)

      if String.contains?(text, "___MURO_") do
        {:error, "session template was not filled"}
      else
        {:ok, text <> "\n\n" <> exports(image, var, idents)}
      end
    end
  end

  @doc false
  def dts(image, idents) do
    consts =
      Enum.map_join(image.sessions, "\n", fn sess ->
        "export const #{Map.fetch!(idents, sess.name)}: SessionStepper;"
      end)

    String.trim(stepper_types()) <> "\n\n" <> consts
  end

  defp well_formed?(sess) do
    is_binary(Map.get(sess, :name)) and Map.has_key?(sess, :proto)
  end

  defp templates_of(image) do
    Map.new(image.sessions, fn sess -> {sess.name, {sess.params, sess.proto}} end)
  end

  defp ends_of(image) do
    Map.new(image.sessions, fn sess -> {sess.name, sess.end_step} end)
  end

  defp runs_js(runs) do
    inner =
      runs
      |> Enum.sort()
      |> Enum.map_join(", ", fn {src, ident} -> js_str(src) <> ": " <> ident end)

    "{ " <> inner <> " }"
  end

  defp exports(image, var, idents) do
    image.sessions
    |> Enum.map_join("\n\n", fn sess -> export_one(sess, var, Map.fetch!(idents, sess.name)) end)
  end

  defp export_one(sess, var, ident) do
    key = js_str(sess.name)
    n = length(sess.params)
    word = if n == 1, do: "argument", else: "arguments"
    init_msg = js_str("session #{sess.name}: init requires #{n} nat #{word}")
    list_msg = js_str("session #{sess.name}: check_trace requires a list")
    args_msg = js_str("session #{sess.name}: check_trace requires args: [...]")

    trace =
      if n == 0 do
        """
          check_trace(trace, opts) {
            if (!Array.isArray(trace)) return { error: { message: #{list_msg} } };
            const complete = !!(opts && opts.complete === true);
            return #{var}.trace(#{key}, [], trace, complete);
          }
        """
      else
        """
          check_trace(trace, opts) {
            if (!Array.isArray(trace)) return { error: { message: #{list_msg} } };
            if (!opts || !Array.isArray(opts.args) || opts.args.length !== #{n}) {
              return { error: { message: #{args_msg} } };
            }
            return #{var}.trace(#{key}, opts.args, trace, opts.complete === true);
          }
        """
      end

    """
    // session #{sess.name}
    export const #{ident} = {
      init(...args) {
        if (args.length !== #{n}) return { error: { message: #{init_msg} } };
        return #{var}.init(#{key}, args);
      },
      send(state, value) { return #{var}.step(#{key}, "send", state, value); },
      recv(state, value) { return #{var}.step(#{key}, "recv", state, value); },
      done(state) { return #{var}.done(#{key}, state); },
      expected(state) { return #{var}.expected(#{key}, state); },
    #{trace}};\
    """
  end

  defp refuse_repr(%{reprs: []} = image), do: {:ok, image}

  defp refuse_repr(image) do
    case Enum.find_value(image.sessions, &repr_hit(&1, image)) do
      nil -> {:ok, image}
      reason -> {:error, reason}
    end
  end

  defp repr_hit(sess, image) do
    case walk(sess.proto, image.reprs, image.decls, MapSet.new()) do
      nil ->
        nil

      type ->
        "#{sess.file}:#{sess.line} session #{sess.name}: repr #{type} is not a JavaScript payload"
    end
  end

  defp walk({:send, _, ty, cont}, reprs, decls, seen) do
    walk_ty(ty, reprs, decls, seen) || walk(cont, reprs, decls, seen)
  end

  defp walk({:recv, _, ty, cont}, reprs, decls, seen) do
    walk_ty(ty, reprs, decls, seen) || walk(cont, reprs, decls, seen)
  end

  defp walk({:dsend, _, _, ty, cont}, reprs, decls, seen) do
    walk_ty(ty, reprs, decls, seen) || walk(cont, reprs, decls, seen)
  end

  defp walk({:drecv, _, _, ty, cont}, reprs, decls, seen) do
    walk_ty(ty, reprs, decls, seen) || walk(cont, reprs, decls, seen)
  end

  defp walk({:esend, _, _, _, cont}, reprs, decls, seen) do
    nat_hit(reprs) || walk(cont, reprs, decls, seen)
  end

  defp walk({:erecv, _, _, _, cont}, reprs, decls, seen) do
    nat_hit(reprs) || walk(cont, reprs, decls, seen)
  end

  defp walk({tag, _step, left, right}, reprs, decls, seen) when tag in [:choose, :branch] do
    walk(left, reprs, decls, seen) || walk(right, reprs, decls, seen)
  end

  defp walk({tag, _step, _name, left, right}, reprs, decls, seen) when tag in [:isend, :irecv] do
    walk(left, reprs, decls, seen) || walk(right, reprs, decls, seen)
  end

  defp walk({:rec, _, body}, reprs, decls, seen), do: walk(body, reprs, decls, seen)

  defp walk({:case, _, arms}, reprs, decls, seen) do
    Enum.find_value(arms, fn {_tag, proto} -> walk(proto, reprs, decls, seen) end)
  end

  defp walk({:sjump, _, _}, _, _, _), do: nil
  defp walk({:svar, _}, _, _, _), do: nil
  defp walk({:end, _}, _, _, _), do: nil
  defp walk(:end, _, _, _), do: nil
  defp walk(_, _, _, _), do: nil

  defp nat_hit(reprs) do
    if "Nat" in reprs, do: "Nat", else: nil
  end

  defp walk_ty(:nat, reprs, _decls, _seen), do: nat_hit(reprs)
  defp walk_ty(:bit, _, _, _), do: nil
  defp walk_ty(:unit, _, _, _), do: nil

  defp walk_ty({:pair, a, b}, reprs, decls, seen) do
    walk_ty(a, reprs, decls, seen) || walk_ty(b, reprs, decls, seen)
  end

  defp walk_ty({:rec, fields}, reprs, decls, seen) when is_list(fields) do
    Enum.find_value(fields, fn {_name, ty} -> walk_ty(ty, reprs, decls, seen) end)
  end

  defp walk_ty({:vec, elem, _ix}, reprs, decls, seen), do: walk_ty(elem, reprs, decls, seen)

  defp walk_ty({:dat, name, args}, reprs, decls, seen) when is_binary(name) and is_list(args) do
    cond do
      name in reprs ->
        name

      true ->
        Enum.find_value(args, &walk_ty(&1, reprs, decls, seen)) ||
          walk_decl(name, reprs, decls, seen)
    end
  end

  defp walk_ty({:bnat, _}, reprs, _, _), do: nat_hit(reprs)
  defp walk_ty(_, _, _, _), do: nil

  defp walk_decl(name, reprs, decls, seen) do
    if MapSet.member?(seen, name) do
      nil
    else
      case Map.get(decls, name) do
        %{ctors: ctors} ->
          seen = MapSet.put(seen, name)

          Enum.find_value(ctors, fn {_tag, fields} ->
            Enum.find_value(fields, &walk_field(&1, name, reprs, decls, seen))
          end)

        _ ->
          nil
      end
    end
  end

  defp walk_field(:nat, _name, reprs, _decls, _seen), do: nat_hit(reprs)
  defp walk_field(:bit, _, _, _, _), do: nil
  defp walk_field(:unit, _, _, _, _), do: nil
  defp walk_field({:par, _}, _, _, _, _), do: nil

  defp walk_field({:pair, a, b}, name, reprs, decls, seen) do
    walk_field(a, name, reprs, decls, seen) || walk_field(b, name, reprs, decls, seen)
  end

  defp walk_field({:rec, fields}, name, reprs, decls, seen) when is_list(fields) do
    Enum.find_value(fields, fn {_field, ty} -> walk_field(ty, name, reprs, decls, seen) end)
  end

  defp walk_field({:vec, elem, _ix}, name, reprs, decls, seen) do
    walk_field(elem, name, reprs, decls, seen)
  end

  defp walk_field({:self, ts}, name, reprs, decls, seen) when is_list(ts) do
    Enum.find_value(ts, &walk_field(&1, name, reprs, decls, seen))
  end

  defp walk_field({:dat, name, ts}, _dname, reprs, decls, seen)
       when is_binary(name) and is_list(ts) do
    cond do
      name in reprs ->
        name

      true ->
        Enum.find_value(ts, &walk_field(&1, name, reprs, decls, seen)) ||
          walk_decl(name, reprs, decls, seen)
    end
  end

  defp walk_field({:bnat, _}, _, reprs, _, _), do: nat_hit(reprs)
  defp walk_field(_, _, _, _, _), do: nil

  defp enc(term) do
    case enc1(term) do
      {:ok, io} -> {:ok, IO.iodata_to_binary(io)}
      {:error, _} = err -> err
    end
  end

  defp enc1(atom) when is_atom(atom), do: {:ok, ["a(", js_str(Atom.to_string(atom)), ")"]}
  defp enc1(bin) when is_binary(bin), do: {:ok, ["s(", js_str(bin), ")"]}

  defp enc1(n) when is_integer(n) do
    digits = Integer.to_string(n)
    lit = if n < 0, do: "(" <> digits <> "n)", else: digits <> "n"
    {:ok, ["n(", lit, ")"]}
  end

  defp enc1(list) when is_list(list) do
    with {:ok, inner} <- enc_list(list) do
      {:ok, ["l([", inner, "])"]}
    end
  end

  defp enc1(tuple) when is_tuple(tuple) do
    with {:ok, inner} <- enc_list(Tuple.to_list(tuple)) do
      {:ok, ["t([", inner, "])"]}
    end
  end

  defp enc1(map) when is_map(map) do
    pairs =
      map
      |> Enum.sort_by(fn {key, _} ->
        inspect(key, limit: :infinity, printable_limit: :infinity)
      end)

    with {:ok, inner} <- enc_pairs(pairs) do
      {:ok, ["m([", inner, "])"]}
    end
  end

  defp enc1(other), do: {:error, "cannot encode session term #{inspect(other, limit: 8)}"}

  defp enc_list(items) do
    Enum.reduce_while(items, {:ok, []}, fn item, {:ok, acc} ->
      case enc(item) do
        {:ok, js} -> {:cont, {:ok, [js | acc]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, rev} -> {:ok, Enum.intersperse(Enum.reverse(rev), ",")}
      err -> err
    end
  end

  defp enc_pairs(pairs) do
    Enum.reduce_while(pairs, {:ok, []}, fn {key, val}, {:ok, acc} ->
      with {:ok, ks} <- enc(key),
           {:ok, vs} <- enc(val) do
        {:cont, {:ok, [["[", ks, ",", vs, "]"] | acc]}}
      else
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, rev} -> {:ok, Enum.intersperse(Enum.reverse(rev), ",")}
      err -> err
    end
  end

  defp js_str(s) when is_binary(s) do
    body =
      s
      |> String.replace("\\", "\\\\")
      |> String.replace("\"", "\\\"")
      |> String.replace("\n", "\\n")
      |> String.replace("\r", "\\r")
      |> String.replace("\u2028", "\\u2028")
      |> String.replace("\u2029", "\\u2029")

    "\"" <> body <> "\""
  end

  defp stepper_types do
    ~S"""
    export type SessionStep =
      | { readonly k: "send"; readonly value: unknown }
      | { readonly k: "recv"; readonly value: unknown };
    export type SessionType =
      | "nat"
      | "bit"
      | "unit"
      | { readonly k: "pair"; readonly left: SessionType; readonly right: SessionType }
      | { readonly k: "record"; readonly fields: readonly { readonly name: string; readonly type: SessionType }[] }
      | { readonly k: "vec"; readonly elem: SessionType; readonly len: number }
      | { readonly k: "data"; readonly name: string; readonly args: readonly SessionType[] }
      | { readonly k: "nat_at_most"; readonly max: number };
    export type SessionExpected =
      | "done"
      | { readonly k: "send"; readonly type: SessionType }
      | { readonly k: "recv"; readonly type: SessionType }
      | { readonly k: "send_pick"; readonly labels: readonly ["b0", "b1"] }
      | { readonly k: "recv_pick"; readonly labels: readonly ["b0", "b1"] };
    export type SessionState = { readonly muro__session: string };
    export type SessionError = {
      readonly unexpected: true;
      readonly step: string;
      readonly expected: SessionExpected | { readonly k: "nat_at_most"; readonly max: number };
      readonly value: unknown;
    };
    export type SessionInitError = { readonly message: string };
    export type SessionTraceError =
      | { readonly index: number; readonly unexpected: true; readonly step: string; readonly expected: SessionExpected | { readonly k: "nat_at_most"; readonly max: number }; readonly value: unknown }
      | { readonly index: number; readonly incomplete: true; readonly step: string; readonly expected: SessionExpected }
      | { readonly message: string };
    export type SessionStepper = {
      init(...args: readonly Nat[]): SessionState | { readonly error: SessionInitError };
      send(state: SessionState, value: unknown): { readonly ok: SessionState } | { readonly error: SessionError };
      recv(state: SessionState, value: unknown): { readonly ok: SessionState } | { readonly error: SessionError };
      done(state: SessionState): boolean;
      expected(state: SessionState): SessionExpected;
      check_trace(trace: readonly SessionStep[], opts?: { readonly complete?: boolean; readonly args?: readonly Nat[] }): { readonly ok: true } | { readonly error: SessionTraceError };
    };
    """
  end

  # The protocol is the opened FSM term. Payloads are the JavaScript run
  # image. `done` is the host name of `done?`. Nothing here is async.
  defp machine do
    ~S"""
    const ___MURO_VAR___ = (() => {
      const cap = 100000n;
      function a(v) { return { k: "a", v: v }; }
      function s(v) { return { k: "s", v: v }; }
      function n(v) { return { k: "n", v: v }; }
      function t(v) { return { k: "t", v: v }; }
      function l(v) { return { k: "l", v: v }; }
      function m(v) { return { k: "m", v: v }; }
      function eq(x, y) {
        if (x === y) return true;
        if (x === null || y === null || typeof x !== "object" || typeof y !== "object") return false;
        if (x.k !== y.k) return false;
        if (x.k === "a" || x.k === "s" || x.k === "n") return x.v === y.v;
        if (x.k === "t" || x.k === "l") {
          if (x.v.length !== y.v.length) return false;
          for (let i = 0; i < x.v.length; i++) if (!eq(x.v[i], y.v[i])) return false;
          return true;
        }
        if (x.k === "m") {
          if (x.v.length !== y.v.length) return false;
          for (let i = 0; i < x.v.length; i++) {
            if (!eq(x.v[i][0], y.v[i][0]) || !eq(x.v[i][1], y.v[i][1])) return false;
          }
          return true;
        }
        return false;
      }
      function isA(term, name) { return !!term && term.k === "a" && term.v === name; }
      function isT(term, name, arity) {
        return !!term && term.k === "t" && term.v.length === arity + 1 && isA(term.v[0], name);
      }
      function at(term, i) { return term.v[i]; }
      function text(term) {
        if (term && (term.k === "s" || term.k === "a")) return term.v;
        return null;
      }
      function seenHas(seen, mark) {
        for (let i = 0; i < seen.length; i++) if (eq(seen[i], mark)) return true;
        return false;
      }
      function mget(map, key) {
        if (!map || map.k !== "m") return undefined;
        for (let i = 0; i < map.v.length; i++) if (eq(map.v[i][0], key)) return map.v[i][1];
        return undefined;
      }
      function numOf(bi) {
        if (typeof bi !== "bigint") return 0;
        const max = 9007199254740991n;
        if (bi <= max && bi >= -max) return Number(bi);
        return bi;
      }
      function plain(value) {
        return !!value && typeof value === "object" && !Array.isArray(value);
      }
      const templates = ___MURO_TEMPLATES___;
      const duals = ___MURO_DUALS___;
      const ends = ___MURO_ENDS___;
      const decls = ___MURO_DECLS___;
      const runs = ___MURO_RUNS___;
      function endOf(key) {
        const got = mget(ends, s(key));
        return got && got.k === "s" ? got.v : "";
      }
      function declOf(name) {
        const row = mget(decls, s(name));
        if (!row) return null;
        const np = mget(row, a("np"));
        const ctors = mget(row, a("ctors"));
        if (!np || np.k !== "n" || !ctors) return null;
        return { np: Number(np.v), ctors: ctors };
      }
      function ctorFields(row, tag) {
        const tmpl = mget(row.ctors, s(tag));
        if (!tmpl || tmpl.k !== "l") return null;
        return tmpl.v;
      }
      function ix(term, env) {
        if (isT(term, "lit", 1)) {
          const lit = at(term, 1);
          if (lit && lit.k === "n" && typeof lit.v === "bigint" && lit.v >= 0n) return lit.v;
          return null;
        }
        if (isT(term, "var", 1)) {
          const name = text(at(term, 1));
          const got = name === null ? undefined : env[name];
          if (typeof got === "bigint" && got >= 0n) return got;
          return null;
        }
        if (isT(term, "suc", 1)) {
          const inner = ix(at(term, 1), env);
          if (inner === null) return null;
          return inner + 1n;
        }
        return null;
      }
      function substIx(term, env) {
        if (isT(term, "var", 1)) {
          const name = text(at(term, 1));
          const got = name === null ? undefined : env[name];
          if (typeof got === "bigint" && got >= 0n) return t([a("lit"), n(got)]);
          return term;
        }
        if (isT(term, "suc", 1)) {
          const inner = substIx(at(term, 1), env);
          if (isT(inner, "lit", 1)) return t([a("lit"), n(at(inner, 1).v + 1n)]);
          return t([a("suc"), inner]);
        }
        return term;
      }
      function subst(ty, env) {
        if (isT(ty, "pair", 2)) return t([a("pair"), subst(at(ty, 1), env), subst(at(ty, 2), env)]);
        if (isT(ty, "rec", 1)) {
          const fields = at(ty, 1).v.map((pair) => t([pair.v[0], subst(pair.v[1], env)]));
          return t([a("rec"), l(fields)]);
        }
        if (isT(ty, "vec", 2)) return t([a("vec"), subst(at(ty, 1), env), substIx(at(ty, 2), env)]);
        if (isT(ty, "dat", 2)) {
          const args = at(ty, 2).v.map((arg) => subst(arg, env));
          return t([a("dat"), at(ty, 1), l(args)]);
        }
        return ty;
      }
      function inst(field, dname, args) {
        if (isT(field, "par", 1)) return args[Number(at(field, 1).v)];
        if (isT(field, "pair", 2)) return t([a("pair"), inst(at(field, 1), dname, args), inst(at(field, 2), dname, args)]);
        if (isT(field, "rec", 1)) {
          const fields = at(field, 1).v.map((pair) => t([pair.v[0], inst(pair.v[1], dname, args)]));
          return t([a("rec"), l(fields)]);
        }
        if (isT(field, "vec", 2)) return t([a("vec"), inst(at(field, 1), dname, args), at(field, 2)]);
        if (isT(field, "self", 1)) {
          const ts = at(field, 1).v.map((item) => inst(item, dname, args));
          return t([a("dat"), s(dname), l(ts)]);
        }
        if (isT(field, "dat", 2)) {
          const ts = at(field, 2).v.map((item) => inst(item, dname, args));
          return t([a("dat"), at(field, 1), l(ts)]);
        }
        return field;
      }
      function describe(ty) {
        if (isA(ty, "nat")) return "nat";
        if (isA(ty, "bit")) return "bit";
        if (isA(ty, "unit")) return "unit";
        if (isT(ty, "pair", 2)) return { k: "pair", left: describe(at(ty, 1)), right: describe(at(ty, 2)) };
        if (isT(ty, "rec", 1)) {
          const fields = at(ty, 1).v.map((pair) => ({ name: text(pair.v[0]), type: describe(pair.v[1]) }));
          return { k: "record", fields: fields };
        }
        if (isT(ty, "vec", 2)) {
          const ixv = at(ty, 2);
          const len = isT(ixv, "lit", 1) ? numOf(at(ixv, 1).v) : 0;
          return { k: "vec", elem: describe(at(ty, 1)), len: len };
        }
        if (isT(ty, "dat", 2)) {
          return { k: "data", name: text(at(ty, 1)), args: at(ty, 2).v.map(describe) };
        }
        if (isT(ty, "nat_at_most", 1)) return { k: "nat_at_most", max: numOf(at(ty, 1).v) };
        return { k: "opaque" };
      }
      function boundDesc(bound, env) {
        const got = ix(bound, env);
        return { k: "nat_at_most", max: numOf(got === null ? 0n : got) };
      }
      function expect(st) {
        const p = st.p;
        const env = st.e;
        if (isT(p, "end", 1) || isT(p, "stuck", 1)) return "done";
        if (isT(p, "send", 3)) return { k: "send", type: describe(subst(at(p, 2), env)) };
        if (isT(p, "recv", 3)) return { k: "recv", type: describe(subst(at(p, 2), env)) };
        if (isT(p, "dsend", 4)) return { k: "send", type: describe(subst(at(p, 3), env)) };
        if (isT(p, "drecv", 4)) return { k: "recv", type: describe(subst(at(p, 3), env)) };
        if (isT(p, "esend", 4)) return { k: "send", type: boundDesc(at(p, 3), env) };
        if (isT(p, "erecv", 4)) return { k: "recv", type: boundDesc(at(p, 3), env) };
        if (isT(p, "isend", 4)) return { k: "send", type: "bit" };
        if (isT(p, "irecv", 4)) return { k: "recv", type: "bit" };
        if (isT(p, "choose", 3)) return { k: "send_pick", labels: ["b0", "b1"] };
        if (isT(p, "branch", 3)) return { k: "recv_pick", labels: ["b0", "b1"] };
        return "done";
      }
      function expectTy(st, ty) {
        const shown = describe(subst(ty, st.e));
        const p = st.p;
        if (isT(p, "isend", 4)) return { k: "send", type: "bit" };
        if (isT(p, "send", 3) || isT(p, "dsend", 4) || isT(p, "esend", 4)) return { k: "send", type: shown };
        return { k: "recv", type: shown };
      }
      function payload(ty, value) {
        if (isA(ty, "nat")) return typeof value === "bigint" && value >= 0n;
        if (isA(ty, "bit")) return value === "b0" || value === "b1";
        if (isA(ty, "unit")) return value === null;
        if (isT(ty, "pair", 2)) {
          return Array.isArray(value) && value.length === 2 && payload(at(ty, 1), value[0]) && payload(at(ty, 2), value[1]);
        }
        if (isT(ty, "rec", 1)) {
          if (!plain(value)) return false;
          const fields = at(ty, 1).v;
          const names = fields.map((pair) => text(pair.v[0]));
          const keys = Object.keys(value).sort();
          const want = names.slice().sort();
          if (keys.length !== want.length) return false;
          for (let i = 0; i < keys.length; i++) if (keys[i] !== want[i]) return false;
          return fields.every((pair) => payload(pair.v[1], value[text(pair.v[0])]));
        }
        if (isT(ty, "vec", 2)) {
          const ixv = at(ty, 2);
          if (!isT(ixv, "lit", 1) || !Array.isArray(value)) return false;
          if (BigInt(value.length) !== at(ixv, 1).v) return false;
          return value.every((item) => payload(at(ty, 1), item));
        }
        if (isT(ty, "dat", 2)) return payloadDat(text(at(ty, 1)), at(ty, 2).v, value);
        return false;
      }
      function payloadDat(name, args, value) {
        const row = declOf(name);
        if (!row || !args || args.length !== row.np) return false;
        if (!plain(value) || typeof value.tag !== "string" || !Array.isArray(value.fields)) return false;
        const tmpl = ctorFields(row, value.tag);
        if (!tmpl || tmpl.length !== value.fields.length) return false;
        for (let i = 0; i < tmpl.length; i++) {
          if (!payload(inst(tmpl[i], name, args), value.fields[i])) return false;
        }
        return true;
      }
      function take(ty, value, env) {
        if (payload(subst(ty, env), value)) return { ok: value };
        return null;
      }
      function toEmitted(value, ty) {
        if (isA(ty, "nat")) {
          if (typeof value !== "bigint" || value < 0n) return "error";
          if (value > cap) return "cap";
          return { ok: value };
        }
        if (isA(ty, "bit")) return value === "b0" || value === "b1" ? { ok: value } : "error";
        if (isA(ty, "unit")) return value === null ? { ok: value } : "error";
        if (isT(ty, "pair", 2)) {
          if (!Array.isArray(value) || value.length !== 2) return "error";
          const left = toEmitted(value[0], at(ty, 1));
          if (left === "cap" || left === "error") return left;
          const right = toEmitted(value[1], at(ty, 2));
          if (right === "cap" || right === "error") return right;
          return { ok: value };
        }
        if (isT(ty, "rec", 1)) {
          if (!plain(value)) return "error";
          for (const pair of at(ty, 1).v) {
            const got = toEmitted(value[text(pair.v[0])], pair.v[1]);
            if (got === "cap" || got === "error") return got;
          }
          return { ok: value };
        }
        if (isT(ty, "vec", 2)) {
          if (!Array.isArray(value)) return "error";
          for (const item of value) {
            const got = toEmitted(item, at(ty, 1));
            if (got === "cap" || got === "error") return got;
          }
          return { ok: value };
        }
        if (isT(ty, "dat", 2)) return emitDat(value, text(at(ty, 1)), at(ty, 2).v);
        return "error";
      }
      function emitDat(value, name, args) {
        const row = declOf(name);
        if (!row || !plain(value) || typeof value.tag !== "string" || !Array.isArray(value.fields)) return "error";
        const tmpl = ctorFields(row, value.tag);
        if (!tmpl || tmpl.length !== value.fields.length) return "error";
        for (let i = 0; i < tmpl.length; i++) {
          const got = toEmitted(value.fields[i], inst(tmpl[i], name, args));
          if (got === "cap" || got === "error") return got;
        }
        return { ok: value };
      }
      function callRun(fname, arg) {
        const fun = runs[fname];
        if (typeof fun !== "function") return null;
        try {
          return { ok: fun(arg) };
        } catch (_err) {
          return null;
        }
      }
      function armTag(value, arms) {
        const names = [];
        for (const arm of arms.v) {
          if (arm && arm.k === "t" && arm.v[0]) {
            const name = text(arm.v[0]);
            if (name !== null) names.push(name);
          }
        }
        if (typeof value === "string" && names.indexOf(value) >= 0) return value;
        if (plain(value) && typeof value.tag === "string" && names.indexOf(value.tag) >= 0) return value.tag;
        return null;
      }
      function resultTag(value, ty) {
        if (isT(ty, "dat", 2)) {
          const row = declOf(text(at(ty, 1)));
          if (!row || !plain(value) || typeof value.tag !== "string") return null;
          return ctorFields(row, value.tag) ? value.tag : null;
        }
        if (isA(ty, "bit") && (value === "b0" || value === "b1")) return value;
        return null;
      }
      function byTag(tag, arms) {
        if (typeof tag !== "string") return "error";
        for (const arm of arms.v) {
          if (arm && arm.k === "t" && arm.v.length === 2 && text(arm.v[0]) === tag) return arm.v[1];
        }
        return "error";
      }
      function scrutName(scrut) {
        if (isT(scrut, "name", 1)) return text(at(scrut, 1));
        if (isT(scrut, "run", 3) && at(scrut, 3) && at(scrut, 3).k === "l") return null;
        if (isT(scrut, "run", 2)) return text(at(scrut, 2));
        return null;
      }
      function select(scrut, ty, arms, st) {
        if (isT(scrut, "name", 1)) {
          const name = text(at(scrut, 1));
          return byTag(resultTag(st.e[name], subst(ty, st.e)), arms);
        }
        if (isT(scrut, "run", 3) && at(scrut, 3) && at(scrut, 3).k === "l") return "error";
        if (isT(scrut, "run", 2)) {
          const fname = text(at(scrut, 1));
          const name = text(at(scrut, 2));
          const sty = subst(ty, st.e);
          const conv = toEmitted(st.e[name], sty);
          if (conv === "cap" || conv === "error") return conv;
          const called = callRun(fname, conv.ok);
          if (!called) return "error";
          return byTag(armTag(called.ok, arms), arms);
        }
        return "error";
      }
      function vals(args, env) {
        if (!args || args.k !== "l") return null;
        const out = [];
        for (const arg of args.v) {
          const got = ix(arg, env);
          if (got === null) return null;
          out.push(got);
        }
        return out;
      }
      function open(table, name, args, env) {
        const entry = mget(table, name);
        if (!entry || entry.k !== "t" || entry.v.length !== 2) return null;
        const params = entry.v[0];
        if (!params || params.k !== "l") return null;
        const vs = vals(args, env);
        if (!vs || vs.length !== params.v.length) return null;
        const next = {};
        for (let i = 0; i < vs.length; i++) {
          const key = text(params.v[i]);
          if (key === null) return null;
          next[key] = vs[i];
        }
        return { proto: entry.v[1], env: next };
      }
      function enter(target, args, env) {
        if (target && target.k === "s") return open(templates, target, args, env);
        if (isT(target, "dual", 1)) return open(duals, at(target, 1), args, env);
        return null;
      }
      function stuck(st) { return { ...st, p: t([a("stuck"), s(st.s)]) }; }
      function expose(st, seen) {
        seen = seen || [];
        const p = st.p;
        if (isT(p, "rec", 2)) {
          const name = text(at(p, 1));
          const body = at(p, 2);
          return expose({ ...st, p: body, r: { ...st.r, [name]: body } }, seen);
        }
        if (isT(p, "svar", 1)) {
          const mark = t([a("svar"), at(p, 1)]);
          if (seenHas(seen, mark)) return stuck(st);
          const body = st.r[text(at(p, 1))];
          if (!body) return stuck(st);
          return expose({ ...st, p: body }, [mark, ...seen]);
        }
        if (isT(p, "sjump", 2)) {
          const mark = t([a("jump"), at(p, 1), at(p, 2)]);
          if (seenHas(seen, mark)) return stuck(st);
          const entered = enter(at(p, 1), at(p, 2), st.e);
          if (!entered) return stuck(st);
          return expose({ ...st, p: entered.proto, e: entered.env, r: {} }, [mark, ...seen]);
        }
        if (isT(p, "case", 2)) return stuck(st);
        if (isT(p, "end", 1)) return { ...st, s: text(at(p, 1)) };
        if (p && p.k === "t" && p.v.length >= 2 && p.v[1] && p.v[1].k === "s") {
          const tag = text(p.v[0]);
          if (tag === "send" || tag === "recv" || tag === "dsend" || tag === "drecv" || tag === "esend" || tag === "erecv" || tag === "isend" || tag === "irecv" || tag === "choose" || tag === "branch" || tag === "stuck") {
            return { ...st, s: p.v[1].v };
          }
        }
        return st;
      }
      function quiet(st, seen) {
        const p = st.p;
        if (isT(p, "rec", 2)) {
          const name = text(at(p, 1));
          const body = at(p, 2);
          return quiet({ ...st, p: body, r: { ...st.r, [name]: body } }, seen);
        }
        if (isT(p, "svar", 1)) {
          const mark = t([a("svar"), at(p, 1)]);
          if (seenHas(seen, mark)) return stuck(st);
          const body = st.r[text(at(p, 1))];
          if (!body) return stuck(st);
          return quiet({ ...st, p: body }, [mark, ...seen]);
        }
        if (isT(p, "sjump", 2)) {
          const mark = t([a("jump"), at(p, 1), at(p, 2)]);
          if (seenHas(seen, mark)) return stuck(st);
          const entered = enter(at(p, 1), at(p, 2), st.e);
          if (!entered) return stuck(st);
          return quiet({ ...st, p: entered.proto, e: entered.env, r: {} }, [mark, ...seen]);
        }
        return st;
      }
      function prep(key, state) {
        if (!plain(state) || state.muro__session !== key) return null;
        if (!state.p || !plain(state.e) || !plain(state.r) || typeof state.s !== "string") return null;
        return state;
      }
      function unexpected(step, expected, value) {
        return { error: { unexpected: true, step: step, expected: expected, value: value } };
      }
      function dirTy(dir, ty, env) {
        const shown = describe(subst(ty, env));
        return dir === "send" ? { k: "send", type: shown } : { k: "recv", type: shown };
      }
      function arm(st, binder, hostValue, ty, scrut, arms, dir) {
        const expected = dirTy(dir, ty, st.e);
        if (scrutName(scrut) !== binder) return unexpected(st.s, expected, hostValue);
        const sel = select(scrut, ty, arms, st);
        if (sel === "cap") return unexpected(st.s, { k: "nat_at_most", max: numOf(cap) }, hostValue);
        if (!sel || sel === "error") return unexpected(st.s, expected, hostValue);
        return { ok: expose({ ...st, p: sel }) };
      }
      function goOn(st, binder, hostValue, ty, dir) {
        const st2 = quiet(st, []);
        if (isT(st2.p, "case", 2)) return arm(st2, binder, hostValue, ty, at(st2.p, 1), at(st2.p, 2), dir);
        return { ok: expose(st2) };
      }
      function payloadStep(st, ty, cont, value, step, nameTerm) {
        const taken = take(ty, value, st.e);
        if (!taken) return unexpected(step, expectTy(st, ty), value);
        const binder = nameTerm ? text(nameTerm) : null;
        const env = binder === null ? st.e : { ...st.e, [binder]: taken.ok };
        const dir = isT(st.p, "send", 3) || isT(st.p, "dsend", 4) ? "send" : "recv";
        return goOn({ ...st, p: cont, e: env }, binder, value, ty, dir);
      }
      function evidence(st, nameTerm, bound, cont, value, step) {
        const shown = boundDesc(bound, st.e);
        const expected = isT(st.p, "erecv", 4) ? { k: "recv", type: shown } : { k: "send", type: shown };
        const max = ix(bound, st.e);
        if (typeof value === "bigint" && value >= 0n && max !== null && value <= max) {
          const binder = text(nameTerm);
          return { ok: expose({ ...st, e: { ...st.e, [binder]: value }, p: cont }) };
        }
        return unexpected(step, expected, value);
      }
      function indexStep(st, nameTerm, left, right, value, step) {
        if (value === "b0" || value === "b1") {
          const binder = text(nameTerm);
          return { ok: expose({ ...st, e: { ...st.e, [binder]: value }, p: value === "b0" ? left : right }) };
        }
        return unexpected(step, expect(st), value);
      }
      function pick(st, left, right, value, step) {
        if (plain(value) && value.k === "pick" && (value.label === "b0" || value.label === "b1")) {
          return { ok: expose({ ...st, p: value.label === "b0" ? left : right }) };
        }
        return unexpected(step, expect(st), value);
      }
      function act(dir, st, value) {
        const p = st.p;
        const step = st.s;
        const pinned = p && p.k === "t" && p.v[1] && p.v[1].k === "s" && p.v[1].v === step;
        if (!pinned) return unexpected(step, expect(st), value);
        if (dir === "send" && isT(p, "send", 3)) return payloadStep(st, at(p, 2), at(p, 3), value, step, null);
        if (dir === "recv" && isT(p, "recv", 3)) return payloadStep(st, at(p, 2), at(p, 3), value, step, null);
        if (dir === "send" && isT(p, "dsend", 4)) return payloadStep(st, at(p, 3), at(p, 4), value, step, at(p, 2));
        if (dir === "recv" && isT(p, "drecv", 4)) return payloadStep(st, at(p, 3), at(p, 4), value, step, at(p, 2));
        if (dir === "send" && isT(p, "esend", 4)) return evidence(st, at(p, 2), at(p, 3), at(p, 4), value, step);
        if (dir === "recv" && isT(p, "erecv", 4)) return evidence(st, at(p, 2), at(p, 3), at(p, 4), value, step);
        if (dir === "send" && isT(p, "isend", 4)) return indexStep(st, at(p, 2), at(p, 3), at(p, 4), value, step);
        if (dir === "recv" && isT(p, "irecv", 4)) return indexStep(st, at(p, 2), at(p, 3), at(p, 4), value, step);
        if (dir === "send" && isT(p, "choose", 3)) return pick(st, at(p, 2), at(p, 3), value, step);
        if (dir === "recv" && isT(p, "branch", 3)) return pick(st, at(p, 2), at(p, 3), value, step);
        return unexpected(step, expect(st), value);
      }
      function nats(key, args) {
        const entry = mget(templates, s(key));
        if (!entry || entry.k !== "t" || !entry.v[0] || entry.v[0].k !== "l" || entry.v[0].v.length !== args.length) {
          return "session " + key + ": check_trace requires args: [...]";
        }
        for (let i = 0; i < args.length; i++) {
          const arg = args[i];
          if (typeof arg !== "bigint" || arg < 0n) {
            return "session " + key + ": argument " + (i + 1) + " is not a nat";
          }
        }
        return null;
      }
      function init(key, args) {
        const msg = nats(key, args);
        if (msg) return { error: { message: msg } };
        const entry = mget(templates, s(key));
        const params = entry.v[0];
        const env = {};
        for (let i = 0; i < args.length; i++) env[text(params.v[i])] = args[i];
        return expose({ muro__session: key, p: entry.v[1], e: env, r: {}, s: endOf(key) });
      }
      function step(key, dir, state, value) {
        const st0 = prep(key, state);
        if (!st0) return unexpected(endOf(key), "done", value);
        const st = expose(st0);
        if (isT(st.p, "end", 1) || isT(st.p, "stuck", 1)) return unexpected(st.s, "done", value);
        return act(dir, st, value);
      }
      function done(key, state) {
        const st = prep(key, state);
        if (!st) return false;
        return isT(expose(st).p, "end", 1);
      }
      function expected(key, state) {
        const st = prep(key, state);
        if (!st) return "done";
        return expect(expose(st));
      }
      function atStep(state) {
        const st = prep(state.muro__session, state);
        if (!st) return endOf(state.muro__session);
        const shown = expose(st);
        return typeof shown.s === "string" ? shown.s : endOf(st.muro__session);
      }
      function trace(key, args, list, complete) {
        const msg = nats(key, args);
        if (msg) return { error: { message: msg } };
        let state = init(key, args);
        if (state && state.error) return state;
        for (let i = 0; i < list.length; i++) {
          const item = list[i];
          const dirOk = item && (item.k === "send" || item.k === "recv") && Object.prototype.hasOwnProperty.call(item, "value");
          if (!dirOk) {
            return { error: { index: i, unexpected: true, step: atStep(state), expected: expected(key, state), value: item } };
          }
          const res = step(key, item.k, state, item.value);
          if (res.error) {
            return { error: { index: i, unexpected: true, step: res.error.step, expected: res.error.expected, value: res.error.value } };
          }
          state = res.ok;
        }
        if (complete && !done(key, state)) {
          return { error: { index: list.length, incomplete: true, step: atStep(state), expected: expected(key, state) } };
        }
        return { ok: true };
      }
      return { init: init, step: step, done: done, expected: expected, trace: trace };
    })();
    """
    |> String.trim()
  end
end
