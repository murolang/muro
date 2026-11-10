defmodule Muro.EmitJSReprTest do
  use ExUnit.Case, async: false

  alias Muro.{Emit, Parser, Prelude}

  @moduletag timeout: 180_000

  @node System.find_executable("node") ||
          if(File.regular?("/opt/homebrew/bin/node"), do: "/opt/homebrew/bin/node")

  if System.get_env("CI") && is_nil(@node) do
    raise "node is required when CI is set and was not found on PATH"
  end

  @node_skip if(is_nil(@node), do: "node not on PATH", else: false)

  @harness """
  function dump(v) {
    if (typeof v === "bigint") return v.toString() + "n";
    if (typeof v === "function") return "fn";
    if (typeof v === "symbol") return v.toString();
    if (v instanceof Map) {
      return "Map(" + [...v].map(([k, x]) => dump(k) + "=>" + dump(x)).join(", ") + ")";
    }
    if (Array.isArray(v)) return "[" + v.map(dump).join(", ") + "]";
    if (v && typeof v === "object") {
      const keys = Object.keys(v);
      if (typeof v.atom === "string" && keys.length === 1) return ":" + v.atom;
      return "{" + keys.map((k) => k + ":" + dump(v[k])).join(", ") + "}";
    }
    return JSON.stringify(v);
  }
  function same(a, b) {
    if (typeof a === "bigint" || typeof b === "bigint") return a === b;
    if (Object.is(a, b)) return true;
    if (a instanceof Map || b instanceof Map) {
      if (!(a instanceof Map) || !(b instanceof Map) || a.size !== b.size) return false;
      for (const [k, v] of a) {
        let hit = false;
        for (const [k2, v2] of b) if (same(k, k2) && same(v, v2)) hit = true;
        if (!hit) return false;
      }
      return true;
    }
    if (Array.isArray(a) || Array.isArray(b)) {
      if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
      for (let i = 0; i < a.length; i++) if (!same(a[i], b[i])) return false;
      return true;
    }
    if (a && b && typeof a === "object" && typeof b === "object") {
      const ka = Object.keys(a);
      const kb = Object.keys(b);
      if (ka.length !== kb.length) return false;
      for (const k of ka) if (!Object.hasOwn(b, k) || !same(a[k], b[k])) return false;
      return true;
    }
    return false;
  }
  function check(cond, msg) { if (!cond) throw new Error(msg); }
  function took(r) {
    if (!r || typeof r !== "object" || !Object.hasOwn(r, "ok")) throw new Error("expected ok, got " + dump(r));
    return r.ok;
  }
  function decoded(r) {
    const o = took(r);
    if (!o || typeof o !== "object" || !Object.hasOwn(o, "value") || !Object.hasOwn(o, "table")) {
      throw new Error("expected {value, table}, got " + dump(o));
    }
    return o;
  }
  function failed(r) {
    if (!r || !r.error || !Array.isArray(r.error.path)) throw new Error("expected error, got " + dump(r));
    return r.error;
  }
  function reason(r, path, k) {
    const e = failed(r);
    check(same(e.path, path), "path " + dump(e.path) + " want " + dump(path) + " :: " + dump(e));
    check(e.reason.k === k, "reason " + e.reason.k + " want " + k + " :: " + dump(e));
    return e.reason;
  }
  function T(tag, ...fields) { return { tag, fields }; }
  function names(table) { return m.muro_repr_table_names(table); }
  function mapGet(map, key) {
    for (const [k, v] of map) if (same(k, key)) return { found: true, value: v };
    return { found: false };
  }
  """

  test "a book with no repr emits no codec" do
    dir = tmp()
    {source, types} = emit_example!(dir, "maybe")
    refute source =~ "decode_"
    refute source =~ "encode_"
    refute source =~ "muro_repr_"
    refute types =~ "decode_"
    refute types =~ "ReprDecode"
    refute types =~ "muro_repr_"
  end

  test "decode and encode are emitted next to the runs" do
    dir = tmp()
    {source, types} = emit_example!(dir, "repr")

    assert source =~ "export function toggle("
    assert source =~ "export function describe("
    assert source =~ "export function widen("
    assert source =~ "export function decode_entry("
    assert source =~ "export function encode_entry("
    assert source =~ "export function decode_outcome("
    assert source =~ "export function encode_shape("
    assert source =~ "const muro_repr_nat_max = 1_000_000;"
    assert source =~ "export function muro_repr_table_new("
    assert source =~ "export function muro_repr_table_names("
    refute source =~ "export const "
    refute source =~ "muro_repr_bin_from"
    refute source =~ "SessionStepper"

    toggle = String.split(source, "export function toggle(", parts: 2) |> hd() |> byte_size()
    decode = String.split(source, "export function decode_bool(", parts: 2) |> hd() |> byte_size()
    assert toggle < decode

    assert types =~ "export type ReprDecode<T>"
    assert types =~ "export type ReprEncode"

    assert types =~
             "export function decode_entry(value: unknown, table?: ReprTable): ReprDecode<Entry>;"

    assert types =~ "export function encode_entry(value: Entry, table: ReprTable): ReprEncode;"

    assert types =~
             "export function decode_bool(value: unknown, table?: ReprTable): ReprDecode<Bool>;"

    assert types =~ "export type Nat = bigint;"

    book = load_example!("examples/repr.muro")
    assert {:ok, outline} = Emit.JS.outline(book, "repr")
    assert "decode_entry" in outline.names
    assert "encode_shape" in outline.names
    assert "muro_repr_table_new" in outline.names
    assert "export function decode_entry(value, table)" in outline.clauses
    assert "export function encode_entry(value, table)" in outline.clauses
  end

  @tag skip: @node_skip
  test "a host calls decode, the proved function, then encode" do
    dir = tmp()
    emit_example!(dir, "repr")

    node!(dir, """
    import * as m from "./repr.mjs";
    #{@harness}
    const empty = m.muro_repr_table_new();
    const dec = decoded(m.decode_entry({ id: 3, enabled: true }, empty));
    check(dec.table === empty, "empty table is reused");
    check(names(dec.table).length === 0, "no names");
    check(same(dec.value, T("entry", 3n, T("just", T("true")))), dump(dec.value));

    const flipped = m.toggle(dec.value);
    const wire = took(m.encode_entry(flipped, dec.table));
    check(same(wire, { id: 3, enabled: false }), dump(wire));
    check(Object.getPrototypeOf(wire) === null, "string-key map has no prototype");

    const described = took(m.encode_outcome(m.describe(dec.value), dec.table));
    check(same(described, { status: "on", id: 3 }), dump(described));

    const missing = decoded(m.decode_entry({ id: 3 }));
    const absent = took(m.encode_outcome(m.describe(missing.value), missing.table));
    check(absent === null, dump(absent));

    const circle = decoded(m.decode_shape({ kind: "circle", r: 3 }));
    const wide = took(m.encode_shape(m.widen(circle.value), circle.table));
    check(same(wide, { kind: "circle", r: 4 }), dump(wide));

    const fresh = m.muro_repr_table_new();
    const again = decoded(m.decode_entry({ id: 3, enabled: false }, fresh));
    check(again.table === fresh, "no intern keeps the table");
    """)
  end

  @tag skip: @node_skip
  test "decode errors name the path and the value, and malformed input does not throw" do
    dir = tmp()
    emit_example!(dir, "repr")

    node!(dir, """
    import * as m from "./repr.mjs";
    #{@harness}
    const yes = m.muro_repr_atom("yes");
    let r = reason(m.decode_bool(1), [], "not_boolean");
    check(r.value === 1, dump(r));
    r = reason(m.decode_bool(null), [], "not_boolean");
    check(r.value === null, dump(r));
    r = reason(m.decode_entry({ id: 3, enabled: 1 }), ["enabled"], "not_boolean");
    check(r.value === 1, dump(r));
    r = reason(m.decode_entry({ id: 1.5 }), ["id"], "not_integer");
    check(r.value === 1.5, dump(r));
    r = reason(m.decode_entry({ id: "1" }), ["id"], "not_integer");
    check(r.value === "1", dump(r));
    r = reason(m.decode_entry({ id: null }), ["id"], "not_integer");
    check(r.value === null, dump(r));
    r = reason(m.decode_entry({ id: -1 }), ["id"], "negative_integer");
    check(r.value === -1, dump(r));
    r = reason(m.decode_entry({ id: 1000001 }), ["id"], "nat_too_large");
    check(r.value === 1000001, "keeps the host number");
    r = reason(m.decode_entry({ id: 1000001n }), ["id"], "nat_too_large");
    check(r.value === 1000001n, "keeps the host bigint");
    r = reason(m.decode_entry(yes), [], "not_map");
    check(r.value.atom === "yes", dump(r));
    r = reason(m.decode_entry({ enabled: true }), [], "missing_key");
    check(r.key === "id", dump(r));
    r = reason(m.decode_entry({ id: 1, enabled: true, extra: 1 }), [], "unexpected_key");
    check(r.key === "extra", dump(r));
    r = reason(m.decode_entry({ id: 1, enabled: null }), ["enabled"], "nil_not_allowed");
    check(r.value === null, dump(r));
    r = reason(m.decode_shape({ kind: "triangle" }), [], "no_variant");
    check(same(r.names, ["circle", "square", "empty"]), dump(r.names));
    r = reason(m.decode_shape({ kind: "circle", r: 1.5 }), ["r"], "not_integer");
    check(r.value === 1.5, dump(r));
    r = reason(m.decode_shape({ kind: "circle" }), [], "missing_key");
    check(r.key === "r", dump(r));
    const empty = decoded(m.decode_shape(null));
    check(same(empty.value, T("empty")), dump(empty.value));

    const odds = [true, false, null, undefined, 0, 1, -1, 1.5, 1000001, "", "x", 1n, -1n, [], [1, 2], {}, { a: 1 }, function () {}, Symbol("s"), new Map([["id", 1]]), Object.create(null), yes];
    for (const term of odds) {
      for (const fun of ["decode_bool", "decode_entry", "decode_shape", "decode_outcome"]) {
        let result;
        try { result = m[fun](term); }
        catch (e) { throw new Error(fun + " threw on " + dump(term) + ": " + e.message); }
        if (Object.hasOwn(result, "ok")) {
          check(result.ok && Object.hasOwn(result.ok, "value") && Object.hasOwn(result.ok, "table"), dump(result));
        } else {
          failed(result);
        }
      }
      for (const fun of ["encode_bool", "encode_entry", "encode_shape", "encode_outcome"]) {
        let result;
        try { result = m[fun](term, m.muro_repr_table_new()); }
        catch (e) { throw new Error(fun + " threw on " + dump(term) + ": " + e.message); }
        check(Object.hasOwn(result, "ok") || result.error, dump(result));
      }
    }
    const bit = decoded(m.decode_bool(true)).value;
    r = reason(m.encode_bool(bit), [], "bad_table");
    check(r.message === "encode_bool table must be %{by_name: %{}, by_index: %{}}", r.message);
    r = reason(m.decode_bool(true, null), [], "bad_table");
    check(r.message === "decode_bool table must be %{by_name: %{}, by_index: %{}}", r.message);
    """)
  end

  @tag skip: @node_skip
  test "round trip over the vocabulary, including open, optional, and nullable" do
    dir = tmp()
    emit_src!(dir, "vocab", vocab_src())

    node!(dir, """
    import * as m from "./vocab.mjs";
    #{@harness}
    const yes = m.muro_repr_atom("yes");
    const ok = m.muro_repr_atom("ok");
    const empty = m.muro_repr_table_new();
    check(Object.getPrototypeOf(empty.by_name) === null, "by_name");
    check(Object.getPrototypeOf(empty.by_index) === null, "by_index");
    check(names(empty).join() === "", "empty names");

    const known = m.muro_repr_table_new(["b", "a"]);
    check(known.by_name.b === 0 && known.by_name.a === 1, dump(known.by_name));
    check(known.by_index["0"] === "b" && known.by_index["1"] === "a", dump(known.by_index));
    check(same(names(known), ["b", "a"]), dump(names(known)));

    function throws(fn, message) {
      try { fn(); throw new Error("did not throw, want " + message); }
      catch (e) {
        if (e.message !== message) throw new Error(dump(e.message) + " want " + dump(message));
      }
    }
    throws(() => m.muro_repr_table_new(yes), 'muro_repr_table_new expects a list of binaries, got: {"atom":"yes"}');
    throws(() => m.muro_repr_table_new(["a", "a"]), 'muro_repr_table_new duplicate name "a"');
    throws(() => m.muro_repr_table_new([1]), "muro_repr_table_new expects a binary, got: 1");
    throws(() => m.muro_repr_table_names({}), "muro_repr_table_names table must be %{by_name: %{}, by_index: %{}}");

    for (const bad of [{}, { by_name: {} }, { by_name: [], by_index: {} }, { by_name: {}, by_index: {}, extra: 1 }, null, [], new Map()]) {
      let r = reason(m.decode_bool(true, bad), [], "bad_table");
      check(r.message === "decode_bool table must be %{by_name: %{}, by_index: %{}}", r.message);
      r = reason(m.encode_nat(0n, bad), [], "bad_table");
      check(r.message === "encode_nat table must be %{by_name: %{}, by_index: %{}}", r.message);
    }

    const bit = decoded(m.decode_bool(true));
    check(bit.table !== undefined && names(bit.table).length === 0, "bool table");
    check(same(bit.value, T("true")), dump(bit.value));
    check(took(m.encode_bool(bit.value, empty)) === true, "encode true");
    const off = decoded(m.decode_bool(false, empty));
    check(off.table === empty, "bool reuses table");
    check(took(m.encode_bool(off.value, empty)) === false, "encode false");

    for (const n of [0, 1, 1000, 1000000]) {
      const d = decoded(m.decode_nat(n, known));
      check(d.table === known, "nat reuses table " + n);
      check(d.value === BigInt(n), dump(d.value));
      check(took(m.encode_nat(d.value, known)) === n, "encode " + n);
      const fromBig = decoded(m.decode_nat(BigInt(n)));
      check(fromBig.value === BigInt(n), "bigint host");
    }
    reason(m.decode_nat(1000001), [], "nat_too_large");
    reason(m.decode_nat(-1), [], "negative_integer");
    reason(m.decode_nat(-1n), [], "negative_integer");
    reason(m.decode_nat(1.5), [], "not_integer");
    reason(m.decode_nat("1"), [], "not_integer");
    reason(m.decode_nat(null), [], "not_integer");
    reason(m.encode_nat(-1n, empty), [], "bad_value");

    reason(m.decode_bag(yes), [], "not_list");
    reason(m.decode_bag([1, "a"]), [1], "not_integer");
    reason(m.decode_pair(yes), [], "not_tuple");
    reason(m.decode_pair([3]), [], "wrong_tuple_size");
    reason(m.decode_pair([0, 1]), [1], "not_boolean");
    const flag = reason(m.decode_flag(1), [], "expected");
    check(flag.literal.atom === "yes" && flag.value === 1, dump(flag));
    const marked = reason(m.decode_marked([m.muro_repr_atom("no"), 1]), [0], "expected");
    check(marked.literal.atom === "ok" && marked.value.atom === "no", dump(marked));
    reason(m.decode_row(1), [], "not_map");
    reason(m.decode_row({}), [], "missing_key");
    const extra = reason(m.decode_row({ id: 1, note: null, b: 1, a: 2 }), [], "unexpected_key");
    check(extra.key === "a", dump(extra));
    reason(m.decode_row({ id: 1, flag: null, note: null }), ["flag"], "nil_not_allowed");
    reason(m.decode_nested({ in: {} }), ["in"], "missing_key");
    reason(m.decode_box({ xs: [0, "a"] }), ["xs", 1], "not_integer");
    reason(m.decode_tree([1.5, null, null]), [0], "not_integer");
    const treeErr = reason(m.decode_tree([1, null]), [], "no_variant");
    check(same(treeErr.names, ["leaf", "node"]), dump(treeErr.names));

    check(same(decoded(m.decode_tree(null)).value, T("leaf")), "leaf");
    check(took(m.encode_tree(T("leaf"), empty)) === null, "encode leaf");
    check(same(decoded(m.decode_tags(yes)).value, T("yes")), "yes");
    check(same(took(m.encode_tags(T("yes"), empty)), yes), "encode yes");
    check(same(decoded(m.decode_tags("no")).value, T("no")), "no");
    check(took(m.encode_tags(T("no"), empty)) === "no", "encode no");

    const opened = decoded(m.decode_open({ id: 4, z: 9 }));
    check(same(opened.value, T("open", 4n)), dump(opened.value));
    check(same(took(m.encode_open(opened.value, empty)), { id: 4 }), "encode open");

    const softMissing = decoded(m.decode_soft({}));
    const softNil = decoded(m.decode_soft({ flag: null }));
    check(same(softMissing.value, softNil.value), "nil normalises to missing");
    check(same(softMissing.value, T("soft", T("nothing"))), dump(softMissing.value));
    check(same(took(m.encode_soft(softMissing.value, empty)), {}), "encode missing soft");
    const softOn = decoded(m.decode_soft({ flag: true }));
    check(same(softOn.value, T("soft", T("just", T("true")))), dump(softOn.value));
    check(same(took(m.encode_soft(softOn.value, empty)), { flag: true }), "encode soft");

    const row = decoded(m.decode_row({ id: 2, note: null }));
    check(same(row.value, T("row", 2n, T("nothing"), T("nothing"))), dump(row.value));
    check(same(took(m.encode_row(row.value, empty)), { id: 2, note: null }), "nullable nil stays a key");
    const pair = decoded(m.decode_pair([3, true]));
    check(same(pair.value, T("pair", 3n, T("true"))), dump(pair.value));
    check(same(took(m.encode_pair(pair.value, empty)), [3, true]), "encode pair");
    const noted = decoded(m.decode_row({ id: 2, flag: false, note: 5 }));
    check(same(noted.value, T("row", 2n, T("just", T("false")), T("just", 5n))), dump(noted.value));
    const notedWire = took(m.encode_row(noted.value, empty));
    check(same(notedWire, { id: 2, flag: false, note: 5 }), dump(notedWire));

    const host = [];
    for (let i = 0; i < 100000; i++) host.push(0);
    const bag = decoded(m.decode_bag(host));
    const back = took(m.encode_bag(bag.value, bag.table));
    check(back.length === 100000 && back[0] === 0 && back[99999] === 0, "100000 list");

    let seed = 1;
    function rnd(n) { seed = (1664525 * seed + 1013904223) >>> 0; return seed % n; }
    function tree(d) {
      if (d === 0 || rnd(3) === 0) return null;
      return [rnd(5), tree(d - 1), tree(d - 1)];
    }
    for (let i = 0; i < 40; i++) {
      const n = rnd(21);
      const nat = decoded(m.decode_nat(n));
      check(took(m.encode_nat(nat.value, nat.table)) === n, "nat loop");
      const hostTree = tree(3);
      const got = decoded(m.decode_tree(hostTree));
      check(same(took(m.encode_tree(got.value, got.table)), hostTree), "tree " + dump(hostTree));
      const shape = rnd(3) === 0 ? null : rnd(2) === 0 ? { kind: "circle", r: rnd(6) } : { kind: "square", side: rnd(6) };
      const gs = decoded(m.decode_shape(shape));
      check(same(took(m.encode_shape(gs.value, gs.table)), shape), "shape " + dump(shape));
      const id = rnd(6);
      check(same(took(m.encode_open(decoded(m.decode_open({ id })).value, empty)), { id }), "open loop");
    }
    """)
  end

  @tag skip: @node_skip
  test "an open map refuses a key that names a declared key in the other form" do
    dir = tmp()
    {source, _} = emit_src!(dir, "ambig", ambig_src())
    assert source =~ "function muro_repr_ambiguous("
    assert source =~ "function muro_repr_no_extra("
    assert source =~ "muro_repr_ambiguous(value, path, [\"read\", \"write\", \"admin\"])"
    assert source =~ "muro_repr_ambiguous(value, path, ["
    refute source =~ "muro_repr_else(step.error && step.error.reason.k === \"ambiguous_key\""

    node!(dir, """
    import * as m from "./ambig.mjs";
    #{@harness}
    const read = m.muro_repr_atom("read");
    const write = m.muro_repr_atom("write");
    const admin = m.muro_repr_atom("admin");
    const source = m.muro_repr_atom("source");
    const preset = m.muro_repr_atom("preset");
    const kind = m.muro_repr_atom("kind");
    const yes = m.muro_repr_atom("yes");
    const parent = m.muro_repr_atom("parent");
    function M(pairs) { return new Map(pairs); }

    let r = reason(m.decode_grant(M([["relation", "x"], [read, false]])), [], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    let g = decoded(m.decode_grant(M([["relation", "x"], [source, preset]])));
    check(same(g.value, T("grant", T("nothing"))), dump(g.value));
    check(same(took(m.encode_grant(g.value, g.table)), {}), "encode ignored");
    g = decoded(m.decode_grant({ relation: "x", token_id: 7 }));
    check(same(g.value, T("grant", T("nothing"))), "unknown string");
    r = reason(m.decode_grant(M([["relation", "x"], ["read", false], [read, true]])), [], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    r = reason(m.decode_grant(M([["read", 1], [read, false]])), [], "ambiguous_key");
    check(r.key.atom === "read", "bad field still ambiguous");
    g = decoded(m.decode_grant(M([["read", false], ["token_id", 7], [source, preset], [1, 2]])));
    check(same(g.value, T("grant", T("just", T("false")))), dump(g.value));
    check(same(took(m.encode_grant(g.value, g.table)), { read: false }), dump(took(m.encode_grant(g.value, g.table))));

    r = reason(m.decode_atom_grant(M([["relation", "x"], ["read", false]])), [], "ambiguous_key");
    check(r.key === "read", dump(r));
    r = reason(m.decode_atom_grant(M([[read, false], ["read", true], ["relation", "x"]])), [], "ambiguous_key");
    check(r.key === "read", dump(r));
    g = decoded(m.decode_atom_grant(M([[read, false], ["token_id", 7], [source, preset]])));
    check(same(g.value, T("atom_grant", T("just", T("false")))), dump(g.value));
    const atomWire = took(m.encode_atom_grant(g.value, g.table));
    check(atomWire instanceof Map && atomWire.size === 1, "atom key stays a Map " + dump(atomWire));
    check(mapGet(atomWire, read).value === false, dump(atomWire));

    const both = decoded(m.decode_both(M([["read", true], [read, false], ["token_id", 7]])));
    check(same(both.value, T("both", T("true"), T("false"))), dump(both.value));
    const bothWire = took(m.encode_both(both.value, both.table));
    check(bothWire instanceof Map && bothWire.get("read") === true && mapGet(bothWire, read).value === false, dump(bothWire));

    g = decoded(m.decode_tag(M([["kind", "circle"], ["ok", true], ["token_id", 7], [source, preset]])));
    check(same(g.value, T("tag", T("true"))), dump(g.value));
    r = reason(m.decode_tag(M([["kind", "circle"], ["ok", true], [kind, "circle"]])), [], "ambiguous_key");
    check(r.key.atom === "kind", dump(r));
    r = reason(m.decode_tag(M([[kind, "circle"]])), [], "ambiguous_key");
    check(r.key.atom === "kind", dump(r));
    r = reason(m.decode_tag({ kind: "square", ok: true }), ["kind"], "expected");
    check(r.literal === "circle" && r.value === "square", dump(r));

    g = decoded(m.decode_atom_tag(M([[kind, yes], [m.muro_repr_atom("ok"), true], ["token_id", 7]])));
    check(same(g.value, T("atom_tag", T("true"))), dump(g.value));
    r = reason(m.decode_atom_tag(M([[kind, yes], [m.muro_repr_atom("ok"), true], ["kind", "x"]])), [], "ambiguous_key");
    check(r.key === "kind", dump(r));
    r = reason(m.decode_atom_tag(M([["kind", yes]])), [], "ambiguous_key");
    check(r.key === "kind", dump(r));

    r = reason(m.decode_hold([M([[read, false]])]), [0], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    g = decoded(m.decode_hold([1]));
    check(same(g.value, T("hold", T("node_none"))), dump(g.value));
    r = reason(m.decode_hold([{ read: 1 }]), [0, "read"], "not_boolean");
    check(r.value === 1, dump(r));

    const strings = [];
    for (let i = 0; i <= 40; i++) strings.push(["p" + i, 0]);
    const atoms = "abcdefghijklmnopqrstuvwxyz".split("").map((ch) => [m.muro_repr_atom("a" + ch), 0]);
    function padded(collisions, order) {
      const pairs = order === "strings" ? strings.concat(atoms, collisions)
        : order === "first" ? collisions.concat(strings, atoms)
        : order === "rev" ? atoms.slice().reverse().concat(strings.slice().reverse(), collisions.slice().reverse())
        : strings.concat(collisions, atoms);
      return M(pairs);
    }
    const collisions = [[admin, false], [write, false], [read, false]];
    for (const order of ["strings", "first", "rev", "middle"]) {
      r = reason(m.decode_many(padded(collisions, order)), [], "ambiguous_key");
      check(r.key.atom === "read", order + " " + dump(r));
    }
    r = reason(m.decode_many(padded([[admin, true], [write, false]], "strings")), [], "ambiguous_key");
    check(r.key.atom === "write", dump(r));
    r = reason(m.decode_many(padded([[admin, true], [write, false]], "rev")), [], "ambiguous_key");
    check(r.key.atom === "write", dump(r));
    r = reason(m.decode_atom_many(padded([["read", false], ["write", true]], "first")), [], "ambiguous_key");
    check(r.key === "write", dump(r));
    r = reason(m.decode_atom_many(padded([["read", false]], "middle")), [], "ambiguous_key");
    check(r.key === "read", dump(r));
    g = decoded(m.decode_many({ write: false }));
    check(same(g.value, T("many", T("nothing"), T("just", T("false")), T("nothing"))), dump(g.value));

    const inner = padded([[read, false]], "middle");
    r = reason(m.decode_parent(M([["child", inner], ["token_id", 7]])), ["child"], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    r = reason(m.decode_grand({ parent: { child: M([["relation", "x"], [read, false]]) } }), ["parent", "child"], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    r = reason(m.decode_grand(M([[parent, 1], ["parent", { child: M([[read, false]]) }]])), [], "ambiguous_key");
    check(r.key.atom === "parent", dump(r));
    r = reason(m.decode_kids([{ read: false }, M([[read, true], ["token_id", 7]])]), [1], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    r = reason(m.decode_kids([M([[read, false]]), { read: true }]), [0], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    g = decoded(m.decode_kids([M([["read", false], [source, preset]])]));
    check(same(g.value, T("kids", T("cons", T("child", T("just", T("false"))), T("nil")))), dump(g.value));

    r = reason(m.decode_closed(M([["read", false], [read, true], ["relation", "x"]])), [], "unexpected_key");
    check(r.key.atom === "read", dump(r));
    r = reason(m.decode_closed(M([["read", 1], [read, false]])), ["read"], "not_boolean");
    check(r.value === 1, dump(r));
    r = reason(m.decode_closed({ read: true, relation: "x" }), [], "unexpected_key");
    check(r.key === "relation", dump(r));
    g = decoded(m.decode_closed({ read: true }));
    check(same(took(m.encode_closed(g.value, g.table)), { read: true }), "closed encode");
    r = reason(m.decode_bag(M([[0, true], [read, false]])), [{ k: "key", key: { atom: "read" } }], "not_integer");
    check(r.value.atom === "read", dump(r));
    r = reason(m.decode_bag(M([[0, true], ["read", false]])), [{ k: "key", key: "read" }], "not_integer");
    check(r.value === "read", dump(r));
    g = decoded(m.decode_bag(M([[0, true]])));
    check(same(g.value, T("bag", T("cons", [0n, T("true")], T("nil")))), dump(g.value));
    const bagWire = took(m.encode_bag(g.value, g.table));
    check(bagWire instanceof Map && bagWire.get(0) === true && bagWire.size === 1, dump(bagWire));
    """)
  end

  test "only the maps that need them emit the extra-key helpers" do
    dir = tmp()
    {open, _} = emit_src!(dir, "open_only", open_only_src())
    assert open =~ "function muro_repr_ambiguous("
    refute open =~ "muro_repr_no_extra"
    {closed, _} = emit_src!(dir, "closed_only", closed_only_src())
    assert closed =~ "function muro_repr_no_extra("
    refute closed =~ "muro_repr_ambiguous"
    refute closed =~ "ambiguous_key"
    {bools, types} = emit_src!(dir, "bool_only", bool_only_src())
    assert bools =~ "export function muro_repr_table_new("
    assert bools =~ "export function muro_repr_table_names("
    refute bools =~ "muro_repr_nat_max"
    refute bools =~ "muro_repr_decode_nat"
    refute bools =~ "muro_repr_else"
    refute bools =~ "muro_repr_map_of"
    refute bools =~ "muro_repr_decode_interned"
    refute bools =~ "muro_repr_borrow_begin"
    refute bools =~ "muro_repr_string_ok"
    refute bools =~ "muro_repr_bin_from"
    refute bools =~ "muro_repr_atom("
    refute types =~ "muro_repr_atom"
  end

  @tag skip: @node_skip
  test "interned names, else, map_of, and the nat guard" do
    dir = tmp()
    emit_src!(dir, "wide", wide_src())
    emit_src!(dir, "named", named_src())
    emit_src!(dir, "kept", named_src() <> box_src())
    {limited, _} = emit_src!(dir, "limit", limit_src())
    assert limited =~ "const muro_repr_nat_max = 1_000_000;"

    File.write!(
      Path.join(dir, "limit.mjs"),
      String.replace(
        limited,
        "const muro_repr_nat_max = 1_000_000;",
        "const muro_repr_nat_max = 2;",
        global: false
      )
    )

    node!(dir, """
    import * as wide from "./wide.mjs";
    import * as named from "./named.mjs";
    import * as kept from "./kept.mjs";
    import * as limit from "./limit.mjs";
    const m = wide;
    #{@harness}
    const empty = m.muro_repr_table_new();
    const yes = m.muro_repr_atom("yes");
    let g = decoded(m.decode_key("*"));
    check(same(g.value, T("wild")) && names(g.table).length === 0, dump(g.value));
    const presetAuth = m.muro_repr_table_new(["auth"]);
    g = decoded(m.decode_key("*", presetAuth));
    check(g.table === presetAuth && same(g.value, T("wild")), "wild keeps preset");
    g = decoded(m.decode_key("auth"));
    check(same(g.value, T("named", 0n)), dump(g.value));
    check(same(names(g.table), ["auth"]), dump(names(g.table)));
    check(took(m.encode_key(g.value, g.table)) === "auth", "encode named");
    check(took(m.encode_key(T("wild"), empty)) === "*", "encode wild");
    const again = decoded(m.decode_key("*", g.table));
    check(again.table === g.table, "existing table reused");
    const variant = reason(m.decode_key(1), [], "no_variant");
    check(same(variant.names, ["named", "wild"]), dump(variant.names));
    reason(m.decode_wrap(null), [], "not_string");
    reason(m.decode_wrap(1), [], "not_string");
    g = decoded(m.decode_wrap(""));
    check(same(names(g.table), [""]), "empty name");
    check(took(m.encode_wrap(g.value, g.table)) === "", "encode empty");
    g = decoded(m.decode_wrap("__proto__"));
    check(same(names(g.table), ["__proto__"]), dump(names(g.table)));
    check(took(m.encode_wrap(g.value, g.table)) === "__proto__", "encode proto");
    const blank = m.muro_repr_table_new();
    let r = reason(m.encode_wrap(T("wrap", 1n), blank), [], "no_name");
    check(r.index === 1 && r.message === "encode_wrap: no name for index 1", dump(r));
    const reserved = m.muro_repr_table_new(["*"]);
    r = reason(m.encode_key(T("named", 0n), reserved), [], "reserved_name");
    check(r.name === "*" && r.message === 'encode_key: name "*" is reserved by a sibling constructor', dump(r));

    const labels = [];
    for (let i = 0; i <= 20; i++) labels.push("n" + i);
    g = decoded(m.decode_names(labels));
    check(same(names(g.table), labels), "21 names");
    check(took(m.encode_names(g.value, g.table)).join() === labels.join(), "encode names");
    g = decoded(m.decode_codes(labels));
    check(same(g.value.fields[0].fields[0], T("z")), "0 is z");
    check(same(g.value.fields[0].fields[1].fields[0], T("d1", T("z"))), "1 is d1 z");
    function nth(list, i) {
      let cur = list;
      for (let k = 0; k < i; k++) cur = cur.fields[1];
      return cur.fields[0];
    }
    check(same(nth(g.value.fields[0], 2), T("d2", T("z"))), dump(nth(g.value.fields[0], 2)));
    check(same(nth(g.value.fields[0], 4), T("d2", T("d1", T("z")))), dump(nth(g.value.fields[0], 4)));
    check(same(took(m.encode_codes(g.value, g.table)), labels), "encode codes");
    const preset = m.muro_repr_table_new(["a", "b", "c", "d", "e"]);
    g = decoded(m.decode_token("e", preset));
    check(g.table === preset, "preset identity");
    check(same(g.value, T("token", T("d2", T("d1", T("z"))))), dump(g.value));
    check(took(m.encode_token(g.value, preset)) === "e", "encode token");

    const start = m.muro_repr_table_new();
    g = decoded(m.decode_names(["b", "a", "b"], start));
    check(g.table !== start && names(start).length === 0, "caller table is not mutated");
    check(same(names(g.table), ["b", "a"]), dump(names(g.table)));
    const seeded = m.muro_repr_table_new(["a"]);
    g = decoded(m.decode_names(["b", "a"], seeded));
    check(same(names(g.table), ["a", "b"]), dump(names(g.table)));
    g = decoded(m.decode_twin(["b", "a"]));
    check(same(g.value, T("twin", 0n, 1n)), dump(g.value));
    check(same(names(g.table), ["b", "a"]), dump(names(g.table)));
    check(same(took(m.encode_twin(g.value, g.table)), ["b", "a"]), "encode twin");
    const rec1 = decoded(m.decode_rec({ a: "second", z: "first" }));
    const rec2 = decoded(m.decode_rec({ z: "first", a: "second" }));
    check(same(rec1.value, T("rec", 0n, 1n)) && same(rec1.value, rec2.value), dump(rec1.value));
    check(same(names(rec1.table), ["first", "second"]) && same(names(rec1.table), names(rec2.table)), dump(names(rec1.table)));
    g = decoded(m.decode_link({ b: "a" }));
    check(same(names(g.table), ["b", "a"]), dump(names(g.table)));

    const lim = decoded(limit.decode_names(["a", "b", "c"]));
    check(same(names(lim.table), ["a", "b", "c"]), dump(names(lim.table)));
    r = reason(limit.decode_names(["a", "b", "c", "d"]), [3], "too_many_names");
    check(r.max === 2, dump(r));

    reason(m.decode_bag(yes), [], "not_map");
    reason(m.decode_bag(null), [], "not_map");
    g = decoded(m.decode_bag(new Map()));
    check(same(g.value, T("bag", T("nil"))), dump(g.value));
    check(same(took(m.encode_bag(g.value, empty)), {}), "empty map is an object");
    r = reason(m.decode_bag(new Map([[1.5, true]])), [{ k: "key", key: 1.5 }], "not_integer");
    check(r.value === 1.5, dump(r));
    r = reason(m.decode_bag(new Map([[1, "x"]])), [1], "not_boolean");
    check(r.value === "x", dump(r));
    g = decoded(m.decode_rows(new Map([[0, true]])));
    check(same(g.value, T("rows", T("cons", T("item", 0n, T("true")), T("nil")))), dump(g.value));
    const rowsWire = took(m.encode_rows(g.value, empty));
    check(rowsWire instanceof Map && rowsWire.get(0) === true, dump(rowsWire));
    g = decoded(m.decode_bag(new Map([[1, true], [0, false]])));
    check(same(g.value, T("bag", T("cons", [0n, T("false")], T("cons", [1n, T("true")], T("nil"))))), dump(g.value));

    const keys = [];
    for (let i = 0; i <= 40; i++) keys.push(i);
    const hostA = new Map(keys.map((k) => [k, k % 2 === 0]));
    const hostB = new Map(keys.slice().reverse().map((k) => [k, k % 2 === 0]));
    const sortedA = decoded(m.decode_bag(hostA));
    const sortedB = decoded(m.decode_bag(hostB));
    check(same(sortedA.value, sortedB.value), "integer key order");
    const natLabels = [];
    for (let i = 1; i <= 40; i++) natLabels.push("k" + i);
    const natA = {};
    const natB = {};
    for (const k of natLabels) natA[k] = true;
    for (const k of natLabels.slice().reverse()) natB[k] = true;
    const na = decoded(m.decode_nat_map(natA));
    const nb = decoded(m.decode_nat_map(natB));
    check(same(na.value, nb.value), "string key order");
    check(same(names(na.table), natLabels.slice().sort()), dump(names(na.table)));
    check(same(took(m.encode_nat_map(na.value, na.table)), natA), "encode nat map");

    g = decoded(m.decode_collide(new Map([[1, false], [1.5, true]])));
    check(same(g.value, T("collide", T("cons", [1n, T("false")], T("cons", [0n, T("true")], T("nil"))))), dump(g.value));
    r = reason(m.decode_collide(new Map([[0, true], ["x", false]])), [], "keys_collide");
    check(r.a === 0 && r.b === "x", dump(r));
    r = reason(m.decode_collide(new Map([[1, false], [1n, true]])), [], "keys_collide");
    check(r.a === 1 && r.b === 1n, dump(r));
    const dup = T("bag", T("cons", [0n, T("true")], T("cons", [0n, T("false")], T("nil"))));
    r = reason(m.encode_bag(dup, empty), [], "duplicate_key");
    check(r.message === "encode_bag: duplicate map key 0", dump(r));
    const unsorted = T("bag", T("cons", [2n, T("true")], T("cons", [0n, T("false")], T("nil"))));
    const encoded = took(m.encode_bag(unsorted, empty));
    check(encoded instanceof Map && encoded.get(2) === true && encoded.get(0) === false, dump(encoded));
    const ordered = decoded(m.decode_bag(encoded));
    check(!same(ordered.value, unsorted), "encode sorts");
    check(same(decoded(m.decode_bag(took(m.encode_bag(ordered.value, empty)), empty)).value, ordered.value), "ordered round trip");

    g = decoded(m.decode_fall([true]));
    check(same(g.value, T("fall", T("true"))), "fall true");
    g = decoded(m.decode_fall([1]));
    check(same(g.value, T("fall", T("false"))), "fall 1");
    g = decoded(m.decode_fall([null]));
    check(same(g.value, T("fall", T("false"))), "fall null");
    g = decoded(m.decode_fall(["yes"]));
    check(same(g.value, T("fall", T("false"))), "fall string");
    g = decoded(m.decode_fall([{}]));
    check(same(g.value, T("fall", T("false"))), "fall map");
    check(same(took(m.encode_fall(T("fall", T("false")), empty)), [false]), "encode fall");
    g = decoded(m.decode_count([1]));
    check(same(g.value, T("count", 1n)), dump(g.value));
    g = decoded(m.decode_count([-1]));
    check(same(g.value, T("count", 0n)), "count fallback");
    r = reason(m.decode_count([1000001]), [0], "nat_too_large");
    check(r.value === 1000001, dump(r));
    check(same(took(m.encode_count(T("count", 0n), empty)), [0]), "encode count");

    const nm = named;
    g = decoded(nm.decode_hold([1000001]));
    check(same(g.value, T("hold", T("zero"))), dump(g.value));
    g = decoded(nm.decode_hold([-1]));
    check(same(g.value, T("hold", T("zero"))), "named negative");
    g = decoded(nm.decode_hold([2]));
    check(same(g.value, T("hold", T("count", 2n))), dump(g.value));
    check(same(took(nm.encode_hold(g.value, empty)), [2]), "encode named");
    r = reason(kept.decode_hold([1000001]), [0], "nat_too_large");
    check(r.value === 1000001, "numeral elsewhere keeps the guard");
    r = reason(kept.decode_box([1000001]), [0], "nat_too_large");
    check(r.value === 1000001, dump(r));
    g = decoded(kept.decode_box([-1]));
    check(same(g.value, T("box", 0n)), dump(g.value));
    g = decoded(kept.decode_hold([2]));
    check(same(g.value, T("hold", T("count", 2n))), "kept two");

    reason(m.decode_need({}), [], "missing_key");
    g = decoded(m.decode_need({ b: 1 }));
    check(same(g.value, T("need", T("false"))), "need 1");
    g = decoded(m.decode_need({ b: null }));
    check(same(g.value, T("need", T("false"))), "need null");
    g = decoded(m.decode_need({ b: "yes" }));
    check(same(g.value, T("need", T("false"))), "need string");
    g = decoded(m.decode_need({ b: true }));
    check(same(g.value, T("need", T("true"))), "need true");
    g = decoded(m.decode_row({}));
    check(same(g.value, T("row", T("nothing"))), "row missing");
    g = decoded(m.decode_row({ b: true }));
    check(same(g.value, T("row", T("just", T("true")))), "row true");
    g = decoded(m.decode_row({ b: null }));
    check(same(g.value, T("row", T("just", T("false")))), "row null");
    g = decoded(m.decode_row({ b: 1 }));
    check(same(g.value, T("row", T("just", T("false")))), "row 1");
    check(same(took(m.encode_row(T("row", T("just", T("false"))), empty)), { b: false }), "encode row just");
    check(same(took(m.encode_row(T("row", T("nothing")), empty)), {}), "encode row nothing");
    g = decoded(m.decode_plain({}));
    check(same(g.value, T("plain", T("nothing"))), "plain missing");
    reason(m.decode_plain({ b: null }), ["b"], "nil_not_allowed");
    reason(m.decode_plain({ b: 1 }), ["b"], "not_boolean");
    g = decoded(m.decode_soft(null));
    check(same(g.value, T("soft", T("nothing"))), "soft null");
    g = decoded(m.decode_soft(true));
    check(same(g.value, T("soft", T("just", T("true")))), "soft true");
    g = decoded(m.decode_soft(1));
    check(same(g.value, T("soft", T("just", T("false")))), "soft 1");
    g = decoded(m.decode_soft("yes"));
    check(same(g.value, T("soft", T("just", T("false")))), "soft string");
    check(took(m.encode_soft(T("soft", T("just", T("false"))), empty)) === false, "encode soft false");
    check(took(m.encode_soft(T("soft", T("nothing")), empty)) === null, "encode soft nothing");
    g = decoded(m.decode_hold([null]));
    check(same(g.value, T("hold", T("no"))), "hold nil");
    g = decoded(m.decode_hold([1]));
    check(same(g.value, T("hold", T("no"))), "hold 1");
    g = decoded(m.decode_hold([{}]));
    check(same(g.value, T("hold", T("no"))), "hold map");
    g = decoded(m.decode_hold([{ n: 1, z: 2 }]));
    check(same(g.value, T("hold", T("no"))), "hold extra");
    r = reason(m.decode_hold([{ n: "x" }]), [0, "n"], "not_integer");
    check(r.value === "x", dump(r));
    r = reason(m.decode_hold([{ n: 1000001 }]), [0, "n"], "nat_too_large");
    check(r.value === 1000001, dump(r));
    g = decoded(m.decode_hold([{ n: 2 }]));
    check(same(g.value, T("hold", T("yes", 2n))), dump(g.value));
    check(same(took(m.encode_hold(T("hold", T("no")), empty)), [null]), "encode hold no");
    check(same(took(m.encode_hold(g.value, g.table)), [{ n: 2 }]), dump(took(m.encode_hold(g.value, g.table))));

    const five = [];
    for (let i = 0; i < 500; i++) five.push("n" + i);
    g = decoded(m.decode_names(five));
    check(same(names(g.table), five), "500 names");
    check(same(took(m.encode_names(g.value, g.table)), five), "encode 500");
    const bits = {};
    const bitKeys = [];
    for (let i = 0; i < 2048; i++) {
      const k = "k" + i;
      bits[k] = true;
      bitKeys.push(k);
    }
    g = decoded(m.decode_dict(bits));
    check(same(took(m.encode_dict(g.value, g.table)), bits), "2048 map");
    check(same(names(g.table), bitKeys.slice().sort()), "2048 names sorted");
    const ints = new Map();
    for (let i = 0; i < 2000; i++) ints.set(i, i % 2 === 0);
    g = decoded(m.decode_bag(ints));
    const intsBack = took(m.encode_bag(g.value, g.table));
    check(intsBack instanceof Map && intsBack.size === 2000 && intsBack.get(0) === true && intsBack.get(1) === false, "2000 integer keys");
    """)
  end

  @tag skip: @node_skip
  test "name tables, string order, and plain maps match the Elixir codec" do
    dir = tmp()
    path = write!(dir, "probe.muro", probe_src())
    {source, _} = emit_path!(dir, "probe")
    assert source =~ "function muro_repr_string_ok("
    assert source =~ "value.isWellFormed()"
    assert source =~ "function muro_repr_str_cmp("
    assert source =~ "new WeakMap()"
    assert source =~ "muro_repr_borrow_begin()"
    refute source =~ "Object.keys(by_name).length"

    mod = Muro.JSReprReviewProbe
    {:ok, ex} = Muro.emit_file(path, mod)
    [{^mod, _bin}] = Code.compile_string(ex)

    smile = "\u{1F600}"
    tilde = "\u{FF5E}"
    assert tilde < smile

    assert {:ok, _value, table} = apply(mod, :decode_nat_map, [%{smile => true, tilde => true}])

    assert table_names(table) == [tilde, smile]
    assert table.by_name[tilde] == 0
    assert table.by_name[smile] == 1

    node!(dir, """
    import * as m from "./probe.mjs";
    #{@harness}
    const smile = "\\u{1F600}";
    const tilde = "\\u{FF5E}";
    check(smile < tilde, "javascript < is utf-16");
    const wire = {};
    wire[smile] = true;
    wire[tilde] = true;
    let g = decoded(m.decode_nat_map(wire));
    check(names(g.table)[0] === tilde && names(g.table)[1] === smile, "code point order " + dump(names(g.table)));
    check(g.table.by_name[tilde] === 0 && g.table.by_name[smile] === 1, dump(g.table.by_name));
    check(same(g.value, T("natmap", T("cons", [0n, T("true")], T("cons", [1n, T("true")], T("nil"))))), dump(g.value));
    const flipped = {};
    flipped[tilde] = true;
    flipped[smile] = true;
    const g2 = decoded(m.decode_nat_map(flipped));
    check(same(names(g2.table), names(g.table)) && same(g2.value, g.value), "insertion order does not matter");

    const preset = m.muro_repr_table_new(["a", "b"]);
    const presetNames = preset.by_name;
    const presetIndex = preset.by_index;
    g = decoded(m.decode_names(["b", "c", "d"], preset));
    check(g.table !== preset, "result table is a new object");
    check(preset.by_name === presetNames && preset.by_index === presetIndex, "preset maps stay");
    check(same(names(preset), ["a", "b"]), dump(names(preset)));
    check(same(names(g.table), ["a", "b", "c", "d"]), dump(names(g.table)));
    check(Object.keys(g.table).length === 2, "result table shape");
    const more = decoded(m.decode_names(["e"], g.table));
    check(more.table !== g.table, "a returned table is copied again");
    check(same(names(g.table), ["a", "b", "c", "d"]), "returned table stays");
    check(same(names(more.table), ["a", "b", "c", "d", "e"]), dump(names(more.table)));
    const known = decoded(m.decode_names(["a", "b"], preset));
    check(known.table === preset, "known names keep the caller's table");

    const lone = "\\uD800";
    const kept = m.muro_repr_table_new(["ok"]);
    let r = reason(m.decode_wrap(lone, kept), [], "not_string");
    check(r.value === lone, "lone surrogate value");
    check(same(names(kept), ["ok"]), "lone surrogate does not intern");
    r = reason(m.decode_wrap("a\\uD800b", kept), [], "not_string");
    check(r.value === "a\\uD800b", "embedded surrogate");
    check(same(names(kept), ["ok"]), "embedded surrogate does not intern");
    g = decoded(m.decode_wrap(smile, kept));
    check(g.table !== kept && same(names(kept), ["ok"]), "astral name leaves the preset");
    check(same(names(g.table), ["ok", smile]), dump(names(g.table)));

    const empty = m.muro_repr_table_new();
    const encoded = took(m.encode_nat(2000000n, empty));
    check(encoded === 2000000 && typeof encoded === "number", "2000000 encodes as a number");
    const max = BigInt(Number.MAX_SAFE_INTEGER);
    check(typeof took(m.encode_nat(max, empty)) === "number", "max safe integer encodes as a number");
    const over = max + 1n;
    check(took(m.encode_nat(over, empty)) === over, "above the safe integer stays a bigint");
    reason(m.decode_nat(1000001), [], "nat_too_large");

    reason(m.decode_bag(new Date(0)), [], "not_map");
    class Holder { constructor() { this.k = true; } }
    const holder = new Holder();
    r = reason(m.decode_bag(holder), [], "not_map");
    check(r.value === holder, "class instance value");
    r = reason(m.decode_nat_map(new Date(0)), [], "not_map");
    check(r.value instanceof Date, "date is not a string map");
    reason(m.decode_nat_map(holder), [], "not_map");
    g = decoded(m.decode_bag({}));
    check(same(g.value, T("bag", T("nil"))), "empty literal map");
    g = decoded(m.decode_bag(Object.create(null)));
    check(same(g.value, T("bag", T("nil"))), "empty null prototype map");
    g = decoded(m.decode_nat_map({ k: true }));
    check(same(names(g.table), ["k"]), "literal map");
    const bare = Object.create(null);
    bare.k = true;
    g = decoded(m.decode_nat_map(bare));
    check(same(names(g.table), ["k"]), "null prototype map");
    const proto = Object.create(null);
    proto["__proto__"] = true;
    g = decoded(m.decode_nat_map(proto));
    check(same(names(g.table), ["__proto__"]), "proto key on a null prototype");

    r = reason(m.decode_same(new Map([["b", true], ["a", false]])), [], "keys_collide");
    check(r.a === "a" && r.b === "b", dump(r));
    r = reason(m.decode_collide(new Map([[1, false], [1n, true]])), [], "keys_collide");
    check(r.a === 1 && r.b === 1n, dump(r));
    g = decoded(m.decode_dict({ b: true, a: false }));
    check(names(g.table)[0] === "a" && names(g.table)[1] === "b", dump(names(g.table)));
    check(same(took(m.encode_dict(g.value, g.table)), { a: false, b: true }), "binary numeral keys round trip");

    const many = [];
    for (let i = 0; i < 10000; i++) many.push("n" + i + "xxxxxxxx");
    const t0 = Date.now();
    g = decoded(m.decode_names(many));
    const nameMs = Date.now() - t0;
    check(nameMs < 5000, "10000 names took " + nameMs + "ms");
    check(names(g.table).length === 10000, "10000 name count " + names(g.table).length);
    const host = {};
    for (let i = 0; i < 10000; i++) host["k" + i + "xxxxxxxx"] = i % 2 === 0;
    const t1 = Date.now();
    g = decoded(m.decode_nat_map(host));
    const mapMs = Date.now() - t1;
    check(mapMs < 5000, "10000 map keys took " + mapMs + "ms");
    check(names(g.table).length === 10000, "10000 map count " + names(g.table).length);
    """)
  end

  @tag skip: @node_skip
  test "the names example decodes the issue wire, and an open entry keeps an ambiguous key" do
    dir = tmp()
    {source, _} = emit_example!(dir, "repr_names")
    assert source =~ "export function reads_off("
    assert source =~ "export function count_entries("
    assert source =~ "muro_repr_decode_interned"
    assert source =~ "muro_repr_map_of_decode"
    assert source =~ "muro_repr_else"
    assert source =~ "const muro_repr_nat_max = 1_000_000;"
    refute source =~ "muro_repr_bin_from"

    strict =
      File.read!("examples/repr_names.muro")
      |> String.replace(
        ~s|repr Entry := map { "relation" => Key, "read" => optional (boolean else false) }|,
        "repr Bool := boolean\nrepr Entry := map { \"relation\" => Key, \"read\" => optional Bool }"
      )

    opened =
      File.read!("examples/repr_names.muro")
      |> String.replace(
        ~s|repr Entry := map { "relation" => Key, "read" => optional (boolean else false) }|,
        ~s|repr Entry := map open { "relation" => Key, "read" => optional (boolean else false) }|
      )

    emit_src!(dir, "strict", strict)
    {open_source, _} = emit_src!(dir, "opened", opened)
    assert open_source =~ "function muro_repr_ambiguous("
    refute open_source =~ "function muro_repr_no_extra("

    node!(dir, """
    import * as m from "./repr_names.mjs";
    import * as strict from "./strict.mjs";
    import * as opened from "./opened.mjs";
    #{@harness}
    const read = m.muro_repr_atom("read");
    const source = m.muro_repr_atom("source");
    const presetAtom = m.muro_repr_atom("preset");
    const empty = m.muro_repr_table_new();
    const wire = { "*": [{ relation: "*", read: true }], auth: [{ relation: "token", read: false }] };
    const wild = T("wild");
    const named = (n) => T("named", n);
    const just = (b) => T("just", b);
    const nothing = T("nothing");
    const nil = T("nil");
    const cons = (a, b) => T("cons", a, b);
    const entry = (k, bit) => T("entry", k, bit);
    const binding = (k, es) => T("binding", k, es);
    const template = (bs) => T("template", bs);
    const True = T("true");
    const False = T("false");
    const expected = template(cons(
      binding(wild, cons(entry(wild, just(True)), nil)),
      cons(binding(named(0n), cons(entry(named(1n), just(False)), nil)), nil)
    ));
    const got = decoded(m.decode_template(wire));
    check(same(got.value, expected), dump(got.value));
    check(same(names(got.table), ["auth", "token"]), dump(names(got.table)));
    check(got.table.by_name.auth === 0 && got.table.by_name.token === 1, dump(got.table.by_name));
    check(got.table.by_index["0"] === "auth" && got.table.by_index["1"] === "token", dump(got.table.by_index));
    const off = template(cons(
      binding(wild, cons(entry(wild, just(False)), nil)),
      cons(binding(named(0n), cons(entry(named(1n), just(False)), nil)), nil)
    ));
    check(same(m.reads_off(expected), off), dump(m.reads_off(expected)));
    check(m.count_entries(expected) === 2n, dump(m.count_entries(expected)));
    const offWire = took(m.encode_template(off, got.table));
    check(Object.getPrototypeOf(offWire) === null, "template object");
    check(same(offWire, { "*": [{ relation: "*", read: false }], auth: [{ relation: "token", read: false }] }), dump(offWire));
    check(same(took(m.encode_template(expected, got.table)), wire), "encode expected");
    const round = decoded(m.decode_template(took(m.encode_template(expected, got.table)), got.table));
    check(round.table === got.table && same(round.value, expected), "round trip keeps the table");
    const preset = m.muro_repr_table_new(["token", "auth"]);
    const presetTerm = template(cons(
      binding(wild, cons(entry(wild, just(True)), nil)),
      cons(binding(named(1n), cons(entry(named(0n), just(False)), nil)), nil)
    ));
    const presetDec = decoded(m.decode_template(wire, preset));
    check(presetDec.table === preset && same(presetDec.value, presetTerm), dump(presetDec.value));
    check(same(took(m.encode_template(presetTerm, preset)), wire), "encode preset");
    for (const bad of [1, null, "yes"]) {
      const flagged = decoded(m.decode_template({ "*": [{ relation: "*", read: bad }] }));
      check(same(flagged.value, template(cons(binding(wild, cons(entry(wild, just(False)), nil)), nil))), dump(bad));
      check(names(flagged.table).length === 0, "fallback does not intern");
    }
    const missing = decoded(m.decode_template({ "*": [{ relation: "*" }] }));
    check(same(missing.value, template(cons(binding(wild, cons(entry(wild, nothing), nil)), nil))), "missing read");
    const strictErr = reason(strict.decode_template({ "*": [{ relation: "*", read: 1 }] }), ["*", 0, "read"], "not_boolean");
    check(strictErr.value === 1, dump(strictErr));

    const one = decoded(opened.decode_entry({ relation: "*", read: true }));
    check(same(one.value, entry(wild, just(True))) && names(one.table).length === 0, dump(one.value));
    for (const bad of [1, null, "yes", {}]) {
      const fell = decoded(opened.decode_entry({ relation: "*", read: bad }));
      check(same(fell.value, entry(wild, just(False))), dump(bad) + " " + dump(fell.value));
    }
    check(same(decoded(opened.decode_entry({ relation: "*" })).value, entry(wild, nothing)), "open missing");
    let r = reason(opened.decode_entry(new Map([["relation", "*"], [read, false]])), [], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    r = reason(opened.decode_entry(new Map([["relation", "*"], ["read", true], [read, false]])), [], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    const ignored = decoded(opened.decode_entry(new Map([["relation", "*"], ["read", 1], [source, presetAtom]])));
    check(same(ignored.value, entry(wild, just(False))), dump(ignored.value));
    r = reason(opened.decode_template({ "*": [new Map([["relation", "*"], [read, false]])] }), ["*", 0], "ambiguous_key");
    check(r.key.atom === "read", dump(r));
    """)
  end

  test "a repr payload session stays omitted, and the runs and the codecs are written" do
    dir = tmp()

    {source, types} =
      emit_src!(dir, "mixed", """
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
      """)

    assert source =~ "export function kept("
    assert source =~ "export const ping ="
    refute source =~ "export const give ="
    refute source =~ "export const num ="
    assert source =~ "export function decode_nat("
    assert source =~ "export function encode_nat("
    assert source =~ "export function decode_box("
    assert source =~ "export function encode_box("
    refute source =~ "export function decode_bool("
    assert types =~ "export const ping: SessionStepper;"
    refute types =~ "give: SessionStepper"
    refute types =~ "num: SessionStepper"

    assert types =~
             "export function decode_box(value: unknown, table?: ReprTable): ReprDecode<Box>;"

    assert types =~
             "export function decode_nat(value: unknown, table?: ReprTable): ReprDecode<Nat>;"

    kept_at = source |> String.split("export function kept(", parts: 2) |> hd() |> byte_size()
    ping_at = source |> String.split("export const ping =", parts: 2) |> hd() |> byte_size()
    codec_at = source |> String.split("export function decode_", parts: 2) |> hd() |> byte_size()
    assert kept_at < ping_at
    assert ping_at < codec_at
  end

  test "a session export that spells a codec name is refused" do
    dir = tmp()

    path =
      write!(dir, "hit.muro", """
      data Bool : Type where
        true : Bool
        false : Bool
      repr Nat := integer
      session decode_nat := recv Bool end
      def kept : run Nat := 0
      """)

    assert {:ok, book} = Muro.Load.file(path)
    book = Prelude.for_emit(book)

    assert {:error, msg} = Emit.JS.render(book, "hit", path: path)
    assert msg =~ "repr Nat: decode_nat collides with an existing JavaScript name"
  end

  test "a repr that does not check is an error from the JavaScript render" do
    assert {:ok, book} =
             Parser.parse("""
             def kept : run Nat := 0
             repr Missing := integer
             """)

    assert {:error, msg} = Emit.JS.render(book, "bad", path: "bad.muro")
    assert msg =~ "Missing"
  end

  defp emit_example!(dir, name) do
    File.cp!(Path.join("examples", name <> ".muro"), Path.join(dir, name <> ".muro"))
    emit_path!(dir, name)
  end

  defp emit_src!(dir, name, src) do
    write!(dir, name <> ".muro", src)
    emit_path!(dir, name)
  end

  defp emit_path!(dir, name) do
    assert {:ok, [mjs, dts]} = Muro.emit_js(Path.join(dir, name <> ".muro"))
    {File.read!(mjs), File.read!(dts)}
  end

  defp load_example!(path) do
    assert {:ok, book} = Muro.Load.file(path)
    Prelude.for_emit(book)
  end

  defp node!(dir, script) do
    path = Path.join(dir, "_drv.mjs")
    File.write!(path, script)

    {out, status} =
      System.cmd(@node, [path],
        cd: dir,
        stderr_to_stdout: true,
        env: [{"NO_COLOR", nil}, {"FORCE_COLOR", nil}]
      )

    assert status == 0, out
    out
  end

  defp write!(dir, name, src) do
    path = Path.join(dir, name)
    File.write!(path, src)
    path
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_js_repr_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp bool_only_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    repr Bool := boolean
    """
  end

  defp open_only_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    data Grant : Type where
      grant : Bool → Grant
    repr Bool := boolean
    repr Grant := map open { "read" => Bool }
    """
  end

  defp closed_only_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    data Grant : Type where
      grant : Bool → Grant
    repr Bool := boolean
    repr Grant := map { "read" => Bool }
    """
  end

  defp vocab_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    data Bag : Type where
      bag : List Nat → Bag
    data Pair : Type where
      pair : Nat → Bool → Pair
    data Row : Type where
      row : Nat → Maybe Bool → Maybe Nat → Row
    data Open : Type where
      open : Nat → Open
    data Tree : Type where
      leaf : Tree
      node : Nat → Tree → Tree → Tree
    data Shape : Type where
      circle : Nat → Shape
      square : Nat → Shape
      empty : Shape
    data Flag : Type where
      flag : Flag
    data Tags : Type where
      yes : Tags
      no : Tags
    data Marked : Type where
      marked : Nat → Marked
    data Inner : Type where
      inner : Nat → Inner
    data Nested : Type where
      nested : Inner → Nested
    data Box : Type where
      box : List Nat → Box
    data Soft : Type where
      soft : Maybe Bool → Soft
    repr Bool := boolean
    repr Bag := list integer
    repr Pair := tuple { integer, boolean }
    repr Row := map { "id" => integer, "flag" => optional Bool, "note" => nullable integer }
    repr Open := map open { "id" => integer }
    repr Tree := leaf => nil | node => tuple { integer, Tree, Tree }
    repr Shape := circle => map { "kind" => "circle", "r" => integer }
                | square => map { "kind" => "square", "side" => integer }
                | empty => nil
    repr Flag := :yes
    repr Tags := yes => :yes | no => "no"
    repr Marked := tuple { :ok, integer }
    repr Inner := map { "n" => integer }
    repr Nested := map { "in" => Inner }
    repr Box := map { "xs" => list integer }
    repr Soft := map { "flag" => optional nullable Bool }
    repr Nat := integer
    """
  end

  defp ambig_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    data Grant : Type where
      grant : Maybe Bool → Grant
    data ChoiceGrant : Type where
      choice_grant : Maybe Bool → ChoiceGrant
      choice_none : ChoiceGrant
    data AtomGrant : Type where
      atom_grant : Maybe Bool → AtomGrant
    data Both : Type where
      both : Bool → Bool → Both
    data Many : Type where
      many : Maybe Bool → Maybe Bool → Maybe Bool → Many
    data AtomMany : Type where
      atom_many : Maybe Bool → Maybe Bool → AtomMany
    data Child : Type where
      child : Maybe Bool → Child
    data Parent : Type where
      parent : Child → Parent
    data Grand : Type where
      grand : Parent → Grand
    data Kids : Type where
      kids : List Child → Kids
    data Closed : Type where
      closed : Maybe Bool → Closed
    data Bag : Type where
      bag : List (Nat × Bool) → Bag
    data Tag : Type where
      tag : Bool → Tag
    data AtomTag : Type where
      atom_tag : Bool → AtomTag
    data Node : Type where
      node_grant : Maybe Bool → Node
      node_none : Node
    data Hold : Type where
      hold : Node → Hold
    repr Bool := boolean
    repr Grant := map open { "read" => optional Bool }
    repr ChoiceGrant := choice_grant => map open { "read" => optional Bool } | choice_none => nil
    repr AtomGrant := map open { :read => optional Bool }
    repr Both := map open { "read" => Bool, :read => Bool }
    repr Many := map open { "read" => optional Bool, "write" => optional Bool, "admin" => optional Bool }
    repr AtomMany := map open { :write => optional Bool, :read => optional Bool }
    repr Child := map open { "read" => optional Bool }
    repr Parent := map open { "child" => Child }
    repr Grand := map open { "parent" => Parent }
    repr Kids := list Child
    repr Closed := map { "read" => optional Bool }
    repr Bag := map_of integer => boolean
    repr Tag := map open { "kind" => "circle", "ok" => Bool }
    repr AtomTag := map open { :kind => :yes, :ok => Bool }
    repr Node := node_grant => map open { "read" => optional Bool } | node_none => nil
    repr Hold := tuple { Node else node_none }
    """
  end

  defp wide_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    data Key : Type where
      named : Nat → Key
      wild : Key
    data Wrap : Type where
      wrap : Nat → Wrap
    data Names : Type where
      names : List Nat → Names
    data Twin : Type where
      twin : Nat → Nat → Twin
    data Rec : Type where
      rec : Nat → Nat → Rec
    data Link : Type where
      link : List (Nat × Nat) → Link
    data Item : Type where
      item : Nat → Bool → Item
    data Rows : Type where
      rows : List Item → Rows
    data Bag : Type where
      bag : List (Nat × Bool) → Bag
    data NatMap : Type where
      natmap : List (Nat × Bool) → NatMap
    data Fall : Type where
      fall : Bool → Fall
    data Count : Type where
      count : Nat → Count
    data Flag : Type where
      no : Flag
      yes : Nat → Flag
    data Hold : Type where
      hold : Flag → Hold
    data Row : Type where
      row : Maybe Bool → Row
    data Soft : Type where
      soft : Maybe Bool → Soft
    data Plain : Type where
      plain : Maybe Bool → Plain
    data Need : Type where
      need : Bool → Need
    data Collide : Type where
      collide : List (Nat × Bool) → Collide
    data Bit : Type where
      d1 : Bit → Bit
      z : Bit
      d2 : Bit → Bit
    data Token : Type where
      token : Bit → Token
    data Codes : Type where
      codes : List Bit → Codes
    data Dict : Type where
      dict : List (Bit × Bool) → Dict
    repr Bool := boolean
    repr Nat := integer
    repr Key := named => interned string | wild => "*"
    repr Wrap := interned string
    repr Names := list interned string
    repr Twin := tuple { interned string, interned string }
    repr Rec := map { "z" => interned string, "a" => interned string }
    repr Link := map_of interned string => interned string
    repr Rows := map_of integer => boolean
    repr Bag := map_of integer => boolean
    repr NatMap := map_of interned string => boolean
    repr Fall := tuple { boolean else false }
    repr Count := tuple { integer else 0 }
    repr Flag := no => nil | yes => map { "n" => integer }
    repr Hold := tuple { Flag else no }
    repr Row := map { "b" => optional (boolean else false) }
    repr Soft := nullable (boolean else false)
    repr Plain := map { "b" => optional Bool }
    repr Need := map { "b" => boolean else false }
    repr Collide := map_of (integer else 0) => boolean
    repr Token := interned string
    repr Codes := list interned string
    repr Dict := map_of interned string => boolean
    """
  end

  defp named_src do
    """
    data Count : Type where
      count : Nat → Count
      zero : Count
    data Hold : Type where
      hold : Count → Hold
    repr Count := count => integer | zero => nil
    repr Hold := tuple { Count else zero }
    """
  end

  defp box_src do
    """
    data Box : Type where
      box : Nat → Box
    repr Box := tuple { integer else 0 }
    """
  end

  defp limit_src do
    """
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    data Names : Type where
      names : List Nat → Names
    repr Names := list interned string
    """
  end

  defp probe_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    data Names : Type where
      names : List Nat → Names
    data Wrap : Type where
      wrap : Nat → Wrap
    data NatMap : Type where
      natmap : List (Nat × Bool) → NatMap
    data Bag : Type where
      bag : List (Nat × Bool) → Bag
    data Flag : Type where
      no : Flag
      yes : Nat → Flag
    data Same : Type where
      same : List (Flag × Bool) → Same
    data Collide : Type where
      collide : List (Nat × Bool) → Collide
    data Bit : Type where
      d1 : Bit → Bit
      z : Bit
      d2 : Bit → Bit
    data Dict : Type where
      dict : List (Bit × Bool) → Dict
    repr Bool := boolean
    repr Nat := integer
    repr Names := list interned string
    repr Wrap := interned string
    repr NatMap := map_of interned string => boolean
    repr Bag := map_of integer => boolean
    repr Flag := no => nil | yes => integer
    repr Same := map_of (Flag else no) => boolean
    repr Collide := map_of (integer else 0) => boolean
    repr Dict := map_of interned string => boolean
    """
  end

  defp table_names(%{by_index: by_index}) do
    by_index
    |> Enum.sort_by(fn {index, _name} -> index end)
    |> Enum.map(fn {_index, name} -> name end)
  end
end
