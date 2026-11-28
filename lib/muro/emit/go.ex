defmodule Muro.Emit.Go do
  @moduledoc false

  alias Muro.Emit.Fsm
  alias Muro.Emit.Go.Choreo
  alias Muro.Emit.Go.Family
  alias Muro.Emit.Go.Match
  alias Muro.Emit.Go.Session
  alias Muro.Emit.Name

  @keywords ~w(break default func interface select case defer go map struct chan else goto package switch const fallthrough if range type continue for import return var)
  @predeclared ~w(any bool byte comparable complex64 complex128 error false float32 float64 int int8 int16 int32 int64 rune string true uint uint8 uint16 uint32 uint64 uintptr iota nil append cap clear close complex copy delete imag len make max min new panic print println real recover)
  @reserved ~w(IllegalTransitionError ErrIllegalTransition ArgumentError ErrArgument FamilyError ErrFamily ErrDuplicate ErrDeparted ErrUnknown ErrHeld ErrOpened ErrResolved ErrWithdrawn ErrHeldBy ErrLive ErrKind ErrBadState ErrIndex ErrUnmarked ErrUnfinished Value Event Send Recv Phase PhaseOpen PhaseHeld PhaseResolved Outcome OutcomeResolve OutcomeRerun Released Row Unit Nat Bit0 Bit1 Con Pair Record Vec Pick0 Pick1 String Error)
  # Package-level helpers the preludes define that are not in `@reserved`.
  @helpers ~w(muroIllegal muroEvent muroClone muroNat muroDown muroSortRecord valKind valUnit valNat valBit0 valBit1 valCon valPair valRecord valVec valPick0 valPick1)

  @doc false
  def render(book, path, opts \\ []) when is_list(book) and is_binary(path) and is_list(opts) do
    package = Keyword.get(opts, :package)

    with :ok <- check_package(package),
         {:ok, plan} <- Fsm.prepare(book, path, Keyword.take(opts, [:root, :fuel])) do
      build(book, path, plan, package)
    end
  end

  @doc false
  def camel(source) when is_binary(source) do
    parts =
      source
      |> String.split(~r/[^0-9A-Za-z]+/, trim: true)
      |> Enum.map(fn part ->
        {first, rest} = String.split_at(part, 1)
        String.upcase(first) <> rest
      end)

    base = if parts == [], do: "X", else: Enum.join(parts)
    if base =~ ~r/^[0-9]/, do: "X" <> base, else: base
  end

  @doc false
  def package_of(stem) when is_binary(stem) do
    base =
      stem
      |> String.downcase()
      |> String.replace(~r/[^a-z0-9_]/, "_")
      |> String.replace(~r/_+/, "_")
      |> String.trim("_")

    base = if base == "" or base =~ ~r/^[0-9]/, do: "p_" <> base, else: base
    if reserved_ident?(base), do: base <> "_k", else: base
  end

  @doc false
  def check_package(nil), do: :ok

  def check_package(name) when is_binary(name) do
    if name =~ ~r/^[a-z][a-z0-9_]*$/ and not reserved_ident?(name) do
      :ok
    else
      {:error, "go: package name"}
    end
  end

  def check_package(_), do: {:error, "go: package name"}

  defp build(book, path, plan, package) do
    package = package || package_of(Path.basename(path, ".muro"))
    marked = Enum.any?(book, &Muro.Fail.marked?/1)
    decls = Muro.Session.payload_decls(book)
    reprs = for %{kind: :repr, name: name} <- book, do: name

    ctx = %{
      decls: decls,
      reprs: reprs,
      match: Match.empty(),
      marked: marked,
      fails: if(marked, do: Fsm.failure_table(book, plan), else: %{})
    }

    used = MapSet.new(@reserved)

    with {:ok, sessions, ctx, used} <- compile_sessions(plan, ctx, used),
         {:ok, families, used} <- compile_families(plan, book, used),
         {:ok, globals, ctx, used} <- compile_globals(plan, ctx, used),
         {:ok, cfams, used} <- compile_cfams(plan, globals, used) do
      {session_src, needs} = render_sessions(sessions, param_scope(used, families))
      preambles = Map.new(plan.cfams, &{&1.plan, &1.preamble})
      {global_src, gneeds} = render_globals(globals, preambles)
      {family_src, fneeds} = render_families(families)
      {cfam_src, cneeds} = render_cfams(cfams)

      match_src = Match.source(ctx.match)

      needs =
        needs
        |> MapSet.union(gneeds)
        |> MapSet.union(fneeds)
        |> MapSet.union(cneeds)
        |> maybe(:argument, Enum.any?(sessions, fn {image, _} -> image.params != [] end))
        |> maybe(:event, sessions != [])
        |> maybe(:value, sessions != [] or globals != [] or cfams != [])
        |> maybe(:illegal, sessions != [] or globals != [] or cfams != [])
        |> maybe(:sort, families != [] or cfams != [])
        |> maybe(:nat, String.contains?(match_src, "muroNat("))

      body =
        [
          prelude(needs),
          match_src,
          session_src,
          global_src,
          if(families == [], do: "", else: Family.engine()),
          family_src,
          cfam_src
        ]
        |> Enum.reject(&(&1 == ""))
        |> Enum.join("\n")

      {:ok, tighten(header(package) <> "\n" <> imports(needs) <> "\n" <> body)}
    end
  end

  defp compile_sessions(plan, ctx, used) do
    pairs =
      Enum.map(plan.sessions, fn sess ->
        {sess, Map.fetch!(plan.opened, sess.name)}
      end)

    Enum.reduce_while(pairs, {:ok, [], ctx, used}, fn {sess, entry}, {:ok, acc, ctx, used} ->
      case Session.compile(sess, entry, ctx) do
        {:error, msg} ->
          {:halt, {:error, msg}}

        {:ok, image} ->
          {go, used} = claim(camel(image.name), used)
          {:cont, {:ok, acc ++ [{image, go}], %{ctx | match: image.match}, used}}
      end
    end)
  end

  defp compile_families(plan, book, used) do
    Enum.reduce_while(plan.families, {:ok, [], used}, fn family, {:ok, acc, used} ->
      case Family.compile(family, book) do
        {:error, msg} ->
          {:halt, {:error, msg}}

        {:ok, image} ->
          {go, used} = claim(camel(image.name), used)
          {kind, used} = claim(go <> "Kind", used)
          {:cont, {:ok, acc ++ [{image, go, kind}], used}}
      end
    end)
  end

  defp compile_globals(plan, ctx, used) do
    Enum.reduce_while(plan.globals, {:ok, [], ctx, used}, fn global, {:ok, acc, ctx, used} ->
      case Choreo.compile(global, ctx.match, ctx.decls, ctx.reprs) do
        {:error, msg} ->
          {:halt, {:error, msg}}

        {:ok, image, match} ->
          {go, used} = claim(camel(image.name), used)
          {:cont, {:ok, acc ++ [{image, go}], %{ctx | match: match}, used}}
      end
    end)
  end

  defp compile_cfams(plan, globals, used) do
    by_name = Map.new(globals, fn {image, go} -> {image.name, {image, go}} end)

    Enum.reduce_while(plan.cfams, {:ok, [], used}, fn cfam, {:ok, acc, used} ->
      case Map.fetch(by_name, cfam.plan) do
        :error ->
          {:halt, {:error, "go: unsupported protocol"}}

        {:ok, {image, monitor}} ->
          {go, used} = claim(camel(cfam.name), used)
          labels = Map.new(image.nodes, &{&1.id, &1.label})

          row = %{
            name: cfam.name,
            plan: cfam.plan,
            start: image.start,
            labels: labels,
            monitor: monitor,
            go: go
          }

          {:cont, {:ok, acc ++ [row], used}}
      end
    end)
  end

  defp render_sessions(sessions, taken) do
    Enum.reduce(sessions, {"", MapSet.new(), taken}, fn {image, go}, {src, needs, taken} ->
      {piece, more, _match, taken} = Session.render(image, go, image, taken)
      {src <> piece <> "\n", MapSet.union(needs, more), taken}
    end)
    |> then(fn {src, needs, _taken} -> {src, needs} end)
  end

  # Constructor parameters are claimed against this set. `@reserved` is
  # already in `used`. Keywords and predeclared identifiers are not:
  # a parameter keeps the source spelling, so `string` and `nil` reach Go
  # as themselves. The family engine's names are in the file only when a
  # keyed family is.
  defp param_scope(used, families) do
    taken =
      [@keywords, @predeclared, @helpers]
      |> Enum.concat()
      |> MapSet.new()
      |> MapSet.union(used)

    if families == [], do: taken, else: MapSet.union(taken, Family.engine_idents())
  end

  defp render_globals(globals, preambles) do
    Enum.reduce(globals, {"", MapSet.new()}, fn {image, go}, {src, needs} ->
      pre =
        if Map.has_key?(preambles, image.name), do: Map.fetch!(preambles, image.name), else: nil

      {piece, more} = Choreo.render_monitor(image, go, pre)
      {src <> piece <> "\n", MapSet.union(needs, more)}
    end)
  end

  defp render_families(families) do
    Enum.reduce(families, {"", MapSet.new()}, fn {image, go, kind}, {src, needs} ->
      {piece, more} = Family.render(Map.put(image, :kind_name, kind), go)
      {src <> piece <> "\n", MapSet.union(needs, more)}
    end)
  end

  defp render_cfams(cfams) do
    Enum.reduce(cfams, {"", MapSet.new()}, fn row, {src, needs} ->
      {piece, more} = Choreo.render_family(row, row.go, row.monitor)
      {src <> piece <> "\n", MapSet.union(needs, more)}
    end)
  end

  defp claim(base, used) do
    Name.claim(base, used)
  end

  defp maybe(needs, _flag, false), do: needs
  defp maybe(needs, flag, true), do: MapSet.put(needs, flag)

  defp header(package) do
    version = Application.spec(:muro, :vsn) |> to_string()

    """
    // Code generated by muro #{version}. DO NOT EDIT.

    // Package #{package} is a session, choreography, and keyed-family image.
    // Callers own each value. One session, monitor, or dispatcher is not
    // safe for concurrent use: synchronize, or give each goroutine its own value.
    package #{package}
    """
  end

  defp imports(needs) do
    mods = ["\"errors\"", "\"fmt\""]
    mods = if :sort in needs, do: mods ++ ["\"sort\""], else: mods
    lines = Enum.map_join(mods, "\n", &("\t" <> &1))
    "import (\n" <> lines <> "\n)\n"
  end

  defp prelude(needs) do
    [
      if(:illegal in needs, do: illegal_prelude(), else: ""),
      if(:argument in needs, do: argument_prelude(), else: ""),
      if(:value in needs, do: value_prelude(), else: ""),
      if(:event in needs, do: event_prelude(), else: ""),
      if(:clone in needs, do: clone_prelude(), else: ""),
      if(:nat in needs, do: nat_prelude(), else: ""),
      if(:down in needs, do: down_prelude(), else: "")
    ]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n")
  end

  defp illegal_prelude do
    """
    // ErrIllegalTransition is the sentinel for a refused step.
    var ErrIllegalTransition = errors.New("muro: illegal transition")

    // IllegalTransitionError is a refused step. Unwrap returns ErrIllegalTransition.
    type IllegalTransitionError struct {
    \tMachine  string
    \tState    string
    \tExpected string
    \tEvent    string
    }

    // Error describes the refused step.
    func (e *IllegalTransitionError) Error() string {
    \tif e == nil {
    \t\treturn "muro: illegal transition"
    \t}
    \treturn fmt.Sprintf("muro: illegal transition in %s at %s expected %s got %s", e.Machine, e.State, e.Expected, e.Event)
    }

    // Unwrap returns ErrIllegalTransition.
    func (e *IllegalTransitionError) Unwrap() error {
    \tif e == nil {
    \t\treturn nil
    \t}
    \treturn ErrIllegalTransition
    }

    func muroIllegal(machine, state, expected, event string) error {
    \treturn &IllegalTransitionError{Machine: machine, State: state, Expected: expected, Event: event}
    }
    """
  end

  defp argument_prelude do
    """
    // ErrArgument is the sentinel for a constructor argument that is not a nat.
    var ErrArgument = errors.New("muro: argument")

    // ArgumentError is a refused constructor argument. Unwrap returns ErrArgument.
    type ArgumentError struct {
    \tMessage string
    }

    // Error returns the message.
    func (e *ArgumentError) Error() string {
    \tif e == nil || e.Message == "" {
    \t\treturn "muro: argument"
    \t}
    \treturn e.Message
    }

    // Unwrap returns ErrArgument.
    func (e *ArgumentError) Unwrap() error {
    \tif e == nil {
    \t\treturn nil
    \t}
    \treturn ErrArgument
    }
    """
  end

  defp value_prelude do
    """
    type valKind uint8

    const (
    \tvalUnit valKind = iota
    \tvalNat
    \tvalBit0
    \tvalBit1
    \tvalCon
    \tvalPair
    \tvalRecord
    \tvalVec
    \tvalPick0
    \tvalPick1
    )

    // Value is one payload. Constructors do not panic: a value that does not
    // match the protocol is refused by Step.
    type Value struct {
    \tk      valKind
    \tn      int
    \ttag    string
    \tnames  []string
    \tfields []Value
    }

    // String returns a short description of the value.
    func (v Value) String() string {
    \tswitch v.k {
    \tcase valUnit:
    \t\treturn "unit"
    \tcase valNat:
    \t\treturn fmt.Sprintf("nat %d", v.n)
    \tcase valBit0:
    \t\treturn "b0"
    \tcase valBit1:
    \t\treturn "b1"
    \tcase valPick0:
    \t\treturn "pick0"
    \tcase valPick1:
    \t\treturn "pick1"
    \tcase valCon:
    \t\treturn "con " + v.tag
    \tcase valPair:
    \t\treturn "pair"
    \tcase valRecord:
    \t\treturn "record"
    \tcase valVec:
    \t\treturn "vec"
    \tdefault:
    \t\treturn "value"
    \t}
    }

    // Unit is the unit payload.
    func Unit() Value { return Value{k: valUnit} }

    // Nat is a natural number. A negative argument is not a nat, and Step refuses it.
    func Nat(n int) Value { return Value{k: valNat, n: n} }

    // Bit0 is the bit 0.
    func Bit0() Value { return Value{k: valBit0} }

    // Bit1 is the bit 1.
    func Bit1() Value { return Value{k: valBit1} }

    // Pick0 is the left choice.
    func Pick0() Value { return Value{k: valPick0} }

    // Pick1 is the right choice.
    func Pick1() Value { return Value{k: valPick1} }

    // Con is one constructor applied to fields.
    func Con(tag string, fields ...Value) Value {
    \treturn Value{k: valCon, tag: tag, fields: append([]Value(nil), fields...)}
    }

    // Pair is an ordered pair.
    func Pair(a, b Value) Value {
    \treturn Value{k: valPair, fields: []Value{a, b}}
    }

    // Record sorts fields by name. A length mismatch does not panic; Step refuses it.
    func Record(names []string, fields []Value) Value {
    \tns, fs := muroSortRecord(names, fields)
    \treturn Value{k: valRecord, names: ns, fields: fs}
    }

    // Vec is a list of values.
    func Vec(fields ...Value) Value {
    \treturn Value{k: valVec, fields: append([]Value(nil), fields...)}
    }

    func muroSortRecord(names []string, fields []Value) ([]string, []Value) {
    \tns := append([]string(nil), names...)
    \tfs := append([]Value(nil), fields...)
    \tif len(ns) != len(fs) {
    \t\treturn ns, fs
    \t}
    \tfor i := 1; i < len(ns); i++ {
    \t\tname, field := ns[i], fs[i]
    \t\tj := i
    \t\tfor j > 0 && ns[j-1] > name {
    \t\t\tns[j], fs[j] = ns[j-1], fs[j-1]
    \t\t\tj--
    \t\t}
    \t\tns[j], fs[j] = name, field
    \t}
    \treturn ns, fs
    }
    """
  end

  defp event_prelude do
    """
    // Event is a send or a receive. The set is closed: only Send and Recv
    // implement the unexported method.
    type Event interface {
    \tisEvent()
    \tString() string
    }

    // Send is an output event.
    type Send struct {
    \tValue Value
    }

    func (Send) isEvent() {}

    // String returns the event.
    func (e Send) String() string { return "send " + e.Value.String() }

    // Recv is an input event.
    type Recv struct {
    \tValue Value
    }

    func (Recv) isEvent() {}

    // String returns the event.
    func (e Recv) String() string { return "recv " + e.Value.String() }

    func muroEvent(ev Event) string {
    \tif ev == nil {
    \t\treturn "nil"
    \t}
    \treturn ev.String()
    }
    """
  end

  defp clone_prelude do
    """
    func muroClone(env map[string]Value) map[string]Value {
    \tif env == nil {
    \t\treturn map[string]Value{}
    \t}
    \tout := make(map[string]Value, len(env))
    \tfor k, v := range env {
    \t\tout[k] = v
    \t}
    \treturn out
    }
    """
  end

  defp nat_prelude do
    """
    func muroNat(env map[string]Value, name string) (int, bool) {
    \tif env == nil {
    \t\treturn 0, false
    \t}
    \tv, ok := env[name]
    \tif !ok || v.k != valNat || v.n < 0 {
    \t\treturn 0, false
    \t}
    \treturn v.n, true
    }
    """
  end

  defp down_prelude do
    """
    func muroDown(reason *Value) string {
    \tif reason == nil {
    \t\treturn "down"
    \t}
    \treturn "down " + reason.String()
    }
    """
  end

  defp reserved_ident?(name), do: name in @keywords or name in @predeclared

  defp tighten(src) do
    src
    |> String.replace(~r/[ \t]+\n/, "\n")
    |> String.replace(~r/\n{3,}/, "\n\n")
    |> String.trim_trailing()
    |> Kernel.<>("\n")
  end
end
