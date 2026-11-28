defmodule Muro.Emit.Go.Family do
  @moduledoc false

  @engine_path Path.join(__DIR__, "go_family_engine.go")
  @external_resource @engine_path

  @engine_body (
                 marker = "// Phase is the phase of one live or retained row.\n"

                 [@engine_path |> File.read!() |> String.split(marker, parts: 2) |> Enum.at(1)]
                 |> then(fn [body] -> marker <> body end)
               )

  @doc false
  def engine, do: @engine_body

  @doc false
  def engine_idents do
    ~r/^(?:func|type|var)\s+([A-Za-z_][A-Za-z0-9_]*)/m
    |> Regex.scan(@engine_body)
    |> Enum.map(fn [_, name] -> name end)
    |> MapSet.new()
  end

  @doc false
  def compile(family, book) when is_map(family) and is_list(book) do
    data = Enum.find(book, &(&1[:kind] == :data and &1.name == family.key))

    if data == nil or not is_list(data.ctors) do
      {:error, "go: unsupported family"}
    else
      ctors = Enum.map(data.ctors, & &1.name)

      if length(ctors) > 255 do
        {:error, "go: unsupported family"}
      else
        index = Map.new(Enum.with_index(ctors))
        by = Map.new(family.rules || [], &{&1.ctor, &1.hold})

        case Enum.reduce_while(ctors, [], fn ctor, acc ->
               case rule_of(Map.get(by, ctor), index) do
                 {:ok, rule} -> {:cont, acc ++ [rule]}
                 {:error, _} = err -> {:halt, err}
               end
             end) do
          {:error, _} = err ->
            err

          rules ->
            {:ok,
             %{
               name: family.name,
               ctors: ctors,
               rules: rules,
               revert: Map.get(family, :revert, false) == true,
               redeliver: Map.get(family, :redeliver, false) == true
             }}
        end
      end
    end
  end

  @doc false
  def render(image, go_name) do
    prefix = unexport(go_name)
    kind = Map.get(image, :kind_name, go_name <> "Kind")
    rules = prefix <> "Rules"
    names = prefix <> "Names"
    marked = if image.revert, do: "true", else: "false"

    src = """
    // #{go_name} is the keyed family #{image.name}.
    #{redeliver_comment(image.redeliver)}// Callers own the value. #{go_name} is not safe for concurrent use:
    // synchronize, or give each goroutine its own value.
    // The zero value is not a dispatcher. Call New#{go_name}.
    // Finish does not step a session. Pass sessionDone from that session.
    type #{go_name} struct {
    \tst famState
    }

    // #{kind} is one constructor of the family's key, in declaration order.
    type #{kind} uint8

    const (
    #{kind_consts(image.ctors, kind)})

    // String returns the constructor name.
    func (k #{kind}) String() string {
    \tswitch k {
    #{kind_strings(image.ctors, kind)}\tdefault:
    \t\treturn "kind"
    \t}
    }

    // New#{go_name} returns a dispatcher with an empty floor.
    func New#{go_name}() *#{go_name} {
    \treturn &#{go_name}{st: famState{ready: true, floor: -1}}
    }

    func #{rules}() []holdRule {
    \treturn []holdRule{
    #{rule_lines(image.rules)}\t}
    }

    func #{names}() []string {
    \treturn []string{#{name_list(image.ctors)}}
    }

    // Arrive opens or holds one instance. On error the dispatcher is unchanged
    // and the id is -1.
    func (s *#{go_name}) Arrive(key string, kind #{kind}, index int) (Phase, int, error) {
    \tif s == nil {
    \t\treturn 0, -1, famErr(ErrBadState)
    \t}
    \tif err := muroFamReady(s.st); err != nil {
    \t\treturn 0, -1, err
    \t}
    \tnext, phase, id, ferr := muroFamArrive(s.st, key, uint8(kind), index, #{rules}(), #{names}())
    \tif ferr != nil {
    \t\treturn 0, -1, ferr
    \t}
    \ts.st = next
    \treturn phase, id, nil
    }

    // Resolved releases an open row. A family marked may revert keeps the row.
    func (s *#{go_name}) Resolved(id int) ([]Released, error) {
    \treturn #{prefix}Release(s, id, true)
    }

    // Withdraw releases a held row and records the departure.
    func (s *#{go_name}) Withdraw(id int) ([]Released, error) {
    \treturn #{prefix}Release(s, id, false)
    }

    func #{prefix}Release(s *#{go_name}, id int, record bool) ([]Released, error) {
    \tif s == nil {
    \t\treturn nil, famErr(ErrBadState)
    \t}
    \tif err := muroFamReady(s.st); err != nil {
    \t\treturn nil, err
    \t}
    \tvar next famState
    \tvar rel []famRel
    \tvar ferr *FamilyError
    \tif record {
    \t\tnext, rel, ferr = muroFamResolve(s.st, id, #{rules}(), #{marked})
    \t} else {
    \t\tnext, rel, ferr = muroFamWithdraw(s.st, id, #{rules}(), #{marked})
    \t}
    \tif ferr != nil {
    \t\treturn nil, ferr
    \t}
    \ts.st = next
    \treturn muroFamReleased(rel, #{names}()), nil
    }

    // WaitingOn lists the kinds and row ids that keep this row held.
    func (s *#{go_name}) WaitingOn(id int) ([]string, []int, error) {
    \tif s == nil {
    \t\treturn nil, nil, famErr(ErrBadState)
    \t}
    \tif err := muroFamReady(s.st); err != nil {
    \t\treturn nil, nil, err
    \t}
    \tkinds, ids, ferr := muroFamWaiting(s.st, id, #{rules}(), #{names}())
    \tif ferr != nil {
    \t\treturn nil, nil, ferr
    \t}
    \treturn kinds, ids, nil
    }

    // Skip records a creation index that will not arrive, unless it is live.
    func (s *#{go_name}) Skip(key string, index int) error {
    \treturn #{prefix}Mut(s, func(st famState) (famState, *FamilyError) {
    \t\treturn muroFamSkip(st, key, index)
    \t})
    }

    // DropKey forgets one key that has no live row.
    func (s *#{go_name}) DropKey(key string) error {
    \treturn #{prefix}Mut(s, func(st famState) (famState, *FamilyError) {
    \t\treturn muroFamDropKey(st, key)
    \t})
    }

    // SkipBelow raises the floor. Indexes at or below it have departed.
    func (s *#{go_name}) SkipBelow(index int) error {
    \treturn #{prefix}Mut(s, func(st famState) (famState, *FamilyError) {
    \t\treturn muroFamSkipBelow(st, index)
    \t})
    }

    // Revert puts a resolved row back to open when the family may revert.
    // An unmarked family returns ErrUnmarked.
    func (s *#{go_name}) Revert(id int) error {
    \treturn #{prefix}Mut(s, func(st famState) (famState, *FamilyError) {
    \t\treturn muroFamRevert(st, id, #{rules}(), #{marked})
    \t})
    }

    // Rerun checks that the row is open and leaves it there.
    func (s *#{go_name}) Rerun(id int) error {
    \treturn #{prefix}Mut(s, func(st famState) (famState, *FamilyError) {
    \t\treturn muroFamRerun(st, id)
    \t})
    }

    func #{prefix}Mut(s *#{go_name}, op func(famState) (famState, *FamilyError)) error {
    \tif s == nil {
    \t\treturn famErr(ErrBadState)
    \t}
    \tif err := muroFamReady(s.st); err != nil {
    \t\treturn err
    \t}
    \tnext, ferr := op(s.st)
    \tif ferr != nil {
    \t\treturn ferr
    \t}
    \ts.st = next
    \treturn nil
    }

    // Finish resolves or reruns an open row after the meeting session is done.
    // It does not step that session.
    func (s *#{go_name}) Finish(id int, sessionDone bool, outcome Outcome) ([]Released, error) {
    \tif s == nil {
    \t\treturn nil, famErr(ErrBadState)
    \t}
    \tif err := muroFamReady(s.st); err != nil {
    \t\treturn nil, err
    \t}
    \tif !sessionDone {
    \t\treturn nil, famErr(ErrUnfinished)
    \t}
    \tswitch outcome {
    \tcase OutcomeResolve:
    \t\tnext, rel, ferr := muroFamResolve(s.st, id, #{rules}(), #{marked})
    \t\tif ferr != nil {
    \t\t\treturn nil, ferr
    \t\t}
    \t\ts.st = next
    \t\treturn muroFamReleased(rel, #{names}()), nil
    \tcase OutcomeRerun:
    \t\tnext, ferr := muroFamRerun(s.st, id)
    \t\tif ferr != nil {
    \t\t\treturn nil, ferr
    \t\t}
    \t\ts.st = next
    \t\treturn []Released{}, nil
    \tdefault:
    \t\treturn nil, famErr(ErrBadState)
    \t}
    }

    // View returns the rows sorted by key, index, then id.
    func (s *#{go_name}) View() []Row {
    \tif s == nil || muroFamReady(s.st) != nil {
    \t\treturn nil
    \t}
    \treturn muroFamView(s.st, #{names}())
    }

    // Floor is the skip_below cursor. A new dispatcher returns -1.
    func (s *#{go_name}) Floor() int {
    \tif s == nil || muroFamReady(s.st) != nil {
    \t\treturn -1
    \t}
    \treturn s.st.floor
    }

    // Departed reports the packed prefix and gaps of one key.
    // A missing key returns prefix -1, no gaps, and false.
    func (s *#{go_name}) Departed(key string) (int, []int, bool) {
    \tif s == nil || muroFamReady(s.st) != nil || s.st.departed == nil {
    \t\treturn -1, nil, false
    \t}
    \trec, ok := s.st.departed[key]
    \tif !ok {
    \t\treturn -1, nil, false
    \t}
    \treturn rec.prefix, muroFamGaps(rec.gaps), true
    }

    // Live reads an open or held row.
    func (s *#{go_name}) Live(id int) (Phase, string, #{kind}, error) {
    \tif s == nil {
    \t\treturn 0, "", 0, famErr(ErrBadState)
    \t}
    \tif err := muroFamReady(s.st); err != nil {
    \t\treturn 0, "", 0, err
    \t}
    \tphase, key, kind, ferr := muroFamLive(s.st, id)
    \tif ferr != nil {
    \t\treturn 0, "", 0, ferr
    \t}
    \treturn phase, key, #{kind}(kind), nil
    }

    """

    {src, MapSet.new([:sort, :family])}
  end

  defp redeliver_comment(true) do
    "// may redeliver is a contract on the graph, not a method.\n"
  end

  defp redeliver_comment(false), do: ""

  defp kind_consts([], kind) do
    "\t// #{kind}Invalid is the zero kind.\n\t#{kind}Invalid #{kind} = iota\n"
  end

  defp kind_consts(ctors, kind) do
    [first | rest] = Enum.map(ctors, &kind_const(kind, &1))

    "\t// #{first} is #{hd(ctors)}.\n\t#{first} #{kind} = iota\n" <>
      Enum.map_join(Enum.zip(rest, tl(ctors)), "", fn {const, ctor} ->
        "\t// #{const} is #{ctor}.\n\t#{const}\n"
      end)
  end

  defp kind_strings(ctors, kind) do
    ctors
    |> Enum.map_join("", fn ctor ->
      "\tcase #{kind_const(kind, ctor)}:\n\t\treturn #{gq(ctor)}\n"
    end)
  end

  defp kind_const(kind, ctor) do
    kind <> Macro.camelize(ctor)
  end

  defp rule_lines(rules) do
    Enum.map_join(rules, "", fn rule ->
      "\t\t{mode: #{mode(rule.mode)}#{spans(rule)}},\n"
    end)
  end

  defp mode(:never), do: "holdNever"
  defp mode(:earlier), do: "holdEarlier"
  defp mode(:any), do: "holdAny"
  defp mode(:named), do: "holdNamed"
  defp mode(:missing), do: "holdMissing"

  defp spans(%{mode: :named, while: w, until: u}) do
    Enum.join([slice("while", w), slice("until", u)], "")
  end

  defp spans(_), do: ""

  defp slice(_field, []), do: ""

  defp slice(field, idxs) do
    ", #{field}: []uint8{#{Enum.join(idxs, ", ")}}"
  end

  defp name_list(ctors), do: Enum.map_join(ctors, ", ", &gq/1)

  defp rule_of(nil, _index), do: {:ok, %{mode: :missing, while: [], until: []}}
  defp rule_of(:never, _index), do: {:ok, %{mode: :never, while: [], until: []}}
  defp rule_of(:earlier, _index), do: {:ok, %{mode: :earlier, while: [], until: []}}
  defp rule_of(:any, _index), do: {:ok, %{mode: :any, while: [], until: []}}

  defp rule_of({:named, %{while: w, until: u}}, index) do
    with {:ok, w} <- idxs(w, index),
         {:ok, u} <- idxs(u, index) do
      {:ok, %{mode: :named, while: w, until: u}}
    end
  end

  defp rule_of(_, _), do: {:error, "go: unsupported family"}

  defp idxs(names, index) do
    Enum.reduce_while(names, [], fn name, acc ->
      case Map.fetch(index, name) do
        {:ok, i} -> {:cont, acc ++ [i]}
        :error -> {:halt, {:error, "go: unsupported family"}}
      end
    end)
    |> case do
      {:error, _} = err -> err
      list -> {:ok, list}
    end
  end

  defp unexport(camel) do
    {first, rest} = String.split_at(camel, 1)
    String.downcase(first) <> rest
  end

  defp gq(s), do: Muro.Emit.Go.Match.gq(s)
end
