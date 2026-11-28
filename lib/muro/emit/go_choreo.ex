defmodule Muro.Emit.Go.Choreo do
  @moduledoc false

  alias Muro.Emit.Go.Match

  @doc false
  def compile(%{name: name, tree: tree}, match, decls, reprs) do
    acc = %{next: 0, nodes: %{}, counts: %{}, match: match, decls: decls, reprs: reprs}

    case walk(tree, acc) do
      {:error, msg} ->
        {:error, msg}

      {start, acc} ->
        {:ok,
         %{
           name: name,
           start: start,
           nodes: ordered(acc)
         }, acc.match}
    end
  end

  @doc false
  def render_monitor(image, go_name, preamble) do
    nodes = image.nodes
    prefix = "muro" <> go_name
    state = go_name <> "State"
    done = state <> "Done"
    invalid = state <> "Invalid"
    labels = Map.new(nodes, &{&1.id, &1.label})
    start = start_const(image.start, state, done, labels)

    src = """
    // #{go_name} follows choreography #{image.name} in the order it is written.
    // The zero value is not started. #{go_name} is not safe for concurrent use.
    type #{go_name} struct {
    \tstate #{state}
    \tready bool
    }

    // #{state} is the next interaction.
    type #{state} uint8

    const (
    \t// #{invalid} is the zero #{go_name}.
    \t#{invalid} #{state} = iota
    #{const_lines(nodes, state)}#{done_line(done)})

    // String returns the state name.
    func (s #{state}) String() string {
    \tswitch s {
    \tcase #{invalid}:
    \t\treturn "invalid"
    #{string_lines(nodes, state)}\tcase #{done}:
    \t\treturn "done"
    \tdefault:
    \t\treturn "state"
    \t}
    }

    // New#{go_name} starts at the first interaction.
    func New#{go_name}() #{go_name} {
    \treturn #{go_name}{state: #{start}, ready: true}
    }

    // State returns the resting position. The zero value is invalid.
    func (m *#{go_name}) State() #{state} {
    \tif m == nil || !m.ready {
    \t\treturn #{invalid}
    \t}
    \treturn m.state
    }

    // Done reports whether the choreography has reached end.
    func (m *#{go_name}) Done() bool {
    \treturn m != nil && m.ready && #{prefix}Done(m.state)
    }

    // Expected is the next message or choice, or "done", or "start".
    func (m *#{go_name}) Expected() string {
    \tif m == nil || !m.ready {
    \t\treturn "start"
    \t}
    \treturn #{prefix}Expected(m.state)
    }

    // Step takes the next message. The value is Unit for a message with no payload.
    // A refused step leaves the value unchanged.
    func (m *#{go_name}) Step(from, to, label string, v Value) error {
    \tev := "message " + from + " " + to + " " + label + " " + v.String()
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{go_name}", "invalid", "start", ev)
    \t}
    \tnext, err := #{prefix}Step(m.state, from, to, label, v)
    \tif err != nil {
    \t\treturn err
    \t}
    \tm.state = next
    \treturn nil
    }

    // Choose takes the next choice.
    func (m *#{go_name}) Choose(role, label string) error {
    \tev := "choose " + role + " " + label
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{go_name}", "invalid", "start", ev)
    \t}
    \tnext, err := #{prefix}Choose(m.state, role, label)
    \tif err != nil {
    \t\treturn err
    \t}
    \tm.state = next
    \treturn nil
    }

    func #{prefix}Done(state #{state}) bool {
    \treturn state == #{done}
    }

    func #{prefix}Expected(state #{state}) string {
    \tswitch state {
    #{expect_lines(nodes, state, prefix)}\tdefault:
    \t\treturn "done"
    \t}
    }

    func #{prefix}Step(state #{state}, from, to, label string, v Value) (#{state}, error) {
    \tev := "message " + from + " " + to + " " + label + " " + v.String()
    \tswitch state {
    #{step_lines(nodes, state, go_name, prefix, labels)}\tdefault:
    \t\treturn state, muroIllegal("#{go_name}", state.String(), "done", ev)
    \t}
    }

    func #{prefix}Choose(state #{state}, role, label string) (#{state}, error) {
    \tev := "choose " + role + " " + label
    \tswitch state {
    #{choose_lines(nodes, state, go_name, labels)}\tdefault:
    \t\treturn state, muroIllegal("#{go_name}", state.String(), #{prefix}Expected(state), ev)
    \t}
    }

    #{preamble_fn(preamble, nodes, state, prefix)}
    """

    {src, MapSet.new()}
  end

  @doc false
  def render_family(cfam, go_name, monitor) do
    prefix = "muro" <> monitor
    state = monitor <> "State"
    start = start_const(cfam.start, state, state <> "Done", cfam.labels)

    src = """
    // #{go_name} runs choreography #{cfam.plan} once per key.
    // StepShared and ChooseShared take the shared preamble, once, before any key.
    // The zero value is not a dispatcher. #{go_name} is not safe for concurrent use.
    type #{go_name} struct {
    \tready  bool
    \tshared #{state}
    \tkeys   map[string]#{state}
    }

    // New#{go_name} starts every key at the shared preamble.
    func New#{go_name}() *#{go_name} {
    \treturn &#{go_name}{ready: true, shared: #{start}, keys: map[string]#{state}{}}
    }

    // StepShared takes one shared message.
    func (m *#{go_name}) StepShared(from, to, label string, v Value) error {
    \tev := "message " + from + " " + to + " " + label + " " + v.String()
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{go_name}", "invalid", "start", ev)
    \t}
    \tif !#{prefix}Pre(m.shared) {
    \t\treturn muroIllegal("#{go_name}", m.shared.String(), "done", ev)
    \t}
    \tnext, err := #{prefix}Step(m.shared, from, to, label, v)
    \tif err != nil {
    \t\treturn err
    \t}
    \tm.shared = next
    \treturn nil
    }

    // ChooseShared takes one shared choice.
    func (m *#{go_name}) ChooseShared(role, label string) error {
    \tev := "choose " + role + " " + label
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{go_name}", "invalid", "start", ev)
    \t}
    \tif !#{prefix}Pre(m.shared) {
    \t\treturn muroIllegal("#{go_name}", m.shared.String(), "done", ev)
    \t}
    \tnext, err := #{prefix}Choose(m.shared, role, label)
    \tif err != nil {
    \t\treturn err
    \t}
    \tm.shared = next
    \treturn nil
    }

    // Step takes one message for a key, after the preamble.
    func (m *#{go_name}) Step(key, from, to, label string, v Value) error {
    \tev := "key=" + key + " message " + from + " " + to + " " + label + " " + v.String()
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{go_name}", "invalid", "start", ev)
    \t}
    \tif #{prefix}Pre(m.shared) {
    \t\treturn muroIllegal("#{go_name}", m.shared.String(), "shared "+#{prefix}Expected(m.shared), ev)
    \t}
    \tcur := m.shared
    \tif got, ok := m.keys[key]; ok {
    \t\tcur = got
    \t}
    \tnext, err := #{prefix}Step(cur, from, to, label, v)
    \tif err != nil {
    \t\treturn err
    \t}
    \tm.keys[key] = next
    \treturn nil
    }

    // Choose takes one choice for a key, after the preamble.
    func (m *#{go_name}) Choose(key, role, label string) error {
    \tev := "key=" + key + " choose " + role + " " + label
    \tif m == nil || !m.ready {
    \t\treturn muroIllegal("#{go_name}", "invalid", "start", ev)
    \t}
    \tif #{prefix}Pre(m.shared) {
    \t\treturn muroIllegal("#{go_name}", m.shared.String(), "shared "+#{prefix}Expected(m.shared), ev)
    \t}
    \tcur := m.shared
    \tif got, ok := m.keys[key]; ok {
    \t\tcur = got
    \t}
    \tnext, err := #{prefix}Choose(cur, role, label)
    \tif err != nil {
    \t\treturn err
    \t}
    \tm.keys[key] = next
    \treturn nil
    }

    // Done reports whether this key has reached end. A key still in the
    // preamble is not done.
    func (m *#{go_name}) Done(key string) bool {
    \tif m == nil || !m.ready || #{prefix}Pre(m.shared) {
    \t\treturn false
    \t}
    \tcur := m.shared
    \tif got, ok := m.keys[key]; ok {
    \t\tcur = got
    \t}
    \treturn #{prefix}Done(cur)
    }

    // SharedDone reports whether the shared preamble has finished.
    func (m *#{go_name}) SharedDone() bool {
    \treturn m != nil && m.ready && !#{prefix}Pre(m.shared)
    }

    // Keys returns the keys that have stepped, in lexicographic order.
    func (m *#{go_name}) Keys() []string {
    \tif m == nil || !m.ready {
    \t\treturn nil
    \t}
    \tout := make([]string, 0, len(m.keys))
    \tfor key := range m.keys {
    \t\tout = append(out, key)
    \t}
    \tsort.Strings(out)
    \treturn out
    }

    """

    {src, MapSet.new([:sort])}
  end

  defp walk({:end, _step}, acc), do: {:done, acc}

  defp walk({:msg, step, from, to, label, ty, cont}, acc) do
    case Match.ensure(ty, acc.decls, acc.reprs, acc.match) do
      {:error, msg} ->
        {:error, msg}

      {:ok, fname, match} ->
        {id, lab, acc} = alloc(:msg, %{acc | match: match})
        {dest, acc} = walk(cont, acc)

        case dest do
          {:error, _} = err ->
            err

          _ ->
            node = %{
              id: id,
              label: lab,
              kind: :msg,
              step: step,
              from: atom_s(from),
              to: atom_s(to),
              label_s: atom_s(label),
              match: fname,
              dest: dest,
              role: nil,
              arms: []
            }

            {{:state, id}, put_in(acc.nodes[id], node)}
        end
    end
  end

  defp walk({:pick, step, role, arms}, acc) do
    {id, lab, acc} = alloc(:pick, acc)

    {compiled, acc} =
      Enum.reduce(arms, {[], acc}, fn {label, cont}, {got, acc} ->
        case walk(cont, acc) do
          {:error, msg} -> {[{:error, msg}], acc}
          {dest, acc} -> {got ++ [{atom_s(label), dest}], acc}
        end
      end)

    case Enum.find(compiled, &match?({:error, _}, &1)) do
      {:error, msg} ->
        {:error, msg}

      nil ->
        node = %{
          id: id,
          label: lab,
          kind: :pick,
          step: step,
          from: nil,
          to: nil,
          label_s: nil,
          match: nil,
          dest: nil,
          role: atom_s(role),
          arms: compiled
        }

        {{:state, id}, put_in(acc.nodes[id], node)}
    end
  end

  defp walk(_other, _acc), do: {:error, "go: unsupported protocol"}

  defp alloc(kind, acc) do
    id = acc.next
    n = Map.get(acc.counts, kind, 0) + 1
    label = if(kind == :msg, do: "Msg", else: "Pick") <> Integer.to_string(n)
    {id, label, %{acc | next: id + 1, counts: Map.put(acc.counts, kind, n)}}
  end

  defp ordered(acc) do
    acc.nodes |> Map.values() |> Enum.sort_by(& &1.id)
  end

  defp atom_s(atom) when is_atom(atom), do: Atom.to_string(atom)
  defp atom_s(other), do: to_string(other)

  defp const_lines(nodes, state) do
    Enum.map_join(nodes, "", fn node ->
      name = state <> node.label
      "\t// #{name} is #{one_line(node.step)}.\n\t#{name}\n"
    end)
  end

  defp done_line(done), do: "\t// #{done} is the end of the choreography.\n\t#{done}\n"

  defp string_lines(nodes, state) do
    Enum.map_join(nodes, "", fn node ->
      "\tcase #{state}#{node.label}:\n\t\treturn #{Match.gq(Macro.underscore(node.label))}\n"
    end)
  end

  defp expect_lines(nodes, state, _prefix) do
    Enum.map_join(nodes, "", fn node ->
      "\tcase #{state}#{node.label}:\n\t\treturn #{Match.gq(expect(node))}\n"
    end)
  end

  defp step_lines(nodes, state, go, prefix, labels) do
    Enum.map_join(nodes, "", fn
      %{kind: :msg} = node ->
        dest = dest_const(node.dest, state, labels)

        """
        \tcase #{state}#{node.label}:
        \t\tif from != #{Match.gq(node.from)} || to != #{Match.gq(node.to)} || label != #{Match.gq(node.label_s)} || !#{node.match}(v, map[string]Value{}) {
        \t\t\treturn state, muroIllegal("#{go}", state.String(), #{prefix}Expected(state), ev)
        \t\t}
        \t\treturn #{dest}, nil
        """

      node ->
        """
        \tcase #{state}#{node.label}:
        \t\treturn state, muroIllegal("#{go}", state.String(), #{prefix}Expected(state), ev)
        """
    end)
  end

  defp choose_lines(nodes, state, go, labels) do
    Enum.map_join(nodes, "", fn
      %{kind: :pick} = node ->
        arms =
          Enum.map_join(node.arms, "", fn {label, dest} ->
            """
            \t\tcase #{Match.gq(label)}:
            \t\t\treturn #{dest_const(dest, state, labels)}, nil
            """
          end)

        """
        \tcase #{state}#{node.label}:
        \t\tif role != #{Match.gq(node.role)} {
        \t\t\treturn state, muroIllegal("#{go}", state.String(), #{Match.gq(expect(node))}, ev)
        \t\t}
        \t\tswitch label {
        #{arms}\t\tdefault:
        \t\t\treturn state, muroIllegal("#{go}", state.String(), #{Match.gq(expect(node))}, ev)
        \t\t}
        """

      node ->
        """
        \tcase #{state}#{node.label}:
        \t\treturn state, muroIllegal("#{go}", state.String(), #{Match.gq(expect(node))}, ev)
        """
    end)
  end

  defp preamble_fn(nil, _nodes, _state, _prefix), do: ""

  defp preamble_fn(steps, nodes, state, prefix) do
    ids =
      nodes
      |> Enum.filter(&(&1.step in steps))
      |> Enum.map(&(&1 |> then(fn n -> state <> n.label end)))

    body =
      case ids do
        [] ->
          "\treturn false"

        _ ->
          """
          \tswitch state {
          \tcase #{Enum.join(ids, ", ")}:
          \t\treturn true
          \tdefault:
          \t\treturn false
          \t}
          """
      end

    """
    func #{prefix}Pre(state #{state}) bool {
    #{body}
    }
    """
  end

  defp expect(%{kind: :msg, from: a, to: b, label_s: l}) do
    "message #{a} #{b} #{l}"
  end

  defp expect(%{kind: :pick, role: role, arms: arms}) do
    "choose #{role} " <> Enum.map_join(arms, "|", &elem(&1, 0))
  end

  defp dest_const(:done, state, _labels), do: state <> "Done"
  defp dest_const({:state, id}, state, labels), do: state <> Map.fetch!(labels, id)

  defp start_const(:done, _state, done, _labels), do: done

  defp start_const({:state, id}, state, _done, labels) do
    state <> Map.fetch!(labels, id)
  end

  defp one_line(step) do
    step |> String.replace("\n", " ") |> String.replace("*/", "")
  end
end
