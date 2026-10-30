defmodule Muro.Toml do
  @moduledoc """
  A total reader for the TOML subset `muro.toml` and
  `[package.metadata.muro]` use.

  The subset is tables, arrays of tables, basic strings, integers,
  booleans, and empty arrays. `#` comments run to the end of the
  line, including after a value. Anything else is an error, and the
  message names the file and the line. The reader does not guess.

  A `Cargo.toml` is not a muro document. Tables other than
  `[package.metadata.muro]` and its children are skipped. Skipping
  is string-aware, so a `[` inside a Cargo string is not a table.
  The muro table itself is read with the same subset. A construct
  the subset does not include is refused there too.

  Dotted keys (`a.b = 1`), inline tables, literal strings, multiline
  strings, floats, datetimes, and non-empty arrays are outside the
  subset. Table headers may use dots (`[muro_deps.name]`,
  `[[package.metadata.muro.modules]]`).
  """

  @backends ~w(elixir c rust asm fsm exunit)
  @dep_name ~r/\A[a-z][a-z0-9_]*\z/

  @doc """
  Parse `text` as a muro manifest.

  `{:ok, keyword}` is the same shape `muro.exs` evaluates to.
  `{:error, message}` names `path` and the line.
  """
  def parse_muro(text, path \\ "muro.toml") when is_binary(text) and is_binary(path) do
    with {:ok, table} <- document(text, path, :muro) do
      to_keyword(table, path)
    end
  end

  @doc """
  Parse `[package.metadata.muro]` out of a `Cargo.toml`.

  `:none` when that table is absent. `{:ok, keyword}` is the same
  shape as `parse_muro/2`. `{:error, message}` names `path` and the
  line when the table is present and the subset refuses it, and when
  the rest of the file cannot be skipped without guessing.
  """
  def parse_cargo_metadata(text, path \\ "Cargo.toml") when is_binary(text) and is_binary(path) do
    case document(text, path, :cargo) do
      :none -> :none
      {:ok, table} -> to_keyword(table, path)
      {:error, message} -> {:error, message}
    end
  end

  @doc false
  def cargo_metadata?(text) when is_binary(text) do
    case scan(strip_bom(text), "Cargo.toml", :cargo) do
      {:ok, %{captured: true}} -> true
      {:error, _line, _message, true} -> true
      _other -> false
    end
  end

  defp document(text, path, kind) do
    case scan(strip_bom(text), path, kind) do
      {:ok, %{kind: :cargo, captured: false}} ->
        :none

      {:ok, %{root: root}} ->
        {:ok, root}

      {:error, line, message, _captured} ->
        {:error, "#{path}:#{line}: #{message}"}
    end
  end

  defp strip_bom(<<0xEF, 0xBB, 0xBF, rest::binary>>), do: rest
  defp strip_bom(text), do: text

  defp scan(bin, path, kind) do
    state = %{
      kind: kind,
      path: path,
      root: %{},
      current: [],
      captured: false
    }

    finish(items(bin, 0, byte_size(bin), 1, state), state)
  end

  defp finish({:ok, state}, _fallback), do: {:ok, state}
  defp finish({:error, line, message}, state), do: {:error, line, message, state.captured}
  defp finish({:error, line, message, captured}, _state), do: {:error, line, message, captured}

  defp items(bin, i, len, line, state) do
    case skip_ignorable(bin, i, len, line) do
      {:error, line, message} ->
        {:error, line, message, state.captured}

      {:eof, _line} ->
        {:ok, state}

      {:at, i, line} ->
        cond do
          at(bin, i) == ?[ ->
            with {:ok, parts, array?, i, line} <- header(bin, i, len, line),
                 {:ok, state} <- open_header(state, parts, array?, line),
                 {:ok, i, line} <- expect_eol(bin, i, len, line) do
              items(bin, i, len, line, state)
            else
              {:error, line, message} -> {:error, line, message, state.captured}
            end

          not capturing?(state) ->
            case skip_statement(bin, i, len, line) do
              {:ok, i, line} -> items(bin, i, len, line, state)
              {:error, line, message} -> {:error, line, message, state.captured}
            end

          true ->
            with {:ok, key, i, line} <- key_name(bin, i, len, line),
                 {:ok, i, line} <- expect_eq(bin, i, len, line),
                 {:ok, value, i, line} <- value(bin, i, len, line),
                 {:ok, state} <- put_value(state, key, value, line),
                 {:ok, i, line} <- expect_eol(bin, i, len, line) do
              items(bin, i, len, line, state)
            else
              {:error, line, message} -> {:error, line, message, state.captured}
            end
        end
    end
  end

  defp capturing?(%{kind: :muro}), do: true
  defp capturing?(%{current: :outside}), do: false
  defp capturing?(%{captured: true}), do: true
  defp capturing?(_state), do: false

  defp skip_ignorable(bin, i, len, line) do
    cond do
      i >= len ->
        {:eof, line}

      at(bin, i) in [?\s, ?\t] ->
        skip_ignorable(bin, i + 1, len, line)

      at(bin, i) == ?# ->
        case rest_of_comment(bin, i, len, line) do
          {:ok, i, line} -> skip_ignorable(bin, i, len, line)
          {:error, _, _} = err -> err
        end

      at(bin, i) == ?\n ->
        skip_ignorable(bin, i + 1, len, line + 1)

      at(bin, i) == ?\r ->
        if i + 1 < len and at(bin, i + 1) == ?\n do
          skip_ignorable(bin, i + 2, len, line + 1)
        else
          {:error, line, "bare carriage return"}
        end

      true ->
        {:at, i, line}
    end
  end

  defp rest_of_comment(bin, i, len, line) do
    cond do
      i >= len ->
        {:ok, i, line}

      at(bin, i) == ?\n ->
        {:ok, i, line}

      at(bin, i) == ?\r and i + 1 < len and at(bin, i + 1) == ?\n ->
        {:ok, i, line}

      at(bin, i) == ?\r ->
        {:error, line, "bare carriage return"}

      true ->
        rest_of_comment(bin, i + 1, len, line)
    end
  end

  defp header(bin, i, len, line) do
    {array?, i} =
      if i + 1 < len and at(bin, i + 1) == ?[ do
        {true, i + 2}
      else
        {false, i + 1}
      end

    with {:ok, i, line} <- skip_spaces(bin, i, len, line),
         {:ok, parts, i, line} <- header_keys(bin, i, len, line, []),
         {:ok, i, line} <- skip_spaces(bin, i, len, line),
         {:ok, i} <- close_header(bin, i, len, line, array?) do
      {:ok, parts, array?, i, line}
    end
  end

  defp header_keys(bin, i, len, line, acc) do
    with {:ok, part, i, line} <- header_key(bin, i, len, line) do
      acc = acc ++ [part]

      with {:ok, i, line} <- skip_spaces(bin, i, len, line) do
        if i < len and at(bin, i) == ?. do
          with {:ok, i, line} <- skip_spaces(bin, i + 1, len, line) do
            header_keys(bin, i, len, line, acc)
          end
        else
          {:ok, acc, i, line}
        end
      end
    end
  end

  defp header_key(bin, i, len, line) do
    cond do
      i >= len -> {:error, line, "unterminated table header"}
      at(bin, i) == ?" -> basic_string(bin, i + 1, len, line, [])
      bare?(at(bin, i)) -> bare(bin, i, len, line, [])
      true -> {:error, line, "expected a table name"}
    end
  end

  defp close_header(bin, i, len, line, true) do
    if i + 1 < len and at(bin, i) == ?] and at(bin, i + 1) == ?] do
      {:ok, i + 2}
    else
      {:error, line, "expected ]]"}
    end
  end

  defp close_header(bin, i, _len, line, false) do
    if i < byte_size(bin) and at(bin, i) == ?] do
      {:ok, i + 1}
    else
      {:error, line, "expected ]"}
    end
  end

  defp open_header(%{kind: :cargo} = state, parts, array?, line) do
    case cargo_relative(parts) do
      :outside ->
        {:ok, %{state | current: :outside}}

      {:inside, []} when state.captured and not array? ->
        {:error, line, "table [package.metadata.muro] is already defined"}

      {:inside, relative} ->
        state = %{state | captured: true, current: []}

        if array? do
          open_aot(state, relative, line)
        else
          open_table(state, relative, line)
        end
    end
  end

  defp open_header(%{kind: :muro} = state, parts, true, line), do: open_aot(state, parts, line)
  defp open_header(%{kind: :muro} = state, parts, false, line), do: open_table(state, parts, line)

  defp cargo_relative(["package", "metadata", "muro" | rest]), do: {:inside, rest}
  defp cargo_relative(_parts), do: :outside

  defp open_table(state, parts, line) do
    case ensure_table(state.root, parts, line) do
      {:ok, root} -> {:ok, %{state | root: root, current: parts}}
      {:error, message} -> {:error, line, message}
    end
  end

  defp open_aot(_state, [], line), do: {:error, line, "an array of tables needs a name"}

  defp open_aot(state, parts, line) do
    {parents, [name]} = Enum.split(parts, -1)

    with {:ok, root} <- ensure_table(state.root, parents, line),
         {:ok, root, index} <- append_aot(root, parents, name) do
      {:ok, %{state | root: root, current: parents ++ [name, index]}}
    else
      {:error, message} -> {:error, line, message}
    end
  end

  defp ensure_table(table, [], _line), do: {:ok, table}

  defp ensure_table(table, [name | rest], line) do
    case Map.get(table, name) do
      nil ->
        with {:ok, child} <- ensure_table(%{}, rest, line) do
          {:ok, Map.put(table, name, {:table, child, line, rest == []})}
        end

      {:table, _child, _mark, true} when rest == [] ->
        {:error, "table #{name} is already defined"}

      {:table, child, mark, false} when rest == [] ->
        {:ok, Map.put(table, name, {:table, child, mark, true})}

      {:table, child, mark, explicit} ->
        with {:ok, child} <- ensure_table(child, rest, line) do
          {:ok, Map.put(table, name, {:table, child, mark, explicit})}
        end

      _other ->
        {:error, "#{name} is already defined and is not a table"}
    end
  end

  defp append_aot(table, [], name) do
    case Map.get(table, name) do
      nil ->
        {:ok, Map.put(table, name, {:aot, [%{}], 0}), 0}

      {:aot, list, mark} ->
        list = list ++ [%{}]
        {:ok, Map.put(table, name, {:aot, list, mark}), length(list) - 1}

      _other ->
        {:error, "#{name} is already defined and is not an array of tables"}
    end
  end

  defp append_aot(table, [name | rest], leaf) do
    case Map.get(table, name) do
      {:table, child, mark, explicit} ->
        with {:ok, child, index} <- append_aot(child, rest, leaf) do
          {:ok, Map.put(table, name, {:table, child, mark, explicit}), index}
        end

      _other ->
        {:error, "#{name} is already defined and is not a table"}
    end
  end

  defp put_value(state, key, value, line) do
    case put_at(state.root, state.current, key, value) do
      {:ok, root} -> {:ok, %{state | root: root}}
      {:error, message} -> {:error, line, message}
    end
  end

  defp put_at(table, [], key, value) do
    if Map.has_key?(table, key) do
      {:error, "duplicate key #{key}"}
    else
      {:ok, Map.put(table, key, value)}
    end
  end

  defp put_at(table, [name, index | rest], key, value) when is_integer(index) do
    case Map.get(table, name) do
      {:aot, list, mark} ->
        with {:ok, child} <- put_at(Enum.at(list, index), rest, key, value) do
          {:ok, Map.put(table, name, {:aot, List.replace_at(list, index, child), mark})}
        end

      _other ->
        {:error, "#{name} is not an array of tables"}
    end
  end

  defp put_at(table, [name | rest], key, value) do
    case Map.get(table, name) do
      {:table, child, mark, explicit} ->
        with {:ok, child} <- put_at(child, rest, key, value) do
          {:ok, Map.put(table, name, {:table, child, mark, explicit})}
        end

      _other ->
        {:error, "#{name} is not a table"}
    end
  end

  defp key_name(bin, i, len, line) do
    with {:ok, part, i, line} <- one_key(bin, i, len, line) do
      i2 = skip_inline(bin, i, len)

      if i2 < len and at(bin, i2) == ?. do
        {:error, line, "dotted keys are not supported"}
      else
        {:ok, part, i, line}
      end
    end
  end

  defp one_key(bin, i, len, line) do
    cond do
      i >= len -> {:error, line, "expected a key"}
      at(bin, i) == ?" -> basic_string(bin, i + 1, len, line, [])
      bare?(at(bin, i)) -> bare(bin, i, len, line, [])
      true -> {:error, line, "expected a key"}
    end
  end

  defp bare(bin, i, len, line, acc) do
    if i < len and bare?(at(bin, i)) do
      bare(bin, i + 1, len, line, [acc, at(bin, i)])
    else
      {:ok, IO.iodata_to_binary(acc), i, line}
    end
  end

  defp bare?(c) when c in ?A..?Z or c in ?a..?z or c in ?0..?9 or c in [?_, ?-], do: true
  defp bare?(_c), do: false

  defp expect_eq(bin, i, len, line) do
    with {:ok, i, line} <- skip_spaces(bin, i, len, line) do
      if i < len and at(bin, i) == ?= do
        skip_spaces(bin, i + 1, len, line)
      else
        {:error, line, "expected ="}
      end
    end
  end

  defp value(bin, i, len, line) do
    cond do
      i >= len ->
        {:error, line, "expected a value"}

      at(bin, i) == ?" ->
        with {:ok, text, i, line} <- basic_string(bin, i + 1, len, line, []) do
          {:ok, {:string, text, line}, i, line}
        end

      at(bin, i) == ?' ->
        {:error, line, "literal strings are not supported"}

      at(bin, i) == ?[ ->
        empty_array(bin, i + 1, len, line)

      at(bin, i) == ?{ ->
        {:error, line, "inline tables are not supported"}

      at(bin, i) in [?t, ?f] ->
        boolean(bin, i, len, line)

      at(bin, i) in [?+, ?-] or at(bin, i) in ?0..?9 ->
        integer(bin, i, len, line)

      true ->
        {:error, line, "unsupported value"}
    end
  end

  defp empty_array(bin, i, len, line) do
    case skip_ignorable(bin, i, len, line) do
      {:at, i, line} ->
        if at(bin, i) == ?] do
          {:ok, {:array, [], line}, i + 1, line}
        else
          {:error, line, "only an empty array is supported"}
        end

      {:eof, line} ->
        {:error, line, "unterminated array"}

      {:error, _, _} = err ->
        err
    end
  end

  defp boolean(bin, i, len, line) do
    {word, j} = word(bin, i, len, [])

    case word do
      "true" -> {:ok, {:bool, true, line}, j, line}
      "false" -> {:ok, {:bool, false, line}, j, line}
      _other -> {:error, line, "unsupported value"}
    end
  end

  defp word(bin, i, len, acc) do
    if i < len and bare?(at(bin, i)) do
      word(bin, i + 1, len, [acc, at(bin, i)])
    else
      {IO.iodata_to_binary(acc), i}
    end
  end

  defp integer(bin, i, len, line) do
    {sign, i} =
      case at(bin, i) do
        ?+ -> {1, i + 1}
        ?- -> {-1, i + 1}
        _other -> {1, i}
      end

    {digits, i, bad?} = digits(bin, i, len, [], false)

    cond do
      bad? or digits == "" ->
        {:error, line, "invalid integer"}

      i < len and at(bin, i) in [?., ?e, ?E] ->
        {:error, line, "floats are not supported"}

      match?(<<"0", _::binary>>, digits) ->
        {:error, line, "invalid integer"}

      true ->
        {:ok, {:int, sign * String.to_integer(digits), line}, i, line}
    end
  end

  defp digits(bin, i, len, acc, bad?) do
    cond do
      i >= len ->
        {IO.iodata_to_binary(acc), i, bad?}

      at(bin, i) in ?0..?9 ->
        digits(bin, i + 1, len, [acc, at(bin, i)], bad?)

      at(bin, i) == ?_ ->
        prev = acc != []
        nxt = i + 1 < len and at(bin, i + 1) in ?0..?9
        digits(bin, i + 1, len, acc, bad? or not (prev and nxt))

      true ->
        {IO.iodata_to_binary(acc), i, bad?}
    end
  end

  defp basic_string(bin, i, len, line, acc) do
    cond do
      i >= len ->
        {:error, line, "unterminated string"}

      at(bin, i) == ?" ->
        {:ok, IO.iodata_to_binary(acc), i + 1, line}

      at(bin, i) == ?\\ ->
        escape(bin, i + 1, len, line, acc)

      at(bin, i) == ?\n ->
        {:error, line, "newline in a basic string"}

      at(bin, i) == ?\r ->
        {:error, line, "bare carriage return"}

      at(bin, i) < 0x20 ->
        {:error, line, "control character in a string"}

      true ->
        basic_string(bin, i + 1, len, line, [acc, at(bin, i)])
    end
  end

  defp escape(bin, i, len, line, acc) do
    cond do
      i >= len ->
        {:error, line, "unterminated escape"}

      at(bin, i) == ?u ->
        unicode(bin, i + 1, len, line, acc, 4)

      at(bin, i) == ?U ->
        unicode(bin, i + 1, len, line, acc, 8)

      true ->
        case escape_byte(at(bin, i)) do
          nil -> {:error, line, "unknown escape"}
          byte -> basic_string(bin, i + 1, len, line, [acc, byte])
        end
    end
  end

  defp escape_byte(?"), do: ?"
  defp escape_byte(?\\), do: ?\\
  defp escape_byte(?/), do: ?/
  defp escape_byte(?b), do: ?\b
  defp escape_byte(?f), do: ?\f
  defp escape_byte(?n), do: ?\n
  defp escape_byte(?r), do: ?\r
  defp escape_byte(?t), do: ?\t
  defp escape_byte(_other), do: nil

  defp unicode(bin, i, len, line, acc, n) do
    case hex(bin, i, len, n, []) do
      {:ok, digits, i} ->
        cp = String.to_integer(digits, 16)

        if cp in 0xD800..0xDFFF or cp > 0x10FFFF do
          {:error, line, "invalid unicode escape"}
        else
          basic_string(bin, i, len, line, [acc, <<cp::utf8>>])
        end

      :error ->
        {:error, line, "invalid unicode escape"}
    end
  end

  defp hex(_bin, i, _len, 0, acc), do: {:ok, IO.iodata_to_binary(acc), i}

  defp hex(bin, i, len, n, acc) do
    if i < len and hex?(at(bin, i)) do
      hex(bin, i + 1, len, n - 1, [acc, at(bin, i)])
    else
      :error
    end
  end

  defp hex?(c) when c in ?0..?9 or c in ?a..?f or c in ?A..?F, do: true
  defp hex?(_c), do: false

  defp expect_eol(bin, i, len, line) do
    with {:ok, i, line} <- skip_spaces(bin, i, len, line) do
      cond do
        i >= len ->
          {:ok, i, line}

        at(bin, i) == ?# ->
          with {:ok, i, line} <- rest_of_comment(bin, i, len, line) do
            expect_eol(bin, i, len, line)
          end

        at(bin, i) == ?\n ->
          {:ok, i, line}

        at(bin, i) == ?\r and i + 1 < len and at(bin, i + 1) == ?\n ->
          {:ok, i, line}

        at(bin, i) == ?\r ->
          {:error, line, "bare carriage return"}

        true ->
          {:error, line, "unexpected text after a value"}
      end
    end
  end

  defp skip_spaces(bin, i, len, line) do
    if i < len and at(bin, i) in [?\s, ?\t] do
      skip_spaces(bin, i + 1, len, line)
    else
      {:ok, i, line}
    end
  end

  defp skip_inline(bin, i, len) do
    if i < len and at(bin, i) in [?\s, ?\t], do: skip_inline(bin, i + 1, len), else: i
  end

  defp skip_statement(bin, i, len, line) do
    cond do
      i >= len ->
        {:ok, i, line}

      at(bin, i) in [?\n] ->
        {:ok, i, line}

      at(bin, i) == ?\r and i + 1 < len and at(bin, i + 1) == ?\n ->
        {:ok, i, line}

      at(bin, i) == ?\r ->
        {:error, line, "bare carriage return"}

      at(bin, i) == ?# ->
        rest_of_comment(bin, i, len, line)

      at(bin, i) == ?" and multiline?(bin, i, ?") ->
        with {:ok, i, line} <- skip_multi(bin, i + 3, len, line, ?") do
          skip_statement(bin, i, len, line)
        end

      at(bin, i) == ?" ->
        with {:ok, i, line} <- skip_basic(bin, i + 1, len, line) do
          skip_statement(bin, i, len, line)
        end

      at(bin, i) == ?' and multiline?(bin, i, ?') ->
        with {:ok, i, line} <- skip_multi(bin, i + 3, len, line, ?') do
          skip_statement(bin, i, len, line)
        end

      at(bin, i) == ?' ->
        with {:ok, i, line} <- skip_literal(bin, i + 1, len, line) do
          skip_statement(bin, i, len, line)
        end

      true ->
        skip_statement(bin, i + 1, len, line)
    end
  end

  defp multiline?(bin, i, quote) do
    i + 2 < byte_size(bin) and at(bin, i + 1) == quote and at(bin, i + 2) == quote
  end

  defp skip_basic(bin, i, len, line) do
    cond do
      i >= len -> {:error, line, "unterminated string"}
      at(bin, i) == ?" -> {:ok, i + 1, line}
      at(bin, i) == ?\\ and i + 1 < len -> skip_basic(bin, i + 2, len, line)
      at(bin, i) == ?\n -> {:error, line, "newline in a basic string"}
      true -> skip_basic(bin, i + 1, len, line)
    end
  end

  defp skip_literal(bin, i, len, line) do
    cond do
      i >= len -> {:error, line, "unterminated string"}
      at(bin, i) == ?' -> {:ok, i + 1, line}
      at(bin, i) == ?\n -> {:error, line, "newline in a literal string"}
      true -> skip_literal(bin, i + 1, len, line)
    end
  end

  defp skip_multi(bin, i, len, line, quote) do
    cond do
      i >= len ->
        {:error, line, "unterminated string"}

      at(bin, i) == ?\n ->
        skip_multi(bin, i + 1, len, line + 1, quote)

      at(bin, i) == quote and multiline?(bin, i, quote) ->
        {:ok, i + 3, line}

      true ->
        skip_multi(bin, i + 1, len, line, quote)
    end
  end

  defp at(bin, i), do: :binary.at(bin, i)

  defp to_keyword(table, path) do
    with {:ok, backend} <- top_backend(table, path),
         {:ok, pairs} <- convert(table, path, backend, []) do
      {:ok, Enum.reverse(pairs)}
    end
  end

  defp convert(table, path, backend, acc) do
    Enum.reduce_while(Map.to_list(table), {:ok, acc}, fn {key, node}, {:ok, acc} ->
      case convert_key(key, node, path, backend) do
        {:ok, pair} -> {:cont, {:ok, [pair | acc]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp convert_key("muro", {:string, value, _line}, _path, _backend), do: {:ok, {:muro, value}}

  defp convert_key("muro", node, path, _backend),
    do: bad_type(path, node, "muro", "a string")

  defp convert_key("fuel", {:int, value, _line}, _path, _backend), do: {:ok, {:fuel, value}}

  defp convert_key("fuel", node, path, _backend),
    do: bad_type(path, node, "fuel", "an integer")

  defp convert_key("backend", {:string, value, _line}, _path, _backend) do
    {:ok, atom} = backend_atom(value)
    {:ok, {:backend, atom}}
  end

  defp convert_key("backend", node, path, _backend),
    do: bad_type(path, node, "backend", "a string")

  defp convert_key("modules", {:array, [], _line}, _path, _backend), do: {:ok, {:modules, []}}

  defp convert_key("modules", {:aot, tables, _line}, path, backend) do
    with {:ok, entries} <- modules(tables, path, backend), do: {:ok, {:modules, entries}}
  end

  defp convert_key("modules", node, path, _backend),
    do: bad_type(path, node, "modules", "an array of tables")

  defp convert_key("muro_deps", {:table, child, _line, _explicit}, path, _backend) do
    with {:ok, deps} <- deps(child, path), do: {:ok, {:muro_deps, deps}}
  end

  defp convert_key("muro_deps", node, path, _backend),
    do: bad_type(path, node, "muro_deps", "a table")

  defp convert_key(key, node, path, _backend) do
    {:error, "#{path}:#{node_line(node)}: unknown key #{key}"}
  end

  defp top_backend(table, path) do
    case Map.get(table, "backend") do
      nil ->
        {:ok, nil}

      {:string, value, line} ->
        case backend_atom(value) do
          {:ok, atom} -> {:ok, atom}
          :error -> {:error, "#{path}:#{line}: unknown backend #{inspect(value)}"}
        end

      node ->
        bad_type(path, node, "backend", "a string")
    end
  end

  defp modules(tables, path, backend) do
    tables
    |> Enum.with_index(1)
    |> Enum.reduce_while({:ok, []}, fn {table, index}, {:ok, acc} ->
      case module_entry(table, index, path, backend) do
        {:ok, entry} -> {:cont, {:ok, acc ++ [entry]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp module_entry(table, index, path, default) do
    with :ok <- module_keys(table, index, path),
         {:ok, book} <- field_string(table, "book", index, path),
         {:ok, target} <- field_string(table, "target", index, path),
         {:ok, kind} <- field_kind(table, index, path, default),
         {:ok, module} <- field_module(table, index, path) do
      opts = [kind: kind]

      entry =
        if module == nil do
          {book, target, opts}
        else
          {book, module, target, opts}
        end

      {:ok, entry}
    end
  end

  defp module_keys(table, index, path) do
    case Map.keys(table) -- ["book", "target", "backend", "module"] do
      [] ->
        :ok

      [key | _] ->
        {:error, "#{path}:#{node_line(table[key])}: modules entry #{index}: unknown key #{key}"}
    end
  end

  defp field_string(table, key, index, path) do
    case Map.get(table, key) do
      {:string, value, _line} ->
        {:ok, value}

      nil ->
        {:error, "#{path}:#{entry_line(table)}: modules entry #{index}: missing #{key}"}

      node ->
        {:error, "#{path}:#{node_line(node)}: modules entry #{index}: #{key} must be a string"}
    end
  end

  defp field_kind(table, index, path, default) do
    case Map.get(table, "backend") do
      nil ->
        if default == nil do
          {:error, "#{path}:#{entry_line(table)}: modules entry #{index}: missing backend"}
        else
          {:ok, default}
        end

      {:string, value, line} ->
        case backend_atom(value) do
          {:ok, atom} ->
            {:ok, atom}

          :error ->
            {:error, "#{path}:#{line}: modules entry #{index}: unknown kind #{inspect(value)}"}
        end

      node ->
        {:error, "#{path}:#{node_line(node)}: modules entry #{index}: backend must be a string"}
    end
  end

  defp field_module(table, index, path) do
    case Map.get(table, "module") do
      nil ->
        {:ok, nil}

      {:string, value, line} ->
        if alias_string?(value) do
          {:ok, Module.concat(String.split(value, "."))}
        else
          {:error,
           "#{path}:#{line}: modules entry #{index}: module is not an alias, got: #{inspect(value)}"}
        end

      node ->
        {:error,
         "#{path}:#{node_line(node)}: modules entry #{index}: module is not an alias, got: #{inspect(elem(node, 1))}"}
    end
  end

  defp alias_string?(value),
    do: value =~ ~r/\A[A-Z][A-Za-z0-9]*(\.[A-Z][A-Za-z0-9]*)*\z/

  defp entry_line(table) do
    table
    |> Map.values()
    |> Enum.map(&node_line/1)
    |> Enum.min(fn -> 1 end)
  end

  defp deps(table, path) do
    Enum.reduce_while(Map.to_list(table), {:ok, []}, fn {name, node}, {:ok, acc} ->
      case dep(name, node, path) do
        {:ok, entry} -> {:cont, {:ok, acc ++ [entry]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp dep(name, {:table, child, line, _explicit}, path) do
    atom = if Regex.match?(@dep_name, name), do: String.to_atom(name), else: name

    with {:ok, spec} <- dep_spec(name, child, path, line) do
      {:ok, {atom, spec}}
    end
  end

  defp dep(name, node, path) do
    {:error, "#{path}:#{node_line(node)}: muro_deps entry #{name} must be a table"}
  end

  defp dep_spec(name, table, path, line) do
    unknown = Map.keys(table) -- ["git", "tag", "ref", "root", "hex", "requirement"]

    cond do
      unknown != [] ->
        key = hd(unknown)

        {:error, "#{path}:#{node_line(table[key])}: muro_deps entry #{name}: unknown key #{key}"}

      Map.has_key?(table, "git") and Map.has_key?(table, "hex") ->
        {:error, "#{path}:#{line}: muro_deps entry #{name}: git and hex are both set"}

      Map.has_key?(table, "git") ->
        git_spec(name, table, path)

      Map.has_key?(table, "hex") ->
        hex_spec(name, table, path)

      true ->
        {:error, "#{path}:#{line}: muro_deps entry #{name}: unknown source"}
    end
  end

  defp git_spec(name, table, path) do
    with {:ok, url} <- dep_string(table, "git", name, path),
         {:ok, opts} <- git_opts(table, name, path) do
      {:ok, {:git, url, opts}}
    end
  end

  defp git_opts(table, name, path) do
    Enum.reduce_while(["tag", "ref", "root"], {:ok, []}, fn key, {:ok, opts} ->
      case Map.get(table, key) do
        nil ->
          {:cont, {:ok, opts}}

        {:string, value, _line} ->
          {:cont, {:ok, opts ++ [{String.to_atom(key), value}]}}

        node ->
          {:halt,
           {:error,
            "#{path}:#{node_line(node)}: muro_deps entry #{name}: #{key} must be a string"}}
      end
    end)
  end

  defp hex_spec(name, table, path) do
    with {:ok, package} <- dep_string(table, "hex", name, path),
         {:ok, requirement} <- dep_string(table, "requirement", name, path) do
      {:ok, {:hex, package, requirement}}
    end
  end

  defp dep_string(table, key, name, path) do
    case Map.get(table, key) do
      {:string, value, _line} ->
        {:ok, value}

      nil ->
        {:error, "#{path}:#{entry_line(table)}: muro_deps entry #{name}: missing #{key}"}

      node ->
        {:error, "#{path}:#{node_line(node)}: muro_deps entry #{name}: #{key} must be a string"}
    end
  end

  defp node_line({:string, _, line}), do: line
  defp node_line({:int, _, line}), do: line
  defp node_line({:bool, _, line}), do: line
  defp node_line({:array, _, line}), do: line
  defp node_line({:table, _, line, _}), do: line
  defp node_line({:aot, _, line}), do: line
  defp node_line(_other), do: 1

  defp backend_atom(value) when value in @backends, do: {:ok, String.to_atom(value)}
  defp backend_atom(_value), do: :error

  defp bad_type(path, node, key, expected) do
    {:error, "#{path}:#{node_line(node)}: #{key} must be #{expected}"}
  end
end
