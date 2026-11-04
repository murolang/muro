defmodule MuroVisor.Code do
  @moduledoc """
  Highlighted muro text for the visor.

  Spans come from `Muro.MakeupLexer`, rendered with Makeup's HTML
  classes. A session is the same text as `Muro.Session.show_proto/1`,
  broken to a width. A break is a space in the flat form, so the tokens
  stay the printer's tokens.
  """

  @width 36

  @doc "The width of a spec in the side panel, in characters."
  def width, do: @width

  @doc """
  `Muro.Session.show_proto/1`, with breaks once a line would pass `width`.

  The flat printer is returned when a clause has no layout, so the
  visor never shows a different token.
  """
  def protocol(proto, width \\ @width) when is_integer(width) and width > 0 do
    flat = Muro.Session.show_proto(proto)

    laid =
      try do
        render(proto_doc(proto), width)
      rescue
        _ -> flat
      end

    if same_tokens?(flat, laid), do: laid, else: flat
  end

  @doc """
  Makeup HTML for `source`.

  `tag` is the element around each token (`span` in HTML, `tspan` in
  SVG). `mark` is a 1-based byte column; the token covering it is
  wrapped in `class="here"`.
  """
  def highlight(source, opts \\ [])

  def highlight(source, opts) when is_binary(source) do
    tag = Keyword.get(opts, :tag, "span")
    mark = Keyword.get(opts, :mark)
    lexer = Keyword.get(opts, :lexer, Muro.MakeupLexer)

    {iodata, _pos} =
      source
      |> lex(lexer)
      |> Enum.map(fn {type, meta, text} -> {type, meta, token_text(text)} end)
      |> Enum.map_reduce(0, fn {type, meta, bin}, pos ->
        html = format_token({type, meta, bin}, tag)

        html =
          if marks?(pos, byte_size(bin), mark) do
            [?<, tag, ~s( class="here">), html, ?<, ?/, tag, ?>]
          else
            html
          end

        {html, pos + byte_size(bin)}
      end)

    IO.iodata_to_binary(iodata)
  end

  def highlight(other, opts), do: highlight(to_string(other), opts)

  @doc "A `<code>` element of highlighted `source`."
  def inline(source, class \\ "muro-code") do
    {:safe, [~s(<code class="#{escape(class)}">), highlight(source || ""), "</code>"]}
  end

  @doc "A `<pre>` element of highlighted `source`."
  def pre(source, attrs \\ []) do
    id = attrs[:id]
    id_attr = if is_binary(id), do: ~s( id="#{escape(id)}"), else: ""
    class = attrs[:class] || "muro-code"

    {:safe, ["<pre", id_attr, ~s( class="#{escape(class)}">), highlight(source || ""), "</pre>"]}
  end

  @doc """
  Source excerpts for a selection.

  `loc` is a `{line, col}`, a `{file, line, col}`, or a configuration
  `%{left: loc, right: loc}`. Each excerpt is the definition that
  contains the location. Line numbers are that definition's lines.
  The location's line is marked, and its column wears `here`.
  """
  def excerpts(book, file, loc) when is_list(book) do
    loc
    |> places(file)
    |> Enum.flat_map(fn place ->
      case excerpt(book, place) do
        nil -> []
        row -> [row]
      end
    end)
  end

  def excerpts(_book, _file, _loc), do: []

  @doc "Highlighted tokens for an SVG `<text>` element."
  def svg(source) do
    {:safe, highlight(blank(source), tag: "tspan")}
  end

  @doc """
  Highlighted tokens, safe to place inside an element.

  `lexer` is a Makeup lexer module. `nil` leaves the text plain.
  """
  def html(source, opts \\ []) do
    {:safe, highlight(blank(source), opts)}
  end

  @doc "Every excerpt from `excerpts/3`, as one safe fragment."
  def blocks(excerpts) when is_list(excerpts) do
    {:safe,
     Enum.map(excerpts, fn excerpt ->
       {:safe, inner} = source_block(excerpt)
       inner
     end)}
  end

  @doc "The `<pre>` for one excerpt map from `excerpts/3`."
  # A definition longer than this folds the tail behind "show more".
  @fold 40

  def source_block(excerpt) when is_map(excerpt) do
    {:safe,
     [
       ~s(<pre id="#{escape(excerpt.id)}" class="muro-code muro-source">),
       folded_rows(excerpt.rows),
       "</pre>"
     ]}
  end

  defp folded_rows(rows) when length(rows) <= @fold, do: Enum.map(rows, &row_html/1)

  defp folded_rows(rows) do
    {head, tail} = Enum.split(rows, @fold)
    open = if Enum.any?(tail, & &1.marked), do: " open", else: ""

    [
      Enum.map(head, &row_html/1),
      ~s(<details class="more"#{open}><summary>show more</summary>),
      Enum.map(tail, &row_html/1),
      "</details>"
    ]
  end

  defp row_html(row) do
    mark = if row.marked, do: " marked", else: ""

    [
      ~s(<span class="row#{mark}" data-line="#{row.n}">),
      ~s(<span class="ln">#{row.n}</span><code>),
      row.html,
      "</code></span>"
    ]
  end

  # A Makeup lexer may return a charlist of code points. `IO.iodata_to_binary`
  # refuses a point above 255, which an Elixir string token contains.
  defp token_text(text) when is_binary(text), do: text

  defp token_text(text) do
    case :unicode.characters_to_binary(text) do
      bin when is_binary(bin) -> bin
    end
  end

  defp lex(source, nil), do: [{nil, %{}, source}]

  defp lex(source, lexer) when is_atom(lexer) do
    lexer.lex(source, [])
  end

  defp format_token({nil, _meta, bin}, _tag), do: escape(bin)

  # A whitespace-only element is dropped unless the space is an entity.
  defp format_token({:whitespace, _meta, bin}, tag) do
    [?<, tag, ~s( class="w">), ws_entities(bin), ?<, ?/, tag, ?>]
  end

  defp format_token(token, tag) do
    Makeup.Formatters.HTML.HTMLFormatter.format_token(token, tag)
  end

  defp ws_entities(bin) do
    for <<byte <- bin>>, into: "" do
      case byte do
        ?\s -> "&#32;"
        ?\n -> "&#10;"
        ?\t -> "&#9;"
        ?\r -> "&#13;"
        _ -> <<byte>>
      end
    end
  end

  defp blank(nil), do: ""
  defp blank(source) when is_binary(source), do: source
  defp blank(source), do: to_string(source)

  defp marks?(_pos, _size, nil), do: false
  defp marks?(_pos, _size, col) when not is_integer(col) or col < 1, do: false
  defp marks?(pos, size, col), do: pos <= col - 1 and col - 1 < pos + size

  defp places({line, col}, file) when is_integer(line) and is_integer(col) and is_binary(file) do
    [%{label: nil, file: file, line: line, col: col}]
  end

  defp places({path, line, col}, _file)
       when is_binary(path) and is_integer(line) and is_integer(col) do
    [%{label: nil, file: path, line: line, col: col}]
  end

  defp places(%{left: left, right: right}, file) do
    label_places(places(left, file), "left") ++ label_places(places(right, file), "right")
  end

  defp places(%{at: at}, file), do: places(at, file)
  defp places(_other, _file), do: []

  defp label_places(places, label), do: Enum.map(places, &%{&1 | label: label})

  defp excerpt(_book, %{line: line}) when line < 1, do: nil

  defp excerpt(book, %{file: file, line: line, col: col, label: label}) do
    with {:ok, src} <- read_source(file) do
      rows =
        case extent_span(book, file, src, line, col) do
          {start, stop} -> rows_from_extent(src, start, stop, line, col)
          :lines -> rows_from_lines(book, file, src, line, col)
        end

      case rows do
        [] -> nil
        _ -> %{id: excerpt_id(label), label: label, rows: rows}
      end
    else
      _ -> nil
    end
  end

  defp extent_span(book, file, src, line, col) do
    offset = loc_to_offset(src, line, col)

    spans =
      for decl <- book,
          match?({_, _, _}, decl_pos(decl)),
          {path, _, _} = decl_pos(decl),
          same_file?(path, file),
          {a, b} = Map.get(decl, :extent, {nil, nil}),
          is_integer(a) and is_integer(b) and a <= b,
          do: {a, b}

    cond do
      spans == [] ->
        :lines

      inside = Enum.filter(spans, fn {a, b} -> a <= offset and offset < b end) ->
        if inside == [] do
          nearest_span(spans, offset)
        else
          Enum.min_by(inside, fn {a, b} -> b - a end)
        end

      true ->
        nearest_span(spans, offset)
    end
  end

  defp nearest_span(spans, offset) do
    before = Enum.filter(spans, fn {a, _b} -> a <= offset end)

    case before do
      [] -> Enum.min_by(spans, fn {a, _b} -> a end)
      some -> Enum.max_by(some, fn {a, _b} -> a end)
    end
  end

  defp rows_from_extent(src, start, stop, mark_line, mark_col) do
    start = min(max(start, 0), byte_size(src))
    stop = min(max(stop, start), byte_size(src))
    slice = binary_part(src, start, stop - start)
    {start_line, _} = Muro.Print.offset_to_loc(src, start)

    slice
    |> source_lines()
    |> Enum.with_index(start_line)
    |> Enum.map(fn {text, n} ->
      %{
        n: n,
        marked: n == mark_line,
        html: highlight(text, mark: if(n == mark_line, do: mark_col, else: nil))
      }
    end)
  end

  # Byte column, matching `Muro.Print.offset_to_loc/2`. A trailing newline
  # is the end of the last line.
  defp loc_to_offset(src, line, col) when line >= 1 and col >= 1 do
    {prior, _} = String.split(src, "\n") |> Enum.split(max(line - 1, 0))
    base = Enum.reduce(prior, 0, fn part, acc -> acc + byte_size(part) + 1 end)
    min(base + col - 1, byte_size(src))
  end

  defp loc_to_offset(src, _line, _col), do: byte_size(src)

  defp rows_from_lines(book, file, src, line, col) do
    lines = source_lines(src)
    starts = decl_lines(book, file)
    owner = owner_line(starts, line) || line
    last = excerpt_last(lines, starts, owner, line)

    if owner < 1 or last < owner or owner > length(lines) do
      []
    else
      for n <- owner..last do
        text = Enum.at(lines, n - 1) || ""

        %{
          n: n,
          marked: n == line,
          html: highlight(text, mark: if(n == line, do: col, else: nil))
        }
      end
    end
  end

  defp excerpt_id(nil), do: "detail-source"
  defp excerpt_id(label), do: "detail-source-" <> label

  defp excerpt_last(lines, starts, owner, mark) do
    raw =
      case next_line(starts, owner) do
        nil ->
          if owner_line(starts, mark), do: length(lines), else: mark

        next ->
          next - 1
      end

    last = raw |> min(length(lines)) |> trim_tail(lines, owner, mark)
    last = max(last, min(mark, length(lines)))
    min(last, length(lines))
  end

  defp trim_tail(last, lines, first, floor) do
    cond do
      last <= floor ->
        max(floor, first)

      last <= first ->
        first

      blank_or_comment?(Enum.at(lines, last - 1)) ->
        trim_tail(last - 1, lines, first, floor)

      true ->
        last
    end
  end

  defp blank_or_comment?(nil), do: true

  defp blank_or_comment?(line) do
    case String.trim_leading(line) do
      "" -> true
      "--" <> _ -> true
      _ -> false
    end
  end

  defp decl_lines(book, file) do
    book
    |> Enum.flat_map(fn decl ->
      case decl_pos(decl) do
        {path, line, _col} -> if same_file?(path, file), do: [line], else: []
        _ -> []
      end
    end)
    |> Enum.sort()
  end

  defp decl_pos(%{file: file, loc: {line, col}})
       when is_binary(file) and is_integer(line) and is_integer(col),
       do: {file, line, col}

  defp decl_pos(%{loc: {file, line, col}})
       when is_binary(file) and is_integer(line) and is_integer(col),
       do: {file, line, col}

  defp decl_pos(_other), do: nil

  defp owner_line(starts, line) do
    starts |> Enum.filter(&(&1 <= line)) |> List.last()
  end

  defp next_line(starts, owner) do
    Enum.find(starts, &(&1 > owner))
  end

  defp same_file?(left, right) when is_binary(left) and is_binary(right) do
    left == right or Path.expand(left) == Path.expand(right)
  end

  defp same_file?(_left, _right), do: false

  defp read_source("std:" <> name) do
    case Muro.Std.source(name) do
      {:ok, src} when is_binary(src) -> {:ok, src}
      _ -> :error
    end
  end

  defp read_source(file) when is_binary(file) do
    case File.read(file) do
      {:ok, src} -> {:ok, src}
      _ -> :error
    end
  end

  defp read_source(_file), do: :error

  defp source_lines(src) do
    lines = String.split(src, "\n")

    if lines != [] and List.last(lines) == "" and String.ends_with?(src, "\n") do
      List.delete_at(lines, -1)
    else
      lines
    end
  end

  defp same_tokens?(left, right), do: sigils(left) == sigils(right)

  defp sigils(src) do
    src
    |> Muro.Lexer.tokenize()
    |> Enum.flat_map(fn
      {:whitespace, _a, _b} -> []
      {kind, a, b} -> [{kind, :binary.part(src, a, b - a)}]
    end)
  end

  defp render(doc, width) do
    {text, _col} = render_doc(doc, :break, 0, 0, width)
    text
  end

  defp render_doc({:text, text}, _mode, col, _indent, _width) do
    {text, col + String.length(text)}
  end

  defp render_doc(:brk, :flat, col, _indent, _width), do: {" ", col + 1}

  defp render_doc(:brk, :break, _col, indent, _width) do
    {"\n" <> spaces(indent), indent}
  end

  defp render_doc(:sep, :flat, col, _indent, _width), do: {"", col}

  defp render_doc(:sep, :break, _col, indent, _width) do
    {"\n" <> spaces(indent), indent}
  end

  defp render_doc({:cat, docs}, mode, col, indent, width) do
    Enum.reduce(docs, {"", col}, fn doc, {acc, col} ->
      {piece, col} = render_doc(doc, mode, col, indent, width)
      {acc <> piece, col}
    end)
  end

  defp render_doc({:nest, doc}, mode, col, indent, width) do
    render_doc(doc, mode, col, indent + 2, width)
  end

  defp render_doc({:group, doc}, mode, col, indent, width) do
    flat = flatten(doc)

    if mode == :flat or col + String.length(flat) <= width do
      {flat, col + String.length(flat)}
    else
      render_doc(doc, :break, col, indent, width)
    end
  end

  defp flatten({:text, text}), do: text
  defp flatten(:brk), do: " "
  defp flatten(:sep), do: ""
  defp flatten({:cat, docs}), do: Enum.map_join(docs, &flatten/1)
  defp flatten({:nest, doc}), do: flatten(doc)
  defp flatten({:group, doc}), do: flatten(doc)

  defp spaces(n) when n > 0, do: String.duplicate(" ", n)
  defp spaces(_n), do: ""

  defp proto_doc(:end), do: text("end")
  defp proto_doc({:send, ty, s}), do: message("send", ty, s)
  defp proto_doc({:recv, ty, s}), do: message("recv", ty, s)

  defp proto_doc({:dsend, name, ty, s}) do
    group(
      cat([
        text("send (#{word(name)} : "),
        pay_doc(ty),
        text(")"),
        nest(cat([:brk, paren_doc(s)]))
      ])
    )
  end

  defp proto_doc({:drecv, name, ty, s}) do
    group(
      cat([
        text("recv (#{word(name)} : "),
        pay_doc(ty),
        text(")"),
        nest(cat([:brk, paren_doc(s)]))
      ])
    )
  end

  defp proto_doc({:esend, name, expr, s}) do
    group(
      cat([
        text("send (#{word(name)} : Nat) {#{word(name)} ≤ #{ix_text(expr)}}"),
        nest(cat([:brk, paren_doc(s)]))
      ])
    )
  end

  defp proto_doc({:erecv, name, expr, s}) do
    group(
      cat([
        text("recv (#{word(name)} : Nat) {#{word(name)} ≤ #{ix_text(expr)}}"),
        nest(cat([:brk, paren_doc(s)]))
      ])
    )
  end

  defp proto_doc({:isend, name, left, right}) do
    group(
      cat([
        text("send (#{word(name)} : Bit) on "),
        paren_doc(left),
        nest(cat([:brk, paren_doc(right)]))
      ])
    )
  end

  defp proto_doc({:irecv, name, left, right}) do
    group(
      cat([
        text("recv (#{word(name)} : Bit) on "),
        paren_doc(left),
        nest(cat([:brk, paren_doc(right)]))
      ])
    )
  end

  defp proto_doc({:choose, left, right}), do: choice("choose", left, right)
  defp proto_doc({:branch, left, right}), do: choice("branch", left, right)

  defp proto_doc({:rec, name, body}) do
    group(cat([text("rec #{word(name)}."), nest(cat([:brk, proto_doc(body)]))]))
  end

  defp proto_doc({:svar, name}), do: text(word(name))
  defp proto_doc({:sjump, target, []}), do: text(jump_name(target))

  defp proto_doc({:sjump, target, args}) when is_list(args) do
    group(cat([text(jump_name(target)) | Enum.map(args, &cat([:brk, ix_doc(&1)]))]))
  end

  defp proto_doc({:case, scrut, arms}) when is_list(arms) do
    arms_doc =
      Enum.map(arms, fn {ctor, proto} ->
        cat([:brk, text("| #{word(ctor)} => "), proto_doc(proto)])
      end)

    group(cat([text("case "), scrut_doc(scrut), nest(cat(arms_doc))]))
  end

  defp proto_doc({:sess, name, []}), do: text(word(name))

  defp proto_doc({:sess, name, args}) when is_list(args) do
    group(cat([text(word(name)) | Enum.map(args, &cat([:brk, arg_doc(&1)]))]))
  end

  defp proto_doc(other), do: text(Muro.Session.show_proto(other))

  defp message(word, ty, cont) do
    group(cat([text(word <> " "), pay_atom_doc(ty), nest(cat([:brk, paren_doc(cont)]))]))
  end

  defp choice(word, left, right) do
    group(cat([text(word <> " "), paren_doc(left), nest(cat([:brk, paren_doc(right)]))]))
  end

  defp paren_doc(proto) do
    if bare?(proto) do
      proto_doc(proto)
    else
      group(cat([text("("), proto_doc(proto), text(")")]))
    end
  end

  defp bare?(:end), do: true
  defp bare?({:svar, _}), do: true
  defp bare?({:sjump, _, _}), do: true
  defp bare?({:sess, _, _}), do: true
  defp bare?(_other), do: false

  defp pay_doc(:nat), do: text("Nat")
  defp pay_doc(:bit), do: text("Bit")
  defp pay_doc(:unit), do: text("Unit")
  defp pay_doc({:rec, []}), do: text("{}")

  defp pay_doc({:rec, fields}) when is_list(fields) do
    inner =
      fields
      |> Enum.map(fn {name, ty} -> cat([text("#{word(name)} : "), pay_doc(ty)]) end)
      |> intersperse(cat([text(","), :brk]))

    group(cat([text("{"), nest(cat([:sep, group(cat(inner))])), :sep, text("}")]))
  end

  defp pay_doc({:pair, left, right}) do
    group(cat([pay_atom_doc(left), nest(cat([:brk, text("*"), :brk, pay_atom_doc(right)]))]))
  end

  defp pay_doc({:vec, elem, expr}) do
    group(cat([text("Vec "), pay_atom_doc(elem), nest(cat([:brk, ix_doc(expr)]))]))
  end

  defp pay_doc({:dat, name, []}), do: text(word(name))

  defp pay_doc({:dat, name, args}) when is_list(args) do
    group(cat([text(word(name)) | Enum.map(args, &cat([:brk, pay_atom_doc(&1)]))]))
  end

  defp pay_doc(other), do: text(to_string(other))

  defp pay_atom_doc({:pair, _, _} = ty), do: wrap_pay(ty)
  defp pay_atom_doc({:vec, _, _} = ty), do: wrap_pay(ty)
  defp pay_atom_doc({:dat, _, [_ | _]} = ty), do: wrap_pay(ty)
  defp pay_atom_doc(ty), do: pay_doc(ty)

  defp wrap_pay(ty), do: group(cat([text("("), pay_doc(ty), text(")")]))

  defp ix_doc(expr), do: text(ix_text(expr))
  defp ix_text({:lit, n}) when is_integer(n), do: Integer.to_string(n)
  defp ix_text({:var, name}), do: word(name)
  defp ix_text(n) when is_integer(n), do: Integer.to_string(n)
  defp ix_text(other), do: word(other)

  defp arg_doc({:lit, n}) when is_integer(n), do: text(Integer.to_string(n))
  defp arg_doc({:var, name}), do: text(word(name))
  defp arg_doc({:suc, arg}), do: group(cat([text("(suc "), arg_doc(arg), text(")")]))
  defp arg_doc({:con, name, []}), do: text(word(name))

  defp arg_doc({:con, name, args}) when is_list(args) do
    group(
      cat([
        text("(" <> word(name)),
        nest(cat(Enum.map(args, &cat([:brk, arg_doc(&1)])))),
        text(")")
      ])
    )
  end

  defp arg_doc(other), do: text(word(other))

  defp scrut_doc({:name, name}), do: text(word(name))

  defp scrut_doc({:run, fun, name}) do
    group(cat([text("(" <> word(fun)), nest(cat([:brk, text(word(name))])), text(")")]))
  end

  defp scrut_doc({:run, fun, name, earlier}) when is_list(earlier) do
    args = earlier ++ [name]

    group(
      cat([
        text("(" <> word(fun)),
        nest(cat(Enum.map(args, &cat([:brk, text(word(&1))])))),
        text(")")
      ])
    )
  end

  defp scrut_doc(_other), do: text("?")

  defp jump_name({:dual, name}), do: word(name)
  defp jump_name(name), do: word(name)

  defp intersperse([], _sep), do: []
  defp intersperse([one], _sep), do: [one]

  defp intersperse([one | rest], sep) do
    [one, sep | intersperse(rest, sep)]
  end

  defp text(value), do: {:text, value}
  defp cat(docs), do: {:cat, List.flatten(docs)}
  defp group(doc), do: {:group, doc}
  defp nest(doc), do: {:nest, doc}

  defp word(name) when is_binary(name), do: name
  defp word(name) when is_atom(name) and name != nil, do: Atom.to_string(name)
  defp word(name) when is_integer(name), do: Integer.to_string(name)
  defp word(name), do: to_string(name)

  defp escape(value) do
    value
    |> to_string()
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
  end
end
