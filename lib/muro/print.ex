defmodule Muro.Print do
  @moduledoc """
  Surface syntax for de Bruijn terms and source locations.

  Names are newest-first, like the checker's context: index 0 is the
  nearest binder. Binder names stored on Π / λ are used when printing
  those binders; free variables use the supplied environment.
  """

  @type loc :: {pos_integer(), pos_integer()}

  @doc "1-based `{line, column}` for a UTF-8 byte offset into `src`."
  def offset_to_loc(src, offset) when is_binary(src) and is_integer(offset) do
    n = min(max(offset, 0), byte_size(src))

    # A trailing newline is the end of the last line, not a line past it.
    n =
      if n == byte_size(src) and n > 0 and binary_part(src, n - 1, 1) == "\n",
        do: n - 1,
        else: n

    prefix = binary_part(src, 0, n)
    parts = String.split(prefix, "\n")
    {length(parts), byte_size(List.last(parts)) + 1}
  end

  def loc_prefix({line, col}) when is_integer(line) and is_integer(col), do: "#{line}:#{col}: "

  def loc_prefix({file, line, col}) when is_binary(file) and is_integer(line) and is_integer(col),
    do: "#{file}:#{line}:#{col}: "

  def loc_prefix(_), do: ""

  @doc "Pretty-print a de Bruijn term. `names` is newest-first."
  def term(t, names \\ []), do: fmt(t, names, :none)

  @doc """
  One line per context entry, oldest first: `n : Nat`.
  `gamma` and `names` are newest-first and the same length.
  """
  def context(gamma, names) do
    Enum.zip(names, gamma)
    |> Enum.reverse()
    |> Enum.map(fn {name, {q, ty}} -> "#{qty_mark(q)}#{name} : #{term(ty, names)}" end)
  end

  def hole_message(loc, gamma, names, expected) do
    ctx =
      case context(gamma, names) do
        [] -> "context: (empty)"
        lines -> "context:\n" <> Enum.map_join(lines, "\n", &("  " <> &1))
      end

    goal =
      case expected do
        nil -> "expected: (none; infer)"
        ty -> "expected: #{term(ty, names)}"
      end

    loc_prefix(loc) <> "unsolved hole\n#{goal}\n#{ctx}"
  end

  @doc "Number of Unicode scalars in a UTF-8 binary. Not grapheme clusters."
  def scalar_count(bin) when is_binary(bin) do
    length(:unicode.characters_to_list(bin))
  end

  @doc """
  A string literal. `\\\\`, `\\\"`, and a newline are escaped. Other
  controls and DEL are `\\\\u{hex}`. Every other scalar is itself.
  """
  def quote_string(bin) when is_binary(bin) do
    body =
      bin
      |> :unicode.characters_to_list()
      |> Enum.map_join(&quote_scalar/1)

    "\"" <> body <> "\""
  end

  defp quote_scalar(?\\), do: "\\\\"
  defp quote_scalar(?"), do: "\\\""
  defp quote_scalar(?\n), do: "\\n"

  defp quote_scalar(n) when n < 0x20 or n == 0x7F,
    do: "\\u{" <> Integer.to_string(n, 16) <> "}"

  defp quote_scalar(n), do: <<n::utf8>>

  # -- format ----------------------------------------------------------------

  defp fmt({:hole, _}, _, _), do: "?"
  defp fmt(:hole, _, _), do: "?"
  defp fmt(:typ, _, _), do: "Type"
  defp fmt(:nat, _, _), do: "Nat"
  defp fmt(:ze, _, _), do: "0"
  defp fmt({:nat, n}, _, _) when is_integer(n), do: Integer.to_string(n)
  defp fmt(:unit, _, _), do: "Unit"
  defp fmt(:one, _, _), do: "tt"
  defp fmt(:empty, _, _), do: "Empty"
  defp fmt(:atom, _, _), do: "Atom"
  defp fmt({:atom, n}, _, _), do: ":#{n}"
  defp fmt(:string, _, _), do: "String"
  defp fmt({:slit, bin}, _, _), do: quote_string(bin)
  defp fmt({:scat, a, b}, names, _), do: "strCat #{fmt(a, names, :app)} #{fmt(b, names, :app)}"
  defp fmt({:slen, a}, names, _), do: "strLen #{fmt(a, names, :app)}"
  defp fmt({:seq, a, b}, names, _), do: "strEq #{fmt(a, names, :app)} #{fmt(b, names, :app)}"
  defp fmt(:rfl, _, _), do: "refl"
  defp fmt(:i64, _, _), do: "I64"
  defp fmt(:f32ty, _, _), do: "F32"

  defp fmt({:var, i}, names, _) when is_integer(i) do
    case Enum.at(names, i) do
      nil -> "##{i}"
      name -> name
    end
  end

  defp fmt({:def, n}, _, _), do: n

  defp fmt({:su, t}, names, _) do
    "suc(#{fmt(t, names, :none)})"
  end

  defp fmt({:pi, q, a, x, b}, names, prec) do
    wrap(
      prec,
      :arrow,
      "Π (#{qty_mark(q)}#{x} : #{fmt(a, names, :none)}) → #{fmt(b, [x | names], :arrow)}"
    )
  end

  defp fmt({:lam, q, a, x, t}, names, prec) do
    wrap(
      prec,
      :arrow,
      "λ (#{qty_mark(q)}#{x} : #{fmt(a, names, :none)}) → #{fmt(t, [x | names], :arrow)}"
    )
  end

  defp fmt({:app, f, a}, names, prec) do
    {h, args} = spine(f, [a])
    printed = Enum.map_join([h | args], " ", &fmt(&1, names, :app))
    wrap(prec, :app, printed)
  end

  defp fmt({:prod, a, b}, names, prec) do
    wrap(prec, :prod, "#{fmt(a, names, :prod)} × #{fmt(b, names, :prod)}")
  end

  defp fmt({:pair, a, b}, names, _) do
    "(#{fmt(a, names, :none)}, #{fmt(b, names, :none)})"
  end

  defp fmt({:letp, e, t}, names, _) do
    "let (a, b) = #{fmt(e, names, :none)} in #{fmt(t, ["b", "a" | names], :none)}"
  end

  defp fmt({:idt, a, l, r}, names, _) do
    "{#{fmt(l, names, :none)} ≡ #{fmt(r, names, :none)} : #{fmt(a, names, :none)}}"
  end

  defp fmt({:rwt, e, p, t}, names, _) do
    "rewrite #{fmt(e, names, :none)} motive (λ z → #{fmt(p, ["z" | names], :none)}) in #{fmt(t, names, :none)}"
  end

  defp fmt({:ann, e, a}, names, _) do
    "{#{fmt(e, names, :none)} : #{fmt(a, names, :none)}}"
  end

  defp fmt({:mnat, e, p, z, s}, names, _) do
    "match #{fmt(e, names, :none)} motive (λ x → #{fmt(p, ["x" | names], :none)}) | 0 => #{fmt(z, names, :none)} | suc n => #{fmt(s, ["n" | names], :none)}"
  end

  defp fmt({:memp, e, p}, names, _) do
    "matchEmpty #{fmt(e, names, :none)} motive (λ x → #{fmt(p, ["x" | names], :none)})"
  end

  defp fmt({:munit, e, p, u}, names, _) do
    "match #{fmt(e, names, :none)} motive (λ x → #{fmt(p, ["x" | names], :none)}) | tt => #{fmt(u, names, :none)}"
  end

  defp fmt({:matom, e, p, bs}, names, _) do
    branches =
      Enum.map_join(bs, " ", fn {name, body} ->
        "| :#{name} => #{fmt(body, names, :none)}"
      end)

    "match #{fmt(e, names, :none)} motive (λ x → #{fmt(p, ["x" | names], :none)}) #{branches}"
  end

  defp fmt({:mdata, e, p, bs}, names, _) do
    branches =
      Enum.map_join(bs, " ", fn {cname, ar, body} ->
        xs = for i <- 0..(ar - 1)//1, do: "x#{i}"
        env = Enum.reverse(xs) ++ names
        "| #{cname} #{Enum.join(xs, " ")} => #{fmt(body, env, :none)}"
      end)

    "match #{fmt(e, names, :none)} motive (λ x → #{fmt(p, ["x" | names], :none)}) #{branches}"
  end

  defp fmt({:nu, f}, names, _) do
    "ν (x : _) → #{fmt(f, ["x" | names], :none)}"
  end

  defp fmt({:unf, s, f}, names, _) do
    "unfold #{fmt(s, names, :app)} #{fmt(f, names, :app)}"
  end

  defp fmt({:ucons, s}, names, _) do
    "uncons #{fmt(s, names, :app)}"
  end

  defp fmt({:bisim, s, t}, names, _) do
    "#{fmt(s, names, :none)} ~ #{fmt(t, names, :none)}"
  end

  defp fmt({:tensor, d, s}, names, _) do
    "Tensor #{fmt(d, names, :app)} #{fmt(s, names, :app)}"
  end

  defp fmt({:addi, x, y}, names, _), do: "addi #{fmt(x, names, :app)} #{fmt(y, names, :app)}"
  defp fmt({:muli, x, y}, names, _), do: "muli #{fmt(x, names, :app)} #{fmt(y, names, :app)}"
  defp fmt({:addt, t, u}, names, _), do: "addt #{fmt(t, names, :app)} #{fmt(u, names, :app)}"
  defp fmt({:toi64, t}, names, _), do: "toI64 #{fmt(t, names, :app)}"
  defp fmt({:packi, x, y}, names, _), do: "packI #{fmt(x, names, :app)} #{fmt(y, names, :app)}"

  defp fmt({:word, op, args}, names, _) do
    head = word_head(op)

    case args do
      [] -> head
      _ -> Enum.map_join([head | Enum.map(args, &fmt(&1, names, :app))], " ", & &1)
    end
  end

  defp fmt(other, _, _), do: inspect(other)

  defp word_head({:ty, :u8}), do: "U8"
  defp word_head({:ty, :u32}), do: "U32"
  defp word_head({:ty, :u64}), do: "U64"
  defp word_head({:lit, k, n}), do: "#{word_kind(k)}##{n}"
  defp word_head({:of, :u8}), do: "toU8"
  defp word_head({:of, :u32}), do: "toU32"
  defp word_head({:of, :u64}), do: "toU64"
  defp word_head({:of, :i64}), do: "toI64"
  defp word_head(:ton), do: "toNat"
  defp word_head(:add), do: "addi"
  defp word_head(:sub), do: "subi"
  defp word_head(:mul), do: "muli"
  defp word_head(:cadd), do: "addc"
  defp word_head(:csub), do: "subc"
  defp word_head(:cmul), do: "mulc"
  defp word_head(:div), do: "divi"
  defp word_head(:rem), do: "remi"
  defp word_head(:eq), do: "eqi"
  defp word_head(:lt), do: "lti"
  defp word_head(:le), do: "lei"
  defp word_head(:and), do: "andi"
  defp word_head(:or), do: "ori"
  defp word_head(:xor), do: "xori"
  defp word_head(:not), do: "noti"
  defp word_head(:shl), do: "shli"
  defp word_head(:shr), do: "shri"
  defp word_head({:cast, :u8}), do: "asU8"
  defp word_head({:cast, :u32}), do: "asU32"
  defp word_head({:cast, :u64}), do: "asU64"
  defp word_head({:cast, :i64}), do: "asI64"
  defp word_head(:bool), do: "WBool"
  defp word_head(true), do: "wtrue"
  defp word_head(false), do: "wfalse"
  defp word_head(:opt), do: "Opt"
  defp word_head({:optk, k}), do: "Opt #{word_kind(k)}"
  defp word_head(:some), do: "wsome"
  defp word_head(:none), do: "wnone"

  defp word_kind(:u8), do: "U8"
  defp word_kind(:u32), do: "U32"
  defp word_kind(:u64), do: "U64"
  defp word_kind(:i64), do: "I64"

  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(h, acc), do: {h, acc}

  defp qty_mark(:erased), do: "-"
  defp qty_mark(:reuse), do: "+"
  defp qty_mark(:linear), do: "%1 "
  defp qty_mark(_), do: ""

  defp wrap(:none, _, s), do: s
  defp wrap(:arrow, :arrow, s), do: s
  defp wrap(:app, :app, s), do: "(#{s})"
  defp wrap(:app, _, s), do: s
  defp wrap(:prod, :prod, s), do: "(#{s})"
  defp wrap(_, _, s), do: "(#{s})"
end
