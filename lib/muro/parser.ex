defmodule Muro.Parser do
  @moduledoc """
  Tiny .muro parser. Agda-looking: Π, λ, match, explicit types.
  """

  alias Muro.Print

  @src_key {__MODULE__, :src}

  def parse(src) when is_binary(src) do
    Process.put(@src_key, src)

    try do
      case parse_book(skip(src)) do
        {:ok, book, rest} ->
          rest = skip(rest)

          if rest == "" do
            {:ok, book}
          else
            {:error, err(rest, "trailing input: #{String.slice(rest, 0, 40)}")}
          end

        other ->
          other
      end
    after
      Process.delete(@src_key)
    end
  end

  defp here(rest) do
    src = Process.get(@src_key, "")
    Print.offset_to_loc(src, max(0, byte_size(src) - byte_size(rest)))
  end

  defp err(rest, msg), do: "#{Print.loc_prefix(here(rest))}#{msg}"

  defp parse_book(s), do: parse_book(s, [])

  defp parse_book(s, acc) do
    s = skip(s)

    cond do
      s == "" ->
        {:ok, Enum.reverse(acc), ""}

      nu_start?(s) ->
        case parse_nu(s) do
          {:ok, rest} -> parse_book(rest, acc)
          err -> err
        end

      import_start?(s) ->
        case parse_import(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      data_start?(s) ->
        case parse_data(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      true ->
        case parse_def(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end
    end
  end

  defp nu_start?(s), do: word_kw?(s, "ν") or word_kw?(s, "nu")

  defp import_start?(s), do: word_kw?(s, "import")

  defp parse_import(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "import"),
         {:ok, path, rest} <- parse_string(skip(rest)) do
      {:ok, %{kind: :import, path: path, loc: loc}, rest}
    end
  end

  defp parse_string(s) do
    case s do
      "\"" <> rest -> read_string(rest, "")
      _ -> {:error, err(s, "expected a string")}
    end
  end

  defp read_string("\"" <> rest, acc), do: {:ok, acc, rest}
  defp read_string("\n" <> _ = s, _acc), do: {:error, err(s, "unclosed string")}
  defp read_string("", _acc), do: {:error, err("", "unclosed string")}

  defp read_string(s, acc) do
    {c, rest} = String.split_at(s, 1)
    read_string(rest, acc <> c)
  end

  # v1: only `ν Stream (A : Type) : Type where uncons : Stream A → A × Stream A`.
  # Stream is primitive; the block is checked for shape and then dropped.
  defp parse_nu(s) do
    rest = s |> skip() |> eat_kw(["ν", "nu"])

    with {:ok, name, rest} <- ident(skip(rest)),
         :ok <- if(name == "Stream", do: :ok, else: {:error, "v1 only supports ν Stream"}),
         {:ok, {_q, _x, a}, rest} <- parse_binder(rest),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "where"),
         {:ok, ctor, rest} <- ident(skip(rest)),
         :ok <- if(ctor == "uncons", do: :ok, else: {:error, "expected uncons"}),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, _ctor_ty, rest} <- parse_term(skip(rest), 0) do
      _ = {a, ty}
      {:ok, rest}
    end
  end

  defp data_start?(s), do: word_kw?(s, "data")

  # Parameters before `:`. Index telescope after `:` before Type.
  defp parse_data(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "data"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, params, rest} <- parse_param_binders(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, sort, rest} <- parse_term(skip(rest), 0),
         {:ok, indices} <- peel_indices(sort),
         {:ok, rest} <- kw(skip(rest), "where"),
         {:ok, ctors, rest} <- parse_ctors(skip(rest), []) do
      {:ok, %{kind: :data, name: name, params: params, indices: indices, ctors: ctors, loc: loc},
       rest}
    end
  end

  defp peel_indices(:typ), do: {:ok, []}

  defp peel_indices({:pi, q, a, x, b}) do
    with {:ok, rest} <- peel_indices(b), do: {:ok, [{q, x, a} | rest]}
  end

  defp peel_indices(_), do: {:error, "data sort must end in Type"}

  defp parse_param_binders(s) do
    s = skip(s)

    if has_prefix?(s, "(") do
      with {:ok, b, rest} <- parse_binder(s),
           {:ok, bs, rest} <- parse_param_binders(rest) do
        {:ok, [b | bs], rest}
      end
    else
      {:ok, [], s}
    end
  end

  defp parse_ctors(s, acc) do
    s = skip(s)

    cond do
      s == "" ->
        {:ok, Enum.reverse(acc), s}

      word_kw?(s, "def") or word_kw?(s, "data") or nu_start?(s) ->
        {:ok, Enum.reverse(acc), s}

      true ->
        with {:ok, cname, rest} <- ident(s),
             {:ok, rest} <- tok(skip(rest), ":"),
             {:ok, ty, rest} <- parse_term(skip(rest), 0) do
          parse_ctors(rest, [%{name: cname, type: ty} | acc])
        end
    end
  end

  defp parse_def(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "def"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, tag, rest} <- parse_mode(skip(rest)),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, body, rest} <- parse_term(skip(rest), 0) do
      {:ok, Map.merge(%{name: name, type: ty, body: body, loc: loc}, tag), rest}
    end
  end

  # tag ::= "run" "internal"? | "spec" | "evidence"
  defp parse_mode(s) do
    s = skip(s)

    cond do
      word_kw?(s, "spec") ->
        {:ok, %{mode: :spec}, after_kw(s, "spec")}

      word_kw?(s, "evidence") ->
        {:ok, %{mode: :evidence}, after_kw(s, "evidence")}

      word_kw?(s, "run") ->
        rest = after_kw(s, "run")
        rest_s = skip(rest)

        if word_kw?(rest_s, "internal") do
          {:ok, %{mode: :run, export: false}, after_kw(rest_s, "internal")}
        else
          {:ok, %{mode: :run, export: true}, rest}
        end

      true ->
        {:error, "expected run, run internal, spec, or evidence"}
    end
  end

  defp word_kw?(s, w) do
    has_prefix?(s, w) and not ident_continue?(s, w)
  end

  defp ident_continue?(s, w) do
    rest = after_kw(s, w)
    rest != "" and ident_char?(String.first(rest))
  end

  # Pratt-ish: apps are juxtaposition, arrows bind looser via Π/λ.
  defp parse_term(s, min_bp) do
    with {:ok, left, rest} <- parse_atom(skip(s)) do
      parse_infix(rest, left, min_bp)
    end
  end

  defp parse_infix(s, left, min_bp) do
    s0 = skip(s)

    cond do
      arrow_tok?(s0) and min_bp <= 5 ->
        with {:ok, rest} <- eat_arrow(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 5) do
          parse_infix(rest, {:pi, :affine, left, "_", right}, min_bp)
        end

      times_tok?(s0) and min_bp <= 15 ->
        with {:ok, rest} <- eat_times(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 16) do
          parse_infix(rest, {:prod, left, right}, min_bp)
        end

      sum_tok?(s0) and min_bp <= 12 ->
        with {:ok, rest} <- eat_sum(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 13) do
          parse_infix(rest, {:app, {:app, {:var, "Either"}, left}, right}, min_bp)
        end

      cons_tok?(s0) and min_bp <= 18 ->
        with {:ok, rest} <- eat_cons(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 18) do
          parse_infix(rest, {:app, {:app, {:var, "cons"}, left}, right}, min_bp)
        end

      bisim_tok?(s0) and min_bp <= 10 ->
        with {:ok, rest} <- eat_bisim(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 11) do
          parse_infix(rest, {:bisim, left, right}, min_bp)
        end

      starts_atom?(s0) and min_bp <= 20 and not ctor_decl_start?(s, s0) ->
        with {:ok, arg, rest} <- parse_atom(s0) do
          parse_infix(rest, {:app, left, arg}, min_bp)
        end

      true ->
        {:ok, left, s}
    end
  end

  defp arrow_tok?(s) do
    (has_prefix?(s, "→") or has_prefix?(s, "->")) and not has_prefix?(s, "=>")
  end

  defp eat_arrow(s) do
    cond do
      has_prefix?(s, "→") -> {:ok, after_kw(s, "→")}
      has_prefix?(s, "->") -> {:ok, after_kw(s, "->")}
      true -> {:error, "expected →"}
    end
  end

  defp times_tok?(s), do: has_prefix?(s, "×") or has_prefix?(s, "*")

  defp eat_times(s) do
    cond do
      has_prefix?(s, "×") -> {:ok, after_kw(s, "×")}
      has_prefix?(s, "*") -> {:ok, after_kw(s, "*")}
      true -> {:error, "expected ×"}
    end
  end

  defp sum_tok?(s), do: has_prefix?(s, "⊎")

  defp eat_sum(s) do
    if has_prefix?(s, "⊎"), do: {:ok, after_kw(s, "⊎")}, else: {:error, "expected ⊎"}
  end

  defp bisim_tok?(s), do: has_prefix?(s, "~") and not ident_char?(after_kw(s, "~"))

  defp eat_bisim(s) do
    if bisim_tok?(s), do: {:ok, after_kw(s, "~")}, else: {:error, "expected ~"}
  end

  defp cons_tok?(s), do: has_prefix?(s, "::")

  defp eat_cons(s) do
    if cons_tok?(s), do: {:ok, after_kw(s, "::")}, else: {:error, "expected ::"}
  end

  # Next constructor in a data block: `name : type`, not `:=` or `::`.
  # `ident :` at the start of a line ends an application: it is the next
  # constructor declaration of a data block. On the same line it is an
  # argument (`{0 == f x : Nat}`).
  defp ctor_decl_start?(s, s0) do
    skipped = binary_part(s, 0, byte_size(s) - byte_size(s0))

    String.contains?(skipped, "\n") and
      case ident(s0) do
        {:ok, _, rest} ->
          rest = skip(rest)
          has_prefix?(rest, ":") and not has_prefix?(rest, ":=") and not has_prefix?(rest, "::")

        _ ->
          false
      end
  end

  defp starts_atom?(s) do
    s = skip(s)

    cond do
      word_kw?(s, "motive") ->
        false

      word_kw?(s, "in") ->
        false

      word_kw?(s, "def") ->
        false

      word_kw?(s, "where") ->
        false

      word_kw?(s, "data") ->
        false

      true ->
        case s do
          <<c, _::binary>>
          when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?( or
                 c == ?{ or c == ?[ or c == ?? or c == ?: ->
            atom_lit?(s) or c != ?:

          _ ->
            false
        end
    end
  end

  defp parse_atom(s) do
    s = skip(s)

    cond do
      atom_lit?(s) ->
        parse_atom_lit(s)

      word_kw?(s, "Atom") ->
        {:ok, :atom, after_kw(s, "Atom")}

      has_prefix?(s, "Type") ->
        {:ok, :typ, after_kw(s, "Type")}

      has_prefix?(s, "Nat") ->
        {:ok, :nat, after_kw(s, "Nat")}

      word_kw?(s, "I64") ->
        {:ok, :i64, after_kw(s, "I64")}

      word_kw?(s, "F32") ->
        {:ok, :f32ty, after_kw(s, "F32")}

      word_kw?(s, "Tensor") ->
        parse_binary(s, "Tensor", :tensor)

      word_kw?(s, "addi") ->
        parse_binary(s, "addi", :addi)

      word_kw?(s, "muli") ->
        parse_binary(s, "muli", :muli)

      word_kw?(s, "addt") ->
        parse_binary(s, "addt", :addt)

      word_kw?(s, "toI64") ->
        parse_unary(s, "toI64", :toi64)

      word_kw?(s, "packI") ->
        parse_binary(s, "packI", :packi)

      has_prefix?(s, "Unit") ->
        {:ok, :unit, after_kw(s, "Unit")}

      has_prefix?(s, "Empty") ->
        {:ok, :empty, after_kw(s, "Empty")}

      has_prefix?(s, "refl") ->
        {:ok, :rfl, after_kw(s, "refl")}

      has_prefix?(s, "tt") ->
        {:ok, :one, after_kw(s, "tt")}

      has_prefix?(s, "?") ->
        {:ok, {:hole, here(s)}, after_kw(s, "?")}

      has_prefix?(s, "0") ->
        {:ok, :ze, after_kw(s, "0")}

      has_prefix?(s, "suc") ->
        parse_suc(s)

      has_prefix?(s, "[]") ->
        {:ok, {:var, "nil"}, after_kw(s, "[]")}

      word_kw?(s, "Stream") ->
        parse_stream(s)

      word_kw?(s, "Always") ->
        parse_always(s)

      word_kw?(s, "bisim") ->
        parse_bisim(s)

      word_kw?(s, "unfold") ->
        parse_unf(s)

      word_kw?(s, "uncons") ->
        parse_ucons(s)

      word_kw?(s, "let") ->
        parse_letp(s)

      # fst / snd are sugar for let: fst t = let (a, b) = t in a.
      word_kw?(s, "fst") ->
        with {:ok, e, rest} <- parse_unary_arg(s, "fst") do
          {:ok, fst_sugar(e), rest}
        end

      word_kw?(s, "snd") ->
        with {:ok, e, rest} <- parse_unary_arg(s, "snd") do
          {:ok, snd_sugar(e), rest}
        end

      word_kw?(s, "head") ->
        with {:ok, e, rest} <- parse_unary_arg(s, "head") do
          {:ok, fst_sugar({:ucons, e}), rest}
        end

      word_kw?(s, "tail") ->
        with {:ok, e, rest} <- parse_unary_arg(s, "tail") do
          {:ok, snd_sugar({:ucons, e}), rest}
        end

      word_kw?(s, "Π") or word_kw?(s, "Pi") ->
        parse_pi(s)

      word_kw?(s, "λ") or word_kw?(s, "lam") ->
        parse_lam(s)

      has_prefix?(s, "matchEmpty") ->
        parse_memp(s)

      has_prefix?(s, "match") ->
        parse_match(s)

      has_prefix?(s, "rewrite") ->
        parse_rwt(s)

      first_char(s) == ?{ ->
        parse_idt(s)

      first_char(s) == ?( ->
        with {:ok, rest} <- tok(s, "("),
             {:ok, t, rest} <- parse_term(skip(rest), 0) do
          rest1 = skip(rest)

          if has_prefix?(rest1, ",") do
            with {:ok, rest} <- tok(rest1, ","),
                 {:ok, u, rest} <- parse_term(skip(rest), 0),
                 {:ok, rest} <- tok(skip(rest), ")") do
              {:ok, {:pair, t, u}, rest}
            end
          else
            with {:ok, rest} <- tok(rest1, ")") do
              {:ok, t, rest}
            end
          end
        end

      true ->
        case ident(s) do
          {:ok, name, rest} -> {:ok, {:var_or_def, name}, rest}
          _ -> {:error, err(s, "expected term")}
        end
    end
    |> resolve_name()
  end

  defp resolve_name({:ok, {:var_or_def, name}, rest}) do
    # defs vs vars are distinguished at to_db / check time: unknown names
    # become {:def, name} if not bound. Parser emits {:var, name}; Check
    # treats free names as defs when converting.
    {:ok, {:var, name}, rest}
  end

  defp resolve_name(other), do: other

  defp parse_suc(s) do
    with {:ok, rest} <- kw(s, "suc") do
      rest = skip(rest)

      if has_prefix?(rest, "(") do
        with {:ok, rest} <- tok(rest, "("),
             {:ok, t, rest} <- parse_term(skip(rest), 0),
             {:ok, rest} <- tok(skip(rest), ")") do
          {:ok, {:su, t}, rest}
        end
      else
        with {:ok, t, rest} <- parse_atom(rest) do
          {:ok, {:su, t}, rest}
        end
      end
    end
  end

  defp parse_stream(s) do
    with {:ok, rest} <- kw(s, "Stream"),
         {:ok, a, rest} <- parse_atom(skip(rest)) do
      {:ok, {:stream, a}, rest}
    end
  end

  defp parse_always(s) do
    with {:ok, rest} <- kw(s, "Always"),
         {:ok, a, rest} <- parse_atom(skip(rest)),
         {:ok, p, rest} <- parse_atom(skip(rest)),
         {:ok, st, rest} <- parse_atom(skip(rest)) do
      {:ok, {:always, a, p, st}, rest}
    end
  end

  defp parse_bisim(s) do
    with {:ok, rest} <- kw(s, "bisim"),
         {:ok, a, rest} <- parse_atom(skip(rest)),
         {:ok, b, rest} <- parse_atom(skip(rest)) do
      {:ok, {:bisim, a, b}, rest}
    end
  end

  defp parse_unf(s) do
    with {:ok, rest} <- kw(s, "unfold"),
         {:ok, seed, rest} <- parse_atom(skip(rest)),
         {:ok, f, rest} <- parse_atom(skip(rest)) do
      {:ok, {:unf, seed, f}, rest}
    end
  end

  defp parse_ucons(s) do
    parse_unary(s, "uncons", :ucons)
  end

  defp parse_unary(s, w, tag) do
    with {:ok, e, rest} <- parse_unary_arg(s, w) do
      {:ok, {tag, e}, rest}
    end
  end

  defp parse_binary(s, w, tag) do
    with {:ok, rest} <- kw(s, w),
         {:ok, a, rest} <- parse_atom(skip(rest)),
         {:ok, b, rest} <- parse_atom(skip(rest)) do
      {:ok, {tag, a, b}, rest}
    end
  end

  defp parse_unary_arg(s, w) do
    with {:ok, rest} <- kw(s, w),
         {:ok, e, rest} <- parse_atom(skip(rest)) do
      {:ok, e, rest}
    end
  end

  defp parse_binder(s) do
    with {:ok, rest} <- tok(skip(s), "("),
         {:ok, q, rest} <- parse_qty(skip(rest)),
         {:ok, x, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, a, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")") do
      {:ok, {q, x, a}, rest}
    end
  end

  defp parse_qty(<<"+", rest::binary>>), do: {:ok, :reuse, rest}
  defp parse_qty(<<"-", rest::binary>>), do: {:ok, :erased, rest}
  defp parse_qty(s), do: {:ok, :affine, s}

  defp parse_pi(s) do
    rest = s |> skip() |> eat_kw(["Π", "Pi"])

    with {:ok, {q, x, a}, rest} <- parse_binder(rest),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, b, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:pi, q, a, x, b}, rest}
    end
  end

  defp parse_lam(s) do
    rest = s |> skip() |> eat_kw(["λ", "lam"])

    with {:ok, {q, x, a}, rest} <- parse_binder(rest),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, t, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:lam, q, a, x, t}, rest}
    end
  end

  defp parse_match(s) do
    with {:ok, rest} <- kw(s, "match"),
         {:ok, e, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "motive"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, rest} <- eat_lam(skip(rest)),
         {:ok, x, rest} <- parse_motive_binder(skip(rest)),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, p, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")"),
         {:ok, rest} <- tok(skip(rest), "|") do
      rest = skip(rest)

      cond do
        word_kw?(rest, "0") -> parse_mnat_cases(e, x, p, rest)
        atom_lit?(rest) -> parse_matom_cases(e, x, p, rest)
        true -> parse_mdata_cases(e, x, p, rest)
      end
    end
  end

  defp parse_motive_binder(s) do
    s = skip(s)

    if has_prefix?(s, "(") do
      with {:ok, {_q, x, _a}, rest} <- parse_binder(s), do: {:ok, x, rest}
    else
      ident(s)
    end
  end

  defp parse_mnat_cases(e, x, p, rest) do
    with {:ok, rest} <- kw(rest, "0"),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, z, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), "|"),
         {:ok, rest} <- kw(skip(rest), "suc"),
         {:ok, y, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, sc, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:mnat, e, x, p, z, y, sc}, rest}
    end
  end

  # The colon is glued to the name. `: List` is the colon of an identity type.
  defp atom_lit?(s) do
    case skip(s) do
      <<":", c, _::binary>> when c in ?a..?z or c in ?A..?Z or c == ?_ -> true
      _ -> false
    end
  end

  defp parse_atom_lit(s) do
    <<":", rest::binary>> = skip(s)

    case rest do
      <<c, _::binary>> when c in ?a..?z or c in ?A..?Z or c == ?_ ->
        {name, rest} = take_ident(rest, "")
        {:ok, {:atom, name}, rest}

      _ ->
        {:error, err(s, "expected atom")}
    end
  end

  defp parse_matom_cases(e, x, p, rest) do
    with {:ok, branches, rest} <- parse_matom_branches(rest, []) do
      {:ok, {:matom, e, x, p, branches}, rest}
    end
  end

  defp parse_matom_branches(s, acc) do
    with {:ok, {:atom, name}, rest} <- parse_atom_lit(skip(s)),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, body, rest} <- parse_term(skip(rest), 0) do
      acc = [{name, body} | acc]
      rest = skip(rest)

      if has_prefix?(rest, "|") do
        with {:ok, rest} <- tok(rest, "|") do
          parse_matom_branches(skip(rest), acc)
        end
      else
        {:ok, Enum.reverse(acc), rest}
      end
    end
  end

  defp parse_mdata_cases(e, x, p, rest) do
    with {:ok, branches, rest} <- parse_mdata_branches(rest, []) do
      {:ok, {:mdata, e, x, p, branches}, rest}
    end
  end

  defp parse_mdata_branches(s, acc) do
    with {:ok, cname, rest} <- ident(skip(s)),
         {:ok, binders, rest} <- parse_branch_binders(skip(rest)),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, body, rest} <- parse_term(skip(rest), 0) do
      acc = [{cname, binders, body} | acc]
      rest = skip(rest)

      if has_prefix?(rest, "|") do
        with {:ok, rest} <- tok(rest, "|") do
          parse_mdata_branches(skip(rest), acc)
        end
      else
        {:ok, Enum.reverse(acc), rest}
      end
    end
  end

  defp parse_branch_binders(s) do
    s = skip(s)

    if has_prefix?(s, "=>") do
      {:ok, [], s}
    else
      case ident(s) do
        {:ok, x, rest} ->
          with {:ok, xs, rest} <- parse_branch_binders(rest) do
            {:ok, [x | xs], rest}
          end

        _ ->
          {:ok, [], s}
      end
    end
  end

  defp parse_memp(s) do
    with {:ok, rest} <- kw(s, "matchEmpty"),
         {:ok, e, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "motive"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, rest} <- eat_lam(skip(rest)),
         {:ok, x, rest} <- ident(skip(rest)),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, p, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")") do
      {:ok, {:memp, e, x, p}, rest}
    end
  end

  defp parse_rwt(s) do
    with {:ok, rest} <- kw(s, "rewrite"),
         {:ok, eq, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "motive"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, rest} <- eat_lam(skip(rest)),
         {:ok, x, rest} <- ident(skip(rest)),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, p, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")"),
         {:ok, rest} <- kw(skip(rest), "in"),
         {:ok, t, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:rwt, eq, x, p, t}, rest}
    end
  end

  defp fst_sugar(e), do: {:letp, e, "a", "b", {:var, "a"}}
  defp snd_sugar(e), do: {:letp, e, "a", "b", {:var, "b"}}

  # let (a, b) = e in t
  defp parse_letp(s) do
    with {:ok, rest} <- kw(s, "let"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, a, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ","),
         {:ok, b, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ")"),
         {:ok, rest} <- tok(skip(rest), "="),
         {:ok, e, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "in"),
         {:ok, t, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:letp, e, a, b, t}, rest}
    end
  end

  defp parse_idt(s) do
    with {:ok, rest} <- tok(s, "{"),
         {:ok, a, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- either_tok(skip(rest), ["≡", "=="]),
         {:ok, b, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), "}") do
      {:ok, {:idt, ty, a, b}, rest}
    end
  end

  defp eat_lam(s) do
    cond do
      word_kw?(s, "λ") -> {:ok, after_kw(s, "λ")}
      word_kw?(s, "lam") -> {:ok, after_kw(s, "lam")}
      true -> {:ok, s}
    end
  end

  defp eat_kw(s, [k | ks]) do
    if word_kw?(s, k), do: after_kw(s, k), else: eat_kw(s, ks)
  end

  defp eat_kw(s, []), do: s

  # -- tokens ----------------------------------------------------------------

  defp skip(<<" ", r::binary>>), do: skip(r)
  defp skip(<<"\n", r::binary>>), do: skip(r)
  defp skip(<<"\t", r::binary>>), do: skip(r)
  defp skip(<<"\r", r::binary>>), do: skip(r)
  defp skip(<<"--", r::binary>>), do: skip(skip_line(r))
  defp skip(s), do: s

  defp skip_line(<<"\n", r::binary>>), do: r
  defp skip_line(<<_, r::binary>>), do: skip_line(r)
  defp skip_line(""), do: ""

  defp has_prefix?(s, kw), do: String.starts_with?(s, kw)

  defp after_kw(s, kw), do: String.slice(s, String.length(kw)..-1//1)

  defp kw(s, w) do
    s = skip(s)

    if has_prefix?(s, w) do
      rest = after_kw(s, w)

      if rest == "" or not ident_char?(String.first(rest)) do
        {:ok, rest}
      else
        {:error, err(s, "expected #{w}")}
      end
    else
      {:error, err(s, "expected #{w}")}
    end
  end

  defp tok(s, t) do
    s = skip(s)

    if has_prefix?(s, t),
      do: {:ok, after_kw(s, t)},
      else: {:error, err(s, "expected #{t}")}
  end

  defp ident(s) do
    s = skip(s)

    case s do
      <<c, _::binary>> when c in ?a..?z or c in ?A..?Z or c == ?_ ->
        {n, rest} = take_ident(s, "")
        {:ok, n, rest}

      _ ->
        {:error, err(s, "expected identifier")}
    end
  end

  defp take_ident(<<c, r::binary>>, acc)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?- or c == ?' do
    take_ident(r, acc <> <<c>>)
  end

  defp take_ident(s, acc), do: {acc, s}

  defp ident_char?(nil), do: false

  defp ident_char?(<<c>>),
    do: c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?- or c == ?'

  defp ident_char?(s) when is_binary(s), do: ident_char?(String.first(s))

  defp first_char(<<c, _::binary>>), do: c
  defp first_char(_), do: nil

  defp either_tok(s, [t | ts]) do
    case tok(s, t) do
      {:ok, rest} -> {:ok, rest}
      _ -> either_tok(s, ts)
    end
  end

  defp either_tok(_, []), do: {:error, "expected token"}
end
