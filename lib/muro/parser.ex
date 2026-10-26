defmodule Muro.Parser do
  @moduledoc """
  Tiny .muro parser. Agda-looking: Π, λ, match, explicit types.
  """

  alias Muro.Print

  @src_key {__MODULE__, :src}
  @noting_key {__MODULE__, :noting_proc}
  @notes_key {__MODULE__, :proc_notes}

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

  # An error with nothing left names the last line of the file.
  defp err(rest, msg) do
    src = Process.get(@src_key, "")

    if skip(rest) == "" do
      "#{Print.loc_prefix(Print.offset_to_loc(src, byte_size(src)))}#{eof_msg(msg)}"
    else
      "#{Print.loc_prefix(here(rest))}#{msg}"
    end
  end

  defp eof_msg("expected " <> what), do: "unexpected end of file, expected #{what}"
  defp eof_msg(msg), do: msg

  # Locations of process steps, in preorder, while a conform or a read is parsed.
  # A parenthesis is not a step. A protocol `rec` is not one either.
  defp note(s) do
    if Process.get(@noting_key) do
      Process.put(@notes_key, [here(s) | Process.get(@notes_key, [])])
    end

    :ok
  end

  defp with_steps(s, bound \\ MapSet.new()) do
    Process.put(@noting_key, true)
    Process.put(@notes_key, [])

    try do
      case parse_proc(s, bound) do
        {:ok, proc, rest} ->
          notes = Enum.reverse(Process.get(@notes_key, []))
          {:ok, proc, zip_steps(proc, notes), rest}

        other ->
          other
      end
    after
      Process.delete(@noting_key)
      Process.delete(@notes_key)
    end
  end

  defp zip_steps(proc, notes) do
    case take_span(proc, notes) do
      {:ok, span, []} -> span
      _ -> nil
    end
  end

  defp take_span(:done, [at | rest]), do: {:ok, %{at: at, down: []}, rest}
  defp take_span(:stop, [at | rest]), do: {:ok, %{at: at, down: []}, rest}
  defp take_span({:call, _}, [at | rest]), do: {:ok, %{at: at, down: []}, rest}

  defp take_span({:put, _, _, p}, [at | rest]), do: take_one(at, p, rest)
  defp take_span({:get, _, _, p}, [at | rest]), do: take_one(at, p, rest)
  defp take_span({:pick0, p}, [at | rest]), do: take_one(at, p, rest)
  defp take_span({:pick1, p}, [at | rest]), do: take_one(at, p, rest)
  defp take_span({:rec, _, p}, [at | rest]), do: take_one(at, p, rest)

  defp take_span({:cover, p, q}, [at | rest]), do: take_two(at, p, q, rest)
  defp take_span({:iget, _, p, q}, [at | rest]), do: take_two(at, p, q, rest)

  defp take_span({:match, _, arms}, [at | rest]) do
    with {:ok, cs, rest} <- take_many(arms, rest) do
      {:ok, %{at: at, down: cs}, rest}
    end
  end

  defp take_span(_, _), do: :error

  defp take_one(at, p, rest) do
    with {:ok, c, rest} <- take_span(p, rest) do
      {:ok, %{at: at, down: [c]}, rest}
    end
  end

  defp take_two(at, p, q, rest) do
    with {:ok, a, rest} <- take_span(p, rest),
         {:ok, b, rest} <- take_span(q, rest) do
      {:ok, %{at: at, down: [a, b]}, rest}
    end
  end

  defp take_many([], rest), do: {:ok, [], rest}

  defp take_many([p | ps], rest) do
    with {:ok, s, rest} <- take_span(p, rest),
         {:ok, ss, rest} <- take_many(ps, rest) do
      {:ok, [s | ss], rest}
    end
  end

  defp parse_book(s), do: parse_book(s, [])

  defp parse_book(s, acc) do
    s = skip(s)

    cond do
      s == "" ->
        {:ok, Enum.reverse(acc), ""}

      nu_start?(s) ->
        case parse_nu(s) do
          {:ok, rest} -> parse_book(rest, acc)
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      import_start?(s) ->
        case parse_import(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      param_start?(s) ->
        case parse_param(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      data_start?(s) ->
        case parse_data(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      session_start?(s) ->
        case parse_session(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      conform_start?(s) ->
        case parse_conform(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      place_start?(s) ->
        case parse_place(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      scheme_start?(s) ->
        case parse_scheme(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      move_start?(s) ->
        case parse_move(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      endpoint_start?(s) ->
        case parse_endpoint(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      read_start?(s) ->
        case parse_read(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      meet_start?(s) ->
        case parse_meet(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      talk_start?(s) ->
        case parse_talk(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      seat_start?(s) ->
        case parse_seat(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end

      link_start?(s) ->
        case parse_link(s) do
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

  defp param_start?(s), do: word_kw?(s, "param")

  defp parse_param(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "param"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, tag, rest} <- parse_mode(skip(rest)),
         {:ok, ty, rest} <- parse_term(skip(rest), 0) do
      {:ok, Map.merge(%{kind: :param, name: name, type: ty, loc: loc}, tag), rest}
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

  # `ν Stream (A : Type) : Type where uncons : Stream A → A × Stream A`
  # is checked for shape and dropped: Stream is primitive. Any other name
  # declares a family over its indices,
  #
  #   ν Name (x₁ : A₁) … (xₙ : Aₙ) : Type where uncons : Name x₁ … xₙ → B
  #
  # and is the spec definition `Name : Π (x₁ : A₁) … → Type` whose body
  # is `ν Name. λ x₁ … xₙ → B`: inside B, Name is the ν-bound family.
  defp parse_nu(s) do
    loc = here(s)
    rest = s |> skip() |> eat_kw(["ν", "nu"])

    with {:ok, name, rest} <- ident(skip(rest)) do
      if name == "Stream", do: parse_nu_stream(rest), else: parse_nu_family(name, loc, rest)
    end
  end

  defp parse_nu_family(name, loc, s) do
    with {:ok, binders, rest} <- parse_param_binders(skip(s)),
         :ok <-
           if(binders == [],
             do: {:error, err(rest, "a ν family takes at least one index")},
             else: :ok
           ),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, sort, rest} <- parse_term(skip(rest), 0),
         :ok <- if(sort == :typ, do: :ok, else: {:error, err(rest, "a ν family is a Type")}),
         {:ok, rest} <- kw(skip(rest), "where"),
         {:ok, ctor, rest} <- ident(skip(rest)),
         :ok <- if(ctor == "uncons", do: :ok, else: {:error, err(rest, "expected uncons")}),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, ctor_ty, rest} <- parse_term(skip(rest), 0),
         {:ok, body} <- nu_family_body(name, binders, ctor_ty, rest) do
      ty = List.foldr(binders, :typ, fn {q, x, a}, acc -> {:pi, q, a, x, acc} end)
      fam = List.foldr(binders, body, fn {q, x, a}, acc -> {:lam, q, a, x, acc} end)
      {:ok, %{name: name, mode: :spec, type: ty, body: {:nu, name, fam}, loc: loc}, rest}
    end
  end

  defp nu_family_body(name, binders, {:pi, _, dom, _, body}, rest) do
    self = Enum.reduce(binders, {:var, name}, fn {_, x, _}, acc -> {:app, acc, {:var, x}} end)

    if dom == self,
      do: {:ok, body},
      else: {:error, err(rest, "uncons must take #{name} applied to its indices in order")}
  end

  defp nu_family_body(name, _binders, _ty, rest),
    do: {:error, err(rest, "uncons must be a function from #{name} applied to its indices")}

  defp parse_nu_stream(rest) do
    with {:ok, {_q, _x, a}, rest} <- parse_binder(rest),
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

  defp session_start?(s), do: word_kw?(s, "session")

  defp conform_start?(s), do: word_kw?(s, "conform")

  # session ping := recv Nat (send Nat end)
  # session %1 ping-done := recv Nat (send Nat end)
  # session back := dual ping
  # %0 is affine, and it is the default. %1 must finish.
  # A dual session with no mark takes the named session's mark.
  # `dual` is a keyword only in that form. Neither mark is a quantity
  # on a Π binder. Keywords here are not term keywords.
  defp parse_session(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "session"),
         {:ok, mult, stated, rest} <- parse_session_mult(skip(rest)),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, params, rest} <- parse_session_params(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, proto, rest} <- parse_session_proto(skip(rest)) do
      mult =
        case proto do
          {:dual, _} -> if stated, do: mult, else: :inherit
          _ -> mult
        end

      {:ok,
       %{
         kind: :session,
         name: name,
         mode: :spec,
         mult: mult,
         params: params,
         proto: proto,
         loc: loc
       }, rest}
    end
  end

  # `(k : Nat)` before `:=`. A parameter is a nat. The name is in scope
  # in the protocol, as a length or as an argument of a later session.
  defp parse_session_params(s) do
    s = skip(s)

    if has_prefix?(s, "(") do
      with {:ok, name, rest} <- parse_session_param(s),
           {:ok, more, rest} <- parse_session_params(rest) do
        {:ok, [name | more], rest}
      end
    else
      {:ok, [], s}
    end
  end

  defp parse_session_param(s) do
    with {:ok, rest} <- tok(s, "("),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, rest} <- session_param_type(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ")") do
      {:ok, String.to_atom(name), rest}
    end
  end

  defp session_param_type(s) do
    if word_kw?(s, "Nat") do
      {:ok, after_kw(s, "Nat")}
    else
      {:error, err(s, "a session parameter is a nat")}
    end
  end

  defp parse_session_mult("%" <> _ = s) do
    with {:ok, mult, rest} <- parse_mult(s), do: {:ok, mult, true, rest}
  end

  defp parse_session_mult(s), do: {:ok, :affine, false, s}

  # session back := dual ping
  # The other end of ping. The mark stays on ping.
  # session ping := seen pong with peer in ping-exchange
  # The session pong has with peer in that description. The mark is
  # the mark written here. `seen` is a keyword only in this form.
  defp parse_session_proto(s) do
    cond do
      word_kw?(s, "dual") ->
        with {:ok, rest} <- kw(s, "dual"),
             {:ok, ref, rest} <- parse_dual_ref(skip(rest)) do
          {:ok, {:dual, ref}, rest}
        end

      word_kw?(s, "seen") ->
        parse_seen(s)

      true ->
        parse_proto(s)
    end
  end

  defp parse_seen(s) do
    with {:ok, rest} <- kw(s, "seen"),
         {:ok, p, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "with"),
         {:ok, q, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "in"),
         {:ok, talk, rest} <- ident(skip(rest)) do
      {:ok, {:seen, p, q, talk}, rest}
    end
  end

  # %1 is a whole token. %10 is not %1 followed by 0.
  defp parse_mult("%" <> rest = s) do
    case take_mult(rest) do
      {:ok, mult, more} -> {:ok, mult, more}
      :error -> {:error, err(s, "expected %0 or %1")}
    end
  end

  defp parse_mult(s), do: {:ok, :affine, s}

  defp take_mult("0" <> more), do: close_mult(:affine, more)
  defp take_mult("1" <> more), do: close_mult(:linear, more)
  defp take_mult(_), do: :error

  defp close_mult(mult, more) do
    if more == "" or not ident_char?(String.first(more)),
      do: {:ok, mult, more},
      else: :error
  end

  # conform pong : ping := get Nat (put 1 done)
  # The process is evidence that it conforms to the named session.
  defp parse_conform(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "conform"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, session, rest} <- parse_session_use(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, proc, steps, rest} <- with_steps(skip(rest)) do
      {:ok,
       %{
         kind: :conform,
         name: name,
         mode: :evidence,
         session: session,
         proc: proc,
         steps: steps,
         loc: loc
       }, rest}
    end
  end

  defp place_start?(s), do: word_kw?(s, "place")

  defp scheme_start?(s), do: word_kw?(s, "scheme")

  defp move_start?(s), do: word_kw?(s, "move")

  # place home := ambient
  # place away := node a
  # `ambient` and `node` are keywords only on this right-hand side.
  defp parse_place(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "place"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, place, rest} <- parse_place_rhs(skip(rest)) do
      {:ok, %{kind: :place, name: name, mode: :spec, place: place, loc: loc}, rest}
    end
  end

  defp parse_place_rhs(s) do
    cond do
      word_kw?(s, "ambient") ->
        {:ok, :ambient, after_kw(s, "ambient")}

      word_kw?(s, "node") ->
        with {:ok, name, rest} <- ident(skip(after_kw(s, "node"))) do
          {:ok, {:node, name}, rest}
        end

      true ->
        {:error, err(s, "expected ambient or node")}
    end
  end

  # scheme local := fixed home
  # scheme poly := any
  defp parse_scheme(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "scheme"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, scheme, rest} <- parse_scheme_rhs(skip(rest)) do
      {:ok, %{kind: :scheme, name: name, mode: :spec, scheme: scheme, loc: loc}, rest}
    end
  end

  defp parse_scheme_rhs(s) do
    cond do
      word_kw?(s, "any") ->
        {:ok, :any, after_kw(s, "any")}

      word_kw?(s, "fixed") ->
        with {:ok, name, rest} <- ident(skip(after_kw(s, "fixed"))) do
          {:ok, {:fixed, name}, rest}
        end

      true ->
        {:error, err(s, "expected any or fixed")}
    end
  end

  # move stay local : home
  # move cross local : away
  # The mark is evidence. `stay` and `cross` are keywords only here.
  defp parse_move(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "move"),
         {:ok, mark, rest} <- parse_mark(skip(rest)),
         {:ok, scheme, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, place, rest} <- ident(skip(rest)) do
      {:ok, %{kind: :move, mode: :evidence, mark: mark, scheme: scheme, place: place, loc: loc},
       rest}
    end
  end

  defp parse_mark(s) do
    cond do
      word_kw?(s, "stay") -> {:ok, :stay, after_kw(s, "stay")}
      word_kw?(s, "cross") -> {:ok, :cross, after_kw(s, "cross")}
      true -> {:error, err(s, "expected stay or cross")}
    end
  end

  defp endpoint_start?(s), do: word_kw?(s, "endpoint")

  defp read_start?(s), do: word_kw?(s, "read")

  # endpoint ping-home := ping at local
  # The session's mark is the endpoint's mark. `at` is a keyword only here.
  defp parse_endpoint(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "endpoint"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, session, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "at"),
         {:ok, scheme, rest} <- ident(skip(rest)) do
      {:ok,
       %{
         kind: :endpoint,
         name: name,
         mode: :spec,
         session: session,
         scheme: scheme,
         loc: loc
       }, rest}
    end
  end

  # read stay pong : ping-home at home := get Nat (put 1 done)
  # read cross pong : ping-home at away := get Nat (put 1 done)
  # The process conforms to the session. The mark is the move.
  defp parse_read(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "read"),
         {:ok, mark, rest} <- parse_mark(skip(rest)),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, endpoint, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "at"),
         {:ok, place, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, proc, steps, rest} <- with_steps(skip(rest)) do
      {:ok,
       %{
         kind: :read,
         name: name,
         mode: :evidence,
         mark: mark,
         endpoint: endpoint,
         place: place,
         proc: proc,
         steps: steps,
         loc: loc
       }, rest}
    end
  end

  # A place or scheme entry is `name := …`. A constructor `place : Box`
  # is not one. A move entry starts `move stay` or `move cross`.
  defp assign_entry?(s, word) do
    if word_kw?(s, word) do
      rest = s |> after_kw(word) |> skip()

      case ident(rest) do
        {:ok, _, rest} -> has_prefix?(skip(rest), ":=")
        _ -> false
      end
    else
      false
    end
  end

  defp place_entry?(s), do: assign_entry?(s, "place")

  defp scheme_entry?(s), do: assign_entry?(s, "scheme")

  defp move_entry?(s) do
    if word_kw?(s, "move") do
      rest = s |> after_kw("move") |> skip()
      word_kw?(rest, "stay") or word_kw?(rest, "cross")
    else
      false
    end
  end

  defp endpoint_entry?(s), do: assign_entry?(s, "endpoint")

  defp read_entry?(s) do
    if word_kw?(s, "read") do
      rest = s |> after_kw("read") |> skip()
      word_kw?(rest, "stay") or word_kw?(rest, "cross")
    else
      false
    end
  end

  defp meet_start?(s), do: meet_entry?(s)

  # meet wire : pong with peer
  # `meet` and `with` are keywords only in this form.
  defp parse_meet(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "meet"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, left, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "with"),
         {:ok, right, rest} <- ident(skip(rest)) do
      {:ok,
       %{
         kind: :meet,
         name: name,
         mode: :evidence,
         left: left,
         right: right,
         loc: loc
       }, rest}
    end
  end

  # talk ping-exchange := say peer pong Nat (say pong peer Nat over)
  # The description is spec. `talk`, `over`, `say`, and `offer` are
  # keywords only in this form. A constructor `talk : Box` is not one.
  defp talk_start?(s), do: assign_entry?(s, "talk")

  defp parse_talk(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "talk"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, body, rest} <- parse_talk_term(skip(rest)) do
      {:ok, %{kind: :talk, name: name, mode: :spec, body: body, loc: loc}, rest}
    end
  end

  defp parse_talk_term(s) do
    s = skip(s)

    cond do
      word_kw?(s, "over") ->
        {:ok, :over, after_kw(s, "over")}

      word_kw?(s, "say") ->
        parse_say(s)

      word_kw?(s, "offer") ->
        parse_talk2(s, "offer", :offer)

      has_prefix?(s, "(") ->
        parse_paren(s, &parse_talk_term/1)

      true ->
        with {:ok, name, rest} <- ident(s) do
          {:ok, {:ref, name}, rest}
        end
    end
  end

  # say peer pong Nat (say pong peer Nat over)
  # One payload type, then one continuation.
  defp parse_say(s) do
    with {:ok, rest} <- kw(s, "say"),
         {:ok, a, rest} <- parse_party(skip(rest)),
         {:ok, b, rest} <- parse_party(skip(rest)),
         {:ok, ty, rest} <- parse_pay(skip(rest)),
         {:ok, t, rest} <- parse_talk_term(skip(rest)) do
      {:ok, {:say, a, b, ty, t}, rest}
    end
  end

  defp parse_talk2(s, word, tag) do
    with {:ok, rest} <- kw(s, word),
         {:ok, a, rest} <- parse_party(skip(rest)),
         {:ok, b, rest} <- parse_party(skip(rest)),
         {:ok, t0, rest} <- parse_talk_term(skip(rest)),
         {:ok, t1, rest} <- parse_talk_term(skip(rest)) do
      {:ok, {tag, a, b, t0, t1}, rest}
    end
  end

  # A party is a name. `over`, `say`, and `offer` stay the description words.
  defp parse_party(s) do
    s = skip(s)

    cond do
      word_kw?(s, "over") or word_kw?(s, "say") or word_kw?(s, "offer") ->
        {:error, err(s, "expected a party")}

      true ->
        ident(s)
    end
  end

  # seat pong-home : pong at home in ping-exchange
  # Where a party of a description sits. `seat`, `at`, and `in` are
  # keywords only in this form. A constructor `seat : Box` is not one.
  defp seat_start?(s), do: colon_entry?(s, "seat")

  defp parse_seat(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "seat"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, party, rest} <- parse_party(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "at"),
         {:ok, place, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "in"),
         {:ok, talk, rest} <- ident(skip(rest)) do
      {:ok,
       %{
         kind: :seat,
         name: name,
         mode: :spec,
         party: party,
         place: place,
         talk: talk,
         loc: loc
       }, rest}
    end
  end

  # link go : cross pong-home with peer-away in ping-exchange
  # The boundary between two seatings. `link` is a keyword only in
  # this form. `stay` and `cross` name the boundary. A constructor
  # `link : Box` is not one.
  defp link_start?(s), do: colon_entry?(s, "link")

  defp parse_link(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "link"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, mark, rest} <- parse_link_mark(skip(rest)),
         {:ok, left, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "with"),
         {:ok, right, rest} <- ident(skip(rest)),
         {:ok, rest} <- kw(skip(rest), "in"),
         {:ok, talk, rest} <- ident(skip(rest)) do
      {:ok,
       %{
         kind: :link,
         name: name,
         mode: :evidence,
         mark: mark,
         left: left,
         right: right,
         talk: talk,
         loc: loc
       }, rest}
    end
  end

  defp parse_link_mark(s) do
    cond do
      word_kw?(s, "stay") -> {:ok, :stay, after_kw(s, "stay")}
      word_kw?(s, "cross") -> {:ok, :cross, after_kw(s, "cross")}
      true -> {:error, err(s, "expected stay or cross")}
    end
  end

  # `name :` and not `:=` or `::`. A constructor `word : Box` is not one.
  defp colon_entry?(s, word) do
    if word_kw?(s, word) do
      rest = s |> after_kw(word) |> skip()

      case ident(rest) do
        {:ok, _, rest} ->
          rest = skip(rest)
          has_prefix?(rest, ":") and not has_prefix?(rest, ":=") and not has_prefix?(rest, "::")

        _ ->
          false
      end
    else
      false
    end
  end

  # A meeting is `meet name :`. A constructor `meet : Box` is not one.
  defp meet_entry?(s) do
    if word_kw?(s, "meet") do
      rest = s |> after_kw("meet") |> skip()

      case ident(rest) do
        {:ok, _, rest} ->
          rest = skip(rest)
          has_prefix?(rest, ":") and not has_prefix?(rest, ":=") and not has_prefix?(rest, "::")

        _ ->
          false
      end
    else
      false
    end
  end

  defp parse_proto(s, bound \\ MapSet.new()) do
    s = skip(s)

    cond do
      word_kw?(s, "end") -> {:ok, :end, after_kw(s, "end")}
      word_kw?(s, "send") -> parse_comm_proto(s, "send", :send, bound)
      word_kw?(s, "recv") -> parse_comm_proto(s, "recv", :recv, bound)
      word_kw?(s, "choose") -> parse_proto2(s, "choose", :choose, bound)
      word_kw?(s, "branch") -> parse_proto2(s, "branch", :branch, bound)
      word_kw?(s, "rec") -> parse_rec(s, &parse_proto/2, bound)
      has_prefix?(s, "(") -> parse_paren(s, fn body -> parse_proto(body, bound) end)
      ident_start?(s) -> parse_proto_name(s, bound)
      true -> {:error, err(s, "expected a protocol")}
    end
  end

  # `recv (n : Nat)` binds `n` for the continuation. `recv (Nat)` and
  # `recv (Vec Nat n)` are payload types and do not bind.
  # `send (d : Nat) {d ≤ w}` is an evidence payload: the sender owes
  # `d ≤ w`. The name is in scope in its bound only.
  defp parse_comm_proto(s, word, tag, bound) do
    with {:ok, rest} <- kw(s, word) do
      rest = skip(rest)

      case try_binder(rest, bound) do
        {:ok, name, ty, rest} ->
          rest = skip(rest)

          cond do
            has_prefix?(rest, "{") ->
              with {:ok, e, rest} <- parse_bound(rest, name, ty),
                   {:ok, p, rest} <- parse_proto(skip(rest), bound) do
                {:ok, {ev_tag(tag), name, e, p}, rest}
              end

            word_kw?(rest, "on") ->
              parse_index_proto(rest, tag, name, ty, bound)

            true ->
              with {:ok, p, rest} <- parse_proto(rest, bound) do
                {:ok, {dep_tag(tag), name, ty, p}, rest}
              end
          end

        :not_binder ->
          with {:ok, ty, rest} <- parse_pay(rest, bound),
               {:ok, p, rest} <- parse_proto(skip(rest), bound) do
            {:ok, {tag, ty, p}, rest}
          end

        {:error, _} = err ->
          err
      end
    end
  end

  defp dep_tag(:send), do: :dsend
  defp dep_tag(:recv), do: :drecv

  defp ev_tag(:send), do: :esend
  defp ev_tag(:recv), do: :erecv

  # `recv (b : Bit) on S T` receives a bit. `b0` continues as `S` and
  # `b1` continues as `T`. A nat does not choose the arm.
  defp parse_index_proto(s, tag, name, :bit, bound) do
    with {:ok, rest} <- kw(s, "on"),
         {:ok, a, rest} <- parse_proto(skip(rest), bound),
         {:ok, b, rest} <- parse_proto(skip(rest), bound) do
      {:ok, {ix_tag(tag), name, a, b}, rest}
    end
  end

  defp parse_index_proto(s, _tag, _name, _ty, _bound) do
    {:error, err(s, "a next action is chosen by a bit")}
  end

  defp ix_tag(:send), do: :isend
  defp ix_tag(:recv), do: :irecv

  # `get (b : Bit) on P Q` offers both arms. The name is bound in each.
  defp parse_index_proc(s, name, :bit, bound) do
    with {:ok, rest} <- kw(s, "on"),
         {:ok, p, rest} <- parse_proc(skip(rest), bound),
         {:ok, q, rest} <- parse_proc(skip(rest), bound) do
      {:ok, {:iget, name, p, q}, rest}
    end
  end

  defp parse_index_proc(s, _name, _ty, _bound) do
    {:error, err(s, "a next action is chosen by a bit")}
  end

  # `{d ≤ w}` or `{d <= w}`. The left side is the name just bound. The
  # bound is a numeral or a name. The payload is a nat.
  defp parse_bound(s, name, :nat) do
    with {:ok, rest} <- tok(s, "{"),
         rest = skip(rest),
         {:ok, left, rest} <- ident(rest),
         :ok <- bound_left(left, name, s),
         rest = skip(rest),
         {:ok, rest} <- either_tok(rest, ["≤", "<="]),
         {:ok, e, rest} <- parse_bound_exp(skip(rest)),
         {:ok, rest} <- tok(skip(rest), "}") do
      {:ok, e, rest}
    end
  end

  defp parse_bound(s, _name, _ty), do: {:error, err(s, "an evidence payload is a nat")}

  defp bound_left(left, name, s) do
    if String.to_atom(left) == name do
      :ok
    else
      {:error, err(s, "the bound names the nat that is sent")}
    end
  end

  defp parse_bound_exp(s) do
    cond do
      number?(s) ->
        {digits, rest} = take_digits(s, "")
        {:ok, {:lit, String.to_integer(digits)}, rest}

      ident_start?(s) ->
        case ident(s) do
          {:ok, name, rest} -> {:ok, {:var, String.to_atom(name)}, rest}
          err -> err
        end

      true ->
        {:error, err(s, "expected a bound")}
    end
  end

  defp try_binder(s, bound) do
    if has_prefix?(s, "(") do
      case tok(s, "(") do
        {:ok, rest} ->
          rest = skip(rest)

          case ident(rest) do
            {:ok, name, rest} ->
              rest = skip(rest)

              if has_prefix?(rest, ":") and not has_prefix?(rest, ":=") and
                   not has_prefix?(rest, "::") do
                with {:ok, rest} <- tok(rest, ":"),
                     {:ok, ty, rest} <- parse_pay(skip(rest), bound),
                     {:ok, rest} <- tok(skip(rest), ")") do
                  {:ok, String.to_atom(name), ty, rest}
                end
              else
                :not_binder
              end

            _ ->
              :not_binder
          end

        _ ->
          :not_binder
      end
    else
      :not_binder
    end
  end

  # `rec X. S`. The variable is a continuation. `rec` is a keyword only
  # inside a protocol or a process. The dot separates the name.
  # `bound` is the recursion variables in scope. One of those names is
  # the continuation, so a payload does not take it as an argument:
  # `send Bool X` is `Bool`, then `X`, and `put n X` is `n`, then `X`.
  defp parse_rec(s, parse_body, bound) do
    note(skip(s))

    with {:ok, rest} <- kw(s, "rec"),
         {:ok, name, rest} <- rec_name(skip(rest)),
         {:ok, rest} <- tok(skip(rest), "."),
         {:ok, body, rest} <- parse_body.(skip(rest), MapSet.put(bound, Atom.to_string(name))) do
      {:ok, {:rec, name, body}, rest}
    end
  end

  defp rec_name(s) do
    with {:ok, name, rest} <- ident(s) do
      if reserved_session?(name) do
        {:error, err(s, "expected a session variable")}
      else
        {:ok, String.to_atom(name), rest}
      end
    end
  end

  # A name in the `rec` bound is that variable. Any other name is a
  # session declared earlier, applied to the arguments that follow.
  # A parenthesis whose body is a protocol is the next protocol, not
  # an argument: `choose ack (send Nat end)`.
  defp parse_proto_name(s, bound) do
    s0 = skip(s)

    with {:ok, name, rest} <- ident(s0) do
      cond do
        reserved_session?(name) ->
          {:error, err(s0, "expected a protocol")}

        MapSet.member?(bound, name) ->
          {:ok, {:svar, String.to_atom(name)}, rest}

        true ->
          with {:ok, args, rest} <- parse_sargs(skip(rest)) do
            {:ok, {:sess, name, args}, rest}
          end
      end
    end
  end

  # `dual ping` keeps the bare name. `dual (stream 0)` carries the arguments.
  defp parse_dual_ref(s) do
    s = skip(s)

    if has_prefix?(s, "(") do
      with {:ok, rest} <- tok(s, "("),
           {:ok, ref, rest} <- parse_session_use(skip(rest)),
           {:ok, rest} <- tok(skip(rest), ")") do
        {:ok, ref, rest}
      end
    else
      parse_session_use(s)
    end
  end

  # No arguments stays a string, so a use that names a session is the
  # name it always was. Arguments are the application.
  defp parse_session_use(s) do
    with {:ok, name, rest} <- ident(skip(s)) do
      if reserved_session?(name) do
        {:error, err(s, "expected a session")}
      else
        # A declaration word is a legal session name (`relay`). It is not
        # an argument: `parse_sarg` stops before the next entry.
        with {:ok, args, rest} <- parse_sargs(skip(rest)) do
          if args == [] do
            {:ok, name, rest}
          else
            {:ok, {:sess, name, args}, rest}
          end
        end
      end
    end
  end

  defp parse_sargs(s) do
    case parse_sarg(skip(s)) do
      {:ok, arg, rest} ->
        with {:ok, more, rest} <- parse_sargs(rest) do
          {:ok, [arg | more], rest}
        end

      :no ->
        {:ok, [], s}

      {:error, _} = err ->
        err
    end
  end

  defp parse_sarg(s) do
    s = skip(s)

    cond do
      number?(s) ->
        {digits, rest} = take_digits(s, "")
        {:ok, {:lit, String.to_integer(digits)}, rest}

      word_kw?(s, "suc") ->
        case parse_sarg(skip(after_kw(s, "suc"))) do
          {:ok, arg, rest} -> {:ok, {:suc, arg}, rest}
          :no -> {:error, err(s, "expected a session argument")}
          {:error, _} = err -> err
        end

      has_prefix?(s, "(") ->
        parse_sarg_paren(s)

      ident_start?(s) ->
        case ident(s) do
          {:ok, name, rest} ->
            if reserved_session?(name) or decl_word?(name) do
              :no
            else
              {:ok, {:var, String.to_atom(name)}, rest}
            end

          _ ->
            :no
        end

      true ->
        :no
    end
  end

  # `(send …)` is a protocol. `(suc n)` and `(bump 0)` are arguments.
  defp parse_sarg_paren(s) do
    with {:ok, rest} <- tok(s, "(") do
      inner = skip(rest)

      if proto_head?(inner) do
        :no
      else
        with {:ok, arg, rest} <- parse_sexpr(inner),
             {:ok, rest} <- tok(skip(rest), ")") do
          {:ok, arg, rest}
        end
      end
    end
  end

  defp proto_head?(s) do
    Enum.any?(~w(end send recv choose branch rec), &word_kw?(s, &1))
  end

  defp parse_sexpr(s) do
    s = skip(s)

    cond do
      number?(s) ->
        {digits, rest} = take_digits(s, "")
        {:ok, {:lit, String.to_integer(digits)}, rest}

      word_kw?(s, "suc") ->
        case parse_sarg(skip(after_kw(s, "suc"))) do
          {:ok, arg, rest} -> {:ok, {:suc, arg}, rest}
          :no -> {:error, err(s, "expected a session argument")}
          {:error, _} = err -> err
        end

      has_prefix?(s, "(") ->
        parse_sarg_paren(s)

      ident_start?(s) ->
        with {:ok, name, rest} <- ident(s) do
          if reserved_session?(name) or decl_word?(name) do
            {:error, err(s, "expected a session argument")}
          else
            parse_sexpr_args(skip(rest), name, [])
          end
        end

      true ->
        {:error, err(s, "expected a session argument")}
    end
  end

  defp parse_sexpr_args(s, name, acc) do
    case parse_sexpr_atom(skip(s)) do
      {:ok, arg, rest} ->
        parse_sexpr_args(rest, name, [arg | acc])

      :no ->
        args = Enum.reverse(acc)

        if args == [] do
          {:ok, {:var, String.to_atom(name)}, s}
        else
          {:ok, {:con, name, args}, s}
        end

      {:error, _} = err ->
        err
    end
  end

  # One atom of an application. An identifier is not itself an application:
  # `bump 0` is `bump` applied to `0`.
  defp parse_sexpr_atom(s) do
    s = skip(s)

    cond do
      number?(s) ->
        {digits, rest} = take_digits(s, "")
        {:ok, {:lit, String.to_integer(digits)}, rest}

      word_kw?(s, "suc") ->
        case parse_sarg(skip(after_kw(s, "suc"))) do
          {:ok, arg, rest} -> {:ok, {:suc, arg}, rest}
          :no -> {:error, err(s, "expected a session argument")}
          {:error, _} = err -> err
        end

      has_prefix?(s, "(") ->
        parse_sarg_paren(s)

      ident_start?(s) ->
        case ident(s) do
          {:ok, name, rest} ->
            if reserved_session?(name) or decl_word?(name) do
              :no
            else
              {:ok, {:var, String.to_atom(name)}, rest}
            end

          _ ->
            :no
        end

      true ->
        :no
    end
  end

  defp parse_name_cont(s, tag, what) do
    s0 = skip(s)
    note(s0)

    with {:ok, name, rest} <- ident(s0) do
      if reserved_session?(name) do
        {:error, err(s0, "expected a #{what}")}
      else
        {:ok, {tag, String.to_atom(name)}, rest}
      end
    end
  end

  defp reserved_session?(name) do
    name in ~w(end send recv choose branch rec done stop put get pick0 pick1 cover match on Nat Bit Unit Vec dual seen)
  end

  defp parse_proto2(s, word, tag, bound) do
    with {:ok, rest} <- kw(s, word),
         {:ok, a, rest} <- parse_proto(skip(rest), bound),
         {:ok, b, rest} <- parse_proto(skip(rest), bound) do
      {:ok, {tag, a, b}, rest}
    end
  end

  defp parse_proc(s, bound) do
    s = skip(s)

    cond do
      word_kw?(s, "done") ->
        note(s)
        {:ok, :done, after_kw(s, "done")}

      word_kw?(s, "stop") ->
        note(s)
        {:ok, :stop, after_kw(s, "stop")}

      word_kw?(s, "put") ->
        parse_comm(s, "put", :put, bound)

      word_kw?(s, "get") ->
        parse_comm(s, "get", :get, bound)

      word_kw?(s, "pick0") ->
        parse_proc1(s, "pick0", :pick0, bound)

      word_kw?(s, "pick1") ->
        parse_proc1(s, "pick1", :pick1, bound)

      word_kw?(s, "cover") ->
        parse_proc2(s, "cover", :cover, bound)

      word_kw?(s, "match") ->
        parse_match(s, bound)

      word_kw?(s, "rec") ->
        parse_rec(s, &parse_proc/2, bound)

      has_prefix?(s, "(") ->
        parse_paren(s, fn body -> parse_proc(body, bound) end)

      ident_start?(s) ->
        parse_name_cont(s, :call, "process")

      true ->
        {:error, err(s, "expected a process")}
    end
  end

  defp parse_comm(s, "put", :put, bound) do
    note(skip(s))

    with {:ok, rest} <- kw(s, "put"),
         {:ok, {ty, val}, rest} <- parse_pval(skip(rest), bound),
         {:ok, p, rest} <- parse_proc(skip(rest), bound) do
      {:ok, {:put, ty, val, p}, rest}
    end
  end

  defp parse_comm(s, "get", :get, bound) do
    note(skip(s))

    with {:ok, rest} <- kw(s, "get") do
      rest = skip(rest)

      # Try parsing with binding: get (name : Type) proc
      if has_prefix?(rest, "(") do
        case tok(rest, "(") do
          {:ok, after_paren} ->
            after_paren = skip(after_paren)

            # Check if this is a binder (identifier followed by :)
            case ident(after_paren) do
              {:ok, name, after_name} ->
                after_name = skip(after_name)

                if has_prefix?(after_name, ":") do
                  # This is get (name : Type) proc, or get (b : Bit) on P Q.
                  with {:ok, rest} <- tok(after_name, ":"),
                       {:ok, ty, rest} <- parse_pay(skip(rest), bound),
                       {:ok, rest} <- tok(skip(rest), ")") do
                    rest = skip(rest)

                    if word_kw?(rest, "on") do
                      parse_index_proc(rest, String.to_atom(name), ty, bound)
                    else
                      with {:ok, p, rest} <- parse_proc(rest, bound) do
                        {:ok, {:get, ty, String.to_atom(name), p}, rest}
                      end
                    end
                  end
                else
                  # Not a binder, fall back to old syntax: get Type proc
                  parse_get_no_binding(s, bound)
                end

              _ ->
                # Couldn't parse identifier, fall back
                parse_get_no_binding(s, bound)
            end

          _ ->
            parse_get_no_binding(s, bound)
        end
      else
        # No opening paren, must be old syntax: get Type proc
        parse_get_no_binding(s, bound)
      end
    end
  end

  defp parse_get_no_binding(s, bound) do
    with {:ok, rest} <- kw(s, "get"),
         {:ok, ty, rest} <- parse_pay(skip(rest), bound) do
      rest = skip(rest)

      if word_kw?(rest, "on") do
        {:error, err(rest, "a bit index is bound")}
      else
        with {:ok, p, rest} <- parse_proc(rest, bound) do
          # Use a generated anonymous variable name
          {:ok, {:get, ty, :_, p}, rest}
        end
      end
    end
  end

  defp parse_proc1(s, word, tag, bound) do
    note(skip(s))

    with {:ok, rest} <- kw(s, word),
         {:ok, p, rest} <- parse_proc(skip(rest), bound) do
      {:ok, {tag, p}, rest}
    end
  end

  defp parse_proc2(s, word, tag, bound) do
    note(skip(s))

    with {:ok, rest} <- kw(s, word),
         {:ok, p, rest} <- parse_proc(skip(rest), bound),
         {:ok, q, rest} <- parse_proc(skip(rest), bound) do
      {:ok, {tag, p, q}, rest}
    end
  end

  # `match b P Q` is one process per constructor of the value `get` just
  # bound, in declaration order. A bit is `b0` then `b1`. The arms stop
  # before the next declaration.
  defp parse_match(s, bound) do
    note(skip(s))

    with {:ok, rest} <- kw(s, "match"),
         {:ok, name, rest} <- match_name(skip(rest)),
         {:ok, arms, rest} <- parse_match_arms(skip(rest), [], bound) do
      {:ok, {:match, name, arms}, rest}
    end
  end

  defp match_name(s) do
    with {:ok, name, rest} <- ident(s) do
      if reserved_session?(name) or decl_word?(name) do
        {:error, err(s, "expected a name")}
      else
        {:ok, String.to_atom(name), rest}
      end
    end
  end

  defp parse_match_arms(s, acc, bound) do
    s = skip(s)

    cond do
      proc_start?(s) ->
        case parse_proc(s, bound) do
          {:ok, p, rest} -> parse_match_arms(rest, [p | acc], bound)
          err -> err
        end

      acc == [] ->
        {:error, err(s, "expected a process")}

      true ->
        {:ok, Enum.reverse(acc), s}
    end
  end

  defp proc_start?(s) do
    s = skip(s)

    cond do
      Enum.any?(~w(done stop put get pick0 pick1 cover rec match), &word_kw?(s, &1)) ->
        true

      has_prefix?(s, "(") ->
        true

      ident_start?(s) ->
        case ident(s) do
          {:ok, name, _} -> not reserved_session?(name) and not decl_word?(name)
          _ -> false
        end

      true ->
        false
    end
  end

  defp decl_word?(name) do
    name in ~w(def data session conform meet place scheme move endpoint read talk seat link relay import param where)
  end

  # A payload type. `Nat`, `Bit`, and `Unit` are those types. A name is
  # a declared data type, applied to the payload types written after it.
  # `*` is a pair, and a pair is a tuple. `{ name : type }` is a record,
  # and a record is a map whose keys are fixed in that order. A key
  # chosen at run time is not a type.
  defp parse_pay(s, bound \\ MapSet.new()) do
    with {:ok, ty, rest} <- parse_pay_atom(skip(s), bound) do
      parse_pay_rest(ty, rest, bound)
    end
  end

  defp parse_pay_rest(ty, s, bound) do
    s = skip(s)

    if has_prefix?(s, "*") and not has_prefix?(s, "**") do
      with {:ok, right, rest} <- parse_pay(after_kw(s, "*"), bound) do
        {:ok, {:pair, ty, right}, rest}
      end
    else
      {:ok, ty, s}
    end
  end

  defp parse_pay_atom(s, bound) do
    s = skip(s)

    cond do
      word_kw?(s, "Nat") -> {:ok, :nat, after_kw(s, "Nat")}
      word_kw?(s, "Bit") -> {:ok, :bit, after_kw(s, "Bit")}
      word_kw?(s, "Unit") -> {:ok, :unit, after_kw(s, "Unit")}
      word_kw?(s, "Vec") -> parse_vec(s, bound)
      has_prefix?(s, "(") -> parse_paren(s, fn body -> parse_pay(body, bound) end)
      has_prefix?(s, "{") -> parse_pay_rec(s, bound)
      ident_start?(s) and not pay_stop?(s) -> parse_dat(s, bound)
      true -> {:error, err(s, "expected a payload")}
    end
  end

  # `Maybe Nat` is that data type applied to `Nat`. A protocol keyword
  # is not an argument: `send Bool end` stops before `end`. A recursion
  # variable is the continuation, not an argument: `send Bool X`.
  defp parse_dat(s, bound) do
    with {:ok, name, rest} <- ident(s),
         {:ok, args, rest} <- take_pay_args(rest, [], bound) do
      {:ok, {:dat, name, args}, rest}
    end
  end

  defp take_pay_args(s, acc, bound) do
    s = skip(s)

    if pay_arg?(s, bound) do
      case parse_pay_atom(s, bound) do
        {:ok, ty, rest} -> take_pay_args(rest, [ty | acc], bound)
        _ -> {:ok, Enum.reverse(acc), s}
      end
    else
      {:ok, Enum.reverse(acc), s}
    end
  end

  defp pay_arg?(s, bound) do
    s = skip(s)

    cond do
      pay_stop?(s) ->
        false

      word_kw?(s, "Nat") or word_kw?(s, "Bit") or word_kw?(s, "Unit") or word_kw?(s, "Vec") ->
        true

      has_prefix?(s, "(") or has_prefix?(s, "{") ->
        true

      ident_start?(s) ->
        case ident(s) do
          {:ok, name, _} -> not MapSet.member?(bound, name)
          _ -> false
        end

      true ->
        false
    end
  end

  defp pay_stop?(s) do
    Enum.any?(
      ~w(end send recv choose branch rec on done stop put get pick0 pick1 cover where),
      &word_kw?(s, &1)
    )
  end

  # `Vec Nat n` and `Vec Nat 2`. The length is a numeral or a name.
  # A successor, or a missing length, is not a length.
  defp parse_vec(s, bound) do
    with {:ok, rest} <- kw(s, "Vec"),
         {:ok, elem, rest} <- parse_pay_atom(skip(rest), bound) do
      rest = skip(rest)

      cond do
        number?(rest) ->
          {digits, rest} = take_digits(rest, "")
          {:ok, {:vec, elem, {:lit, String.to_integer(digits)}}, rest}

        ident_start?(rest) ->
          case ident(rest) do
            {:ok, name, rest} -> {:ok, {:vec, elem, {:var, String.to_atom(name)}}, rest}
            err -> err
          end

        true ->
          {:error, err(rest, "expected a vector length")}
      end
    end
  end

  defp parse_pay_rec(s, bound) do
    with {:ok, rest} <- tok(s, "{"),
         {:ok, fields, rest} <- parse_pay_fields(skip(rest), [], bound) do
      {:ok, {:rec, fields}, rest}
    end
  end

  defp parse_pay_fields(s, acc, bound) do
    s = skip(s)

    if has_prefix?(s, "}") do
      {:ok, Enum.reverse(acc), after_kw(s, "}")}
    else
      with {:ok, name, rest} <- ident(s),
           {:ok, rest} <- tok(skip(rest), ":"),
           {:ok, ty, rest} <- parse_pay(skip(rest), bound),
           :ok <- fresh_field(name, acc, s),
           {:ok, more, rest} <- field_sep(skip(rest)) do
        case more do
          :end -> {:ok, Enum.reverse([{name, ty} | acc]), rest}
          :next -> parse_pay_fields(rest, [{name, ty} | acc], bound)
        end
      end
    end
  end

  # A payload value. A numeral is a nat. `tt` is unit. `b0` and `b1`
  # are bits. `(v, w)` is a pair. `{ name = v }` is a record. A name
  # with arguments is a constructor (`just 0`, `node leaf leaf`). A
  # name alone is a variable or a nullary constructor. The type is the
  # type of that value. `get` names a type and does not bind.
  defp parse_pval(s, bound) do
    parse_pval_atom(skip(s), bound)
  end

  defp parse_pval_atom(s, bound) do
    s = skip(s)

    cond do
      number?(s) ->
        parse_nat_val(s)

      word_kw?(s, "tt") ->
        {:ok, {:unit, :tt}, after_kw(s, "tt")}

      word_kw?(s, "b0") ->
        {:ok, {:bit, :b0}, after_kw(s, "b0")}

      word_kw?(s, "b1") ->
        {:ok, {:bit, :b1}, after_kw(s, "b1")}

      word_kw?(s, "rep") ->
        parse_rep(s, bound)

      has_prefix?(s, "(") ->
        parse_pval_paren(s, bound)

      has_prefix?(s, "{") ->
        parse_val_rec(s, bound)

      ident_start?(s) ->
        # A name with no arguments is a variable or a nullary constructor.
        # The binding wins; the checker decides which. Arguments make it
        # a constructor. A process keyword is not a value. A recursion
        # variable is the continuation, so it is not an argument.
        case ident(s) do
          {:ok, name, rest} ->
            if proc_word?(name) do
              {:error, err(s, "expected a value")}
            else
              case take_val_args(rest, [], bound) do
                {:ok, [], rest} -> {:ok, {:unknown, {:var, String.to_atom(name)}}, rest}
                {:ok, args, rest} -> {:ok, {:unknown, {:con, name, args}}, rest}
              end
            end

          err ->
            err
        end

      true ->
        {:error, err(s, "expected a value")}
    end
  end

  defp ident_start?(<<c, _::binary>>) when c in ?a..?z or c in ?A..?Z or c == ?_, do: true
  defp ident_start?(_), do: false

  # An argument is one value: a name does not take arguments of its own.
  # `node leaf leaf` is `node` applied to `leaf` and `leaf`.
  # `rep n 0` keeps `n` and `0` as two operands. A nested application
  # is parenthesized: `cons 0 (cons 0 nil)`.
  defp take_val_args(s, acc, bound) do
    s = skip(s)

    if val_arg?(s, bound) do
      case parse_pval_atomic(s, bound) do
        {:ok, {_ty, val}, rest} -> take_val_args(rest, [val | acc], bound)
        _ -> {:ok, Enum.reverse(acc), s}
      end
    else
      {:ok, Enum.reverse(acc), s}
    end
  end

  defp parse_pval_atomic(s, bound) do
    s = skip(s)

    cond do
      number?(s) ->
        parse_nat_val(s)

      word_kw?(s, "tt") ->
        {:ok, {:unit, :tt}, after_kw(s, "tt")}

      word_kw?(s, "b0") ->
        {:ok, {:bit, :b0}, after_kw(s, "b0")}

      word_kw?(s, "b1") ->
        {:ok, {:bit, :b1}, after_kw(s, "b1")}

      word_kw?(s, "rep") ->
        parse_rep(s, bound)

      has_prefix?(s, "(") ->
        parse_pval_paren(s, bound)

      has_prefix?(s, "{") ->
        parse_val_rec(s, bound)

      ident_start?(s) ->
        case ident(s) do
          {:ok, name, rest} ->
            if proc_word?(name) do
              {:error, err(s, "expected a value")}
            else
              {:ok, {:unknown, {:var, String.to_atom(name)}}, rest}
            end

          err ->
            err
        end

      true ->
        {:error, err(s, "expected a value")}
    end
  end

  defp val_arg?(s, bound) do
    s = skip(s)

    cond do
      number?(s) or word_kw?(s, "tt") or word_kw?(s, "b0") or word_kw?(s, "b1") or
          word_kw?(s, "rep") ->
        true

      has_prefix?(s, "(") or has_prefix?(s, "{") ->
        true

      ident_start?(s) ->
        case ident(s) do
          {:ok, name, _} -> not proc_word?(name) and not MapSet.member?(bound, name)
          _ -> false
        end

      true ->
        false
    end
  end

  defp proc_word?(name) do
    name in ~w(done stop put get pick0 pick1 cover rec match end send recv choose branch on)
  end

  defp number?(<<c, _::binary>>) when c in ?0..?9, do: true
  defp number?(_), do: false

  defp parse_nat_val(s) do
    {digits, rest} = take_digits(s, "")
    {:ok, {:nat, {:nat, String.to_integer(digits)}}, rest}
  end

  # `rep n 0` is a vector of that length. The length is a numeral or a name.
  defp parse_rep(s, bound) do
    with {:ok, rest} <- kw(s, "rep"),
         {:ok, {_ity, ix}, rest} <- parse_pval_atomic(skip(rest), bound),
         {:ok, {ety, elem}, rest} <- parse_pval_atomic(skip(rest), bound),
         {:ok, ixexp} <- length_exp(ix, s) do
      {:ok, {{:vec, ety, ixexp}, {:rep, ix, elem}}, rest}
    end
  end

  defp length_exp({:nat, n}, _s) when is_integer(n) and n >= 0, do: {:ok, {:lit, n}}
  defp length_exp({:var, name}, _s), do: {:ok, {:var, name}}
  defp length_exp(_ix, s), do: {:error, err(s, "vector length is not a nat")}

  defp take_digits(<<c, r::binary>>, acc) when c in ?0..?9, do: take_digits(r, acc <> <<c>>)
  defp take_digits(s, acc), do: {acc, s}

  defp parse_pval_paren(s, bound) do
    with {:ok, rest} <- tok(s, "("),
         {:ok, {ty, val}, rest} <- parse_pval(skip(rest), bound) do
      rest = skip(rest)

      cond do
        has_prefix?(rest, ",") ->
          with {:ok, {ty2, val2}, rest} <- parse_pval(after_kw(rest, ","), bound),
               {:ok, rest} <- tok(skip(rest), ")") do
            {:ok, {{:pair, ty, ty2}, {:tup, val, val2}}, rest}
          end

        has_prefix?(rest, ")") ->
          {:ok, {ty, val}, after_kw(rest, ")")}

        true ->
          {:error, err(rest, "expected , or )")}
      end
    end
  end

  defp parse_val_rec(s, bound) do
    with {:ok, rest} <- tok(s, "{"),
         {:ok, fields, rest} <- parse_val_fields(skip(rest), [], bound) do
      tys = Enum.map(fields, fn {name, ty, _} -> {name, ty} end)
      vals = Enum.map(fields, fn {name, _, val} -> {name, val} end)
      {:ok, {{:rec, tys}, {:rec, vals}}, rest}
    end
  end

  defp parse_val_fields(s, acc, bound) do
    s = skip(s)

    if has_prefix?(s, "}") do
      {:ok, Enum.reverse(acc), after_kw(s, "}")}
    else
      with {:ok, name, rest} <- ident(s),
           {:ok, rest} <- field_eq(skip(rest)),
           {:ok, {ty, val}, rest} <- parse_pval(skip(rest), bound),
           :ok <- fresh_field(name, acc, s),
           {:ok, more, rest} <- field_sep(skip(rest)) do
        case more do
          :end -> {:ok, Enum.reverse([{name, ty, val} | acc]), rest}
          :next -> parse_val_fields(rest, [{name, ty, val} | acc], bound)
        end
      end
    end
  end

  defp field_sep(s) do
    cond do
      has_prefix?(s, ",") -> {:ok, :next, after_kw(s, ",")}
      has_prefix?(s, "}") -> {:ok, :end, after_kw(s, "}")}
      true -> {:error, err(s, "expected , or }")}
    end
  end

  defp field_eq(s) do
    if has_prefix?(s, "=") and not has_prefix?(s, "==") and not has_prefix?(s, "=>") do
      {:ok, after_kw(s, "=")}
    else
      {:error, err(s, "expected =")}
    end
  end

  defp fresh_field(name, acc, s) do
    if Enum.any?(acc, fn
         {n, _, _} -> n == name
         {n, _} -> n == name
       end) do
      {:error, err(s, "duplicate field #{name}")}
    else
      :ok
    end
  end

  defp parse_paren(s, parse) do
    with {:ok, rest} <- tok(s, "("),
         {:ok, x, rest} <- parse.(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ")") do
      {:ok, x, rest}
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

      word_kw?(s, "def") or word_kw?(s, "data") or word_kw?(s, "param") or
        word_kw?(s, "session") or word_kw?(s, "conform") or nu_start?(s) or
        place_entry?(s) or scheme_entry?(s) or move_entry?(s) or
        endpoint_entry?(s) or read_entry?(s) or meet_entry?(s) or talk_start?(s) or
        seat_start?(s) or link_start?(s) ->
        {:ok, Enum.reverse(acc), s}

      true ->
        with {:ok, cname, rest} <- ident(s),
             {:ok, rest} <- tok(skip(rest), ":"),
             {:ok, ty, rest} <- parse_term(skip(rest), 0) do
          parse_ctors(rest, [%{name: cname, type: ty} | acc])
        end
    end
  end

  # `def name : run|spec|evidence …` is a core definition.
  # `def name : (s : session) ⊸ …` is an endpoint function. The type
  # starts with `(`, which a tagged definition does not.
  defp parse_def(s) do
    loc = here(s)

    with {:ok, rest} <- kw(s, "def"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":") do
      rest = skip(rest)

      if has_prefix?(rest, "("),
        do: parse_relay(loc, name, rest),
        else: parse_tagged_def(loc, name, rest)
    end
  end

  defp parse_tagged_def(loc, name, s) do
    with {:ok, tag, rest} <- parse_mode(s),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, body, rest} <- parse_term(skip(rest), 0) do
      {:ok, Map.merge(%{name: name, type: ty, body: body, loc: loc}, tag), rest}
    end
  end

  # Evidence. The arrow's multiplicity is the binder's obligation.
  # `⊸` (`-o`) accepts or returns a linear endpoint. `→` is affine.
  defp parse_relay(loc, name, s) do
    with {:ok, ty, rest} <- parse_etype(s, :aff),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, body, rest} <- parse_eterm(skip(rest)) do
      {:ok, %{kind: :relay, name: name, mode: :evidence, type: ty, body: body, loc: loc}, rest}
    end
  end

  # A bare session name takes `bare`. `done` is the meeting, not a session.
  defp parse_etype(s, bare) do
    s = skip(s)

    cond do
      has_prefix?(s, "(") ->
        with {:ok, _x, sess, rest} <- parse_ebinder(s),
             {:ok, q, rest} <- eat_earrow(rest),
             {:ok, cod, rest} <- parse_etype(rest, q) do
          {:ok, {:arr, q, {:sess, q, sess}, cod}, rest}
        end

      word_kw?(s, "done") ->
        {:ok, {:done}, after_kw(s, "done")}

      true ->
        with {:ok, name, rest} <- ident(s) do
          {:ok, {:sess, bare, name}, rest}
        end
    end
  end

  # `+`, `-`, and `%` are term quantities. An endpoint is affine or linear.
  defp parse_ebinder(s) do
    with {:ok, rest} <- tok(skip(s), "(") do
      rest = skip(rest)

      cond do
        has_prefix?(rest, "+") or has_prefix?(rest, "-") or has_prefix?(rest, "%") ->
          {:error, err(rest, "a session endpoint is affine or linear")}

        true ->
          with {:ok, name, rest} <- ident(rest),
               {:ok, rest} <- tok(skip(rest), ":"),
               {:ok, sess, rest} <- ident(skip(rest)),
               {:ok, rest} <- tok(skip(rest), ")") do
            {:ok, name, sess, rest}
          end
      end
    end
  end

  # `λ¹` (`lam1`) is linear. `λ` (`lam`) is affine. The arrow after the
  # binder may be `→` or `⊸`. The multiplicity is the lambda's.
  defp parse_eterm(s) do
    with {:ok, left, rest} <- parse_eatom(skip(s)) do
      parse_eapp(rest, left)
    end
  end

  defp parse_eapp(s, left) do
    s0 = skip(s)

    cond do
      s0 == "" or eboundary?(s0) or not eatom_start?(s0) ->
        {:ok, left, s}

      true ->
        with {:ok, arg, rest} <- parse_eatom(s0) do
          parse_eapp(rest, {:app, left, arg})
        end
    end
  end

  defp parse_eatom(s) do
    s = skip(s)

    cond do
      has_prefix?(s, "(") ->
        with {:ok, rest} <- tok(s, "("),
             {:ok, t, rest} <- parse_eterm(rest),
             {:ok, rest} <- tok(skip(rest), ")") do
          {:ok, t, rest}
        end

      word_kw?(s, "λ¹") || word_kw?(s, "lam1") || word_kw?(s, "λ") || word_kw?(s, "lam") ->
        parse_elam(s)

      word_kw?(s, "dual") ->
        parse_edual(s)

      word_kw?(s, "meet") ->
        parse_emeet(s)

      true ->
        with {:ok, name, rest} <- ident(s) do
          {:ok, {:var, name}, rest}
        end
    end
  end

  defp parse_elam(s) do
    s = skip(s)

    {q, rest} =
      cond do
        word_kw?(s, "λ¹") -> {:lin, after_kw(s, "λ¹")}
        word_kw?(s, "lam1") -> {:lin, after_kw(s, "lam1")}
        word_kw?(s, "λ") -> {:aff, after_kw(s, "λ")}
        word_kw?(s, "lam") -> {:aff, after_kw(s, "lam")}
      end

    with {:ok, name, sess, rest} <- parse_ebinder(rest),
         {:ok, _arrow, rest} <- eat_earrow(rest),
         {:ok, body, rest} <- parse_eterm(rest) do
      {:ok, {:lam, q, name, {:sess, q, sess}, body}, rest}
    end
  end

  defp parse_edual(s) do
    with {:ok, rest} <- kw(s, "dual"),
         {:ok, t, rest} <- parse_eatom(skip(rest)) do
      {:ok, {:dual, t}, rest}
    end
  end

  defp parse_emeet(s) do
    with {:ok, rest} <- kw(s, "meet"),
         {:ok, a, rest} <- parse_eatom(skip(rest)),
         {:ok, b, rest} <- parse_eatom(skip(rest)) do
      {:ok, {:meet, a, b}, rest}
    end
  end

  defp eat_earrow(s) do
    s = skip(s)

    cond do
      has_prefix?(s, "⊸") -> {:ok, :lin, after_kw(s, "⊸")}
      has_prefix?(s, "-o") -> {:ok, :lin, after_kw(s, "-o")}
      has_prefix?(s, "→") -> {:ok, :aff, after_kw(s, "→")}
      has_prefix?(s, "->") and not has_prefix?(s, "=>") -> {:ok, :aff, after_kw(s, "->")}
      true -> {:error, err(s, "expected ⊸")}
    end
  end

  # A following book entry is not an argument. `meet s t` is the term.
  # `meet name :` is the next entry.
  defp eboundary?(s) do
    s = skip(s)

    word_kw?(s, "def") or word_kw?(s, "data") or word_kw?(s, "param") or
      word_kw?(s, "import") or word_kw?(s, "session") or word_kw?(s, "conform") or
      word_kw?(s, "where") or word_kw?(s, "motive") or word_kw?(s, "in") or
      nu_start?(s) or place_entry?(s) or scheme_entry?(s) or move_entry?(s) or
      endpoint_entry?(s) or read_entry?(s) or meet_entry?(s) or talk_start?(s) or
      seat_start?(s) or link_start?(s)
  end

  defp eatom_start?(s) do
    s = skip(s)

    cond do
      eboundary?(s) ->
        false

      has_prefix?(s, "(") ->
        true

      word_kw?(s, "λ¹") || word_kw?(s, "lam1") || word_kw?(s, "λ") || word_kw?(s, "lam") ->
        true

      word_kw?(s, "dual") or word_kw?(s, "meet") ->
        true

      true ->
        case s do
          <<c, _::binary>> when c in ?a..?z or c in ?A..?Z or c == ?_ -> true
          _ -> false
        end
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
    rest != "" and ident_char?(String.first(rest)) and not String.starts_with?(rest, "->")
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

      starts_atom?(s0) and min_bp <= 20 and not ctor_decl_start?(s, s0) and
          not session_line?(s, s0) ->
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

  # `session` and `conform` use `:=`, so ctor_decl_start? does not see
  # them. A new line that starts either form, or a place, scheme, move,
  # endpoint, reading, meeting, talk, seat, or link entry, ends the
  # constructor's type.
  defp session_line?(s, s0) do
    skipped = binary_part(s, 0, byte_size(s) - byte_size(s0))

    String.contains?(skipped, "\n") and
      (session_start?(s0) or conform_start?(s0) or place_entry?(s0) or scheme_entry?(s0) or
         move_entry?(s0) or endpoint_entry?(s0) or read_entry?(s0) or meet_entry?(s0) or
         talk_start?(s0) or seat_start?(s0) or link_start?(s0))
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

      word_kw?(s, "param") ->
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

      word_kw?(s, "Type") ->
        {:ok, :typ, after_kw(s, "Type")}

      word_kw?(s, "Nat") ->
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

      word_kw?(s, "Unit") ->
        {:ok, :unit, after_kw(s, "Unit")}

      word_kw?(s, "Empty") ->
        {:ok, :empty, after_kw(s, "Empty")}

      word_kw?(s, "refl") ->
        {:ok, :rfl, after_kw(s, "refl")}

      word_kw?(s, "tt") ->
        {:ok, :one, after_kw(s, "tt")}

      has_prefix?(s, "?") ->
        {:ok, {:hole, here(s)}, after_kw(s, "?")}

      has_prefix?(s, "0") ->
        {:ok, :ze, after_kw(s, "0")}

      word_kw?(s, "suc") ->
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

      word_kw?(s, "matchEmpty") ->
        parse_memp(s)

      word_kw?(s, "match") ->
        parse_match(s)

      word_kw?(s, "rewrite") ->
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

  # %0 is affine. %1 is the affine quantity that must be used.
  # Both are whole tokens. %10 is not %1 followed by 0.
  defp parse_qty("%" <> _ = s) do
    case parse_mult(s) do
      {:ok, :linear, rest} -> {:ok, :linear, rest}
      {:ok, :affine, rest} -> {:ok, :affine, rest}
      {:error, _} = err -> err
    end
  end

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
      # Keep the newline. A following `session` or `conform` is not an argument.
      looked = skip(rest)

      if has_prefix?(looked, "|") do
        with {:ok, rest} <- tok(looked, "|") do
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
      # Keep the newline. A following `session` or `conform` is not an argument.
      looked = skip(rest)

      if has_prefix?(looked, "|") do
        with {:ok, rest} <- tok(looked, "|") do
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
