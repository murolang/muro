defmodule Muro.Fill do
  @moduledoc """
  Fill one definition body by type-directed search.

  The book already declares the definition and its type. Candidates are
  terms the checker already accepts. The first one the checker accepts is
  written back. A run is kept only when the book's closed equations about
  that name still check. Evidence is kept when the type checks, and a spec
  is kept the same way. Nothing here is a new judgment, and nothing here
  is `mix muro.synth`.
  """

  @default_bound 8

  @doc false
  def default_bound, do: @default_bound

  @doc """
  Fill `name` in `path`. Options: `name`, `bound` (default #{@default_bound}),
  `fuel` (default `Muro.Check.default_fuel/0`).

  Returns `{:ok, info}` when a body was written, `{:error, {:bound, info}}`
  when the bound was reached and the file is unchanged, or `{:error, message}`.
  """
  def fill(path, opts \\ []) when is_binary(path) and is_list(opts) do
    name = Keyword.get(opts, :name)
    bound = Keyword.get(opts, :bound, @default_bound)
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())

    cond do
      not is_binary(name) or name == "" ->
        {:error, "missing --def"}

      not (is_integer(bound) and bound >= 1) ->
        {:error, "--bound must be a positive integer"}

      not (is_integer(fuel) and fuel >= 1) ->
        {:error, "--fuel must be a positive integer"}

      true ->
        fill_file(path, name, bound, fuel)
    end
  end

  @doc false
  def candidates(source, name, bound)
      when is_binary(source) and is_binary(name) and is_integer(bound) do
    with {:ok, book} <- Muro.Parser.parse(source),
         {:ok, d} <- one_def(book, name) do
      Muro.Fill.Enum.clear()

      try do
        env = environment(Muro.Prelude.for_check(book), d)

        terms =
          Enum.flat_map(1..max(bound, 0), fn size ->
            Muro.Fill.Enum.terms(env, d.type, size)
          end)

        {:ok, terms}
      after
        Muro.Fill.Enum.clear()
      end
    end
  end

  @doc false
  def refers?(term, name) when is_binary(name), do: Muro.Fill.Enum.refers?(term, name)

  @doc false
  def distinct_count(source, name, terms, fuel \\ Muro.Check.default_fuel())
      when is_binary(source) and is_binary(name) and is_list(terms) and is_integer(fuel) do
    with {:ok, book} <- Muro.Parser.parse(source),
         {:ok, _d} <- one_def(book, name),
         user = stamp(book, "fill-distinct.muro"),
         full = Muro.Prelude.for_check(user),
         {:ok, db_book} <- Muro.Ast.book_to_db(full) do
      count =
        terms
        |> Enum.reduce({0, MapSet.new()}, fn term, {n, seen} ->
          case observe(term, seen, db_book, fuel) do
            {:dup, seen} -> {n, seen}
            {:new, _db, seen} -> {n + 1, seen}
            {:bad, seen} -> {n + 1, seen}
          end
        end)
        |> elem(0)

      {:ok, count}
    end
  end

  @doc false
  def bound_message(%{
        bound: bound,
        tried: tried,
        equations_failed: equations,
        book_failed: book,
        fuel_failed: fuel
      }) do
    head = "bound #{bound} reached: tried #{tried} #{plural(tried, "candidate")}"

    parts =
      Enum.reject(
        [
          equation_clause(equations, book, fuel),
          if(book > 0, do: "#{book} failed the book"),
          if(fuel > 0, do: "#{fuel} ran out of fuel")
        ],
        &is_nil/1
      )

    Enum.join([head | parts], ", ")
  end

  defp equation_clause(equations, book, fuel)
       when equations > 0 or (book == 0 and fuel == 0) do
    "#{equations} type-checked but failed the closed equations"
  end

  defp equation_clause(_equations, _book, _fuel), do: nil

  defp fill_file(path, name, bound, fuel) do
    expanded = Path.expand(path)

    with {:ok, src} <- read(expanded),
         {:ok, book} <- parse(src),
         :ok <- no_import(book),
         {:ok, d} <- one_def(book, name),
         {:ok, loc} <- hole_loc(d),
         :ok <- no_other_hole(book, name),
         user = stamp(book, expanded),
         full = Muro.Prelude.for_check(user),
         {:ok, db_book} <- Muro.Ast.book_to_db(full) do
      Muro.Fill.Enum.clear()

      try do
        env = environment(full, d)

        ctx = %{
          name: name,
          mode: d.mode,
          db_book: db_book,
          user_book: user,
          equations: equation_names(user, expanded, name),
          fuel: fuel
        }

        case search(env, d.type, bound, ctx) do
          {:ok, term, state} ->
            write_body(expanded, src, loc, term, name, state, bound, fuel)

          {:bound, state} ->
            {:error, {:bound, bound_info(state, bound)}}
        end
      after
        Muro.Fill.Enum.clear()
      end
    end
  end

  defp search(env, goal, bound, ctx) do
    initial = %{tried: 0, equations_failed: 0, book_failed: 0, fuel_failed: 0, seen: MapSet.new()}

    1..bound
    |> Enum.reduce_while(initial, fn size, state ->
      case try_size(Muro.Fill.Enum.terms(env, goal, size), state, ctx) do
        {:accept, _term, _state} = done -> {:halt, done}
        state -> {:cont, state}
      end
    end)
    |> case do
      {:accept, term, state} -> {:ok, term, state}
      state -> {:bound, state}
    end
  end

  defp try_size(terms, state, ctx) do
    Enum.reduce_while(terms, state, fn term, state ->
      case consider(term, state, ctx) do
        {:accept, _term, _state} = done -> {:halt, done}
        state -> {:cont, state}
      end
    end)
  end

  defp consider(term, state, ctx) do
    case observe(term, state.seen, ctx.db_book, ctx.fuel) do
      {:dup, _seen} ->
        state

      {:bad, _seen} ->
        %{state | tried: state.tried + 1}

      {:new, db, seen} ->
        state = %{state | seen: seen, tried: state.tried + 1}
        judge(term, db, state, ctx)
    end
  end

  # One normal form is tried once. `distinct_count/4` uses this same key,
  # so a redex that normalizes away is not a second candidate.
  defp observe(term, seen, db_book, fuel) do
    case Muro.Ast.to_db(term) do
      {:ok, db} ->
        key = nf_key(db_book, db, fuel)

        if MapSet.member?(seen, key),
          do: {:dup, seen},
          else: {:new, db, MapSet.put(seen, key)}

      {:error, _} ->
        {:bad, seen}
    end
  end

  defp judge(term, db, state, ctx) do
    book = install(ctx.db_book, ctx.name, db)

    case Muro.Check.check_def(book, find_body(book, ctx.name), ctx.fuel) do
      :ok ->
        if ctx.mode == :run do
          case check_equations(book, ctx) do
            :ok -> accept_sig(term, state, ctx)
            {:error, msg} -> note_failure(state, msg, :equations_failed)
          end
        else
          accept_sig(term, state, ctx)
        end

      {:error, msg} ->
        if Muro.Check.out_of_fuel?(msg), do: bump(state, :fuel_failed), else: state
    end
  end

  defp accept_sig(term, state, ctx) do
    named = install(ctx.user_book, ctx.name, term)

    case Muro.Check.check_sig(Muro.Prelude.for_check(named), fuel: ctx.fuel) do
      :ok -> {:accept, term, state}
      {:error, msg} -> note_failure(state, msg, :book_failed)
    end
  end

  # A closed equation that does not hold is the equation counter. Fuel,
  # another hole, and any other book failure are not that counter.
  defp note_failure(state, msg, :equations_failed) do
    cond do
      Muro.Check.out_of_fuel?(msg) -> bump(state, :fuel_failed)
      String.contains?(msg, "unsolved hole") -> bump(state, :book_failed)
      true -> bump(state, :equations_failed)
    end
  end

  defp note_failure(state, msg, :book_failed) do
    cond do
      Muro.Check.out_of_fuel?(msg) -> bump(state, :fuel_failed)
      true -> bump(state, :book_failed)
    end
  end

  defp check_equations(book, ctx) do
    Enum.reduce_while(ctx.equations, :ok, fn name, :ok ->
      case Muro.Check.check_def(book, find_body(book, name), ctx.fuel) do
        :ok -> {:cont, :ok}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp bump(state, key), do: Map.update!(state, key, &(&1 + 1))

  defp bound_info(state, bound) do
    %{
      bound: bound,
      tried: state.tried,
      equations_failed: state.equations_failed,
      book_failed: state.book_failed,
      fuel_failed: state.fuel_failed
    }
  end

  defp nf_key(book, term, fuel) do
    case nf_term(book, term, fuel, 0) do
      {:ok, normal} -> {:nf, Muro.Fill.Enum.erase(normal)}
      _ -> {:raw, Muro.Fill.Enum.erase(term)}
    end
  end

  # `Check.normalize/3` does not enter a λ. Walk under binders so
  # `λ n → pred 0` meets `λ n → 0`.
  defp nf_term(_book, term, _fuel, depth) when depth > 32, do: {:ok, term}

  defp nf_term(book, term, fuel, depth) do
    case Muro.Check.normalize(book, term, fuel) do
      {:ok, normal} -> open_binders(book, normal, fuel, depth)
      {:error, _} = err -> err
    end
  end

  defp open_binders(book, {:lam, qty, dom, name, body}, fuel, depth) do
    with {:ok, dom} <- nf_term(book, dom, fuel, depth + 1),
         {:ok, body} <- nf_term(book, body, fuel, depth + 1) do
      {:ok, {:lam, qty, dom, name, body}}
    end
  end

  defp open_binders(book, {:mnat, scrut, motive, zero, suc}, fuel, depth) do
    with {:ok, scrut} <- nf_term(book, scrut, fuel, depth + 1),
         {:ok, motive} <- nf_term(book, motive, fuel, depth + 1),
         {:ok, zero} <- nf_term(book, zero, fuel, depth + 1),
         {:ok, suc} <- nf_term(book, suc, fuel, depth + 1) do
      {:ok, {:mnat, scrut, motive, zero, suc}}
    end
  end

  # The motive sits under one binder. Each branch body sits under that
  # branch's arity. A stuck scrutinee stays a match, so a redex in a
  # branch is still part of the normal form.
  defp open_binders(book, {:mdata, scrut, motive, branches}, fuel, depth) do
    with {:ok, scrut1} <- nf_term(book, scrut, fuel, depth + 1),
         {:ok, motive1} <- nf_term(book, motive, fuel, depth + 2),
         {:ok, branches1} <- nf_mdata_branches(book, branches, fuel, depth) do
      rebuilt = {:mdata, scrut1, motive1, branches1}

      if rebuilt == {:mdata, scrut, motive, branches},
        do: {:ok, rebuilt},
        else: nf_term(book, rebuilt, fuel, depth + 1)
    end
  end

  defp open_binders(book, {:su, term}, fuel, depth) do
    with {:ok, term} <- nf_term(book, term, fuel, depth + 1), do: {:ok, {:su, term}}
  end

  defp open_binders(book, {:app, fun, arg}, fuel, depth) do
    with {:ok, fun1} <- nf_term(book, fun, fuel, depth + 1),
         {:ok, arg1} <- nf_term(book, arg, fuel, depth + 1) do
      rebuilt = {:app, fun1, arg1}

      if rebuilt == {:app, fun, arg},
        do: {:ok, rebuilt},
        else: nf_term(book, rebuilt, fuel, depth + 1)
    end
  end

  defp open_binders(_book, term, _fuel, _depth), do: {:ok, term}

  defp nf_mdata_branches(_book, [], _fuel, _depth), do: {:ok, []}

  defp nf_mdata_branches(book, [{name, arity, body} | rest], fuel, depth) do
    with {:ok, body1} <- nf_term(book, body, fuel, depth + 1 + arity),
         {:ok, rest1} <- nf_mdata_branches(book, rest, fuel, depth) do
      {:ok, [{name, arity, body1} | rest1]}
    end
  end

  defp equation_names(user, path, name) do
    user
    |> Muro.Emit.ExUnitSuite.closed_equations(path)
    |> Enum.filter(&(Muro.Emit.ExUnitSuite.equation_head(&1) == name))
    |> Enum.map(& &1.name)
  end

  defp environment(book, target) do
    defs =
      for d <- book,
          term_def?(d),
          d.name != target.name,
          mode_ok?(d.mode, target.mode),
          not hole_body?(d.body) do
        %{name: d.name, mode: d.mode, type: d.type}
      end

    datas =
      for %{kind: :data} = d <- book do
        %{name: d.name, params: d.params, indices: Map.get(d, :indices, []), ctors: d.ctors}
      end

    %{mode: target.mode, binders: [], defs: defs, datas: datas, target: target.name}
  end

  defp term_def?(%{mode: mode, type: _, body: _} = d) when mode in [:run, :spec, :evidence] do
    Map.get(d, :kind) in [nil, :def]
  end

  defp term_def?(_other), do: false

  defp mode_ok?(from, to) do
    from == to or from == :run or (from == :evidence and to == :spec)
  end

  defp hole_body?({:hole, _}), do: true
  defp hole_body?(_other), do: false

  defp one_def(book, name) do
    case Enum.filter(book, &(term_def?(&1) and &1.name == name)) do
      [d] -> {:ok, d}
      [] -> {:error, "unknown definition #{name}"}
      _ -> {:error, "#{name} is defined more than once"}
    end
  end

  defp hole_loc(%{body: {:hole, {line, col}}}) when is_integer(line) and is_integer(col) do
    {:ok, {line, col}}
  end

  defp hole_loc(%{name: name, body: {:hole, _}}),
    do: {:error, "#{name}: the hole has no source location"}

  defp hole_loc(%{name: name}), do: {:error, "#{name}: the body is not ?"}

  defp no_import(book) do
    if Enum.any?(book, &(Map.get(&1, :kind) in [:import, :param])) do
      {:error, "fill reads one file and the prelude"}
    else
      :ok
    end
  end

  defp no_other_hole(book, name) do
    if other_holes(book, name) == [], do: :ok, else: {:error, "the book has another hole"}
  end

  defp other_holes(book, name) do
    Enum.flat_map(book, fn d ->
      holes = entry_holes(d)

      case d do
        %{name: ^name, body: {:hole, _} = hole} -> List.delete(holes, hole)
        _ -> holes
      end
    end)
  end

  defp entry_holes(d) when is_map(d) do
    d
    |> Map.drop([:file, :loc, :name, :mode, :kind, :export, :type_span, :body_span])
    |> Map.values()
    |> Enum.flat_map(&holes_in/1)
  end

  defp holes_in({:hole, _} = hole), do: [hole]

  defp holes_in(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&holes_in/1)

  defp holes_in(term) when is_list(term), do: Enum.flat_map(term, &holes_in/1)
  defp holes_in(term) when is_map(term), do: term |> Map.values() |> Enum.flat_map(&holes_in/1)
  defp holes_in(_other), do: []

  defp stamp(book, path), do: Enum.map(book, &Map.put(&1, :file, path))

  defp install(book, name, body) do
    Enum.map(book, fn
      %{name: ^name, body: _} = d -> %{d | body: body}
      other -> other
    end)
  end

  defp find_body(book, name) do
    Enum.find(book, fn d -> Map.get(d, :name) == name and Map.has_key?(d, :body) end)
  end

  defp read(path) do
    case File.read(path) do
      {:ok, src} -> {:ok, src}
      {:error, _} -> {:error, "missing file #{path}"}
    end
  end

  defp parse(src) do
    case Muro.Parser.parse(src) do
      {:ok, book} -> {:ok, book}
      {:error, msg} -> {:error, msg}
    end
  end

  defp write_body(path, src, loc, term, name, state, bound, fuel) do
    with {:ok, written} <- surface(term),
         {:ok, text} <- splice(src, loc, written),
         :ok <- round_trip(text, path, fuel),
         :ok <- write_atomic(path, text) do
      {:ok,
       %{
         status: :filled,
         name: name,
         tried: state.tried,
         equations_failed: state.equations_failed,
         book_failed: state.book_failed,
         fuel_failed: state.fuel_failed,
         bound: bound,
         body: term
       }}
    end
  end

  defp surface(term) do
    try do
      {:ok, show(term)}
    catch
      :muro_fill_show -> {:error, "the candidate has no surface form"}
    end
  end

  defp round_trip(text, path, fuel) do
    with {:ok, book} <- parse(text) do
      case Muro.Check.check_sig(Muro.Prelude.for_check(stamp(book, path)), fuel: fuel) do
        :ok -> :ok
        {:error, msg} -> {:error, msg}
      end
    end
  end

  defp splice(src, {line, col}, replacement) do
    parts = String.split(src, "\n")

    if line < 1 or line > length(parts) or col < 1 do
      {:error, "the hole is outside the file"}
    else
      line_text = Enum.at(parts, line - 1)
      prefix_len = col - 1

      if prefix_len > byte_size(line_text) do
        {:error, "the hole is outside the file"}
      else
        prefix = binary_part(line_text, 0, prefix_len)
        rest = binary_part(line_text, prefix_len, byte_size(line_text) - prefix_len)

        case rest do
          "?" <> after_hole ->
            updated = prefix <> replacement <> after_hole
            {head, [_old | tail]} = Enum.split(parts, line - 1)
            {:ok, Enum.join(head ++ [updated | tail], "\n")}

          _ ->
            {:error, "the hole byte is not ?"}
        end
      end
    end
  end

  defp write_atomic(path, text) do
    tmp = Path.join(Path.dirname(path), ".muro-fill-#{System.unique_integer([:positive])}.tmp")

    try do
      File.write!(tmp, text, [:sync])
      File.rename!(tmp, path)
      :ok
    rescue
      error ->
        _ = File.rm(tmp)
        {:error, Exception.message(error)}
    end
  end

  def show(term), do: show(term, :none)

  defp show(:ze, _), do: "0"
  defp show(:one, _), do: "tt"
  defp show(:rfl, _), do: "refl"
  defp show(:nat, _), do: "Nat"
  defp show(:unit, _), do: "Unit"
  defp show(:empty, _), do: "Empty"
  defp show(:typ, _), do: "Type"
  defp show({:nat, n}, _) when is_integer(n), do: Integer.to_string(n)
  defp show({:var, name}, _), do: name
  defp show({:def, name}, _), do: name
  defp show({:su, term}, _), do: "suc(" <> show(term, :none) <> ")"

  defp show({:lam, qty, dom, name, body}, prec) do
    wrap(prec, :arrow, "λ (#{mark(qty)}#{name} : #{show(dom, :none)}) → #{show(body, :arrow)}")
  end

  defp show({:pi, qty, dom, name, cod}, prec) do
    wrap(prec, :arrow, "Π (#{mark(qty)}#{name} : #{show(dom, :none)}) → #{show(cod, :arrow)}")
  end

  defp show({:app, _, _} = term, prec) do
    {head, args} = spine(term, [])
    text = Enum.join([show_head(head) | Enum.map(args, &show_arg/1)], " ")
    wrap(prec, :app, text)
  end

  defp show({:idt, ty, left, right}, _) do
    "{#{show(left, :none)} ≡ #{show(right, :none)} : #{show(ty, :none)}}"
  end

  defp show({:mnat, scrut, motive, motive_body, zero, suc_name, suc}, prec) do
    text =
      "match #{show(scrut, :none)} motive (λ #{motive_name(motive)} → #{show(motive_body, :none)}) | 0 => #{show_branch(zero)} | suc #{suc_name} => #{show_branch(suc)}"

    wrap(prec, :app, text)
  end

  defp show({:mdata, scrut, motive, motive_body, branches}, prec) do
    arms =
      Enum.map_join(branches, " ", fn {ctor, binders, body} ->
        args = if binders == [], do: "", else: " " <> Enum.join(binders, " ")
        "| #{ctor}#{args} => #{show_branch(body)}"
      end)

    text =
      "match #{show(scrut, :none)} motive (λ #{motive_name(motive)} → #{show(motive_body, :none)}) #{arms}"

    wrap(prec, :app, text)
  end

  defp show(_other, _), do: throw(:muro_fill_show)

  defp spine({:app, fun, arg}, acc), do: spine(fun, [arg | acc])
  defp spine(head, acc), do: {head, acc}

  defp show_head(term) do
    if atom?(term), do: show(term, :none), else: "(" <> show(term, :none) <> ")"
  end

  defp show_arg(term) do
    if atom?(term), do: show(term, :none), else: "(" <> show(term, :none) <> ")"
  end

  defp show_branch({:mnat, _, _, _, _, _, _} = term), do: "(" <> show(term, :none) <> ")"
  defp show_branch({:mdata, _, _, _, _} = term), do: "(" <> show(term, :none) <> ")"
  defp show_branch({:lam, _, _, _, _} = term), do: "(" <> show(term, :none) <> ")"
  defp show_branch(term), do: show(term, :none)

  defp motive_name("_"), do: "_"
  defp motive_name(name), do: name

  defp atom?(:ze), do: true
  defp atom?(:one), do: true
  defp atom?(:rfl), do: true
  defp atom?(:nat), do: true
  defp atom?(:unit), do: true
  defp atom?(:empty), do: true
  defp atom?(:typ), do: true
  defp atom?({:var, _}), do: true
  defp atom?({:def, _}), do: true
  defp atom?({:nat, n}) when is_integer(n), do: true
  defp atom?(_other), do: false

  defp mark(:erased), do: "-"
  defp mark(:reuse), do: "+"
  defp mark(:linear), do: "%1 "
  defp mark({:grade, c, t}), do: "(#{Muro.Grade.show(c)}, #{Muro.Grade.show(t)}) "
  defp mark(_qty), do: ""

  defp wrap(:none, _kind, text), do: text
  defp wrap(:arrow, :arrow, text), do: text
  defp wrap(_prec, _kind, text), do: "(" <> text <> ")"

  defp plural(1, word), do: word
  defp plural(_n, word), do: word <> "s"
end
