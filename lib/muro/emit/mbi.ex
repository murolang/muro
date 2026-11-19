defmodule Muro.Emit.Mbi do
  @moduledoc """
  Erase one exported run to an .mbi image.

  The rules for one term are `agda/Muro/Beam.agda`. A grade pair and
  the `%1` mark are not constructors of `Tm`, so this module reads
  them. A run the entry reaches is a closed definition in the image.
  `GTm` has no `gref`; the index is written here. Success is exactly
  one exported run. The image is text. muro-beam loads it and checks
  the term again. The file is not Erlang BEAM bytecode. Writing the
  image is not that check. See [MBI images](manual/mbi.md).
  """

  alias Muro.Ast

  @format_version 1
  @format_defs 2
  @boundary_version 1

  @type point :: non_neg_integer() | :w
  @type grade :: point() | {:iv, point(), point()}
  @type gtm ::
          {:gvar, non_neg_integer()}
          | {:gtyp, non_neg_integer()}
          | {:glam, grade(), grade(), gtm()}
          | {:gpi, grade(), grade(), gtm()}
          | {:gapp, gtm(), gtm()}
          | :gze
          | {:gsu, gtm()}
          | {:gmatch, gtm(), gtm(), gtm()}
          | {:gref, non_neg_integer()}

  @doc """
  The image of `book`, including the trailing newline, and the refusals
  of every other exported run.

  `{:ok, image, ""}` is exactly one exported run, and that body erased.
  `Muro.emit_mbi/2` writes that image.
  `{:ok, _image, message}` is the first body that erased, and `message`
  names every other exported run. `Muro.emit_mbi/2` does not write that
  image. It returns `{:error, message}` and leaves a previous file byte
  for byte.
  `{:error, "mbi:entry"}` is a book with no exported run.
  `{:error, message}` is a book whose exported runs all failed.
  This function does not write. On either error, `Muro.emit_mbi/2`
  writes nothing and leaves a previous file byte for byte.
  """
  def render(book) when is_list(book) do
    case Enum.filter(book, &entry?/1) do
      [] ->
        {:error, "mbi:entry"}

      entries ->
        case choose(Enum.map(entries, &classify(book, &1))) do
          {:ok, defs, gtm, []} ->
            {:ok, show_image(defs, gtm) <> "\n", ""}

          {:ok, defs, gtm, reasons} ->
            {:ok, show_image(defs, gtm) <> "\n", Enum.join(reasons, "\n")}

          {:error, reasons} ->
            {:error, Enum.join(reasons, "\n")}
        end
    end
  end

  @doc """
  Erase one de Bruijn term. `{:error, reason}` is the bare tag, without
  the `mbi:` prefix and without a definition name.

  A `{:def, name}` is `def`. The book emitter resolves a run before
  this function sees it, and writes `(gref n)` for that index.
  """
  def erase(term), do: erase(term, %{})

  def erase({:var, i}, _env) when is_integer(i) and i >= 0, do: {:ok, {:gvar, i}}

  # The domain is dropped. `glam` opens one binder, the body. A later
  # loader does not recover the domain type.
  def erase({:lam, q, _dom, _name, body}, env) do
    with {:ok, c, t} <- grades(q),
         {:ok, body} <- erase(body, env) do
      {:ok, {:glam, c, t, body}}
    end
  end

  # The domain is dropped. `gpi` opens one binder, the same way.
  def erase({:pi, q, _dom, _name, body}, env) do
    with {:ok, c, t} <- grades(q),
         {:ok, body} <- erase(body, env) do
      {:ok, {:gpi, c, t, body}}
    end
  end

  def erase({:app, f, a}, env) do
    with {:ok, f} <- erase(f, env),
         {:ok, a} <- erase(a, env) do
      {:ok, {:gapp, f, a}}
    end
  end

  def erase(:ze, _env), do: {:ok, :gze}
  def erase({:su, t}, env), do: with({:ok, t} <- erase(t, env), do: {:ok, {:gsu, t}})

  def erase({:nat, n}, _env) when is_integer(n) and n >= 0, do: {:ok, peano(n)}
  def erase({:nat, _}, _env), do: {:error, "numeral"}

  def erase({:mnat, e, _motive, z, s}, env) do
    with {:ok, e} <- erase(e, env),
         {:ok, z} <- erase(z, env),
         {:ok, s} <- erase(s, env) do
      {:ok, {:gmatch, e, z, s}}
    end
  end

  def erase({:ann, e, _ty}, env), do: erase(e, env)

  def erase(:typ, _env), do: {:error, "typ"}
  def erase(:nat, _env), do: {:error, "nat"}
  def erase(:unit, _env), do: {:error, "unit"}
  def erase(:one, _env), do: {:error, "unit"}
  def erase({:munit, _, _, _}, _env), do: {:error, "unit"}
  def erase(:empty, _env), do: {:error, "empty"}
  def erase({:memp, _, _}, _env), do: {:error, "empty"}
  def erase({:mdata, _, _, _}, _env), do: {:error, "data"}
  def erase({:mwbool, _, _, _}, _env), do: {:error, "data"}
  def erase({:mopt, _, _, _}, _env), do: {:error, "data"}
  def erase({:idt, _, _, _}, _env), do: {:error, "id"}
  def erase(:rfl, _env), do: {:error, "id"}
  def erase({:rwt, _, _, _}, _env), do: {:error, "id"}
  def erase({:def, name}, env), do: gref(name, env)
  def erase({:prod, _, _}, _env), do: {:error, "pair"}
  def erase({:pair, _, _}, _env), do: {:error, "pair"}
  def erase({:letp, _, _}, _env), do: {:error, "pair"}
  def erase({:nu, _}, _env), do: {:error, "stream"}
  def erase({:unf, _, _}, _env), do: {:error, "stream"}
  def erase({:ucons, _}, _env), do: {:error, "stream"}
  def erase({:bisim, _, _}, _env), do: {:error, "stream"}
  def erase({:stream, _}, _env), do: {:error, "stream"}
  def erase({:always, _, _, _}, _env), do: {:error, "stream"}
  def erase(:i64, _env), do: {:error, "machine"}
  def erase(:f32ty, _env), do: {:error, "machine"}
  def erase({:tensor, _, _}, _env), do: {:error, "machine"}
  def erase({:addi, _, _}, _env), do: {:error, "machine"}
  def erase({:muli, _, _}, _env), do: {:error, "machine"}
  def erase({:addt, _, _}, _env), do: {:error, "machine"}
  def erase({:toi64, _}, _env), do: {:error, "machine"}
  def erase({:packi, _, _}, _env), do: {:error, "machine"}
  def erase({:word, _, _}, _env), do: {:error, "word"}
  def erase(:string, _env), do: {:error, "string"}
  def erase({:slit, _}, _env), do: {:error, "string"}
  def erase({:scat, _, _}, _env), do: {:error, "string"}
  def erase({:slen, _}, _env), do: {:error, "string"}
  def erase({:seq, _, _}, _env), do: {:error, "string"}
  def erase(:bytes, _env), do: {:error, "bytes"}
  def erase(:slice, _env), do: {:error, "bytes"}
  def erase({:blit, _}, _env), do: {:error, "bytes"}
  def erase({:bcat, _, _}, _env), do: {:error, "bytes"}
  def erase({:blen, _}, _env), do: {:error, "bytes"}
  def erase({:beq, _, _}, _env), do: {:error, "bytes"}
  def erase({:xlen, _}, _env), do: {:error, "bytes"}
  def erase({:xeq, _, _}, _env), do: {:error, "bytes"}
  def erase({:bsub, _, _, _}, _env), do: {:error, "bytes"}
  def erase({:bget, _, _}, _env), do: {:error, "bytes"}
  def erase({:aget, _, _}, _env), do: {:error, "bytes"}
  def erase({:bunc, _}, _env), do: {:error, "bytes"}
  def erase({:bfold, _, _, _, _}, _env), do: {:error, "bytes"}
  def erase({:afold, _, _, _, _}, _env), do: {:error, "bytes"}
  def erase({:sbytes, _}, _env), do: {:error, "bytes"}
  def erase({:btil, _, _}, _env), do: {:error, "bytes"}
  def erase({:baft, _, _}, _env), do: {:error, "bytes"}
  def erase(:atom, _env), do: {:error, "atom"}
  def erase({:atom, _}, _env), do: {:error, "atom"}
  def erase({:matom, _, _, _}, _env), do: {:error, "atom"}
  def erase({:hole, _}, _env), do: {:error, "hole"}
  def erase(_, _env), do: {:error, "term"}

  @doc "One line, no trailing newline. The file writer adds the newline."
  def show_pure(gtm) do
    "(muro-beam-image #{@format_version} (boundary #{@boundary_version}) (entry (seq " <>
      show_gtm(gtm) <> " (done))))"
  end

  @doc """
  One line, no trailing newline.

  An empty definition list is version 1, with no `(defs)` section. An
  empty nest is junk to the loader. A non-empty list is version 2.
  Definition `i` may mention itself or an earlier index. The entry may
  mention any definition.
  """
  def show_image([], gtm), do: show_pure(gtm)

  def show_image(defs, gtm) when is_list(defs) do
    body = Enum.map_join(defs, " ", &show_gtm/1)

    "(muro-beam-image #{@format_defs} (boundary #{@boundary_version}) (defs " <>
      body <> ") (entry (seq " <> show_gtm(gtm) <> " (done))))"
  end

  @doc "The term, without the image wrapper."
  def show_gtm({:gvar, n}), do: "(gvar " <> nat(n) <> ")"
  def show_gtm({:gtyp, n}), do: "(gtyp " <> nat(n) <> ")"
  def show_gtm({:glam, c, t, b}), do: "(glam " <> pair(c, t) <> " " <> show_gtm(b) <> ")"
  def show_gtm({:gpi, c, t, b}), do: "(gpi " <> pair(c, t) <> " " <> show_gtm(b) <> ")"
  def show_gtm({:gapp, f, a}), do: "(gapp " <> show_gtm(f) <> " " <> show_gtm(a) <> ")"
  def show_gtm(:gze), do: "gze"
  def show_gtm({:gsu, e}), do: "(gsu " <> show_gtm(e) <> ")"

  def show_gtm({:gmatch, e, z, s}) do
    "(gmatch " <> show_gtm(e) <> " " <> show_gtm(z) <> " " <> show_gtm(s) <> ")"
  end

  def show_gtm({:gref, n}), do: "(gref " <> nat(n) <> ")"

  @doc "A grade the way the image spells it. `ω` is `w`."
  def show_grade(n) when is_integer(n) and n >= 0, do: Integer.to_string(n)
  def show_grade(:w), do: "w"

  def show_grade({:iv, a, b}) do
    "(iv " <> show_grade(a) <> " " <> show_grade(b) <> ")"
  end

  defp entry?(%{mode: :run, type: _, body: _, export: false}), do: false
  defp entry?(%{mode: :run, type: _, body: _}), do: true
  defp entry?(_), do: false

  defp classify(book, %{name: name, body: body}) do
    case Ast.to_db(body) do
      {:ok, db} ->
        case plan(book, db) do
          {:ok, defs, gtm} ->
            {:ok, name, defs, gtm}

          # `{:def, name}` is a definition, a data type, or a constructor.
          # Agda splits those three. A data type and a constructor are `data`.
          {:error, "def"} ->
            {:error, name, def_tag(book, db)}

          {:error, reason} ->
            {:error, name, reason}
        end

      {:error, _} ->
        {:error, name, "term"}
    end
  end

  # The run definitions the entry reaches, in an order where each one
  # mentions itself or an earlier index. A cycle that is not a
  # self-call has no such order. That is `forward-def`, not a later
  # index written anyway.
  defp plan(book, entry) do
    case probe(entry, book, empty_reach()) do
      {:error, reason} ->
        {:error, reason}

      {:ok, reach} ->
        names = Map.keys(reach.defs)

        case topo(book, names, reach.edges) do
          :cycle ->
            {:error, "forward-def"}

          {:ok, order} ->
            env = Map.new(Enum.with_index(order), fn {name, i} -> {name, i} end)

            with {:ok, defs} <- erase_defs(order, reach.defs, env),
                 {:ok, gtm} <- erase(entry, env),
                 :ok <- guard_refs(defs, gtm) do
              {:ok, defs, gtm}
            end
        end
    end
  end

  defp erase_defs(order, defs, env) do
    Enum.reduce_while(order, {:ok, []}, fn name, {:ok, acc} ->
      case erase(Map.fetch!(defs, name), env) do
        {:ok, gtm} -> {:cont, {:ok, acc ++ [gtm]}}
        {:error, reason} -> {:halt, {:error, reason}}
      end
    end)
  end

  defp guard_refs(defs, entry) do
    later? =
      Enum.with_index(defs)
      |> Enum.any?(fn {gtm, i} -> gref_later?(gtm, i) end)

    cond do
      later? -> {:error, "forward-def"}
      gref_oob?(entry, length(defs)) -> {:error, "def"}
      true -> :ok
    end
  end

  defp gref_later?({:gref, n}, i), do: n > i
  defp gref_later?({:glam, _, _, b}, i), do: gref_later?(b, i)
  defp gref_later?({:gpi, _, _, b}, i), do: gref_later?(b, i)
  defp gref_later?({:gapp, f, a}, i), do: gref_later?(f, i) or gref_later?(a, i)
  defp gref_later?({:gsu, e}, i), do: gref_later?(e, i)

  defp gref_later?({:gmatch, e, z, s}, i) do
    gref_later?(e, i) or gref_later?(z, i) or gref_later?(s, i)
  end

  defp gref_later?(_, _), do: false

  defp gref_oob?({:gref, n}, bound), do: n >= bound
  defp gref_oob?({:glam, _, _, b}, bound), do: gref_oob?(b, bound)
  defp gref_oob?({:gpi, _, _, b}, bound), do: gref_oob?(b, bound)
  defp gref_oob?({:gapp, f, a}, bound), do: gref_oob?(f, bound) or gref_oob?(a, bound)
  defp gref_oob?({:gsu, e}, bound), do: gref_oob?(e, bound)

  defp gref_oob?({:gmatch, e, z, s}, bound) do
    gref_oob?(e, bound) or gref_oob?(z, bound) or gref_oob?(s, bound)
  end

  defp gref_oob?(_, _), do: false

  defp empty_reach, do: %{current: nil, seen: MapSet.new(), edges: %{}, defs: %{}}

  defp probe({:var, i}, _book, reach) when is_integer(i) and i >= 0, do: {:ok, reach}

  defp probe({:lam, q, _dom, _name, body}, book, reach) do
    case grades(q) do
      {:ok, _, _} -> probe(body, book, reach)
      {:error, _} = err -> err
    end
  end

  defp probe({:pi, q, _dom, _name, body}, book, reach) do
    case grades(q) do
      {:ok, _, _} -> probe(body, book, reach)
      {:error, _} = err -> err
    end
  end

  defp probe({:app, f, a}, book, reach) do
    with {:ok, reach} <- probe(f, book, reach), do: probe(a, book, reach)
  end

  defp probe(:ze, _book, reach), do: {:ok, reach}
  defp probe({:su, t}, book, reach), do: probe(t, book, reach)
  defp probe({:nat, n}, _book, reach) when is_integer(n) and n >= 0, do: {:ok, reach}
  defp probe({:nat, _}, _book, _reach), do: {:error, "numeral"}

  defp probe({:mnat, e, _motive, z, s}, book, reach) do
    with {:ok, reach} <- probe(e, book, reach),
         {:ok, reach} <- probe(z, book, reach),
         do: probe(s, book, reach)
  end

  defp probe({:ann, e, _ty}, book, reach), do: probe(e, book, reach)
  defp probe({:def, name}, book, reach), do: probe_def(name, book, reach)

  defp probe(term, _book, reach) do
    case erase(term) do
      {:ok, _} -> {:ok, reach}
      {:error, reason} -> {:error, reason}
    end
  end

  defp probe_def(name, book, reach) do
    cond do
      data_ref?(book, name) ->
        {:error, "data"}

      defn = run_def(book, name) ->
        follow(name, defn, book, reach)

      true ->
        {:error, "def"}
    end
  end

  defp follow(name, defn, book, reach) do
    reach = add_edge(reach, name)

    if MapSet.member?(reach.seen, name) do
      {:ok, reach}
    else
      case Ast.to_db(defn.body) do
        {:error, _} ->
          {:error, "term"}

        {:ok, db} ->
          parent = reach.current

          reach = %{
            reach
            | current: name,
              seen: MapSet.put(reach.seen, name),
              defs: Map.put(reach.defs, name, db)
          }

          case probe(db, book, reach) do
            {:ok, reach} -> {:ok, %{reach | current: parent}}
            {:error, _} = err -> err
          end
      end
    end
  end

  defp add_edge(%{current: nil} = reach, _name), do: reach

  defp add_edge(reach, name) do
    edges =
      Map.update(reach.edges, reach.current, MapSet.new([name]), &MapSet.put(&1, name))

    %{reach | edges: edges}
  end

  defp run_def(book, name) when is_binary(name) do
    Enum.find(book, fn
      %{mode: :run, name: ^name, body: body} when not is_nil(body) -> true
      _ -> false
    end)
  end

  defp run_def(_book, _name), do: nil

  defp topo(book, names, edges) do
    pos = book_positions(book)

    deps =
      Map.new(names, fn name ->
        {name, edges |> Map.get(name, MapSet.new()) |> MapSet.delete(name)}
      end)

    indeg = Map.new(deps, fn {name, ds} -> {name, MapSet.size(ds)} end)

    rev =
      Enum.reduce(deps, %{}, fn {name, ds}, acc ->
        Enum.reduce(ds, acc, fn dep, acc ->
          Map.update(acc, dep, [name], &[name | &1])
        end)
      end)

    ready =
      names
      |> Enum.filter(&(Map.get(indeg, &1) == 0))
      |> Enum.sort_by(&Map.fetch!(pos, &1))

    case drain(ready, indeg, rev, pos, []) do
      order when length(order) == length(names) -> {:ok, order}
      _ -> :cycle
    end
  end

  defp drain([], _indeg, _rev, _pos, acc), do: Enum.reverse(acc)

  defp drain([name | ready], indeg, rev, pos, acc) do
    {ready, indeg} =
      Enum.reduce(Map.get(rev, name, []), {ready, indeg}, fn user, {ready, indeg} ->
        left = indeg[user] - 1
        indeg = Map.put(indeg, user, left)
        ready = if left == 0, do: insert_ready(ready, user, pos), else: ready
        {ready, indeg}
      end)

    drain(ready, indeg, rev, pos, [name | acc])
  end

  defp insert_ready(ready, name, pos) do
    {pre, post} = Enum.split_while(ready, &(pos[&1] < pos[name]))
    pre ++ [name | post]
  end

  defp book_positions(book) do
    book
    |> Enum.with_index()
    |> Enum.reduce(%{}, fn
      {%{name: name}, i}, acc -> Map.put_new(acc, name, i)
      _, acc -> acc
    end)
  end

  # A name the book placed in the image. An unknown name stays `def`.
  defp gref(name, env) do
    case Map.get(env, name) do
      i when is_integer(i) and i >= 0 -> {:ok, {:gref, i}}
      _ -> {:error, "def"}
    end
  end

  defp def_tag(book, term) do
    case first_def(term) do
      {:ok, name} -> if data_ref?(book, name), do: "data", else: "def"
      :none -> "def"
    end
  end

  # The first `{:def, _}` `erase` would refuse. The walk follows only the
  # constructors `erase` enters, in the same order.
  defp first_def({:def, name}), do: {:ok, name}

  defp first_def({:lam, q, _, _, body}) do
    case grades(q) do
      {:ok, _, _} -> first_def(body)
      _ -> :none
    end
  end

  defp first_def({:pi, q, _, _, body}) do
    case grades(q) do
      {:ok, _, _} -> first_def(body)
      _ -> :none
    end
  end

  defp first_def({:app, f, a}) do
    case first_def(f) do
      {:ok, _} = hit -> hit
      :none -> first_def(a)
    end
  end

  defp first_def({:su, t}), do: first_def(t)

  defp first_def({:mnat, e, _, z, s}) do
    Enum.reduce_while([e, z, s], :none, fn t, :none ->
      case first_def(t) do
        {:ok, _} = hit -> {:halt, hit}
        :none -> {:cont, :none}
      end
    end)
  end

  defp first_def({:ann, e, _}), do: first_def(e)
  defp first_def(_), do: :none

  defp data_ref?(book, name) when is_binary(name) do
    Enum.any?(book, fn
      %{kind: :data, name: ^name} ->
        true

      %{kind: :data, ctors: ctors} when is_list(ctors) ->
        Enum.any?(ctors, &match?(%{name: ^name}, &1))

      _ ->
        false
    end)
  end

  defp data_ref?(_book, _name), do: false

  defp choose(rows), do: choose(rows, [])

  defp choose([{:error, name, tag} | rest], failed) do
    choose(rest, failed ++ [named(name, tag)])
  end

  defp choose([{:ok, _name, defs, gtm} | rest], failed) do
    {:ok, defs, gtm, failed ++ Enum.map(rest, &rest_reason/1)}
  end

  defp choose([], failed), do: {:error, failed}

  defp rest_reason({:ok, name, _defs, _gtm}), do: "mbi:entry in #{name}"
  defp rest_reason({:error, name, tag}), do: named(name, tag)

  defp named(name, tag), do: "mbi:#{tag} in #{name}"

  # A quantity atom. The type grade is 0. A written pair is kept.
  # An unknown quantity is refused.
  defp grades(:affine), do: {:ok, {:iv, 0, 1}, 0}
  defp grades(:reuse), do: {:ok, :w, 0}
  defp grades(:erased), do: {:ok, 0, 0}
  defp grades(:linear), do: {:ok, 1, 0}

  defp grades({:grade, c, t}) do
    with {:ok, c} <- grade(c),
         {:ok, t} <- grade(t) do
      {:ok, c, t}
    end
  end

  defp grades(_), do: {:error, "grade"}

  defp grade(n) when is_integer(n) and n >= 0, do: {:ok, n}
  defp grade(:w), do: {:ok, :w}

  defp grade({:iv, a, b}) do
    with {:ok, a} <- point(a),
         {:ok, b} <- point(b) do
      {:ok, {:iv, a, b}}
    end
  end

  defp grade(_), do: {:error, "grade"}

  defp point(n) when is_integer(n) and n >= 0, do: {:ok, n}
  defp point(:w), do: {:ok, :w}
  defp point(_), do: {:error, "grade"}

  defp peano(n) when is_integer(n) and n >= 0, do: peano(n, :gze)
  defp peano(0, acc), do: acc
  defp peano(n, acc), do: peano(n - 1, {:gsu, acc})

  defp pair(c, t), do: "(" <> show_grade(c) <> " " <> show_grade(t) <> ")"
  defp nat(n) when is_integer(n) and n >= 0, do: Integer.to_string(n)
end
