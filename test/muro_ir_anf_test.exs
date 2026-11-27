defmodule Muro.IRAnfTest do
  # `Muro.IR.Anf`. The differential loop over the corpus and the HTTP
  # step book runs every image in A-normal form too
  # (test/ir_diff_helper.exs); this module holds the pass to its grammar,
  # to `Muro.IR.Check`, and to `Muro.IR.Eval` directly.
  use ExUnit.Case, async: true

  alias Muro.IR
  alias Muro.IR.{Anf, Check, Eval, Share}

  # The corpus walks emit or Share every book, the HTTP step book too.
  @moduletag timeout: 600_000

  @corpus ["examples/**/*.muro", "test/fixtures/**/*.muro", "lib/muro/std/*.muro"]

  test "a nested operand is bound by a let, left to right" do
    funs = [
      fun("id", [{"x", :nat, :reuse}], :nat, {:var, "x"}),
      fun("add", [{"a", :nat, :reuse}, {"b", :nat, :reuse}], :nat, {:var, "a"}),
      fun(
        "f",
        [],
        :nat,
        {:call, "add", [{:call, "id", [{:nat, 1}]}, {:su, {:call, "id", [:ze]}}]}
      )
    ]

    refute Anf.anf?(funs)
    anf = Anf.funs(funs)
    assert Anf.anf?(anf)

    assert body(anf, "f") ==
             {:let, "a%0", :nat, :reuse, {:call, "id", [{:nat, 1}]},
              {:let, "a%1", :nat, :reuse, {:call, "id", [:ze]},
               {:let, "a%2", :nat, :reuse, {:su, {:var, "a%1"}},
                {:call, "add", [{:var, "a%0"}, {:var, "a%2"}]}}}}

    assert Check.check(anf) == :ok
    assert Eval.call(anf, "f", []) == Eval.call(funs, "f", [])
  end

  test "a binder is renamed when it would shadow a later operand" do
    add =
      fun(
        "add",
        [{"a", :nat, :reuse}, {"b", :nat, :reuse}],
        :nat,
        {:match, {:var, "a"},
         [
           {:arm, "zero", [], {:var, "b"}},
           {:arm, "suc", ["p"], {:su, {:call, "add", [{:var, "p"}, {:var, "b"}]}}}
         ]}
      )

    f =
      fun(
        "f",
        [{"y", :nat, :reuse}],
        :nat,
        {:call, "add", [{:let, "y", :nat, :reuse, {:nat, 1}, {:su, {:var, "y"}}}, {:var, "y"}]}
      )

    anf = Anf.funs([add, f])

    assert body(anf, "f") ==
             {:let, "y%0", :nat, :reuse, {:nat, 1},
              {:let, "a%1", :nat, :reuse, {:su, {:var, "y%0"}},
               {:call, "add", [{:var, "a%1"}, {:var, "y"}]}}}

    assert Anf.unique_binders?(anf)
    assert Eval.call(anf, "f", [{:nat, 5}]) == {:ok, {:nat, 7}}
    assert Eval.call([add, f], "f", [{:nat, 5}]) == {:ok, {:nat, 7}}
  end

  test "a let in a let is flattened" do
    f =
      fun(
        "f",
        [],
        :nat,
        {:let, "z", :nat, :reuse, {:let, "w", :nat, :reuse, {:nat, 2}, {:su, {:var, "w"}}},
         {:var, "z"}}
      )

    refute Anf.anf?([f])
    [g] = Anf.funs([f])

    assert g.body ==
             {:let, "w", :nat, :reuse, {:nat, 2},
              {:let, "z", :nat, :reuse, {:su, {:var, "w"}}, {:var, "z"}}}

    assert Eval.call([g], "f", []) == {:ok, {:nat, 3}}
  end

  test "stream captures are bound before the seed, as Eval evaluates them" do
    t = {:stream, {:call, "s", []}, [{"c", {:call, "c", []}}], "step0"}
    [g] = Anf.funs([fun("f", [], {:stream, :nat}, t)])

    assert g.body ==
             {:let, "a%0", :opaque, :reuse, {:call, "c", []},
              {:let, "a%1", :opaque, :reuse, {:call, "s", []},
               {:stream, {:var, "a%1"}, [{"c", {:var, "a%0"}}], "step0"}}}
  end

  test "grades: a scrutinee is affine, an operand of a linear value is linear" do
    id = fun("id", [{"x", :nat, :linear}], :nat, {:var, "x"})

    m =
      fun(
        "m",
        [{"x", :nat, :linear}],
        :nat,
        {:match, {:su, {:var, "x"}}, [{:arm, "zero", [], :ze}, {:arm, "suc", ["p"], :ze}]}
      )

    c = fun("c", [{"x", :nat, :linear}], :nat, {:call, "id", [{:su, {:var, "x"}}]})
    funs = [id, m, c]
    assert Check.check(funs) == :ok

    anf = Anf.funs(funs)

    assert {:let, "a%0", :nat, :affine, {:su, {:var, "x"}}, {:match, {:var, "a%0"}, _}} =
             body(anf, "m")

    assert {:let, "a%0", :nat, :linear, {:su, {:var, "x"}}, _} = body(anf, "c")
    assert Check.check(anf) == :ok
    assert Eval.call(anf, "m", [{:nat, 3}]) == {:ok, {:nat, 0}}
  end

  test "a reusable position still refuses a linear operand" do
    id = fun("id", [{"x", :opaque, :reuse}], :opaque, {:var, "x"})
    c = fun("c", [{"x", :opaque, :linear}], :opaque, {:call, "id", [{:pair, {:var, "x"}, :ze}]})
    assert {:error, _} = Check.check([id, c])
    assert {:error, errors} = Check.check(Anf.funs([id, c]))
    assert Enum.any?(errors, &(&1 =~ "as reusable"))
  end

  test "violations name each operand that is not atomic" do
    t = {:call, "f", [{:su, :ze}]}
    assert Anf.violations([fun("g", [], :nat, t)]) == [{"g", t}]
    assert Anf.violations([fun("g", [], :nat, {:su, :ze})]) == []

    m = {:match, {:su, :ze}, [{:arm, "zero", [], :ze}, {:arm, "suc", ["p"], :ze}]}
    assert Anf.violations([fun("g", [], :nat, m)]) == [{"g", m}]
  end

  test "every image of the corpus keeps its Check verdict and its values in A-normal form" do
    results =
      (corpus() ++ ["test/http_step/step.muro"])
      |> Task.async_stream(&images/1, timeout: :infinity)
      |> Enum.flat_map(fn {:ok, r} -> r end)

    assert length(results) >= 300

    bad =
      for {path, k, before, after_, anf?, uniq?, evals} <- results,
          not (after_ == before and anf? and uniq? and Enum.all?(evals, &agree?/1)),
          do: {path, k, before, after_, anf?, uniq?, Enum.reject(evals, &agree?/1)}

    assert bad == []
    assert Enum.count(results, fn r -> elem(r, 2) == :ok end) >= 300
    assert results |> Enum.flat_map(&elem(&1, 6)) |> length() >= 1000
  end

  # Each image of a book: the default image, its Share, the closures
  # image, and its Share; Check and Eval of every closed run, before and
  # after A-normal form.
  defp images(path) do
    with {:ok, b} <- Muro.Load.file(path) do
      book = Muro.Prelude.for_emit(b)

      for {k, opts} <- [plain: [], closures: [closures: true]],
          {:ok, funs} <- [IR.elaborate(book, opts)],
          {k, funs} <- [{k, funs}, {:"#{k}_share", Share.funs(funs)}] do
        clos = Keyword.get(opts, :closures, false)
        anf = Anf.funs(funs, book: book, closures: clos)

        evals =
          for f <- funs, not Map.get(f, :generated, false), f.params == [] do
            {f.name, observe(funs, f.name), observe(anf, f.name)}
          end

        {path, k, Check.check(funs, book: book, closures: clos),
         Check.check(anf, book: book, closures: clos), Anf.anf?(anf), Anf.unique_binders?(anf),
         evals}
      end
    else
      _ -> []
    end
  end

  defp observe(funs, name) do
    case Eval.call(funs, name, [], fuel: 200_000) do
      {:ok, {:stream, _, _, _} = s} -> erase(Eval.take(funs, s, 3, fuel: 200_000))
      r -> erase(r)
    end
  end

  defp agree?({_name, a, b}), do: a == b

  # A closure holds the same code under other binder names.
  defp erase({:clo, _, _, _}), do: :closure

  defp erase(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&erase/1) |> List.to_tuple()

  defp erase(t) when is_list(t), do: Enum.map(t, &erase/1)
  defp erase(t), do: t

  defp corpus, do: @corpus |> Enum.flat_map(&Path.wildcard/1) |> Enum.sort()

  defp fun(name, params, ret, body),
    do: %{name: name, export: true, params: params, ret: ret, body: body}

  defp body(funs, name), do: Enum.find(funs, &(&1.name == name)).body
end
