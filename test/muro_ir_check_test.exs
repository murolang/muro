defmodule Muro.IRCheckTest do
  use ExUnit.Case, async: true

  alias Muro.IR
  alias Muro.IR.Check
  alias Muro.IR.Share

  test "elaborated plus and half are well-formed" do
    {:ok, book} = load_example("examples/half_ok.muro")
    assert {:ok, funs} = IR.elaborate(book)
    assert :ok = Check.check(funs, book: book)
    assert :ok = Check.check(Share.funs(funs), book: book)
  end

  test "a reuse parameter may be used twice" do
    fun = fun("twice", [{"s", :slice, :reuse}], :u64, {:call, "id", [{:var, "s"}, {:var, "s"}]})
    id = fun("id", [{"a", :slice, :reuse}, {"b", :slice, :reuse}], :u64, wrd(0))
    assert :ok = Check.check([fun, id])
  end

  test "a linear parameter must be used once on every path" do
    ok = fun("go", [{"n", :nat, :linear}], :nat, {:var, "n"})
    assert :ok = Check.check([ok])

    unused = fun("drop", [{"n", :nat, :linear}], :nat, :ze)
    assert {:error, errors} = Check.check([unused])
    assert Enum.any?(errors, &(&1 =~ "linear binder n used 0"))

    twice =
      fun("add", [{"n", :nat, :linear}], :nat, {:pair, {:var, "n"}, {:var, "n"}})

    assert {:error, errors} = Check.check([twice])
    assert Enum.any?(errors, &(&1 =~ "linear binder n used 2"))
  end

  test "an affine parameter may be unused but not used twice" do
    unused = fun("drop", [{"n", :nat, :affine}], :nat, :ze)
    assert :ok = Check.check([unused])

    once = fun("go", [{"n", :nat, :affine}], :nat, {:var, "n"})
    assert :ok = Check.check([once])

    twice =
      fun("add", [{"n", :nat, :affine}], :nat, {:pair, {:var, "n"}, {:var, "n"}})

    assert {:error, errors} = Check.check([twice])
    assert Enum.any?(errors, &(&1 =~ "affine binder n used 2"))
  end

  test "linear use must hold on every match arm" do
    both =
      fun(
        "go",
        [{"p", {:data, "Pick"}, :affine}, {"n", :nat, :linear}],
        :nat,
        {:match, {:var, "p"}, [{:arm, "yes", [], {:var, "n"}}, {:arm, "no", [], {:var, "n"}}]}
      )

    assert :ok = Check.check([both])

    one_arm =
      fun(
        "go",
        [{"p", {:data, "Pick"}, :affine}, {"n", :nat, :linear}],
        :nat,
        {:match, {:var, "p"}, [{:arm, "yes", [], {:var, "n"}}, {:arm, "no", [], :ze}]}
      )

    assert {:error, errors} = Check.check([one_arm])
    assert Enum.any?(errors, &(&1 =~ "linear binder n used 0"))
  end

  test "a free variable is rejected" do
    fun = fun("go", [], :nat, {:var, "missing"})
    assert {:error, errors} = Check.check([fun])
    assert Enum.any?(errors, &(&1 =~ "free variable missing"))
  end

  test "an erased dummy let is accepted when unused and rejected when used" do
    ok =
      fun("go", [{"n", :nat, :affine}], :nat, {:let, "e", :erased, :affine, :ze, {:var, "n"}})

    assert :ok = Check.check([ok])

    used =
      fun("go", [], :nat, {:let, "e", :erased, :affine, :ze, {:var, "e"}})

    assert {:error, errors} = Check.check([used])
    assert Enum.any?(errors, &(&1 =~ "erased variable e"))

    bad_val =
      fun("go", [], :nat, {:let, "e", :erased, :affine, {:su, :ze}, :ze})

    assert {:error, errors} = Check.check([bad_val])
    assert Enum.any?(errors, &(&1 =~ "erased let e does not bind Ze"))
  end

  test "erased layout is not a live parameter" do
    fun = fun("go", [{"e", :erased, :affine}], :nat, :ze)
    assert {:error, errors} = Check.check([fun])
    assert Enum.any?(errors, &(&1 =~ "parameter e has erased layout"))
  end

  test "call arity and argument layouts are checked" do
    callee = fun("id", [{"n", :nat, :affine}], :nat, {:var, "n"})

    bad_arity = fun("go", [{"n", :nat, :affine}], :nat, {:call, "id", []})
    assert {:error, errors} = Check.check([bad_arity, callee])
    assert Enum.any?(errors, &(&1 =~ "has 0 argument(s), expected 1"))

    bad_lay =
      fun("go", [{"s", :slice, :affine}], :nat, {:call, "id", [{:var, "s"}]})

    assert {:error, errors} = Check.check([bad_lay, callee])
    assert Enum.any?(errors, &(&1 =~ "expected :nat"))

    missing = fun("go", [], :nat, {:call, "absent", []})
    assert {:error, errors} = Check.check([missing])
    assert Enum.any?(errors, &(&1 =~ "unknown call absent"))
  end

  test "constructor field counts are checked when a book is given" do
    book = box_book()
    good = fun("go", [], {:data, "Box"}, {:con, "Box", "mk", [{:su, :ze}]})
    assert :ok = Check.check([good], book: book)

    bad = fun("go", [], {:data, "Box"}, {:con, "Box", "mk", []})
    assert {:error, errors} = Check.check([bad], book: book)
    assert Enum.any?(errors, &(&1 =~ "constructor mk has 0 field(s), expected 1"))
  end

  test "match exhaustiveness is checked when a book is given" do
    book = box_book()

    missing =
      fun("go", [{"b", {:data, "Box"}, :affine}], :nat, {:match, {:var, "b"}, []})

    assert {:error, errors} = Check.check([missing], book: book)
    assert Enum.any?(errors, &(&1 =~ "missing arm(s) mk"))

    extra =
      fun(
        "go",
        [{"b", {:data, "Box"}, :affine}],
        :nat,
        {:match, {:var, "b"}, [{:arm, "mk", ["n"], {:var, "n"}}, {:arm, "other", [], :ze}]}
      )

    assert {:error, errors} = Check.check([extra], book: book)
    assert Enum.any?(errors, &(&1 =~ "unknown arm(s) other"))
  end

  test "without a book, missing arms are not reported" do
    fun =
      fun("go", [{"b", {:data, "Box"}, :affine}], :nat, {:match, {:var, "b"}, []})

    assert :ok = Check.check([fun])
  end

  test "a nat match must cover zero and suc when a book is given" do
    fun =
      fun("go", [{"n", :nat, :affine}], :nat, {:match, {:var, "n"}, [{:arm, "zero", [], :ze}]})

    assert {:error, errors} = Check.check([fun], book: [])
    assert Enum.any?(errors, &(&1 =~ "missing arm(s) suc"))
  end

  test "an invalid grade is rejected" do
    fun = fun("go", [{"n", :nat, :omega}], :nat, {:var, "n"})
    assert {:error, errors} = Check.check([fun])
    assert Enum.any?(errors, &(&1 =~ "invalid grade"))
  end

  test "closure forms are refused outside the closures image" do
    lam =
      fun("go", [], {:fn, :nat, :nat}, {:lam, "n", :nat, :affine, {:var, "n"}})

    assert {:error, errors} = Check.check([lam], closures: false)
    assert Enum.any?(errors, &(&1 =~ "outside the closures image"))

    assert :ok = Check.check([lam], closures: true)
  end

  test "an application is refused outside the closures image" do
    f = {"f", {:fn, :nat, :nat}, :affine}
    a = {"n", :nat, :affine}
    fun = fun("go", [f, a], :nat, {:appv, {:var, "f"}, {:var, "n"}})
    assert {:error, errors} = Check.check([fun], closures: false)
    assert Enum.any?(errors, &(&1 =~ "application outside the closures image"))
    assert :ok = Check.check([fun], closures: true)
  end

  test "Share CSE lets stay reuse and the shared book still checks" do
    {:ok, book} = load_source(share_book())
    assert {:ok, funs} = IR.elaborate(book)
    assert :ok = Check.check(funs, book: book)
    shared = Share.funs(funs)
    assert :ok = Check.check(shared, book: book)

    twice = Enum.find(shared, &(&1.name == "twice"))
    assert reuse_let?(twice.body)
  end

  test "an unused linear let after pruning is affine and checks" do
    # Share downgrades; Check also accepts a hand-written affine leftover.
    fun =
      fun("go", [{"n", :nat, :affine}], :nat, {:let, "x", :nat, :affine, {:var, "n"}, :ze})

    assert :ok = Check.check([fun])

    still_linear =
      fun("go", [{"n", :nat, :affine}], :nat, {:let, "x", :nat, :linear, {:var, "n"}, :ze})

    assert {:error, errors} = Check.check([still_linear])
    assert Enum.any?(errors, &(&1 =~ "linear binder x used 0"))
  end

  test "let layout agrees with the right-hand side" do
    bad = fun("go", [], :nat, {:let, "x", :nat, :affine, {:str, "hi"}, {:var, "x"}})
    assert {:error, errors} = Check.check([bad])
    assert Enum.any?(errors, &(&1 =~ "let x has layout :string, expected :nat"))
  end

  test "Share pruning a dead arm does not require linear use on the abort path" do
    both =
      fun(
        "go",
        [{"n", :nat, :linear}],
        :nat,
        {:match, {:con, "Pick", "yes", []},
         [{:arm, "yes", [], {:var, "n"}}, {:arm, "no", [], {:var, "n"}}]}
      )

    # Share may collapse the match to the live arm. The image `kill_dead`
    # actually produces still has the unreachable arm as `:abort`; Check
    # must treat that path as bottom.
    pruned =
      fun(
        "go",
        [{"n", :nat, :linear}],
        :nat,
        {:match, {:con, "Pick", "yes", []},
         [{:arm, "yes", [], {:var, "n"}}, {:arm, "no", [], :abort}]}
      )

    assert :ok = Check.check([pruned])
    assert :ok = Check.check(Share.funs([both]))

    twice_pruned =
      fun(
        "go",
        [{"n", :nat, :linear}],
        :nat,
        {:match, {:con, "Pick", "yes", []},
         [
           {:arm, "yes", [], {:pair, {:var, "n"}, {:var, "n"}}},
           {:arm, "no", [], :abort}
         ]}
      )

    assert {:error, errors} = Check.check([twice_pruned])
    assert Enum.any?(errors, &(&1 =~ "linear binder n used 2"))

    twice =
      fun(
        "go",
        [{"n", :nat, :linear}],
        :nat,
        {:match, {:con, "Pick", "yes", []},
         [
           {:arm, "yes", [], {:pair, {:var, "n"}, {:var, "n"}}},
           {:arm, "no", [], {:var, "n"}}
         ]}
      )

    assert {:error, errors} = Check.check(Share.funs([twice]))
    assert Enum.any?(errors, &(&1 =~ "linear binder n used 2"))
  end

  test "linear arm fields are accounted from the book" do
    book = lin_box_book()

    once =
      fun(
        "go",
        [{"b", {:data, "LinBox"}, :affine}],
        :nat,
        {:match, {:var, "b"}, [{:arm, "mk", ["n"], {:var, "n"}}]}
      )

    assert :ok = Check.check([once], book: book)

    unused =
      fun(
        "go",
        [{"b", {:data, "LinBox"}, :affine}],
        :nat,
        {:match, {:var, "b"}, [{:arm, "mk", ["n"], :ze}]}
      )

    assert {:error, errors} = Check.check([unused], book: book)
    assert Enum.any?(errors, &(&1 =~ "linear binder n used 0"))

    twice =
      fun(
        "go",
        [{"b", {:data, "LinBox"}, :affine}],
        :nat,
        {:match, {:var, "b"}, [{:arm, "mk", ["n"], {:pair, {:var, "n"}, {:var, "n"}}}]}
      )

    assert {:error, errors} = Check.check([twice], book: book)
    assert Enum.any?(errors, &(&1 =~ "linear binder n used 2"))
  end

  test "linear fold-step parameters are accounted" do
    ok = fun("step0", [{"b", :nat, :linear}, {"acc", :nat, :reuse}], :nat, {:var, "b"})
    assert :ok = Check.check([ok])

    unused = fun("step0", [{"b", :nat, :linear}, {"acc", :nat, :reuse}], :nat, {:var, "acc"})
    assert {:error, errors} = Check.check([unused])
    assert Enum.any?(errors, &(&1 =~ "linear binder b used 0"))

    twice =
      fun(
        "step0",
        [{"b", :nat, :linear}, {"acc", :nat, :reuse}],
        :nat,
        {:pair, {:var, "b"}, {:var, "b"}}
      )

    assert {:error, errors} = Check.check([twice])
    assert Enum.any?(errors, &(&1 =~ "linear binder b used 2"))
  end

  test "a linear capture is charged at lambda formation" do
    returned =
      fun(
        "go",
        [{"x", :nat, :linear}],
        {:fn, :nat, :nat},
        {:lam, "n", :nat, :affine, {:var, "x"}}
      )

    assert :ok = Check.check([returned], closures: true)

    unused =
      fun(
        "go",
        [{"x", :nat, :linear}],
        {:fn, :nat, :nat},
        {:lam, "n", :nat, :affine, {:var, "n"}}
      )

    assert {:error, errors} = Check.check([unused], closures: true)
    assert Enum.any?(errors, &(&1 =~ "linear binder x used 0"))

    twice =
      fun(
        "go",
        [{"x", :nat, :linear}],
        {:fn, :nat, :nat},
        {:lam, "n", :nat, :affine, {:pair, {:var, "x"}, {:var, "x"}}}
      )

    assert {:error, errors} = Check.check([twice], closures: true)
    assert Enum.any?(errors, &(&1 =~ "linear binder x used 2"))

    reuse =
      fun(
        "go",
        [{"x", :nat, :linear}],
        {:fn, :nat, :nat},
        {:let, "f", {:fn, :nat, :nat}, :reuse, {:lam, "n", :nat, :affine, {:var, "x"}},
         {:var, "f"}}
      )

    assert {:error, errors} = Check.check([reuse], closures: true)
    assert Enum.any?(errors, &(&1 =~ "uses x as reusable"))
  end

  test "a missing grade is refused" do
    param = %{name: "go", export: true, params: [{"n", :nat}], ret: :nat, body: {:var, "n"}}
    assert {:error, errors} = Check.check([param])
    assert Enum.any?(errors, &(&1 =~ "parameter n is missing a grade"))

    let = %{
      name: "go",
      export: true,
      params: [],
      ret: :nat,
      body: {:let, "x", :nat, :ze, {:var, "x"}}
    }

    assert {:error, errors} = Check.check([let])
    assert Enum.any?(errors, &(&1 =~ "let x is missing a grade"))
  end

  test "a let-bound argument is inferred so a wrong layout is reported" do
    callee = fun("id", [{"n", :nat, :affine}], :nat, {:var, "n"})

    bad =
      fun(
        "go",
        [],
        :nat,
        {:call, "id", [{:let, "x", :string, :affine, {:str, "hi"}, {:var, "x"}}]}
      )

    assert {:error, errors} = Check.check([bad, callee])
    assert Enum.any?(errors, &(&1 =~ "expected :nat"))
  end

  test "the body layout must agree with the function return" do
    bad = fun("go", [], :nat, {:str, "hi"})
    assert {:error, errors} = Check.check([bad])
    assert Enum.any?(errors, &(&1 =~ "return has layout :string, expected :nat"))
  end

  test "match arm binder counts are checked when the fields are known" do
    book = box_book()

    few =
      fun(
        "go",
        [{"b", {:data, "Box"}, :affine}],
        :nat,
        {:match, {:var, "b"}, [{:arm, "mk", [], :ze}]}
      )

    assert {:error, errors} = Check.check([few], book: book)
    assert Enum.any?(errors, &(&1 =~ "arm mk has 0 binder(s), expected 1"))

    many =
      fun(
        "go",
        [{"b", {:data, "Box"}, :affine}],
        :nat,
        {:match, {:var, "b"}, [{:arm, "mk", ["n", "m"], {:var, "n"}}]}
      )

    assert {:error, errors} = Check.check([many], book: book)
    assert Enum.any?(errors, &(&1 =~ "arm mk has 2 binder(s), expected 1"))
  end

  test "Share relaxes an unused linear parameter after inlining drops its only use" do
    drop = fun("drop", [{"x", :nat, :affine}, {"k", :nat, :affine}], :nat, :ze)
    go = fun("go", [{"n", :nat, :linear}], :nat, {:call, "drop", [{:var, "n"}, :ze]})
    shared = Share.funs([drop, go])
    go_s = Enum.find(shared, &(&1.name == "go"))
    assert go_s.body == :ze
    assert IR.param_grade(hd(go_s.params)) == :affine
    assert :ok = Check.check(shared)
  end

  test "arrow.muro elaborates %1 as a linear parameter and checks in both images" do
    {:ok, book} = load_example("examples/arrow.muro")
    assert {:ok, funs} = IR.elaborate(book)
    keep = Enum.find(funs, &(&1.name == "keep"))
    assert keep
    assert IR.param_grade(hd(keep.params)) == :linear
    assert :ok = Check.check(funs, book: book)
    assert :ok = Check.check(Share.funs(funs), book: book)

    assert {:ok, closed} = IR.elaborate(book, closures: true)
    assert :ok = Check.check(closed, book: book, closures: true)
    assert :ok = Check.check(Share.funs(closed), book: book, closures: true)
  end

  test "corpus elaborations and Share images check" do
    {ok, skipped, failures} =
      Enum.reduce(corpus_paths(), {0, 0, []}, fn path, {ok, skipped, failures} ->
        case load_path(path) do
          {:error, _} ->
            {ok, skipped + 1, failures}

          {:ok, book} ->
            case IR.elaborate(book) do
              {:error, _} ->
                {ok, skipped + 1, failures}

              {:ok, funs} ->
                default =
                  {Check.check(funs, book: book), Check.check(Share.funs(funs), book: book)}

                closed =
                  case IR.elaborate(book, closures: true) do
                    {:error, _} ->
                      {:ok, :ok}

                    {:ok, cfuns} ->
                      {Check.check(cfuns, book: book, closures: true),
                       Check.check(Share.funs(cfuns), book: book, closures: true)}
                  end

                case {default, closed} do
                  {{:ok, :ok}, {:ok, :ok}} ->
                    {ok + 1, skipped, failures}

                  {a, b} ->
                    {ok, skipped, [{path, a, b} | failures]}
                end
            end
        end
      end)

    assert failures == [], """
    Muro.IR.Check failed on #{length(failures)} file(s); checked #{ok}, skipped #{skipped}.

    #{Enum.map_join(Enum.take(failures, 12), "\n", &format_fail/1)}
    """

    assert ok > 0
  end

  defp format_fail({path, a, b}),
    do: "#{path}\n  default: #{inspect(a)}\n  closures: #{inspect(b)}"

  defp fun(name, params, ret, body) do
    %{name: name, export: true, params: params, ret: ret, body: body}
  end

  defp wrd(n), do: {:wrd, :u64, {:lit, :u64, n}, []}

  defp reuse_let?({:let, _x, _lay, :reuse, _v, _b}), do: true
  defp reuse_let?({:let, _x, _lay, _g, v, b}), do: reuse_let?(v) or reuse_let?(b)
  defp reuse_let?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&reuse_let?/1)
  defp reuse_let?(t) when is_list(t), do: Enum.any?(t, &reuse_let?/1)
  defp reuse_let?(_), do: false

  defp lin_box_book do
    [
      %{
        kind: :data,
        name: "LinBox",
        params: [],
        indices: [],
        ctors: [
          %{
            name: "mk",
            type: {:pi, :linear, :nat, "n", {:const, "LinBox"}}
          }
        ]
      }
    ]
  end

  defp box_book do
    [
      %{
        kind: :data,
        name: "Box",
        params: [],
        indices: [],
        ctors: [
          %{
            name: "mk",
            type: {:pi, :erased, :nat, "e", {:pi, :affine, :nat, "n", {:const, "Box"}}}
          }
        ]
      }
    ]
  end

  defp load_example(path) do
    {:ok, book} = Muro.Load.file(path)
    {:ok, Muro.Prelude.for_emit(book)}
  end

  defp load_path(path) do
    with {:ok, book} <- Muro.Load.file(path) do
      {:ok, Muro.Prelude.for_emit(book)}
    end
  end

  defp load_source(src) do
    dir = Path.join(System.tmp_dir!(), "muro_ir_check_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    load_path(path)
  end

  defp corpus_paths do
    ["examples", "test/fixtures", "lib/muro/std"]
    |> Enum.flat_map(&Path.wildcard("#{&1}/**/*.muro"))
    |> Enum.sort()
  end

  defp share_book do
    """
    data Pick : Type where
      yes : Pick
      no : Pick

    def count : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        sliceFold U64 (toU64 0)
          (λ (_b : U8) → λ (_r : Slice) → λ (acc : U64) → addi acc (toU64 1))
          s

    def twice : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) → addi (count s) (count s)
    """
  end
end
