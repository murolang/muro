defmodule Muro.IREvalTest do
  use ExUnit.Case, async: true

  alias Muro.IR
  alias Muro.IR.Eval
  alias Muro.IR.Eval.Ref

  defp fun(name, params, body, extra \\ %{}) do
    Map.merge(%{name: name, export: true, params: params, ret: :opaque, body: body}, extra)
  end

  defp w(k, n), do: {:wrd, k, {:lit, k, n}, []}
  defp ev(t, env \\ %{}), do: Eval.eval([], t, env)

  describe "nat, unit, pair, let" do
    test "numerals and successors" do
      assert ev(:ze) == {:ok, {:nat, 0}}
      assert ev({:su, {:su, {:nat, 3}}}) == {:ok, {:nat, 5}}
      assert ev(:tt) == {:ok, :tt}
    end

    test "let, letp, and pair" do
      t =
        {:let, "p", {:pair, :nat, :nat}, :reuse, {:pair, {:nat, 1}, {:nat, 2}},
         {:letp, "a", "b", {:var, "p"}, {:pair, {:var, "b"}, {:var, "a"}}}}

      assert ev(t) == {:ok, {:pair, {:nat, 2}, {:nat, 1}}}
    end

    test "an erased let binds :erased and a five-field let is accepted" do
      assert ev({:let, "x", :erased, :affine, :ze, {:var, "x"}}) == {:ok, :erased}
      assert ev({:let, "x", :nat, {:nat, 4}, {:var, "x"}}) == {:ok, {:nat, 4}}
    end
  end

  describe "calls and matches" do
    test "plus from examples/half_ok.muro" do
      assert {:ok, funs} = IR.elaborate_file("examples/half_ok.muro")
      assert Eval.call(funs, "plus", [{:nat, 3}, {:nat, 4}]) == {:ok, {:nat, 7}}
      assert Eval.call(funs, "half", [{:nat, 9}]) == {:ok, {:nat, 4}}
    end

    test "data, atom, wbool, and opt arms" do
      m =
        {:match, {:var, "x"},
         [
           {:arm, "leaf", [], {:nat, 0}},
           {:arm, "node", ["l", "r"], {:pair, {:var, "r"}, {:var, "l"}}}
         ]}

      node = {:con, "T", "node", [{:nat, 1}, {:nat, 2}]}
      assert ev(m, %{"x" => node}) == {:ok, {:pair, {:nat, 2}, {:nat, 1}}}
      assert ev(m, %{"x" => {:con, "T", "leaf", []}}) == {:ok, {:nat, 0}}

      atoms =
        {:match, {:con, "Atom", "b", []}, :atom, [{:arm, "a", [], :ze}, {:arm, "b", [], :tt}]}

      assert ev(atoms) == {:ok, :tt}

      wb = {:match, {:wrd, :u8, false, []}, [{:arm, "wtrue", [], :ze}, {:arm, "wfalse", [], :tt}]}
      assert ev(wb) == {:ok, :tt}

      opt = fn s ->
        {:match, s, {:opt, :u8},
         [{:arm, "wsome", ["y"], {:var, "y"}}, {:arm, "wnone", [], w(:u8, 9)}]}
      end

      assert ev(opt.({:wrd, :u8, :some, [w(:u8, 3)]})) == {:ok, {:word, :u8, 3}}
      assert ev(opt.({:wrd, :u8, :none, []})) == {:ok, {:word, :u8, 9}}
    end

    test "nat match peels one successor" do
      m = {:match, {:nat, 3}, [{:arm, "zero", [], :ze}, {:arm, "suc", ["p"], {:var, "p"}}]}
      assert ev(m) == {:ok, {:nat, 2}}
    end

    test "a step and a source run may share a name" do
      funs = [
        fun("step0", [], {:nat, 1}),
        fun("s", [], {:uncons, {:stream, :ze, [], "step0"}}),
        fun("step0", [{"k", :nat, :reuse}], {:pair, {:var, "k"}, {:su, {:var, "k"}}}, %{
          generated: true
        })
      ]

      assert Eval.call(funs, "step0", []) == {:ok, {:nat, 1}}

      assert {:ok, {:pair, {:nat, 0}, {:stream, "step0", [], {:nat, 1}}}} =
               Eval.call(funs, "s", [])
    end
  end

  describe "streams" do
    test "nats from examples/nats.muro" do
      assert {:ok, funs} = IR.elaborate_file("examples/nats.muro")
      assert {:ok, s} = Eval.call(funs, "natsFrom", [{:nat, 5}])
      assert Eval.take(funs, s, 4) == {:ok, [{:nat, 5}, {:nat, 6}, {:nat, 7}, {:nat, 8}]}
    end

    test "captures come first and an erased seed is not passed" do
      funs = [
        fun("s", [{"c", :nat, :reuse}], {:stream, :ze, [{"c", {:var, "c"}}], "step1"}),
        fun("step1", [{"c", :nat, :reuse}], {:pair, {:var, "c"}, :ze}, %{generated: true})
      ]

      assert {:ok, s} = Eval.call(funs, "s", [{:nat, 7}])
      assert Eval.take(funs, s, 2) == {:ok, [{:nat, 7}, {:nat, 7}]}
    end
  end

  describe "closures" do
    test "lam and appv" do
      t =
        {:appv, {:appv, {:lam, "x", :nat, :reuse, {:lam, "y", :nat, :reuse, {:var, "x"}}}, :ze},
         {:nat, 2}}

      assert ev(t) == {:ok, {:nat, 0}}
    end

    test "higher_order.muro on the closure image" do
      {:ok, book} = Muro.Load.file("examples/higher_order.muro")
      {:ok, funs} = IR.elaborate(Muro.Prelude.for_emit(book), closures: true)
      assert {:ok, list} = Eval.call(funs, "add2", [])

      assert list ==
               {:con, "List", "cons",
                [{:nat, 2}, {:con, "List", "cons", [{:nat, 3}, {:con, "List", "nil", []}]}]}

      assert {:ok, s} = Eval.call(funs, "nats", [])
      assert Eval.take(funs, s, 3) == {:ok, [{:nat, 0}, {:nat, 1}, {:nat, 2}]}
      assert Eval.call(funs, "len-one", []) == {:ok, {:nat, 1}}
    end

    test "apply_value applies a closure value" do
      clo = {:clo, %{}, "x", {:su, {:var, "x"}}}
      assert Eval.apply_value([], clo, {:nat, 1}) == {:ok, {:nat, 2}}
      assert Eval.apply_value([], {:nat, 1}, {:nat, 1}) == {:error, {:type, :fn, {:nat, 1}}}
    end
  end

  describe "words" do
    test "wrapping, checked, signed, shifts, casts" do
      assert ev({:wrd, :u8, :add, [w(:u8, 255), w(:u8, 1)]}) == {:ok, {:word, :u8, 0}}

      assert ev({:wrd, :u64, :sub, [w(:u64, 0), w(:u64, 1)]}) ==
               {:ok, {:word, :u64, 18_446_744_073_709_551_615}}

      assert ev({:wrd, :u8, :cadd, [w(:u8, 255), w(:u8, 1)]}) == {:ok, :none}
      assert ev({:wrd, :u8, :csub, [w(:u8, 3), w(:u8, 1)]}) == {:ok, {:some, {:word, :u8, 2}}}
      assert ev({:wrd, :u32, :div, [w(:u32, 7), w(:u32, 0)]}) == {:ok, :none}
      assert ev({:wrd, :u32, :rem, [w(:u32, 7), w(:u32, 3)]}) == {:ok, {:some, {:word, :u32, 1}}}

      min = 9_223_372_036_854_775_808
      neg1 = 18_446_744_073_709_551_615
      assert ev({:wrd, :i64, :div, [w(:i64, min), w(:i64, neg1)]}) == {:ok, :none}
      assert ev({:wrd, :i64, :lt, [w(:i64, neg1), w(:i64, 0)]}) == {:ok, true}
      assert ev({:wrd, :u64, :lt, [w(:u64, neg1), w(:u64, 0)]}) == {:ok, false}
      assert ev({:wrd, :i64, :shr, [w(:i64, neg1), {:nat, 70}]}) == {:ok, {:word, :i64, neg1}}
      assert ev({:wrd, :u8, :shl, [w(:u8, 1), {:nat, 8}]}) == {:ok, {:word, :u8, 0}}
      assert ev({:wrd, :u8, :not, [w(:u8, 0)]}) == {:ok, {:word, :u8, 255}}
      assert ev({:wrd, :u8, :xor, [w(:u8, 12), w(:u8, 10)]}) == {:ok, {:word, :u8, 6}}
      assert ev({:wrd, :u8, {:cast, :u8}, [w(:u32, 257)]}) == {:ok, {:word, :u8, 1}}
      assert ev({:wrd, :u8, {:of, :u8}, [{:nat, 300}]}) == {:ok, {:word, :u8, 44}}
      assert ev({:wrd, :i64, :ton, [w(:i64, neg1)]}) == {:ok, {:nat, neg1}}
      assert ev({:wrd, :u8, :eq, [w(:u8, 1), w(:u8, 1)]}) == {:ok, true}
      assert ev({:wrd, :string, :some, [{:str, "a"}]}) == {:ok, {:some, {:str, "a"}}}
    end

    test "a word operation on a non-word is stuck" do
      assert {:error, {:stuck_word, :add, _}} = ev({:wrd, :u8, :add, [{:str, "a"}, w(:u8, 1)]})
      assert {:error, {:stuck_word, :add, _}} = ev({:wrd, :u8, :add, [w(:u32, 1), w(:u8, 1)]})
    end
  end

  describe "strings and bytes" do
    test "strings count scalars" do
      assert ev({:scat, {:str, "a"}, {:str, "é"}}) == {:ok, {:str, "aé"}}
      assert ev({:slen, {:str, "e\u0301"}}) == {:ok, {:nat, 2}}
      assert ev({:seq, {:str, "a"}, {:str, "a"}}) == {:ok, true}
      assert ev({:sbytes, {:str, "é"}}) == {:ok, {:bytes, "é"}}
    end

    test "bytes operations" do
      b = {:byt, "GET /x"}
      assert ev({:bcat, b, {:byt, "!"}}) == {:ok, {:bytes, "GET /x!"}}
      assert ev({:blen, b}) == {:ok, {:word, :u64, 6}}
      assert ev({:beq, b, {:byt, "GET /x"}}) == {:ok, true}
      assert ev({:bsub, b, w(:u64, 1), w(:u64, 2)}) == {:ok, {:bytes, "ET"}}
      assert ev({:bsub, b, w(:u64, 5), w(:u64, 9)}) == {:ok, {:bytes, ""}}
      assert ev({:bget, b, w(:u64, 0)}) == {:ok, {:some, {:word, :u8, ?G}}}
      assert ev({:bget, b, w(:u64, 6)}) == {:ok, :none}
      assert ev({:btil, b, w(:u8, 32)}) == {:ok, {:bytes, "GET"}}
      assert ev({:baft, b, w(:u8, 32)}) == {:ok, {:bytes, "/x"}}
      assert ev({:baft, b, w(:u8, 0)}) == {:ok, {:bytes, ""}}

      assert ev({:bunc, b}) ==
               {:ok, {:con, "Maybe", "just", [{:pair, {:word, :u8, ?G}, {:bytes, "ET /x"}}]}}

      assert ev({:bunc, {:byt, ""}}) == {:ok, {:con, "Maybe", "nothing", []}}
      assert ev({:bget, b, w(:u32, 0)}) == {:error, {:type, :u64, {:word, :u32, 0}}}
    end

    test "bfold passes captures, the octet, the rest, and the accumulator" do
      step =
        fun(
          "step3",
          [{"k", :u64, :reuse}, {"b", :u8, :reuse}, {"r", :slice, :reuse}, {"a", :u64, :reuse}],
          {:wrd, :u64, :add,
           [{:var, "a"}, {:wrd, :u64, :add, [{:var, "k"}, {:blen, {:var, "r"}}]}]},
          %{generated: true, fold: true}
        )

      t = {:bfold, "step3", [{"k", w(:u64, 10)}], w(:u64, 0), {:byt, "abc"}}
      # (10 + 2) + (10 + 1) + (10 + 0)
      assert Eval.eval([step], t) == {:ok, {:word, :u64, 33}}
      assert Eval.eval([step], t, %{}, fuel: 2) == {:error, :out_of_fuel}
    end
  end

  describe "errors" do
    test "non-termination runs out of fuel" do
      funs = [fun("loop", [{"x", :nat, :reuse}], {:call, "loop", [{:su, {:var, "x"}}]})]
      assert Eval.call(funs, "loop", [{:nat, 0}], fuel: 1000) == {:error, :out_of_fuel}
      assert Eval.call(funs, "loop", [{:nat, 0}]) == {:error, :out_of_fuel}
      assert Eval.default_fuel() > 0
    end

    test "abort, unbound, unknown, arity, missing arm, bad term" do
      assert ev(:abort) == {:error, :abort}
      assert ev({:var, "nope"}) == {:error, {:unbound, "nope"}}
      assert Eval.call([], "f", []) == {:error, {:unknown_fun, "f"}}
      funs = [fun("f", [{"x", :nat, :reuse}], {:var, "x"})]
      assert Eval.call(funs, "f", []) == {:error, {:arity, "f", 1, 0}}
      assert ev({:match, :tt, [{:arm, "zero", [], :ze}]}) == {:error, {:no_arm, :tt}}

      assert ev({:match, {:nat, 0}, [{:arm, "suc", ["p"], :ze}]}) ==
               {:error, {:no_arm, {:nat, 0}}}

      assert ev({:letp, "a", "b", :ze, :ze}) == {:error, {:type, :pair, {:nat, 0}}}
      assert ev({:uncons, :ze}) == {:error, {:type, :stream, {:nat, 0}}}
      assert ev({:mystery, 1}) == {:error, {:unknown_term, {:mystery, 1}}}
    end
  end

  describe "Ref" do
    setup do
      {:ok, book} = Muro.Load.file("examples/bytes-uncons.muro")
      {:ok, book: Muro.Prelude.for_emit(book)}
    end

    test "normal forms read as values", %{book: book} do
      nf = {:app, {:def, "just"}, {:pair, {:word, {:lit, :u8, 97}, []}, {:blit, "b"}}}

      assert Ref.of_normal(book, nf) ==
               {:ok, {:con, "Maybe", "just", [{:pair, {:word, :u8, 97}, {:bytes, "b"}}]}}

      assert Ref.of_normal(book, {:su, {:nat, 2}}) == {:ok, {:nat, 3}}
      assert Ref.of_normal(book, :one) == {:ok, :tt}
      assert Ref.of_normal(book, {:atom, "x"}) == {:ok, {:con, "Atom", "x", []}}
      assert Ref.of_normal(book, {:word, :some, [{:word, true, []}]}) == {:ok, {:some, true}}
      assert Ref.of_normal(book, {:slit, "s"}) == {:ok, {:str, "s"}}

      lam = {:lam, :affine, :nat, "x", {:var, 0}}
      assert Ref.of_normal(book, lam) == {:error, {:not_value, lam}}
      assert {:error, {:not_value, _}} = Ref.of_normal(book, {:def, "just"})
    end

    test "values write back as terms", %{book: book} do
      v = {:con, "Maybe", "just", [{:pair, {:word, :u8, 1}, {:bytes, "x"}}]}
      assert {:ok, t} = Ref.to_term(book, v)
      assert Ref.of_normal(book, t) == {:ok, v}
      assert Ref.to_term(book, {:con, "Atom", "k", []}) == {:ok, {:atom, "k"}}
      assert Ref.to_term(book, {:some, :none}) == {:ok, {:word, :some, [{:word, :none, []}]}}
      assert {:error, {:not_term, _}} = Ref.to_term(book, {:con, "Maybe", "just", []})
      assert {:error, {:not_term, _}} = Ref.to_term(book, {:clo, %{}, "x", :ze})
    end

    test "an erased constructor field is dropped and refilled" do
      book = [
        %{
          kind: :data,
          name: "Box",
          params: [],
          ctors: [
            %{
              name: "box",
              type: {:pi, :erased, :nat, "i", {:pi, :affine, :nat, "x", {:var, "Box"}}}
            }
          ]
        }
      ]

      t = {:app, {:app, {:def, "box"}, {:nat, 9}}, {:nat, 1}}
      assert Ref.of_normal(book, t) == {:ok, {:con, "Box", "box", [{:nat, 1}]}}

      assert Ref.to_term(book, {:con, "Box", "box", [{:nat, 1}]}, :one) ==
               {:ok, {:app, {:app, {:def, "box"}, :one}, {:nat, 1}}}
    end
  end
end
