defmodule Muro.IRTest do
  use ExUnit.Case, async: true

  test "half_ok elaborates plus and half and drops evidence" do
    assert {:ok, funs} = Muro.IR.elaborate_file("examples/half_ok.muro")
    assert Enum.map(funs, & &1.name) == ["plus", "half"]

    plus = Enum.find(funs, &(&1.name == "plus"))

    assert plus == %{
             name: "plus",
             export: true,
             params: [{"n", :nat}, {"m", :nat}],
             ret: :nat,
             body:
               {:match, {:var, "n"},
                [
                  {:arm, "zero", [], {:var, "m"}},
                  {:arm, "suc", ["np"], {:su, {:call, "plus", [{:var, "np"}, {:var, "m"}]}}}
                ]}
           }

    half = Enum.find(funs, &(&1.name == "half"))

    assert half.body ==
             {:match, {:var, "n"},
              [
                {:arm, "zero", [], :ze},
                {:arm, "suc", ["n1"],
                 {:match, {:var, "n1"},
                  [
                    {:arm, "zero", [], :ze},
                    {:arm, "suc", ["p"], {:su, {:call, "half", [{:var, "p"}]}}}
                  ]}}
              ]}
  end

  test "nats is a stream step" do
    assert {:ok, funs} = Muro.IR.elaborate_file("examples/nats.muro")

    assert funs == [
             %{
               name: "natsFrom",
               export: true,
               params: [{"n", :nat}],
               ret: {:stream, :nat},
               body: {:stream, {:var, "n"}, [], "step0"}
             },
             %{
               name: "step0",
               export: false,
               generated: true,
               params: [{"k", :nat}],
               ret: {:pair, :nat, :nat},
               body: {:pair, {:var, "k"}, {:su, {:var, "k"}}}
             }
           ]
  end

  test "list stores cons fields and drops the erased parameter" do
    assert {:ok, funs} = Muro.IR.elaborate_file("examples/list.muro")
    names = Enum.map(funs, & &1.name)
    assert "length" in names
    assert "ones2" in names

    length = Enum.find(funs, &(&1.name == "length"))
    assert length.params == [{"xs", {:data, "List"}}]
    assert length.ret == :nat

    assert length.body ==
             {:match, {:var, "xs"},
              [
                {:arm, "nil", [], :ze},
                {:arm, "cons", ["_", "as"], {:su, {:call, "length", [{:var, "as"}]}}}
              ]}

    ones2 = Enum.find(funs, &(&1.name == "ones2"))
    assert ones2.params == []
    assert ones2.ret == {:data, "List"}

    assert ones2.body ==
             {:con, "List", "cons",
              [
                {:su, :ze},
                {:con, "List", "cons", [{:su, :ze}, {:con, "List", "nil", []}]}
              ]}
  end

  test "sort lowers atom literals to the closed enumeration" do
    assert {:ok, funs} = Muro.IR.elaborate_file("examples/sort.muro")
    insert = Enum.find(funs, &(&1.name == "insert"))
    assert insert.params |> Enum.at(0) == {"d", {:data, "Atom"}}
    assert Enum.any?(funs, &(&1.name == "sort"))
    assert atom?(insert.body, "asc")
    assert atom?(insert.body, "desc")
    refute Enum.any?(funs, &(&1.name == "sort-two"))
  end

  test "nx_add is c:machine" do
    assert {:error, "c:machine"} = Muro.IR.elaborate_file("examples/nx_add.muro")
  end

  test "a bare lambda is c:lambda" do
    book = [
      %{
        name: "bad",
        mode: :run,
        type: :nat,
        body: {:lam, :affine, :nat, "n", :ze}
      }
    ]

    assert {:error, "c:lambda"} = Muro.IR.elaborate(book)
  end

  test "an erased argument is not elaborated" do
    book = [
      %{
        name: "drop",
        mode: :run,
        type: {:pi, :erased, :nat, "n", :nat},
        body: {:lam, :erased, :nat, "n", :ze}
      }
    ]

    assert {:ok, [fun]} = Muro.IR.elaborate(book)
    assert fun.params == []
    assert fun.body == :ze

    used = [
      %{
        name: "use",
        mode: :run,
        type: {:pi, :erased, :nat, "n", :nat},
        body: {:lam, :erased, :nat, "n", {:var, "n"}}
      }
    ]

    assert {:error, "c:erased"} = Muro.IR.elaborate(used)
  end

  test "a raw nu is c:stream and a name outside the book is c:unsupported" do
    nu = [
      %{
        name: "bad",
        mode: :run,
        type: :nat,
        body: {:nu, "X", :nat}
      }
    ]

    assert {:error, "c:stream"} = Muro.IR.elaborate(nu)

    missing = [
      %{
        name: "bad",
        mode: :run,
        type: :nat,
        body: {:var, "missing"}
      }
    ]

    assert {:error, "c:unsupported"} = Muro.IR.elaborate(missing)
  end

  test "an atom literal is a nullary constructor of Atom" do
    book = [
      %{
        name: "dir",
        mode: :run,
        type: :atom,
        body: {:atom, "asc"}
      }
    ]

    assert {:ok, [fun]} = Muro.IR.elaborate(book)
    assert fun.body == {:con, "Atom", "asc", []}
    assert fun.ret == {:data, "Atom"}
  end

  test "an erased constructor field is marked erased and a spec alias of Nat is not" do
    dir = Path.join(System.tmp_dir!(), "muro_ir_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "mark.muro")

    File.write!(path, """
    def R : spec Type := Nat

    data Box : Type where
      mk : Π (- e : Nat) → Nat → Box

    def one : run Nat := (λ (r : R) → suc r) 0

    def boxed : run Box := mk 0 (suc (suc 0))

    def live : run Nat :=
      match boxed motive (λ _ → Nat)
        | mk e n => n
    """)

    {:ok, book} = Muro.Load.file(path)
    book = Muro.Prelude.for_emit(book)

    assert {:ok, plain} = Muro.IR.elaborate(book)
    assert {:ok, closed} = Muro.IR.elaborate(book, closures: true)

    assert fun_body(plain, "one") == {:let, "r", :nat, :ze, {:su, {:var, "r"}}}
    assert fun_body(closed, "one") == {:let, "r", :nat, :ze, {:su, {:var, "r"}}}

    assert fun_body(plain, "live") ==
             {:match, {:call, "boxed", []},
              [{:arm, "mk", ["n"], {:let, "e", :erased, :ze, {:var, "n"}}}]}

    assert fun_body(closed, "live") ==
             {:match, {:call, "boxed", []}, {:data, "Box"},
              [{:arm, "mk", ["n"], {:let, "e", :erased, :ze, {:var, "n"}}}]}

    assert fun_body(plain, "boxed") == {:con, "Box", "mk", [{:su, {:su, :ze}}]}

    for funs <- [plain, closed] do
      refute Enum.any?(["one", "live", "boxed"], fn name ->
               opaque_zero?(fun_body(funs, name))
             end)
    end
  end

  defp fun_body(funs, name) do
    Enum.find(funs, &(&1.name == name)).body
  end

  defp opaque_zero?({:let, _, :opaque, :ze, _}), do: true
  defp opaque_zero?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&opaque_zero?/1)
  defp opaque_zero?(t) when is_list(t), do: Enum.any?(t, &opaque_zero?/1)
  defp opaque_zero?(_), do: false

  defp atom?({:con, "Atom", name, []}, name), do: true
  defp atom?(t, name) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&atom?(&1, name))
  defp atom?(t, name) when is_list(t), do: Enum.any?(t, &atom?(&1, name))
  defp atom?(_, _), do: false
end
