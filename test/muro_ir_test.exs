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
               params: [{"k", :nat}],
               ret: {:pair, :nat, :nat},
               body: {:pair, {:var, "k"}, {:su, {:var, "k"}}}
             }
           ]
  end

  test "list stores cons fields and drops the erased parameter" do
    assert {:ok, funs} = Muro.IR.elaborate_file("examples/list.muro")
    assert Enum.map(funs, & &1.name) == ["length", "ones2"]

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

  defp atom?({:con, "Atom", name, []}, name), do: true
  defp atom?(t, name) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&atom?(&1, name))
  defp atom?(t, name) when is_list(t), do: Enum.any?(t, &atom?(&1, name))
  defp atom?(_, _), do: false
end
