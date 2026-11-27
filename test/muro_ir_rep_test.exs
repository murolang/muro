defmodule Muro.IRRepTest do
  use ExUnit.Case, async: true

  alias Muro.IR
  alias Muro.IR.Rep
  alias Muro.Emit.C

  # The corpus walks emit or Share every book, the HTTP step book too.
  @moduletag timeout: 600_000

  @corpus ["examples/**/*.muro", "test/fixtures/**/*.muro", "lib/muro/std/*.muro"]

  test "each data type resolves to an enum, a value struct, or a boxed object" do
    book = book!(reps_src())
    reps = Rep.of_book(book)

    assert reps["Color"] == {:enum, ["red", "green"]}
    # An all-nullary unboxed type is the same enum.
    assert reps["Flag"] == {:enum, ["go", "stop"]}
    # A constructor whose only field is erased is still nullary.
    assert reps["Tagged"] == {:enum, ["mark", "plain"]}

    assert reps["Acc"] ==
             {:value, [{"acc", [{"n", :u64, :live}, {"s", :slice, :live}]}]}

    assert reps["E"] == {:value, [{"e", [{"n", :nat, :erased}, {"k", :u64, :live}]}]}

    assert reps["Box"] ==
             {:boxed,
              [{"box", [{"n", :nat, :live}, {"a", {:data, "Acc"}, :live}]}, {"empty", []}]}

    assert Rep.kind(reps["Color"]) == :enum
    assert Rep.kind(reps["Acc"]) == :value
    assert Rep.kind(reps["Box"]) == :boxed
    assert Rep.data_rep(book, "Box") == reps["Box"]
    assert Rep.data_rep(book, "Nope") == nil
  end

  test "the predicates C reads follow the representation" do
    book = book!(reps_src())

    assert Rep.enum?(book, "Flag")
    refute Rep.value?(book, "Flag")
    assert Rep.unboxed?(book, "Flag")
    assert Rep.value?(book, "Acc")
    refute Rep.value?(book, "Box")

    assert Rep.value_lay?(book, {:data, "Acc"})
    refute Rep.value_lay?(book, {:data, "Flag"})
    refute Rep.value_lay?(book, {:data, "Box"})
    refute Rep.value_lay?(book, :u64)

    assert Rep.value_opt_payload?(book, {:opt, {:data, "Acc"}})
    assert Rep.value_opt_payload?(book, {:opt, {:opt, {:data, "Acc"}}})
    refute Rep.value_opt_payload?(book, {:opt, {:data, "Flag"}})
    refute Rep.value_opt_payload?(book, {:opt, :u8})

    # A by-value field is embedded in a boxed object and a value struct alike.
    assert Rep.value_deps(book, find(book, "Box")) == ["Acc"]
    assert Rep.value_deps(book, find(book, "Wrap")) == ["Acc"]
    assert Rep.value_deps(book, find(book, "Color")) == []
    assert Rep.live_layouts(book, ctor(book, "E", "e")) == [:u64]
  end

  test "every data type of the corpus has the C type the representation names" do
    for path <- corpus(), {:ok, book} <- [load(path)], d <- datas(book) do
      rep = Rep.of_data(book, d)
      assert C.enum_type?(book, d.name) == (Rep.kind(rep) == :enum), "#{path} #{d.name}"
      value? = Rep.unboxed_data?(d) and not C.enum_type?(book, d.name)
      assert Rep.kind(rep) == :value == value?, "#{path} #{d.name}"
      assert Rep.value?(book, d.name) == value?, "#{path} #{d.name}"

      {_, ctors} = rep

      if Rep.kind(rep) != :enum do
        assert Enum.map(ctors, &elem(&1, 0)) == Enum.map(d.ctors, & &1.name)
      end
    end
  end

  test "c:unboxed is refused in one place, as C refuses it" do
    for src <- [pair_src(), stream_src(), opt_src()] do
      book = book!(src)
      {:ok, funs} = IR.elaborate(book)
      assert Rep.check(funs, book) == {:error, "c:unboxed"}
      assert C.prepare(book, "b") == {:error, "c:unboxed"}
    end

    opt = book!(opt_src())
    {:ok, opt_funs} = IR.elaborate(opt)
    assert Rep.refuse_unboxed_opt(opt, opt_funs) == {:error, "c:unboxed"}
    assert Muro.Emit.refuse_unboxed_opt(opt, opt_funs) == {:error, "c:unboxed"}
    assert Rep.refuse_unboxed_opt(book!(nest_src()), []) == :ok

    # An unboxed field embeds by value, and an enum is a word in a pair.
    for src <- [nest_src(), enum_pair_src()] do
      book = book!(src)
      {:ok, funs} = IR.elaborate(book)
      assert Rep.check(funs, book) == :ok
      assert {:ok, _, _, _} = C.prepare(book, "b")
    end
  end

  test "Rep.check agrees with C on every C book of the corpus" do
    results =
      (corpus() ++ ["test/http_step/step.muro"])
      |> Task.async_stream(
        fn path ->
          with {:ok, book} <- load(path), {:ok, funs} <- IR.elaborate(book) do
            stem = Path.basename(path, ".muro")
            c = C.prepare(book, stem, path: path)
            {path, c_verdict(c), Rep.check(funs, book)}
          else
            _ -> nil
          end
        end,
        timeout: :infinity
      )
      |> Enum.flat_map(fn {:ok, r} -> List.wrap(r) end)

    emitted = for {p, :ok, rep} <- results, do: {p, rep}
    assert length(emitted) >= 60
    assert Enum.reject(emitted, fn {_p, rep} -> rep == :ok end) == []

    for {p, {:error, "c:unboxed"}, rep} <- results,
        do: assert({p, rep} == {p, {:error, "c:unboxed"}})
  end

  defp c_verdict({:ok, _, _, _}), do: :ok
  defp c_verdict(err), do: err

  # -- books ---------------------------------------------------------------

  defp reps_src do
    """
    data Color : Type where
      red : Color
      green : Color

    unboxed data Flag : Type where
      go : Flag
      stop : Flag

    data Tagged : Type where
      mark : Π (- n : Nat) → Tagged
      plain : Tagged

    unboxed data Acc : Type where
      acc : Π (+ n : U64) → Π (+ s : Slice) → Acc

    unboxed data E : Type where
      e : Π (- n : Nat) → Π (+ k : U64) → E

    unboxed data Wrap : Type where
      wrap : Π (+ a : Acc) → Wrap

    data Box : Type where
      box : Π (+ n : Nat) → Π (+ a : Acc) → Box
      empty : Box

    def one : run U64 := toU64 1
    """
  end

  defp pair_src do
    """
    unboxed data W : Type where
      w : Π (+ n : U64) → W

    def both : run Π (+ n : U64) → (W × U64) :=
      λ (+ n : U64) → (w n, n)
    """
  end

  defp stream_src do
    """
    unboxed data W : Type where
      w : Π (+ n : U64) → W

    def seed : run W := w (toU64 0)

    def zs : run Stream W :=
      unfold seed (λ (+ s : W) → (s, s))
    """
  end

  defp opt_src do
    """
    unboxed data W : Type where
      w : Π (n : U64) → W

    def o : run Opt W := wnone
    """
  end

  defp nest_src do
    """
    unboxed data Inner : Type where
      inner : Π (+ n : U64) → Inner

    unboxed data Outer : Type where
      outer : Π (+ i : Inner) → Π (+ n : U64) → Outer

    def wrap : run Π (+ n : U64) → Outer :=
      λ (+ n : U64) → outer (inner n) n
    """
  end

  defp enum_pair_src do
    """
    unboxed data Flag : Type where
      go : Flag
      stop : Flag

    def both : run Π (+ n : U64) → (Flag × U64) :=
      λ (+ n : U64) → (go, n)
    """
  end

  # -- helpers ---------------------------------------------------------------

  defp book!(src) do
    dir = Path.join(System.tmp_dir!(), "muro_ir_rep_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "b.muro")
    File.write!(path, src)
    {:ok, book} = load(path)
    book
  end

  # The book every emitter reads (`Muro.emit_c/2`).
  defp load(path) do
    with {:ok, book} <- Muro.Load.file(path) do
      {:ok, book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()}
    end
  end

  defp corpus, do: @corpus |> Enum.flat_map(&Path.wildcard/1) |> Enum.sort()

  defp datas(book), do: Enum.filter(book, &(Map.get(&1, :kind) == :data))
  defp find(book, name), do: Enum.find(datas(book), &(&1.name == name))
  defp ctor(book, d, c), do: Enum.find(find(book, d).ctors, &(&1.name == c))
end
