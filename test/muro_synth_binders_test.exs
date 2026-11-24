defmodule Muro.SynthBindersTest do
  use ExUnit.Case, async: false

  alias Muro.Synth
  alias Muro.Synth.Names
  alias Muro.Synth.Term

  @iu "test/fixtures/synth_fresh_iu.muro"
  @list "test/fixtures/synth_fresh_list.muro"
  @quant "test/fixtures/synth_fresh_quant.muro"

  test "actions named i and u still certify a PredProg book" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@iu, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.book =~ "def survivor"
    assert result.book =~ "run PredProg :="
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "Finder"
    refute result.book =~ "def survivor : run PredProg := find-policy"
    refute result.book =~ "λ (+ i : Carrier)"
    refute result.book =~ "step i i"
    assert result.book =~ "| true => i"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "certificate CoindHomo"
    assert text =~ "prefers i"
  end

  test "a list cover with k0 and rk0 still certifies a PredProg book" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@list, depth: 0, max_depth: 0)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.book =~ "run PredProg :="
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "Finder"
    refute result.book =~ "def survivor : run PredProg := find-policy"
    refute result.book =~ "λ (k0 :"
    refute result.book =~ "suc k0"
    refute result.book =~ "λ (f0_0 :"
    assert result.book =~ "f0_0-2"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "certificate CoindHomo"
    refute text =~ "find-policy"
  end

  test "reach nests freshen rk0 when it is reserved and the book checks" do
    assert {:ok, host} = Muro.Synth.Host.open(@list)
    taken = Names.reserved(host.book)
    {binders, taken} = Names.table(taken)
    {pos, taken} = Muro.Synth.Book.reserve("dyn-pos", taken)

    reach =
      Names.with_binders(binders, taken, fn ->
        {text, _} =
          Muro.Synth.Reach.sources(
            host,
            "dyn-best-pos",
            "dyn-one",
            "dyn-any",
            pos,
            taken,
            nil,
            binders
          )

        text
      end)

    refute reach =~ "λ (rk0 :"
    refute reach =~ "| suc rk0 =>"
    assert reach =~ "rk0-2"
    refute reach =~ "Finder"

    r = Map.get(binders, "r", "r")

    pos_src = """
    def #{pos} : run Π (#{r} : Nat) → Bool :=
      λ (#{r} : Nat) →
        match #{r} motive (λ _ → Bool)
          | 0 => false
          | suc _ => true
    """

    dir = tmp()
    on_exit(fn -> File.rm_rf(dir) end)
    path = Path.join(dir, "reach.muro")

    File.write!(path, """
    import "#{rel_import(dir, @list)}"
    #{pos_src}
    #{reach}
    """)

    assert Muro.check_file(path) == :ok
  end

  test "quantified act and car binders miss reserved constructors and the book checks" do
    assert {:ok, host} = Muro.Synth.Host.open(@quant)
    families = Synth.Feature.families(host.feature_specs, host.actions)
    family = Enum.find(families, &(&1.stem == "has-pos-reward")) || hd(families)
    self = {:self, family.stem, "up", Map.fetch!(family.by_action, "up")}
    {dir, head} = quant_book(host, [self])
    on_exit(fn -> File.rm_rf(dir) end)

    refute head =~ "λ (+ act : Action)"
    refute head =~ "λ (+ car : Carrier)"
    assert head =~ "λ (+ act-2 : Action)"
    assert head =~ "λ (+ car-2 : Carrier)"
    refute head =~ "Finder"

    path = Path.join(dir, "agree.muro")

    File.write!(path, """
    #{head}
    def hold-up-s0 : evidence {stem-at has-pos-reward up s0 ≡ true : Bool} := refl
    def hold-up-s1 : evidence {stem-at has-pos-reward up s1 ≡ false : Bool} := refl
    """)

    assert Muro.check_file(path) == :ok
  end

  test "list equality freshens i and u when they are constructors" do
    schema = {:data, "State", [%{name: "cell", fields: [{:list, :nat}]}]}
    taken = Names.take(MapSet.new(), ["i", "u"])
    {binders, taken} = Names.table(taken)

    text =
      Names.with_binders(binders, taken, fn ->
        assert {:ok, src, _} = Term.eq_source("dyn-same", schema, taken, binders)
        src
      end)

    refute text =~ "λ (i :"
    refute text =~ "λ (u :"
    refute text =~ "cons i u"
    assert text =~ "i-2"
    assert text =~ "u-2"

    dir = tmp()
    on_exit(fn -> File.rm_rf(dir) end)

    path =
      write_book(dir, "list-eq.muro", """
      import "std:bool.muro"
      import "std:list.muro"

      data State : Type where
        cell : Π (xs : List Nat) → State

      data Marker : Type where
        i : Marker
        u : Marker

      #{text}
      def same-nil : evidence {dyn-same (cell nil) (cell nil) ≡ true : Bool} := refl
      def diff-cons : evidence {dyn-same (cell nil) (cell (cons 0 nil)) ≡ false : Bool} := refl
      def same-cons : evidence {dyn-same (cell (cons 0 nil)) (cell (cons 0 nil)) ≡ true : Bool} := refl
      """)

    assert Muro.check_file(path) == :ok
  end

  test "exhaust freshens k0 against a reserved constructor and the book checks" do
    schema = {:data, "State", [%{name: "here", fields: []}, %{name: "there", fields: []}]}
    taken = Names.take(MapSet.new(), ["k0"])
    {binders, taken} = Names.table(taken)

    text =
      Names.with_binders(binders, taken, fn ->
        Term.same_source("dyn-same", schema, ["here", "there"], binders)
      end)

    refute text =~ "λ (k0 :"
    assert text =~ "k0-2"

    dir = tmp()
    on_exit(fn -> File.rm_rf(dir) end)

    path =
      write_book(dir, "exhaust-k0.muro", """
      import "std:bool.muro"

      data State : Type where
        here : State
        there : State

      data Marker : Type where
        k0 : Marker

      #{text}
      def same-here : evidence {dyn-same here here ≡ true : Bool} := refl
      def diff-arm : evidence {dyn-same here there ≡ false : Bool} := refl
      def same-there : evidence {dyn-same there there ≡ true : Bool} := refl
      """)

    assert Muro.check_file(path) == :ok
  end

  defp quant_book(host, preds) do
    arms =
      preds
      |> Enum.with_index()
      |> Enum.map(fn {pred, i} ->
        %{
          name: "survivor-#{i}",
          pred: pred,
          action: hd(host.actions),
          else: hd(host.actions),
          observations: []
        }
      end)

    dir = tmp()
    assert {:ok, src, _meta} = Muro.Synth.Book.render(host, arms, dir, "trace")
    [head, _rest] = String.split(src, "\ndef policy ", parts: 2)
    assert head =~ "def stem-at "
    {dir, head}
  end

  defp rel_import(from_dir, to_file) do
    from = from_dir |> Path.expand() |> Path.split()
    to = to_file |> Path.expand() |> Path.split()
    {from, to} = drop_common(from, to)
    Path.join(List.duplicate("..", length(from)) ++ to)
  end

  defp drop_common([head | from], [head | to]), do: drop_common(from, to)
  defp drop_common(from, to), do: {from, to}

  defp joined(result), do: Enum.join(result.lines, "\n")

  defp write_book(dir, name, src) do
    path = Path.join(dir, name)
    File.write!(path, src)
    path
  end

  defp tmp do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_synth_binders_#{System.unique_integer([:positive])}_#{System.system_time(:nanosecond)}"
      )

    File.rm_rf!(dir)
    File.mkdir_p!(dir)
    dir
  end
end
