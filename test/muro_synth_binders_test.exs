defmodule Muro.SynthBindersTest do
  use ExUnit.Case, async: false

  alias Muro.Synth
  alias Muro.Synth.Names
  alias Muro.Synth.Term

  @iu "test/fixtures/synth_fresh_iu.muro"
  @list "test/fixtures/synth_fresh_list.muro"
  @quant "test/fixtures/synth_fresh_quant.muro"
  @reach_js "test/fixtures/synth_fresh_reach_js.muro"
  @feat_rk0 "test/fixtures/synth_fresh_feat_rk0.muro"
  @class "test/fixtures/synth_fresh_class.muro"
  @class_actions ~w(c0 c1 c2 c3)

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

  test "a list cover with reserved f0_0 still certifies a PredProg book" do
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

  test "actions named j and s still certify a PredProg book" do
    assert {:ok, result} = Muro.Synth.cegis_loop(@reach_js, depth: 0, max_depth: 1)
    assert result.status == :certified
    assert result.certificate == "CoindHomo"
    assert result.book =~ "run PredProg :="
    assert result.book =~ "evidence CoindHomo rank"
    refute result.book =~ "Finder"
    refute result.book =~ "def survivor : run PredProg := find-policy"
    refute result.book =~ "λ (+ s : State)"
    assert result.book =~ "s-2"

    text = joined(result)
    assert text =~ "muro synth: homomorphism checked"
    assert text =~ "certificate CoindHomo"
    refute text =~ "find-policy"
  end

  test "Book.render freshens j, s, rk0, k0, and f0_0 on the production path" do
    {dir, src, meta} = render_reach(@reach_js, also_self_loop: true)
    on_exit(fn -> File.rm_rf(dir) end)

    assert meta.kind == :certified
    refute src =~ "Finder"

    refute src =~ "Π (+ j : Nat)"
    refute src =~ "λ (+ j : Nat)"
    refute src =~ "Π (+ s : State)"
    refute src =~ "λ (+ s : State)"
    refute src =~ "| suc rk0 =>"
    refute src =~ "λ (rk0 :"
    refute src =~ "λ (k0 :"
    refute src =~ "λ (f0_0 :"
    assert src =~ "j-2"
    assert src =~ "s-2"
    assert src =~ "rk0-2"
    assert src =~ "k0-2"
    assert src =~ "f0_0-2"
    # Action constructors stay bare in any_body / step; only binders freshen.
    assert src =~ ~r/dyn-one(?:-tab)?\s+s-2\s+j\s+j-2/
    assert src =~ ~r/dyn-one(?:-tab)?\s+s-2\s+s\s+j-2/

    path = Path.join(dir, "reach-js.muro")
    File.write!(path, src)
    assert Muro.check_file(path) == :ok
  end

  test "Book.render keeps Feature rk0, k0, and f0_0 distinct from Reach binders" do
    {dir, src, meta} =
      render_reach(@feat_rk0, also_self_loop: true, also_hints: ["rk0", "k0", "f0_0"])

    on_exit(fn -> File.rm_rf(dir) end)

    assert meta.kind == :certified
    refute src =~ "find-policy"
    assert src =~ "rk0-2"
    assert src =~ "k0-2"
    assert src =~ "f0_0-2"
    assert_distinct_spelling(src, "rk0")
    assert_distinct_spelling(src, "k0")
    assert_distinct_spelling(src, "f0_0")

    path = Path.join(dir, "feat-rk0.muro")
    File.write!(path, src)
    assert Muro.check_file(path) == :ok
  end

  @tag timeout: 180_000
  test "ClassCert freshens reserved standard binders and the book checks" do
    assert {:ok, host} = Muro.Synth.Host.open(@class)
    assert {:ok, specs} = Synth.Feature.extend_reach(host)
    host = Muro.Synth.Host.install_features(host, specs)
    arms = class_arms()
    dir = tmp()
    on_exit(fn -> File.rm_rf(dir) end)

    assert {:ok, src, meta} = Muro.Synth.Book.render(host, arms, dir, "coind-homo")
    assert meta.kind == :certified
    assert meta.class_proof == true
    refute src =~ "find-policy"
    refute src =~ "find-ranking"
    refute src =~ "λ (c : Config)"
    refute src =~ "Π (c : Config)"
    refute src =~ "λ (s : State)"
    refute src =~ "Π (s : State)"
    assert src =~ "λ (c-2 : Config)" or src =~ "Π (c-2 : Config)"
    assert src =~ "s-2"
    assert src =~ "a-2"
    assert src =~ "class-ongoing"

    path = Path.join(dir, "class.muro")
    File.write!(path, src)
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

  defp render_reach(path, opts) do
    assert {:ok, host} = Muro.Synth.Host.open(path)

    host =
      case Synth.Feature.extend_reach(host) do
        {:ok, specs} -> Muro.Synth.Host.install_features(host, specs)
        :same -> flunk("expected reaches-pos to extend on #{path}")
      end

    host =
      case Keyword.get(opts, :also_hints, []) do
        [] ->
          host

        names ->
          present = MapSet.new(host.feature_specs, & &1.name)

          added =
            names
            |> Enum.reject(&MapSet.member?(present, &1))
            |> Enum.map(&%{name: &1, kind: :hint, action: nil})

          if added == [] do
            host
          else
            Muro.Synth.Host.install_features(host, host.feature_specs ++ added)
          end
      end

    families = Synth.Feature.families(host.feature_specs, host.actions)
    reach = Enum.find(families, &(&1.stem == "reaches-pos"))
    assert reach, "expected a reaches-pos family on #{path}"
    action = hd(host.actions)
    preds = [{:self, reach.stem, action, Map.fetch!(reach.by_action, action)}]

    preds =
      if Keyword.get(opts, :also_self_loop, false) do
        loop = Enum.find(families, &(&1.stem == "is-self-loop"))
        assert loop, "expected an is-self-loop family on #{path}"
        preds ++ [{:self, loop.stem, action, Map.fetch!(loop.by_action, action)}]
      else
        preds
      end

    preds =
      preds ++
        Enum.map(Keyword.get(opts, :also_hints, []), fn name ->
          {:feat, name}
        end)

    arms =
      preds
      |> Enum.with_index()
      |> Enum.map(fn {pred, i} ->
        %{
          name: "survivor-#{i}",
          pred: pred,
          action: action,
          else: action,
          observations: []
        }
      end)

    dir = tmp()
    assert {:ok, src, meta} = Muro.Synth.Book.render(host, arms, dir, "trace")
    {dir, src, meta}
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

  defp assert_distinct_spelling(src, base) do
    escaped = Regex.escape(base)

    binders =
      Regex.scan(~r/(?:suc |λ \(|spot )(#{escaped}-\d+)/, src)
      |> Enum.map(&Enum.at(&1, 1))
      |> Enum.uniq()

    ctors =
      Regex.scan(~r/^  (#{escaped}-\d+) : /m, src)
      |> Enum.map(&Enum.at(&1, 1))
      |> Enum.uniq()

    assert binders != [], "expected freshened binder #{base}-N in reach or exhaust"
    assert ctors != [], "expected freshened Feature constructor #{base}-N"

    assert MapSet.disjoint?(MapSet.new(binders), MapSet.new(ctors)),
           "#{base} binder #{inspect(binders)} collided with constructor #{inspect(ctors)}"
  end

  defp class_arms do
    others = fn action ->
      for other <- @class_actions, other != action, do: "reaches-pos-#{other}"
    end

    spec = fn action, pred ->
      %{
        name: "survivor-#{action}",
        pred: pred,
        action: action,
        else: "c0",
        observations: []
      }
    end

    [
      spec.(
        "c0",
        {:or, {:feat, "has-pos-reward-c0"}, {:not, {:other, "reaches-pos", "c0", others.("c0")}}}
      ),
      spec.(
        "c1",
        {:or, {:feat, "reaches-pos-c1"}, {:not, {:other, "reaches-pos", "c1", others.("c1")}}}
      ),
      spec.(
        "c2",
        {:or, {:feat, "reaches-pos-c2"}, {:not, {:other, "reaches-pos", "c2", others.("c2")}}}
      ),
      spec.(
        "c3",
        {:or, {:feat, "has-pos-reward-c0"}, {:not, {:other, "reaches-pos", "c3", others.("c3")}}}
      )
    ]
  end

  defp joined(result), do: Enum.join(result.lines, "\\n")

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
