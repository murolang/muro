defmodule Muro.EmitMbiTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.Emit.Mbi

  @images ~w(once affine reuse twice drop app suc match pi iv)

  @failures ~w(
    fail-typ fail-nat fail-unit fail-empty fail-data fail-id fail-def
    fail-pair fail-stream fail-machine fail-word
  )

  test "Agda agree strings are the Elixir images, the erased terms, and the golden files" do
    agreed = agreements()

    for name <- @images do
      assert Map.has_key?(agreed, name), "missing agree:#{name}"
    end

    for name <- @failures do
      assert Map.has_key?(agreed, name), "missing agree:#{name}"
    end

    for {term, gtm, name} <- shared_terms() do
      assert Mbi.erase(term) == {:ok, gtm}
      assert Mbi.show_pure(gtm) == agreed[name]
    end

    for name <- @images do
      assert File.read!("examples/images/#{name}.mbi") == agreed[name] <> "\n"
    end
  end

  test "erase agrees with the Agda terms, not only the printed strings" do
    agreed = agreements()

    for {term, gtm, name} <- shared_terms() do
      assert {:ok, ^gtm} = Mbi.erase(term)
      assert Mbi.show_pure(gtm) == agreed[name]
    end

    assert Mbi.erase({:nat, 2}) == {:ok, {:gsu, {:gsu, :gze}}}
    assert Mbi.show_pure({:gsu, {:gsu, :gze}}) == agreed["suc"]

    assert Mbi.erase(:typ) == {:error, agreed["fail-typ"]}
    assert Mbi.erase(:nat) == {:error, agreed["fail-nat"]}
    assert Mbi.erase(:unit) == {:error, agreed["fail-unit"]}
    assert Mbi.erase(:one) == {:error, agreed["fail-unit"]}
    assert Mbi.erase({:munit, :ze, :ze, :ze}) == {:error, agreed["fail-unit"]}
    assert Mbi.erase(:empty) == {:error, agreed["fail-empty"]}
    assert Mbi.erase({:memp, :ze, :ze}) == {:error, agreed["fail-empty"]}
    assert Mbi.erase({:mdata, :ze, :ze, []}) == {:error, agreed["fail-data"]}
    assert Mbi.erase({:mwbool, :ze, :ze, []}) == {:error, agreed["fail-data"]}
    assert Mbi.erase({:mopt, :ze, :ze, []}) == {:error, agreed["fail-data"]}
    assert Mbi.erase(:rfl) == {:error, agreed["fail-id"]}
    assert Mbi.erase({:idt, :nat, :ze, :ze}) == {:error, agreed["fail-id"]}
    assert Mbi.erase({:rwt, :ze, :ze, :ze}) == {:error, agreed["fail-id"]}
    assert Mbi.erase({:def, 0}) == {:error, agreed["fail-def"]}
    assert Mbi.erase({:def, "plus"}) == {:error, agreed["fail-def"]}
    assert Mbi.erase({:pair, :ze, :ze}) == {:error, agreed["fail-pair"]}
    assert Mbi.erase({:prod, :nat, :nat}) == {:error, agreed["fail-pair"]}
    assert Mbi.erase({:letp, :ze, :ze}) == {:error, agreed["fail-pair"]}
    assert Mbi.erase({:nu, :ze}) == {:error, agreed["fail-stream"]}
    assert Mbi.erase({:unf, {:pair, :ze, :ze}, :ze}) == {:error, agreed["fail-stream"]}
    assert Mbi.erase({:ucons, :ze}) == {:error, agreed["fail-stream"]}
    assert Mbi.erase({:bisim, :ze, :ze}) == {:error, agreed["fail-stream"]}
    assert Mbi.erase({:stream, :nat}) == {:error, agreed["fail-stream"]}
    assert Mbi.erase({:always, :nat, :ze, :ze}) == {:error, agreed["fail-stream"]}
    assert Mbi.erase(:i64) == {:error, agreed["fail-machine"]}
    assert Mbi.erase(:f32ty) == {:error, agreed["fail-machine"]}
    assert Mbi.erase({:tensor, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Mbi.erase({:addi, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Mbi.erase({:muli, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Mbi.erase({:addt, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Mbi.erase({:toi64, :ze}) == {:error, agreed["fail-machine"]}
    assert Mbi.erase({:packi, :ze, :ze}) == {:error, agreed["fail-machine"]}
    assert Mbi.erase({:word, :add, []}) == {:error, agreed["fail-word"]}
  end

  test "every Elixir-only refusal is named, and a bad numeral is not a successor" do
    assert Mbi.erase(:string) == {:error, "string"}
    assert Mbi.erase({:slit, "hi"}) == {:error, "string"}
    assert Mbi.erase({:scat, :ze, :ze}) == {:error, "string"}
    assert Mbi.erase({:slen, :ze}) == {:error, "string"}
    assert Mbi.erase({:seq, :ze, :ze}) == {:error, "string"}
    assert Mbi.erase(:bytes) == {:error, "bytes"}
    assert Mbi.erase(:slice) == {:error, "bytes"}
    assert Mbi.erase({:blit, "hi"}) == {:error, "bytes"}
    assert Mbi.erase({:bcat, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:blen, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:beq, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:xlen, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:xeq, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:bsub, :ze, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:bget, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:aget, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:bunc, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:bfold, :ze, :ze, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:afold, :ze, :ze, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:sbytes, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:btil, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase({:baft, :ze, :ze}) == {:error, "bytes"}
    assert Mbi.erase(:atom) == {:error, "atom"}
    assert Mbi.erase({:atom, "hello"}) == {:error, "atom"}
    assert Mbi.erase({:matom, :ze, :ze, []}) == {:error, "atom"}
    assert Mbi.erase({:hole, nil}) == {:error, "hole"}
    assert Mbi.erase({:nat, -1}) == {:error, "numeral"}
    assert Mbi.erase({:nat, 1.5}) == {:error, "numeral"}
    assert Mbi.erase({:lam, {:grade, :nope, 0}, :nat, "n", :ze}) == {:error, "grade"}
    assert Mbi.erase({:lam, {:grade, {:iv, :nope, 1}, 0}, :nat, "n", :ze}) == {:error, "grade"}
    assert Mbi.erase({:lam, :nope, :nat, "n", {:var, 0}}) == {:error, "grade"}
    assert Mbi.erase({:pi, :nope, :nat, "n", :ze}) == {:error, "grade"}
    assert Mbi.erase(:nope) == {:error, "term"}
    assert Mbi.show_grade(:w) == "w"
    assert Mbi.show_grade(10) == "10"
    assert Mbi.erase({:ann, :ze, :nat}) == {:ok, :gze}
  end

  test "a checked book writes the golden image" do
    assert emit_src(affine_src()) == golden("affine")
    assert emit_src(percent_zero_src()) == golden("affine")
    assert emit_src(app_src()) == golden("app")
    assert emit_src(suc_src()) == golden("suc")
    assert emit_src(numeral_src()) == golden("suc")
    assert emit_src(match_src()) == golden("match")
    assert emit_src(drop_src()) == golden("drop")
    assert emit_src(reuse_src()) == golden("reuse")
    assert emit_src(linear_src()) == golden("once")
    assert emit_src(interval_src()) == golden("iv")

    dir = tmp_dir()
    path = write_book(dir, "keep", data_and_zero_src())
    assert {:ok, [file]} = Muro.emit_mbi(path)
    assert File.read!(file) == Mbi.show_pure(:gze) <> "\n"

    path = write_book(dir, "both", spec_and_zero_src())
    assert {:ok, [file]} = Muro.emit_mbi(path)
    assert File.read!(file) == Mbi.show_pure(:gze) <> "\n"

    path = write_book(dir, "hid", internal_and_zero_src())
    assert {:ok, [file]} = Muro.emit_mbi(path)
    assert File.read!(file) == Mbi.show_pure(:gze) <> "\n"
  end

  test "grades.muro refuses many and writes nothing" do
    dir = tmp_dir()
    path = Path.join(dir, "grades.muro")
    File.cp!("examples/grades.muro", path)
    file = Path.join(dir, "grades.mbi")
    prior = "prior-image\n"
    File.write!(file, prior)

    out =
      capture_io(fn ->
        assert_raise Mix.Error, ~r/\Ambi:def in many\z/, fn ->
          Mix.Tasks.Muro.Emit.run([path, "--backend", "mbi"])
        end
      end)

    assert out == ""
    assert File.read!(file) == prior
    assert {:error, "mbi:def in many"} = Muro.emit_mbi(path)
    assert File.read!(file) == prior
    assert {:raise, "", "mbi:def in many"} = Muro.CLI.Emit.run([path, "--backend", "mbi"])
    assert File.read!(file) == prior
  end

  test "a later run is named, an earlier failure keeps its reason, and a miss writes nothing" do
    dir = tmp_dir()

    path = write_book(dir, "two", two_src())
    assert {:error, "mbi:entry in b"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "two.mbi"))

    path = write_book(dir, "repair", repair_src())
    assert {:error, "mbi:pair in bad"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "repair.mbi"))

    path = write_book(dir, "none", "def p : spec Nat := 0\n")
    none = Path.join(dir, "none.mbi")
    prior = "prior-image\nnot-rewritten\n"
    File.write!(none, prior)
    assert {:error, "mbi:entry"} = Muro.emit_mbi(path)
    assert File.read!(none) == prior

    assert {:raise, "", "mbi:entry"} = Muro.CLI.Emit.run([path, "--backend", "mbi"])
    assert File.read!(none) == prior

    path = write_book(dir, "hid", "def hidden : run internal Nat := 0\n")
    assert {:error, "mbi:entry"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "hid.mbi"))

    path = write_book(dir, "data", data_match_src())
    assert {:error, "mbi:data in n"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "data.mbi"))

    path = write_book(dir, "str", "def hello : run String := \"hello\"\n")
    assert {:error, "mbi:string in hello"} = Muro.emit_mbi(path)

    path = write_book(dir, "oct", "def hello : run Bytes := b\"hello\"\n")
    assert {:error, "mbi:bytes in hello"} = Muro.emit_mbi(path)

    path = write_book(dir, "tag", "def tag : run Atom := :hello\n")
    assert {:error, "mbi:atom in tag"} = Muro.emit_mbi(path)

    path = write_book(dir, "zeros", zeros_src())
    assert {:error, "mbi:stream in zeros"} = Muro.emit_mbi(path)

    src = File.read!("examples/internal_ok.muro")
    path = write_book(dir, "internal_ok", src)
    assert {:error, "mbi:def in inc"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "internal_ok.mbi"))

    assert {:error, "mbi:term in bad"} =
             Mbi.render([%{name: "bad", mode: :run, type: :nat, body: {:nope}}])

    assert {:error, "mbi:grade in id"} =
             Mbi.render([
               %{
                 name: "id",
                 mode: :run,
                 type: :nat,
                 body: {:lam, :nope, :nat, "n", {:var, "n"}}
               }
             ])

    assert {:error, "mbi:entry"} = Mbi.render([])
  end

  test "success is exactly one exported run" do
    dir = tmp_dir()

    path = write_book(dir, "one", "def z : run Nat := 0\n")
    assert {:ok, [file]} = Muro.emit_mbi(path)
    assert File.read!(file) == Mbi.show_pure(:gze) <> "\n"

    path = write_book(dir, "empty", "")
    empty = Path.join(dir, "empty.mbi")
    prior = "prior-image\nnot-rewritten\n"
    File.write!(empty, prior)
    assert {:error, "mbi:entry"} = Muro.emit_mbi(path)
    assert File.read!(empty) == prior

    assert {:raise, "", "mbi:entry"} = Muro.CLI.Emit.run([path, "--backend", "mbi"])
    assert File.read!(empty) == prior

    path = write_book(dir, "spec", "def p : spec Nat := 0\n")
    assert {:error, "mbi:entry"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "spec.mbi"))

    path = write_book(dir, "three", three_src())
    assert {:error, "mbi:entry in b\nmbi:entry in c"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "three.mbi"))

    path = write_book(dir, "bothbad", both_bad_src())
    File.write!(Path.join(dir, "bothbad.mbi"), "stale\n")
    assert {:error, "mbi:pair in a\nmbi:string in b"} = Muro.emit_mbi(path)
    assert File.read!(Path.join(dir, "bothbad.mbi")) == "stale\n"

    path = write_book(dir, "only", "def n : run Nat × Nat := (0, 0)\n")
    assert {:error, "mbi:pair in n"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "only.mbi"))
  end

  test "a multi-run refusal leaves a previous image byte for byte" do
    dir = tmp_dir()
    prior = "prior-image\nnot-rewritten\n"

    for {name, src, message} <- [
          {"two", two_src(), "mbi:entry in b"},
          {"repair", repair_src(), "mbi:pair in bad"},
          {"three", three_src(), "mbi:entry in b\nmbi:entry in c"},
          {"bothbad", both_bad_src(), "mbi:pair in a\nmbi:string in b"}
        ] do
      path = write_book(dir, name, src)
      file = Path.join(dir, name <> ".mbi")
      File.write!(file, prior)
      assert {:error, ^message} = Muro.emit_mbi(path)
      assert File.read!(file) == prior

      assert {:raise, "", ^message} = Muro.CLI.Emit.run([path, "--backend", "mbi"])
      assert File.read!(file) == prior
    end

    path = write_book(dir, "only", "def n : run Nat × Nat := (0, 0)\n")
    file = Path.join(dir, "only.mbi")
    File.write!(file, prior)
    assert {:error, "mbi:pair in n"} = Muro.emit_mbi(path)
    assert File.read!(file) == prior

    help = Muro.CLI.Emit.help()
    assert help =~ "Writing it is not acceptance."
    refute help =~ "The module or the files were emitted."
  end

  test "a constructor or a data type is mbi:data, and a definition is mbi:def" do
    dir = tmp_dir()

    path = write_book(dir, "ctor", ctor_src())
    assert {:error, "mbi:data in n"} = Muro.emit_mbi(path)
    refute File.exists?(Path.join(dir, "ctor.mbi"))

    path = write_book(dir, "box", box_src())
    assert {:error, "mbi:data in n"} = Muro.emit_mbi(path)

    path = write_book(dir, "call", "def n : run Nat := plus 0 0\n")
    assert {:error, "mbi:def in n"} = Muro.emit_mbi(path)

    bool = %{kind: :data, name: "Bool", ctors: [%{name: "true"}, %{name: "false"}]}

    assert {:error, "mbi:data in n"} =
             Mbi.render([
               bool,
               %{name: "n", mode: :run, type: {:var, "Bool"}, body: {:var, "true"}}
             ])

    # A checked run cannot return a data type. The tag is still `data`
    # when that name is the term `erase` refuses.
    assert {:error, "mbi:data in n"} =
             Mbi.render([
               bool,
               %{
                 name: "n",
                 mode: :run,
                 type: :nat,
                 body: {:app, {:lam, :affine, :typ, "_", :ze}, {:var, "Bool"}}
               }
             ])

    assert {:error, "mbi:def in n"} =
             Mbi.render([
               %{name: "n", mode: :run, type: :nat, body: {:var, "plus"}}
             ])
  end

  test "a domain is dropped, so a data type written there is not a refusal" do
    image = Mbi.show_pure({:glam, {:iv, 0, 1}, 0, :gze}) <> "\n"
    assert emit_src(dropped_domain_src()) == image
    assert image =~ "(glam ((iv 0 1) 0) gze)"
    refute image =~ "Bool"
  end

  test "the mix task prints the path, and node and imports are refused before a file" do
    dir = tmp_dir()
    path = write_book(dir, "id", affine_src())

    assert capture_io(fn ->
             Mix.Tasks.Muro.Emit.run([path, "--backend", "mbi"])
           end) == Path.join(dir, "id.mbi") <> "\n"

    assert {:ok, out, ""} = Muro.CLI.Emit.run([path, "--backend", "mbi"])
    assert out == Path.join(dir, "id.mbi") <> "\n"

    assert {:raise, "", "--node writes the placement calls"} =
             Muro.CLI.Emit.run([path, "--backend", "mbi", "--node", "a"])

    assert {:raise, "", "--imports is only valid with --backend exunit or --backend pytest"} =
             Muro.CLI.Emit.run([path, "--backend", "mbi", "--imports"])

    bad = write_book(dir, "bad", "def n : run Nat := (0, 0)\n")
    stale = Path.join(dir, "bad.mbi")
    File.write!(stale, "stale\n")

    assert {:raise, "", message} = Muro.CLI.Emit.run([bad, "--backend", "mbi"])
    refute String.starts_with?(message, "mbi:")
    assert File.read!(stale) == "stale\n"
  end

  test "--backend beam is refused and names --backend mbi" do
    dir = tmp_dir()
    path = write_book(dir, "id", affine_src())
    stale = Path.join(dir, "id.mbi")
    File.write!(stale, "stale\n")

    message =
      "--backend beam is refused. Use --backend mbi. The file is the .mbi image muro-beam loads, not Erlang BEAM bytecode."

    assert {:raise, "", ^message} = Muro.CLI.Emit.run([path, "--backend", "beam"])
    assert {:raise, "", ^message} = Muro.CLI.Emit.run([path, "--backend", "beam", "--node", "a"])

    assert {:raise, "", ^message} =
             Muro.CLI.Emit.run([path, "--backend", "beam", "--imports"])

    assert File.read!(stale) == "stale\n"

    assert capture_io(fn ->
             assert_raise Mix.Error, ~r/\A#{Regex.escape(message)}\z/, fn ->
               Mix.Tasks.Muro.Emit.run([path, "--backend", "beam"])
             end
           end) == ""
  end

  defp shared_terms do
    [
      {{:lam, :linear, :nat, "n", {:var, 0}}, {:glam, 1, 0, {:gvar, 0}}, "once"},
      {{:lam, {:grade, 1, 0}, :nat, "n", {:var, 0}}, {:glam, 1, 0, {:gvar, 0}}, "once"},
      {{:lam, :affine, :nat, "n", {:var, 0}}, {:glam, {:iv, 0, 1}, 0, {:gvar, 0}}, "affine"},
      {{:lam, :reuse, :nat, "n", {:var, 0}}, {:glam, :w, 0, {:gvar, 0}}, "reuse"},
      {{:lam, :reuse, :nat, "n", {:app, {:var, 0}, {:var, 0}}},
       {:glam, :w, 0, {:gapp, {:gvar, 0}, {:gvar, 0}}}, "twice"},
      {{:lam, :erased, :nat, "n", :ze}, {:glam, 0, 0, :gze}, "drop"},
      {{:app, {:lam, :affine, :nat, "n", {:var, 0}}, :ze},
       {:gapp, {:glam, {:iv, 0, 1}, 0, {:gvar, 0}}, :gze}, "app"},
      {{:su, {:su, :ze}}, {:gsu, {:gsu, :gze}}, "suc"},
      {{:mnat, :ze, {:lam, :affine, :nat, "_", :nat}, :ze, {:var, 0}},
       {:gmatch, :gze, :gze, {:gvar, 0}}, "match"},
      {{:pi, :affine, :nat, "n", {:var, 0}}, {:gpi, {:iv, 0, 1}, 0, {:gvar, 0}}, "pi"},
      {{:lam, {:grade, {:iv, 0, 2}, 0}, :nat, "n", {:var, 0}},
       {:glam, {:iv, 0, 2}, 0, {:gvar, 0}}, "iv"}
    ]
  end

  defp agreements do
    "agda/Muro/Beam.agda"
    |> File.read!()
    |> then(fn src ->
      Regex.scan(~r/-- agree:(\S+)\n[^\n]*≡ (?:fail )?"([^"]*)"/u, src)
    end)
    |> Map.new(fn [_, name, image] -> {name, image} end)
  end

  defp golden(name), do: File.read!("examples/images/#{name}.mbi")

  defp emit_src(src) do
    dir = tmp_dir()
    path = write_book(dir, "book", src)
    assert {:ok, [file]} = Muro.emit_mbi(path)
    File.read!(file)
  end

  defp write_book(dir, name, src) do
    path = Path.join(dir, name <> ".muro")
    File.write!(path, src)
    path
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_mbi_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp affine_src do
    """
    def id : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    """
  end

  defp percent_zero_src do
    """
    def id : run Π (%0 n : Nat) → Nat :=
      λ (%0 n : Nat) → n
    """
  end

  defp app_src do
    """
    def z : run Nat := (λ (n : Nat) → n) 0
    """
  end

  defp suc_src do
    """
    def two : run Nat := suc (suc 0)
    """
  end

  defp numeral_src do
    """
    def two : run Nat := 2
    """
  end

  defp match_src do
    """
    def pred0 : run Nat :=
      match 0 motive (λ _ → Nat)
        | 0 => 0
        | suc m => m
    """
  end

  defp drop_src do
    """
    def drop : run Π (- n : Nat) → Nat :=
      λ (- n : Nat) → 0
    """
  end

  defp reuse_src do
    """
    def id : run Π (+ n : Nat) → Nat :=
      λ (+ n : Nat) → n
    """
  end

  defp linear_src do
    """
    def id : run Π (%1 n : Nat) → Nat :=
      λ (%1 n : Nat) → n
    """
  end

  defp interval_src do
    """
    def id : run Π (n : ([0, 2], 0) Nat) → Nat :=
      λ (n : ([0, 2], 0) Nat) → n
    """
  end

  defp two_src do
    """
    def a : run Nat := 0
    def b : run Nat := suc 0
    """
  end

  defp repair_src do
    """
    def bad : run Nat × Nat := (0, 0)
    def good : run Nat := 0
    """
  end

  defp data_and_zero_src do
    """
    data Bool : Type where
      tt : Bool
      ff : Bool

    def z : run Nat := 0
    """
  end

  defp data_match_src do
    """
    data Bool : Type where
      tt : Bool
      ff : Bool

    def n : run Π (b : Bool) → Nat :=
      λ (b : Bool) →
        match b motive (λ _ → Nat)
          | tt => 0
          | ff => 0
    """
  end

  defp spec_and_zero_src do
    """
    def p : spec Nat := 0
    def z : run Nat := 0
    """
  end

  defp internal_and_zero_src do
    """
    def hidden : run internal Nat := 0
    def z : run Nat := 0
    """
  end

  defp three_src do
    """
    def a : run Nat := 0
    def b : run Nat := suc 0
    def c : run Nat := suc (suc 0)
    """
  end

  defp both_bad_src do
    """
    def a : run Nat × Nat := (0, 0)
    def b : run String := "x"
    """
  end

  defp ctor_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool

    def n : run Bool := true
    """
  end

  defp box_src do
    """
    data Box : Type where
      box : Nat → Box

    def n : run Box := box 0
    """
  end

  defp dropped_domain_src do
    """
    data Bool : Type where
      tt : Bool
      ff : Bool

    def z : run Π (b : Bool) → Nat :=
      λ (b : Bool) → 0
    """
  end

  defp zeros_src do
    """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def zeros : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))
    """
  end
end
