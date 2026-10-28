defmodule Muro.ReprTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.{Check, Emit, Parser}

  @shapes """
  repr Demo := circle => map open { "id" => integer, :flag => optional nullable boolean, "xs" => list integer }
             | empty => nil
             | bare => :tag
             | text => "circle"
             | num => tuple { :ok, integer, nil }
  """

  test "every shape form parses to the same AST" do
    assert {:ok, [repr]} = Parser.parse(@shapes)
    assert repr.kind == :repr
    assert repr.name == "Demo"
    assert repr.mode == :spec
    assert repr.loc == {1, 1}

    assert repr.body ==
             {:choice,
              [
                {"circle",
                 {:map, true,
                  [
                    {"id", {:integer}},
                    {:flag, {:optional, {:nullable, {:boolean}}}},
                    {"xs", {:list, {:integer}}}
                  ]}},
                {"empty", {nil}},
                {"bare", {:atom, "tag"}},
                {"text", {:string, "circle"}},
                {"num", {:tuple, [{:atom, "ok"}, {:integer}, {nil}]}}
              ]}
  end

  test "a repr parses after data, after a def, and after another repr" do
    assert {:ok, book} =
             Parser.parse("""
             data Bool : Type where
               true : Bool
               false : Bool
             def one : run Nat := 0
             repr Bool := boolean
             repr Nat := integer
             def two : run Nat := suc 0
             """)

    assert Enum.map(book, &entry_tag/1) == [:data, :def, :repr, :repr, :def]
    assert :ok = Check.check_sig(book)
  end

  test "repr stays a definition name and a constructor name" do
    assert {:ok, [d]} = Parser.parse("def repr : run Nat := 0\n")
    assert entry_tag(d) == :def
    assert d.name == "repr"
    assert :ok = Check.check_sig([d])

    src = """
    data Box : Type where
      repr : Box
    def one : run Box := repr
    """

    assert {:ok, [data, defn]} = Parser.parse(src)
    assert hd(data.ctors).name == "repr"
    assert defn.name == "one"
    assert :ok = Check.check_sig([data, defn])
  end

  test "parse errors name line:col" do
    assert {:error, "1:18: tuple needs {"} = Parser.parse("repr Box := tuple\n")

    assert {:error, "1:12: unexpected end of file, expected a shape"} =
             Parser.parse("repr Box :=\n")

    assert {:error, "1:19: expected a string or atom key"} =
             Parser.parse("repr Box := map { 1 => integer }\n")

    assert {:error, "1:17: list needs a shape"} = Parser.parse("repr Box := list\n")
  end

  test "duplicate repr names both lines" do
    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           repr Bool := boolean
           repr Bool := boolean
           """) == "4:1: repr Bool: duplicate repr\n5:1: repr Bool: duplicate repr"
  end

  test "repr of an unknown type" do
    assert error("repr Missing := nil\n") == "1:1: repr Missing: unknown type Missing"
  end

  test "repr of a parameterised type" do
    assert error("""
           data Maybe (A : Type) : Type where
             nothing : Maybe A
             just : A → Maybe A
           repr Maybe := nil
           """) == "4:1: repr Maybe: Maybe has parameters"
  end

  test "repr of an indexed type" do
    assert error("""
           data Fin : Nat → Type where
             fzero : Π (n : Nat) → Fin suc(n)
             fsuc : Π (n : Nat) → Fin n → Fin suc(n)
           repr Fin := nil
           """) == "4:1: repr Fin: Fin has indices"
  end

  test "a choice names a missing constructor" do
    assert error("""
           data Shape : Type where
             circle : Nat → Shape
             square : Nat → Shape
             empty : Shape
           repr Shape := circle => map { "kind" => "circle", "r" => integer }
                       | empty => nil
           """) == "5:1: repr Shape: missing constructor square"
  end

  test "a choice names an unknown constructor" do
    assert error("""
           data Shape : Type where
             circle : Nat → Shape
             empty : Shape
           repr Shape := circle => integer
                       | empty => nil
                       | other => nil
           """) == "4:1: repr Shape: unknown constructor other"
  end

  test "a choice names a repeated constructor" do
    assert error("""
           data Shape : Type where
             circle : Nat → Shape
             empty : Shape
           repr Shape := circle => integer
                       | circle => integer
                       | empty => nil
           """) == "4:1: repr Shape: repeated constructor circle"
  end

  test "wrong field count names the constructor and both counts" do
    assert error("""
           data Box : Type where
             box : Nat → Nat → Box
           repr Box := tuple { integer }
           """) == "3:1: repr Box: constructor box has 2 fields but the shape binds 1"

    assert error("""
           data Box : Type where
             box : Nat → Box
           repr Box := tuple { integer, integer }
           """) == "3:1: repr Box: constructor box has 1 field but the shape binds 2"
  end

  test "a field type outside the vocabulary is refused" do
    assert error("""
           data Box : Type where
             box : Atom → Box
           repr Box := tuple { integer }
           """) ==
             "3:1: repr Box: constructor box field 0 has type Atom; free-form strings and interned names are not supported; model the closed set as a type and give it a repr"

    assert error("""
           data Box : Type where
             box : Unit → Box
           repr Box := integer
           """) ==
             "3:1: repr Box: constructor box field 0 has type Unit, which this version does not support"

    assert error("""
           data Box : Type where
             box : (Nat × Nat) → Box
           repr Box := integer
           """) ==
             "3:1: repr Box: constructor box field 0 has type (Nat × Nat), which this version does not support"

    assert error("""
           data Box : Type where
             box : I64 → Box
           repr Box := integer
           """) ==
             "3:1: repr Box: constructor box field 0 has type I64, which this version does not support"

    assert error("""
           data Box : Type where
             box : (Nat → Nat) → Box
           repr Box := integer
           """) ==
             "3:1: repr Box: constructor box field 0 has type (Nat → Nat), which this version does not support"
  end

  test "a reference to a type with no repr" do
    assert error("""
           data Box : Type where
             box : Bool → Box
           data Bool : Type where
             true : Bool
             false : Bool
           repr Box := Bool
           """) == "6:1: repr Box: Bool has no repr"
  end

  test "boolean is only the constructors true and false" do
    assert error("""
           data OnOff : Type where
             on : OnOff
             off : OnOff
           repr OnOff := boolean
           """) ==
             "4:1: repr OnOff: boolean is only for a type with nullary constructors true and false; write a choice such as on => :true | off => :false"
  end

  test "optional outside a map" do
    assert error("""
           data Box : Type where
             box : Maybe Bool → Box
           data Maybe (A : Type) : Type where
             nothing : Maybe A
             just : A → Maybe A
           data Bool : Type where
             true : Bool
             false : Bool
           repr Bool := boolean
           repr Box := optional Bool
           """) == "10:1: repr Box: optional is only a map entry; use nullable"
  end

  test "integer on a non-Nat field" do
    assert error("""
           data Box : Type where
             box : Bool → Box
           data Bool : Type where
             true : Bool
             false : Bool
           repr Bool := boolean
           repr Box := integer
           """) ==
             "7:1: repr Box: constructor box field 0 has type Bool, which does not suit integer"
  end

  test "Nat is represented by integer" do
    assert error("repr Nat := nil\n") == "1:1: repr Nat: Nat is represented by integer"
  end

  test "a shape word cannot name a type" do
    assert error("""
           data Box : Type where
             box : Nat → Box
           data open : Type where
             o : open
           repr open := nil
           repr Box := open
           """) == "6:1: repr Box: open is a shape word and cannot name a type"
  end

  test "an inline nested map is refused" do
    assert error("""
           data Box : Type where
             box : Nat → Box
           repr Box := map { "n" => map { "x" => integer } }
           """) ==
             "3:1: repr Box: constructor box field 0 nests a map; name a type with its own repr"
  end

  test "a repr that does not consume a host value is refused" do
    msg =
      "decoding would not terminate; the repr must match nil, a boolean, an integer, a literal, a list, a tuple, or a map before it refers to itself"

    assert error("""
           data Loop : Type where
             loop : Loop → Loop
           repr Loop := Loop
           """) == "3:1: repr Loop: #{msg}"

    assert error("""
           data A : Type where
             a : B → A
           data B : Type where
             b : A → B
           repr A := B
           repr B := A
           """) == "5:1: repr A: #{msg}\n\n6:1: repr B: #{msg}"
  end

  test "nullable of a shape that accepts nil names both constructors" do
    assert error("""
           data None : Type where
             none : None
           repr None := nil
           data Maybe (A : Type) : Type where
             nothing : Maybe A
             just : A → Maybe A
           data Box : Type where
             box : Maybe None → Box
           repr Box := nullable None
           """) == "9:1: repr Box: constructors nothing and none share a host shape (nil)"
  end

  test "two constructors both nil" do
    assert error("""
           data E : Type where
             a : E
             b : E
           repr E := a => nil | b => nil
           """) == "4:1: repr E: constructors a and b share a host shape (nil)"
  end

  test "two constructors both integer" do
    assert error("""
           data E : Type where
             left : Nat → E
             right : Nat → E
           repr E := left => integer | right => integer
           """) == "4:1: repr E: constructors left and right share a host shape (integer)"
  end

  test "two maps with the same keys and no distinct tag" do
    assert error("""
           data E : Type where
             left : Nat → E
             right : Nat → E
           repr E := left => map { "n" => integer } | right => map { "n" => integer }
           """) == "4:1: repr E: constructors left and right share a host shape (map)"
  end

  test "a distinct kind tag is accepted, and so are tuples of different arity" do
    ok!("""
    data Shape : Type where
      circle : Nat → Shape
      square : Nat → Shape
      empty : Shape
    repr Shape := circle => map { "kind" => "circle", "r" => integer }
                | square => map { "kind" => "square", "side" => integer }
                | empty => nil
    """)

    ok!("""
    data T : Type where
      one : Nat → T
      two : Nat → Nat → T
    repr T := one => tuple { integer } | two => tuple { integer, integer }
    """)
  end

  test "overlapping through a type reference names both constructors" do
    assert error("""
           data Tag : Type where
             yes : Tag
             no : Tag
           data E : Type where
             one : Tag → E
             two : E
           repr Tag := yes => :yes | no => :no
           repr E := one => Tag | two => :yes
           """) == "8:1: repr E: constructors one and two share a host shape (:yes)"
  end

  test "two open maps overlap even when their tags differ" do
    assert error("""
           data Shape : Type where
             circle : Nat → Shape
             square : Nat → Shape
           repr Shape := circle => map open { "kind" => "circle", "r" => integer }
                       | square => map open { "kind" => "square", "side" => integer }
           """) ==
             "4:1: repr Shape: constructors circle and square share a host shape (map with \"kind\" => \"circle\")"
  end

  test "decode and encode names that collide are refused" do
    assert error("""
           data Entry : Type where
             entry : Nat → Entry
           repr Entry := map { "id" => integer }
           def decode_entry : run Nat := 0
           """) == "3:1: repr Entry: decode_entry collides with run decode_entry"

    assert error("""
           data HttpRequest : Type where
             httpRequest : Nat → HttpRequest
           data Http_request : Type where
             http_request : Nat → Http_request
           repr HttpRequest := integer
           repr Http_request := integer
           """) ==
             "5:1: repr HttpRequest: decode_http_request collides with repr Http_request\n\n6:1: repr Http_request: decode_http_request collides with repr HttpRequest"

    assert error("""
           data NatBox : Type where
             natBox : Nat → NatBox
           def muro_repr_decode_nat : run Nat := 0
           repr Nat := integer
           """) ==
             "4:1: repr Nat: muro_repr_decode_nat collides with run muro_repr_decode_nat"
  end

  test "a book with no repr emits no codec" do
    assert {:ok, source} = Muro.emit_file("examples/maybe.muro", MaybeEmit)
    refute source =~ "decode_"
    refute source =~ "encode_"
    refute source =~ "muro_repr_"
  end

  test "decode and encode are emitted next to the run functions" do
    assert {:ok, source} = Muro.emit_file("examples/repr.muro", Repr)
    assert source =~ "def toggle("
    assert source =~ "def describe("
    assert source =~ "def decode_entry("
    assert source =~ "def encode_entry("
    assert source =~ "def decode_outcome("
    assert source =~ "def encode_outcome("
    assert source =~ "def decode_shape("
    assert source =~ "@muro_repr_nat_max 1_000_000"

    out = capture_io(fn -> Mix.Tasks.Muro.Emit.run(["examples/repr.muro"]) end)
    assert String.trim_trailing(out) == String.trim_trailing(source)
  end

  test "a host calls decode, the proved function, then encode" do
    mod = example()
    assert {:ok, v} = mod.decode_entry(%{"id" => 3, "enabled" => true})
    assert mod.encode_entry(mod.toggle(v)) == %{"id" => 3, "enabled" => false}
    assert mod.encode_outcome(mod.describe(v)) == %{"status" => "on", "id" => 3}

    assert {:ok, missing} = mod.decode_entry(%{"id" => 3})
    assert mod.encode_outcome(mod.describe(missing)) == nil
  end

  test "decode errors name the path and the value" do
    mod = example()

    assert mod.decode_bool(1) == {:error, {[], {:not_boolean, 1}}}
    assert mod.decode_bool(nil) == {:error, {[], {:not_boolean, nil}}}

    assert mod.decode_entry(%{"id" => 3, "enabled" => 1}) ==
             {:error, {["enabled"], {:not_boolean, 1}}}

    assert mod.decode_entry(%{"id" => 1.0}) == {:error, {["id"], {:not_integer, 1.0}}}
    assert mod.decode_entry(%{"id" => "1"}) == {:error, {["id"], {:not_integer, "1"}}}
    assert mod.decode_entry(%{"id" => nil}) == {:error, {["id"], {:not_integer, nil}}}
    assert mod.decode_entry(%{"id" => -1}) == {:error, {["id"], {:negative_integer, -1}}}

    assert_nat_rejected(
      mod,
      %{"id" => 1_000_001},
      ["id"],
      {:nat_too_large, 1_000_001},
      :decode_entry
    )

    assert mod.decode_entry(:no) == {:error, {[], {:not_map, :no}}}
    assert mod.decode_entry(%{"enabled" => true}) == {:error, {[], {:missing_key, "id"}}}

    assert mod.decode_entry(%{"id" => 1, "enabled" => true, "extra" => 1}) ==
             {:error, {[], {:unexpected_key, "extra"}}}

    assert mod.decode_entry(%{"id" => 1, "enabled" => nil}) ==
             {:error, {["enabled"], {:nil_not_allowed, nil}}}

    assert mod.decode_shape(%{"kind" => "triangle"}) ==
             {:error, {[], {:no_variant, [:circle, :square, :empty], %{"kind" => "triangle"}}}}

    assert mod.decode_shape(%{"kind" => "circle", "r" => 1.0}) ==
             {:error, {["r"], {:not_integer, 1.0}}}

    assert mod.decode_shape(%{"kind" => "circle"}) == {:error, {[], {:missing_key, "r"}}}
    assert {:ok, :empty} = mod.decode_shape(nil)
  end

  test "list, tuple, tag, open, and nullable errors" do
    mod = codec()

    assert mod.decode_bag([1 | :x]) == {:error, {[], {:not_list, [1 | :x]}}}
    assert mod.decode_bag(:no) == {:error, {[], {:not_list, :no}}}
    assert mod.decode_bag([1, "a"]) == {:error, {[1], {:not_integer, "a"}}}

    assert mod.decode_pair(:no) == {:error, {[], {:not_tuple, :no}}}
    assert mod.decode_pair({3}) == {:error, {[], {:wrong_tuple_size, 2, {3}}}}
    assert mod.decode_pair({0, 1}) == {:error, {[1], {:not_boolean, 1}}}

    assert mod.decode_flag(1) == {:error, {[], {:expected, :yes, 1}}}
    assert mod.decode_marked({:no, 1}) == {:error, {[0], {:expected, :ok, :no}}}

    assert mod.decode_row(1) == {:error, {[], {:not_map, 1}}}
    assert mod.decode_row(%{}) == {:error, {[], {:missing_key, "id"}}}

    assert mod.decode_row(%{"id" => 1, "note" => nil, "b" => 1, "a" => 2}) ==
             {:error, {[], {:unexpected_key, "a"}}}

    assert mod.decode_row(%{"id" => 1, "flag" => nil, "note" => nil}) ==
             {:error, {["flag"], {:nil_not_allowed, nil}}}

    assert mod.decode_nested(%{"in" => %{}}) == {:error, {["in"], {:missing_key, "n"}}}
    assert mod.decode_box(%{"xs" => [0, "a"]}) == {:error, {["xs", 1], {:not_integer, "a"}}}

    assert {:ok, _} = mod.decode_open(%{"id" => 1, "z" => 9})
    assert mod.decode_tree({1.0, nil, nil}) == {:error, {[0], {:not_integer, 1.0}}}
    assert mod.decode_tree({1, nil}) == {:error, {[], {:no_variant, [:leaf, :node], {1, nil}}}}
  end

  test "round trip over the vocabulary" do
    mod = codec()
    :rand.seed(:exsss, {1, 2, 3})

    for _ <- 1..200 do
      host = Enum.random([true, false])
      assert mod.encode_bool(host) == host
      assert mod.decode_bool(host) == {:ok, host}
      assert mod.decode_bool(mod.encode_bool(host)) == {:ok, host}

      n = :rand.uniform(21) - 1
      assert mod.decode_nat(n) |> elem(1) |> then(&mod.encode_nat/1) == n
      {:ok, nat} = mod.decode_nat(n)
      assert mod.decode_nat(mod.encode_nat(nat)) == {:ok, nat}

      assert mod.decode_tree(nil) == {:ok, :leaf}
      assert mod.encode_tree(:leaf) == nil

      tag = Enum.random([:yes, :no])
      host = if tag == :yes, do: :yes, else: "no"
      assert mod.decode_tags(host) == {:ok, tag}
      assert mod.encode_tags(tag) == host

      {list_host, list_muro} = gen_list()
      assert mod.decode_bag(list_host) == {:ok, list_muro}
      assert mod.encode_bag(list_muro) == list_host

      {tuple_host, tuple_muro} = gen_pair()
      assert mod.decode_pair(tuple_host) == {:ok, tuple_muro}
      assert mod.encode_pair(tuple_muro) == tuple_host

      {row_host, row_muro} = gen_row()
      assert mod.decode_row(row_host) == {:ok, row_muro}
      assert mod.encode_row(row_muro) == row_host
      assert mod.decode_row(mod.encode_row(row_muro)) == {:ok, row_muro}

      id = :rand.uniform(6) - 1
      assert mod.decode_open(%{"id" => id}) == {:ok, {:open, peano(id)}}
      assert mod.encode_open({:open, peano(id)}) == %{"id" => id}

      {tree_host, tree_muro} = gen_tree(3)
      assert mod.decode_tree(tree_host) == {:ok, tree_muro}
      assert mod.encode_tree(tree_muro) == tree_host
      assert mod.decode_tree(mod.encode_tree(tree_muro)) == {:ok, tree_muro}

      {shape_host, shape_muro} = gen_shape()
      assert mod.decode_shape(shape_host) == {:ok, shape_muro}
      assert mod.encode_shape(shape_muro) == shape_host
    end
  end

  test "open drops unknown keys, and optional nullable normalises nil" do
    mod = codec()
    {:ok, v} = mod.decode_open(%{"id" => 4, "z" => 9})
    assert mod.encode_open(v) == %{"id" => 4}
    assert mod.decode_open(mod.encode_open(v)) == {:ok, v}

    {:ok, missing} = mod.decode_soft(%{})
    {:ok, present_nil} = mod.decode_soft(%{"flag" => nil})
    assert missing == present_nil
    assert mod.encode_soft(missing) == %{}
    assert mod.encode_soft(present_nil) == %{}
    {:ok, on} = mod.decode_soft(%{"flag" => true})
    assert mod.encode_soft(on) == %{"flag" => true}
    assert mod.decode_soft(mod.encode_soft(on)) == {:ok, on}
  end

  test "a list of 100000 elements decodes" do
    mod = codec()
    host = List.duplicate(0, 100_000)

    case mod.decode_bag(host) do
      {:ok, v} ->
        if mod.encode_bag(v) != host, do: flunk("encode did not return the 100000 host zeros")

      other ->
        flunk("decode of 100000 zeros failed: #{inspect(other, limit: 5)}")
    end
  end

  # Never build a Peano term above 10_000. A failed assertion inspects its
  # value, and a million-deep `{:suc, _}` chain exhausts the machine.
  # `decode_nat(1_000_001)` is only the integer. The boundary (the largest
  # accepted integer, and one past it) uses a copy whose guard is 10_000.
  test "Nat decode and encode stay within the guard" do
    mod = codec()

    for n <- [0, 1, 1000] do
      assert_nat_integer(mod, n)
    end

    assert_nat_rejected(mod, 1_000_001, [], {:nat_too_large, 1_000_001}, :decode_nat)
    assert mod.decode_nat(-1) == {:error, {[], {:negative_integer, -1}}}
    assert mod.decode_nat(1.0) == {:error, {[], {:not_integer, 1.0}}}
    assert mod.decode_nat("1") == {:error, {[], {:not_integer, "1"}}}
    assert mod.decode_nat(nil) == {:error, {[], {:not_integer, nil}}}

    limited = nat_limit_codec(10_000)
    assert_nat_integer(limited, 0)
    assert_nat_integer(limited, 10_000)
    assert_nat_rejected(limited, 10_001, [], {:nat_too_large, 10_001}, :decode_nat)
    assert_nat_rejected(limited, 1_000_001, [], {:nat_too_large, 1_000_001}, :decode_nat)
  end

  test "other backends ignore a repr" do
    base = File.read!("examples/half_ok.muro")

    data = """
    data Bool : Type where
      true : Bool
      false : Bool
    """

    {:ok, without} = Parser.parse(base <> data)
    {:ok, with_repr} = Parser.parse(base <> data <> "repr Bool := boolean\n")

    assert Emit.C.prepare(with_repr, "half_ok") == Emit.C.prepare(without, "half_ok")
    assert Emit.Rust.render(with_repr, "half_ok") == Emit.Rust.render(without, "half_ok")
    assert Emit.Asm.render(with_repr, "half_ok") == Emit.Asm.render(without, "half_ok")
    assert Emit.Otp.render(with_repr, "half_ok") == Emit.Otp.render(without, "half_ok")
    assert Emit.Node.render(with_repr, "half_ok", :a) == Emit.Node.render(without, "half_ok", :a)
  end

  test "decode of the example never raises" do
    mod = example()

    for term <- odd_terms() do
      for fun <- [:decode_bool, :decode_entry, :decode_shape, :decode_outcome] do
        result = apply(mod, fun, [term])

        assert match?({:ok, _}, result) or
                 match?({:error, {path, _}} when is_list(path), result)
      end
    end
  end

  defp example do
    compile_file("examples/repr.muro", HostReprEx)
  end

  defp codec do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A

    data Bag : Type where
      bag : List Nat → Bag

    data Pair : Type where
      pair : Nat → Bool → Pair

    data Row : Type where
      row : Nat → Maybe Bool → Maybe Nat → Row

    data Open : Type where
      open : Nat → Open

    data Tree : Type where
      leaf : Tree
      node : Nat → Tree → Tree → Tree

    data Shape : Type where
      circle : Nat → Shape
      square : Nat → Shape
      empty : Shape

    data Flag : Type where
      flag : Flag

    data Tags : Type where
      yes : Tags
      no : Tags

    data Marked : Type where
      marked : Nat → Marked

    data Inner : Type where
      inner : Nat → Inner

    data Nested : Type where
      nested : Inner → Nested

    data Box : Type where
      box : List Nat → Box

    data Soft : Type where
      soft : Maybe Bool → Soft

    repr Bool := boolean
    repr Bag := list integer
    repr Pair := tuple { integer, boolean }
    repr Row := map { "id" => integer, "flag" => optional Bool, "note" => nullable integer }
    repr Open := map open { "id" => integer }
    repr Tree := leaf => nil | node => tuple { integer, Tree, Tree }
    repr Shape := circle => map { "kind" => "circle", "r" => integer }
                | square => map { "kind" => "square", "side" => integer }
                | empty => nil
    repr Flag := :yes
    repr Tags := yes => :yes | no => "no"
    repr Marked := tuple { :ok, integer }
    repr Inner := map { "n" => integer }
    repr Nested := map { "in" => Inner }
    repr Box := map { "xs" => list integer }
    repr Soft := map { "flag" => optional nullable Bool }
    repr Nat := integer
    """

    book = ok!(src)
    compile_book(book, ReprCodec)
  end

  defp compile_file(path, mod) do
    assert {:ok, source} = Muro.emit_file(path, mod)
    compile_source(source, mod)
  end

  defp compile_book(book, mod) do
    compile_source(Emit.emit_module(mod, book), mod)
  end

  defp compile_source(source, mod) do
    Code.compiler_options(ignore_module_conflict: true)
    [{^mod, _bin}] = Code.compile_string(source)

    on_exit(fn ->
      :code.purge(mod)
      :code.delete(mod)
    end)

    mod
  end

  # A `def` has no `:kind`. Data, repr, and the session entries do.
  defp entry_tag(%{kind: kind}), do: kind
  defp entry_tag(%{mode: :run}), do: :def
  defp entry_tag(%{mode: mode}), do: mode

  defp error(src) do
    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    msg
  end

  defp ok!(src) do
    assert {:ok, book} = Parser.parse(src)
    assert :ok = Check.check_sig(book)
    book
  end

  defp odd_terms do
    [
      :atom,
      true,
      false,
      nil,
      0,
      1,
      -1,
      1.0,
      1_000_001,
      "",
      "x",
      self(),
      make_ref(),
      fn -> :ok end,
      [1 | 2],
      [],
      %{a: 1},
      %{},
      {},
      {1},
      {1, 2, 3},
      [:a, %{b: nil}, 1.5],
      <<1, 2>>
    ]
  end

  defp peano(n), do: peano(n, 0)
  defp peano(0, acc), do: acc
  defp peano(n, acc) when n > 0, do: peano(n - 1, {:suc, acc})

  # Compare the integer encode returns. Do not assert on the Peano term.
  defp assert_nat_integer(mod, n) when is_integer(n) and n >= 0 and n <= 10_000 do
    case mod.decode_nat(n) do
      {:ok, v} ->
        assert mod.encode_nat(v) == n

      other ->
        flunk("decode_nat(#{n}) failed: #{inspect(other, limit: 5)}")
    end
  end

  # A success is discarded. Inspecting `{:ok, nat}` is what exhausts memory.
  defp assert_nat_rejected(mod, value, path, reason, fun) do
    case apply(mod, fun, [value]) do
      {:ok, _} ->
        flunk("#{fun} built a Nat from #{inspect(value, limit: 5)}")

      {:error, {^path, ^reason}} ->
        :ok

      other ->
        flunk("#{fun} returned #{inspect(other, limit: 8)}")
    end
  end

  defp nat_limit_codec(max) when is_integer(max) and max > 0 and max <= 10_000 do
    book =
      ok!("""
      repr Nat := integer
      """)

    source = Emit.emit_module(ReprNatLimit, book)
    needle = "@muro_repr_nat_max 1_000_000"
    assert source =~ needle

    source =
      String.replace(source, needle, "@muro_repr_nat_max #{Integer.to_string(max)}",
        global: false
      )

    compile_source(source, ReprNatLimit)
  end

  defp gen_list do
    n = :rand.uniform(8) - 1
    xs = if n == 0, do: [], else: Enum.map(1..n, fn _ -> :rand.uniform(6) - 1 end)
    muro = Enum.reduce(Enum.reverse(xs), nil, fn k, acc -> {:cons, peano(k), acc} end)
    {xs, {:bag, muro}}
  end

  defp gen_pair do
    n = :rand.uniform(6) - 1
    bit = Enum.random([true, false])
    {{n, bit}, {:pair, peano(n), bit}}
  end

  defp gen_row do
    id = :rand.uniform(6) - 1
    flag = Enum.random([:omit, true, false])
    note = Enum.random([nil, 0, 1, 2])

    host = %{"id" => id, "note" => note}
    host = if flag == :omit, do: host, else: Map.put(host, "flag", flag)

    flag_m =
      case flag do
        :omit -> :nothing
        true -> {:just, true}
        false -> {:just, false}
      end

    note_m = if note == nil, do: :nothing, else: {:just, peano(note)}
    {host, {:row, peano(id), flag_m, note_m}}
  end

  defp gen_tree(0), do: {nil, :leaf}

  defp gen_tree(d) do
    if :rand.uniform(3) == 1 do
      {nil, :leaf}
    else
      n = :rand.uniform(4) - 1
      {h1, t1} = gen_tree(d - 1)
      {h2, t2} = gen_tree(d - 1)
      {{n, h1, h2}, {:node, peano(n), t1, t2}}
    end
  end

  defp gen_shape do
    case :rand.uniform(3) do
      1 ->
        n = :rand.uniform(5) - 1
        {%{"kind" => "circle", "r" => n}, {:circle, peano(n)}}

      2 ->
        n = :rand.uniform(5) - 1
        {%{"kind" => "square", "side" => n}, {:square, peano(n)}}

      3 ->
        {nil, :empty}
    end
  end
end
