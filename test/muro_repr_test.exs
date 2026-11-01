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

    assert {:error, "1:21: interned needs string"} = Parser.parse("repr Box := interned\n")
    assert {:error, "1:22: interned needs string"} = Parser.parse("repr Box := interned name\n")
    assert {:error, "1:19: map_of needs a shape"} = Parser.parse("repr Box := map_of\n")

    assert {:error, "1:25: unexpected end of file, expected a fallback"} =
             Parser.parse("repr Box := boolean else\n")

    assert {:error, "1:21: unexpected end of file, expected )"} =
             Parser.parse("repr Box := (boolean\n")
  end

  test "the new shapes parse, and parentheses add no node" do
    assert {:ok, [repr]} =
             Parser.parse("""
             repr Demo := wild => "*" | named => interned string | nums => map_of integer => list boolean | flag => optional (boolean else false) | bare => (integer) | whole => list boolean else false | n => integer else 0
             """)

    assert repr.body ==
             {:choice,
              [
                {"wild", {:string, "*"}},
                {"named", {:interned}},
                {"nums", {:map_of, {:integer}, {:list, {:boolean}}}},
                {"flag", {:optional, {:else, {:boolean}, {:ctor, "false"}}}},
                {"bare", {:integer}},
                {"whole", {:else, {:list, {:boolean}}, {:ctor, "false"}}},
                {"n", {:else, {:integer}, {:numeral, 0}}}
              ]}

    assert {:ok, [plain]} = Parser.parse("repr Demo := boolean\n")
    assert {:ok, [paren]} = Parser.parse("repr Demo := (boolean)\n")
    assert plain.body == paren.body
  end

  test "interned, map_of, and else stay names outside a repr" do
    assert {:ok, [defn]} = Parser.parse("def else : run Nat := 0\n")
    assert defn.name == "else"
    assert :ok = Check.check_sig([defn])

    src = """
    data map_of : Type where
      empty : map_of
    data Box : Type where
      interned : Box
    def else : run Nat := 0
    """

    assert {:ok, [map_of, box, else_def]} = Parser.parse(src)
    assert map_of.name == "map_of"
    assert hd(map_of.ctors).name == "empty"
    assert hd(box.ctors).name == "interned"
    assert else_def.name == "else"
    assert :ok = Check.check_sig([map_of, box, else_def])
  end

  test "else is a shape word inside a repr" do
    assert error("""
           data Box : Type where
             box : Nat → Box
           data else : Type where
             c : else
           repr else := nil
           repr Box := else
           """) == "6:1: repr Box: else is a shape word and cannot name a type"
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
             "3:1: repr Box: constructor box field 0 has type Atom; model the closed set as a type and give it a repr, or intern a name as Nat or a binary numeral"

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

  test "decode and encode names that collide are refused, and a reserved helper is claimed" do
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

    # A run whose source name is a repr helper is claimed to `_2`.
    # The helper keeps its name, and the module compiles.
    nat_book =
      ok!("""
      data NatBox : Type where
        natBox : Nat → NatBox
      def muro_repr_decode_nat : run Nat := 0
      repr Nat := integer
      """)

    assert Emit.elixir_names(nat_book)["muro_repr_decode_nat"] == "muro_repr_decode_nat_2"
    nat_src = Emit.emit_module(NatReserve, nat_book)
    assert nat_src =~ "def muro_repr_decode_nat_2 do"
    assert nat_src =~ "defp muro_repr_decode_nat("
    compile_source(nat_src, NatReserve)
    assert apply(NatReserve, :muro_repr_decode_nat_2, []) == 0

    bool_book =
      ok!("""
      data Bool : Type where
        true : Bool
        false : Bool
      def muro_repr_table_new : run Nat := 0
      repr Bool := boolean
      """)

    assert Emit.elixir_names(bool_book)["muro_repr_table_new"] == "muro_repr_table_new_2"
    bool_src = Emit.emit_module(BoolReserve, bool_book)
    assert bool_src =~ "def muro_repr_table_new_2 do"
    assert bool_src =~ "def muro_repr_table_new, do:"
    compile_source(bool_src, BoolReserve)
    assert apply(BoolReserve, :muro_repr_table_new_2, []) == 0
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

    # Mix.Shell.IO.info prints "==> muro" the first time the shell is used
    # after another project has taken it. Dep compilation does that, and
    # which test runs first decides whether this capture sees the line.
    out =
      fn -> Mix.Tasks.Muro.Emit.run(["examples/repr.muro"]) end
      |> capture_io()
      |> String.replace(~r/^==> \S+\n/m, "")

    assert String.trim_trailing(out) == String.trim_trailing(source)
  end

  test "a host calls decode, the proved function, then encode" do
    mod = example()
    assert {:ok, v, table} = mod.decode_entry(%{"id" => 3, "enabled" => true})
    assert table == mod.muro_repr_table_new()
    assert mod.encode_entry(mod.toggle(v), table) == %{"id" => 3, "enabled" => false}
    assert mod.encode_outcome(mod.describe(v), table) == %{"status" => "on", "id" => 3}

    assert {:ok, missing, table} = mod.decode_entry(%{"id" => 3})
    assert mod.encode_outcome(mod.describe(missing), table) == nil
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
    assert {:ok, :empty, _table} = mod.decode_shape(nil)
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

    assert {:ok, _, _} = mod.decode_open(%{"id" => 1, "z" => 9})
    assert mod.decode_tree({1.0, nil, nil}) == {:error, {[0], {:not_integer, 1.0}}}
    assert mod.decode_tree({1, nil}) == {:error, {[], {:no_variant, [:leaf, :node], {1, nil}}}}
  end

  test "round trip over the vocabulary" do
    mod = codec()
    :rand.seed(:exsss, {1, 2, 3})
    table = mod.muro_repr_table_new()

    for _ <- 1..200 do
      host = Enum.random([true, false])
      assert mod.encode_bool(host, table) == host
      assert mod.decode_bool(host) == {:ok, host, table}
      assert mod.decode_bool(mod.encode_bool(host, table)) == {:ok, host, table}

      n = :rand.uniform(21) - 1
      {:ok, nat, table} = mod.decode_nat(n)
      assert mod.encode_nat(nat, table) == n
      assert mod.decode_nat(mod.encode_nat(nat, table)) == {:ok, nat, table}

      assert mod.decode_tree(nil) == {:ok, :leaf, table}
      assert mod.encode_tree(:leaf, table) == nil

      tag = Enum.random([:yes, :no])
      host = if tag == :yes, do: :yes, else: "no"
      assert mod.decode_tags(host) == {:ok, tag, table}
      assert mod.encode_tags(tag, table) == host

      {list_host, list_muro} = gen_list()
      assert mod.decode_bag(list_host) == {:ok, list_muro, table}
      assert mod.encode_bag(list_muro, table) == list_host

      {tuple_host, tuple_muro} = gen_pair()
      assert mod.decode_pair(tuple_host) == {:ok, tuple_muro, table}
      assert mod.encode_pair(tuple_muro, table) == tuple_host

      {row_host, row_muro} = gen_row()
      assert mod.decode_row(row_host) == {:ok, row_muro, table}
      assert mod.encode_row(row_muro, table) == row_host
      assert mod.decode_row(mod.encode_row(row_muro, table)) == {:ok, row_muro, table}

      id = :rand.uniform(6) - 1
      assert mod.decode_open(%{"id" => id}) == {:ok, {:open, peano(id)}, table}
      assert mod.encode_open({:open, peano(id)}, table) == %{"id" => id}

      {tree_host, tree_muro} = gen_tree(3)
      assert mod.decode_tree(tree_host) == {:ok, tree_muro, table}
      assert mod.encode_tree(tree_muro, table) == tree_host
      assert mod.decode_tree(mod.encode_tree(tree_muro, table)) == {:ok, tree_muro, table}

      {shape_host, shape_muro} = gen_shape()
      assert mod.decode_shape(shape_host) == {:ok, shape_muro, table}
      assert mod.encode_shape(shape_muro, table) == shape_host
    end
  end

  test "open drops unknown keys, and optional nullable normalises nil" do
    mod = codec()
    table = mod.muro_repr_table_new()
    {:ok, v, ^table} = mod.decode_open(%{"id" => 4, "z" => 9})
    assert mod.encode_open(v, table) == %{"id" => 4}
    assert mod.decode_open(mod.encode_open(v, table)) == {:ok, v, table}

    {:ok, missing, ^table} = mod.decode_soft(%{})
    {:ok, present_nil, ^table} = mod.decode_soft(%{"flag" => nil})
    assert missing == present_nil
    assert mod.encode_soft(missing, table) == %{}
    assert mod.encode_soft(present_nil, table) == %{}
    {:ok, on, ^table} = mod.decode_soft(%{"flag" => true})
    assert mod.encode_soft(on, table) == %{"flag" => true}
    assert mod.decode_soft(mod.encode_soft(on, table)) == {:ok, on, table}
  end

  test "an open map refuses a key that names a declared key in the other form" do
    {mod, source} = ambig_mod(ReprAmbig)
    refute source =~ "String.to_atom"
    assert source =~ "muro_repr_ambiguous"
    assert source =~ "muro_repr_no_extra"
    assert source =~ "defp muro_repr_else({:error, {path, reason}} = err, at, incoming, fallback)"
    assert source =~ "{:ambiguous_key, _} ->"
    refute source =~ "defp muro_repr_else({:error, {_path, {:ambiguous_key, _}}}"

    assert source =~
             ~r/muro_repr_ambiguous\(value, path, \[\s*"read",\s*"write",\s*"admin"\s*\]\)/

    assert source =~ ~r/muro_repr_ambiguous\(value, path, \[\s*:write,\s*:read\s*\]\)/

    assert mod.decode_grant(%{"relation" => "x", :read => false}) ==
             {:error, {[], {:ambiguous_key, :read}}}

    assert {:ok, {:grant, :nothing}, table} =
             mod.decode_grant(%{"relation" => "x", :source => :preset})

    assert mod.encode_grant({:grant, :nothing}, table) == %{}

    assert {:ok, {:grant, :nothing}, table} =
             mod.decode_grant(%{"relation" => "x", "token_id" => 7})

    assert mod.encode_grant({:grant, :nothing}, table) == %{}

    assert mod.decode_grant(%{"relation" => "x", "read" => false, :read => true}) ==
             {:error, {[], {:ambiguous_key, :read}}}

    assert mod.decode_grant(%{"read" => 1, :read => false}) ==
             {:error, {[], {:ambiguous_key, :read}}}

    assert {:ok, {:grant, {:just, false}}, table} =
             mod.decode_grant(%{"read" => false, "token_id" => 7, :source => :preset, 1 => 2})

    assert mod.encode_grant({:grant, {:just, false}}, table) == %{"read" => false}

    assert mod.decode_atom_grant(%{"relation" => "x", "read" => false}) ==
             {:error, {[], {:ambiguous_key, "read"}}}

    assert mod.decode_atom_grant(%{:read => false, "read" => true, "relation" => "x"}) ==
             {:error, {[], {:ambiguous_key, "read"}}}

    assert {:ok, {:atom_grant, {:just, false}}, table} =
             mod.decode_atom_grant(%{:read => false, "token_id" => 7, :source => :preset})

    assert mod.encode_atom_grant({:atom_grant, {:just, false}}, table) == %{:read => false}

    assert {:ok, {:both, true, false}, table} =
             mod.decode_both(%{"read" => true, :read => false, "token_id" => 7})

    assert mod.encode_both({:both, true, false}, table) == %{"read" => true, :read => false}

    assert {:ok, {:tag, true}, _} =
             mod.decode_tag(%{
               "kind" => "circle",
               "ok" => true,
               "token_id" => 7,
               :source => :preset
             })

    assert mod.decode_tag(%{"kind" => "circle", "ok" => true, :kind => "circle"}) ==
             {:error, {[], {:ambiguous_key, :kind}}}

    assert mod.decode_tag(%{:kind => "circle"}) == {:error, {[], {:ambiguous_key, :kind}}}

    assert mod.decode_tag(%{"kind" => "square", "ok" => true, :source => :preset}) ==
             {:error, {["kind"], {:expected, "circle", "square"}}}

    assert {:ok, {:atom_tag, true}, _} =
             mod.decode_atom_tag(%{:kind => :yes, :ok => true, "token_id" => 7})

    assert mod.decode_atom_tag(%{:kind => :yes, :ok => true, "kind" => "x"}) ==
             {:error, {[], {:ambiguous_key, "kind"}}}

    assert mod.decode_atom_tag(%{"kind" => :yes}) == {:error, {[], {:ambiguous_key, "kind"}}}

    assert mod.decode_hold({%{:read => false}}) == {:error, {[0], {:ambiguous_key, :read}}}
    assert {:ok, {:hold, :node_none}, _} = mod.decode_hold({1})

    assert mod.decode_hold({%{"read" => 1}}) ==
             {:error, {[0, "read"], {:not_boolean, 1}}}
  end

  test "several ambiguous keys report the first declared key, in any map order" do
    {mod, _source} = ambig_mod(ReprAmbigOrder)
    collisions = [{:admin, false}, {:write, false}, {:read, false}]

    results =
      Enum.map([:strings_first, :collisions_first, :rev, :middle], fn order ->
        mod.decode_many(padded(collisions, order))
      end)

    assert results == List.duplicate({:error, {[], {:ambiguous_key, :read}}}, 4)

    later = [{:admin, true}, {:write, false}]

    assert mod.decode_many(padded(later, :strings_first)) ==
             {:error, {[], {:ambiguous_key, :write}}}

    assert mod.decode_many(padded(later, :rev)) == {:error, {[], {:ambiguous_key, :write}}}

    strings = [{"read", false}, {"write", true}]

    assert mod.decode_atom_many(padded(strings, :collisions_first)) ==
             {:error, {[], {:ambiguous_key, "write"}}}

    assert mod.decode_atom_many(padded(strings, :rev)) ==
             {:error, {[], {:ambiguous_key, "write"}}}

    assert mod.decode_atom_many(padded([{"read", false}], :middle)) ==
             {:error, {[], {:ambiguous_key, "read"}}}

    assert {:ok, {:many, :nothing, {:just, false}, :nothing}, _} =
             mod.decode_many(%{"write" => false, :source => :preset, "token_id" => 7})
  end

  test "a nested open map reports the ambiguous key at the inner path" do
    {mod, _source} = ambig_mod(ReprAmbigNest)
    inner = padded([{:read, false}], :middle)

    assert mod.decode_parent(%{"child" => inner, "token_id" => 7}) ==
             {:error, {["child"], {:ambiguous_key, :read}}}

    assert mod.decode_grand(%{"parent" => %{"child" => %{"relation" => "x", :read => false}}}) ==
             {:error, {["parent", "child"], {:ambiguous_key, :read}}}

    assert mod.decode_grand(%{
             :parent => 1,
             "parent" => %{"child" => %{:read => false}}
           }) == {:error, {[], {:ambiguous_key, :parent}}}

    assert mod.decode_kids([%{"read" => false}, %{:read => true, "token_id" => 7}]) ==
             {:error, {[1], {:ambiguous_key, :read}}}

    assert mod.decode_kids([%{:read => false}, %{"read" => true}]) ==
             {:error, {[0], {:ambiguous_key, :read}}}

    assert {:ok, {:kids, {:cons, {:child, {:just, false}}, nil}}, _} =
             mod.decode_kids([%{"read" => false, :source => :preset}])
  end

  test "a closed map and map_of do not use the ambiguous-key rule" do
    {mod, _source} = ambig_mod(ReprAmbigClosed)

    assert mod.decode_closed(%{"read" => false, :read => true, "relation" => "x"}) ==
             {:error, {[], {:unexpected_key, :read}}}

    assert mod.decode_closed(%{"read" => 1, :read => false}) ==
             {:error, {["read"], {:not_boolean, 1}}}

    assert mod.decode_closed(%{"read" => true, "relation" => "x"}) ==
             {:error, {[], {:unexpected_key, "relation"}}}

    assert {:ok, {:closed, {:just, true}}, table} = mod.decode_closed(%{"read" => true})
    assert mod.encode_closed({:closed, {:just, true}}, table) == %{"read" => true}

    assert mod.decode_bag(%{0 => true, :read => false}) ==
             {:error, {[{:key, :read}], {:not_integer, :read}}}

    assert mod.decode_bag(%{0 => true, "read" => false}) ==
             {:error, {[{:key, "read"}], {:not_integer, "read"}}}

    assert mod.decode_bag(%{:read => false, "read" => true}) ==
             {:error, {[{:key, :read}], {:not_integer, :read}}}

    assert {:ok, {:bag, {:cons, {0, true}, nil}}, table} = mod.decode_bag(%{0 => true})
    assert mod.encode_bag({:bag, {:cons, {0, true}, nil}}, table) == %{0 => true}
  end

  test "the emitted decoder and the in-process module agree on the same inputs" do
    {direct, _source} = ambig_mod(ReprAmbigDirect)
    path = Path.join(System.tmp_dir!(), "muro_ambig_#{System.unique_integer([:positive])}.muro")
    File.write!(path, ambig_src())
    on_exit(fn -> File.rm(path) end)
    emitted = compile_file(path, ReprAmbigEmitted)

    inputs = [
      %{"relation" => "x", :read => false},
      %{"relation" => "x", :source => :preset},
      %{"relation" => "x", "token_id" => 7},
      %{"relation" => "x", "read" => false, :read => true},
      %{"read" => false},
      %{"read" => true, "token_id" => 7, :source => :preset},
      %{"read" => 1},
      %{"read" => 1, :read => false},
      %{},
      %{"read" => false, 1 => 2, {:a, :b} => 3},
      padded([{:read, false}], :strings_first),
      padded([{:read, false}, {:other, 1}], :rev)
    ]

    Enum.each(inputs, fn input ->
      direct_grant = direct.decode_grant(input)
      direct_choice = direct.decode_choice_grant(input)
      assert direct_grant == emitted.decode_grant(input)
      assert direct_choice == emitted.decode_choice_grant(input)

      assert direct.decode_parent(%{"child" => input}) ==
               emitted.decode_parent(%{"child" => input})

      assert same_arm(direct_grant, direct_choice)
    end)
  end

  test "only the maps that need them emit the extra-key helpers" do
    {_mod, open_source} =
      ambig_shape(
        ReprAmbigOpenOnly,
        """
        data Bool : Type where
          true : Bool
          false : Bool

        data Grant : Type where
          grant : Bool → Grant

        repr Bool := boolean
        repr Grant := map open { "read" => Bool }
        """
      )

    assert open_source =~ "muro_repr_ambiguous"
    refute open_source =~ "muro_repr_no_extra"

    {_mod, closed_source} =
      ambig_shape(
        ReprAmbigClosedOnly,
        """
        data Bool : Type where
          true : Bool
          false : Bool

        data Grant : Type where
          grant : Bool → Grant

        repr Bool := boolean
        repr Grant := map { "read" => Bool }
        """
      )

    assert closed_source =~ "muro_repr_no_extra"
    refute closed_source =~ "muro_repr_ambiguous"
    refute closed_source =~ "ambiguous_key"
  end

  test "a list of 100000 elements decodes" do
    mod = codec()
    host = List.duplicate(0, 100_000)

    case mod.decode_bag(host) do
      {:ok, v, table} ->
        if mod.encode_bag(v, table) != host,
          do: flunk("encode did not return the 100000 host zeros")

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
    assert Emit.Zig.render(with_repr, "half_ok") == Emit.Zig.render(without, "half_ok")
    assert Emit.Asm.render(with_repr, "half_ok") == Emit.Asm.render(without, "half_ok")
    assert Emit.Otp.render(with_repr, "half_ok") == Emit.Otp.render(without, "half_ok")
    assert Emit.Node.render(with_repr, "half_ok", :a) == Emit.Node.render(without, "half_ok", :a)
  end

  test "interned string is refused unless the field is Nat or a binary numeral" do
    name =
      "which does not suit interned string; a name is Nat or a binary numeral type (a nullary constructor and two constructors that each take one field of the type itself)"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Bool → Box
           repr Box := tuple { interned string }
           """) == "6:1: repr Box: constructor box field 0 has type Bool, #{name}"

    assert error("""
           data Box : Type where
             box : Atom → Box
           repr Box := tuple { interned string }
           """) == "3:1: repr Box: constructor box field 0 has type Atom, #{name}"

    assert error("""
           data Box : Type where
             box : Unit → Box
           repr Box := tuple { interned string }
           """) == "3:1: repr Box: constructor box field 0 has type Unit, #{name}"

    assert error("""
           data List (A : Type) : Type where
             nil : List A
             cons : A → List A → List A
           data Box : Type where
             box : List Nat → Box
           repr Box := tuple { interned string }
           """) == "6:1: repr Box: constructor box field 0 has type List Nat, #{name}"

    assert error("""
           data Box : Type where
             box : (Nat × Nat) → Box
           repr Box := tuple { interned string }
           """) == "3:1: repr Box: constructor box field 0 has type (Nat × Nat), #{name}"

    assert error("""
           data Maybe (A : Type) : Type where
             nothing : Maybe A
             just : A → Maybe A
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Maybe Bool → Box
           repr Box := tuple { interned string }
           """) == "9:1: repr Box: constructor box field 0 has type Maybe Bool, #{name}"

    assert error("""
           data Tri : Type where
             a : Tri
             b : Nat → Tri
             c : Tri → Tri
           data Box : Type where
             box : Tri → Box
           repr Box := tuple { interned string }
           """) == "7:1: repr Box: constructor box field 0 has type Tri, #{name}"

    assert error("repr Nat := interned string\n") ==
             "1:1: repr Nat: Nat is represented by integer"

    assert error("""
           data Bit : Type where
             z : Bit
             d1 : Bit → Bit
             d2 : Bit → Bit
           repr Bit := interned string
           """) ==
             "5:1: repr Bit: Bit has 3 constructors; interned string names a field, not the type. A name is Nat or a binary numeral type (a nullary constructor and two constructors that each take one field of the type itself)"
  end

  test "map_of is refused unless the field is a list of pairs or of a two-field record" do
    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Bool → Box
           repr Box := map_of integer => boolean
           """) ==
             "6:1: repr Box: constructor box field 0 has type Bool, which does not suit map_of; map_of decodes a list of pairs or of a two-field record"

    assert error("""
           data List (A : Type) : Type where
             nil : List A
             cons : A → List A → List A
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : List Bool → Box
           repr Box := map_of integer => boolean
           """) ==
             "9:1: repr Box: constructor box field 0 has type List Bool; map_of needs a list of pairs or of a single-constructor record with two fields"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Pair : Type where
             pair : Bool → Nat → Pair
           data List (A : Type) : Type where
             nil : List A
             cons : A → List A → List A
           data Box : Type where
             box : List Pair → Box
           repr Nat := integer
           repr Box := map_of integer => boolean
           """) ==
             "12:1: repr Box: constructor box field 0 has type Bool, which does not suit integer"
  end

  test "else is refused except on a boolean, an integer, or a type with a repr" do
    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Bool → Box
           repr Box := tuple { list boolean else false }
           """) ==
             "6:1: repr Box: constructor box field 0: else follows boolean, integer, or a type with its own repr, not list"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Maybe (A : Type) : Type where
             nothing : Maybe A
             just : A → Maybe A
           data Box : Type where
             box : Maybe Bool → Box
           repr Box := map { "b" => optional boolean else false }
           """) ==
             "9:1: repr Box: constructor box field 0: else follows boolean, integer, or a type with its own repr, not optional"

    assert error("""
           data List (A : Type) : Type where
             nil : List A
             cons : A → List A → List A
           data Box : Type where
             box : List Nat → Box
           repr Box := tuple { map_of integer => boolean else false }
           """) ==
             "6:1: repr Box: constructor box field 0: else follows boolean, integer, or a type with its own repr, not map_of"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Bool → Box
           repr Box := tuple { interned string else false }
           """) ==
             "6:1: repr Box: constructor box field 0: else follows boolean, integer, or a type with its own repr, not interned string"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Bool → Box
           repr Box := tuple { boolean else false else true }
           """) ==
             "6:1: repr Box: constructor box field 0: else follows boolean, integer, or a type with its own repr, not else"

    assert error("""
           data Key : Type where
             named : Nat → Key
             wild : Key
           repr Key := named => boolean else false | wild => "*"
           """) ==
             "4:1: repr Key: constructor named: else is a component of a shape; it is not the whole arm"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           repr Bool := boolean else false
           """) == "4:1: repr Bool: else is a component of a shape; it is not the whole repr"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Bool → Box
           repr Box := tuple { boolean else missing }
           """) ==
             "6:1: repr Box: constructor box field 0: missing is not a nullary constructor of Bool; nullary constructors are true, false"

    assert error("""
           data Flag : Type where
             no : Flag
             yes : Nat → Flag
           data Box : Type where
             box : Flag → Box
           repr Flag := no => nil | yes => integer
           repr Box := tuple { Flag else yes }
           """) ==
             "7:1: repr Box: constructor box field 0: yes takes fields; a fallback is a nullary constructor of Flag (no)"

    assert error("""
           data Bool : Type where
             true : Bool
             false : Bool
           data Box : Type where
             box : Bool → Box
           repr Box := tuple { boolean else 1 }
           """) ==
             "6:1: repr Box: constructor box field 0: a numeral is a fallback for Nat, and this field has type Bool; nullary constructors are true, false"

    assert error("""
           data Box : Type where
             box : Nat → Box
           repr Box := tuple { integer else 1000001 }
           repr Nat := integer
           """) ==
             "3:1: repr Box: constructor box field 0: 1000001 is above the Nat guard 1000000"
  end

  test "two interned arms overlap, and a string reached through a reference still overlaps" do
    assert error("""
           data Key : Type where
             a : Nat → Key
             b : Nat → Key
           repr Key := a => interned string | b => interned string
           """) ==
             "4:1: repr Key: constructors a and b share a host shape (interned string)"

    assert error("""
           data Other : Type where
             other : Other
           data Key : Type where
             named : Nat → Key
             lit : Other → Key
           repr Other := "hello"
           repr Key := named => interned string | lit => Other
           """) ==
             "7:1: repr Key: constructors named and lit share a host shape (interned string)"
  end

  test "decode and encode share one table shape" do
    mod = codec()
    empty = mod.muro_repr_table_new()
    assert empty == %{by_name: %{}, by_index: %{}}
    assert map_size(empty.by_name) == map_size(empty.by_index)

    known = mod.muro_repr_table_new(["b", "a"])
    assert known.by_name == %{"b" => 0, "a" => 1}
    assert known.by_index == %{0 => "b", 1 => "a"}
    assert mod.muro_repr_table_names(known) == ["b", "a"]

    assert_raise ArgumentError, "muro_repr_table_new expects a list of binaries, got: :no", fn ->
      mod.muro_repr_table_new(:no)
    end

    assert_raise ArgumentError, ~s(muro_repr_table_new duplicate name "a"), fn ->
      mod.muro_repr_table_new(["a", "a"])
    end

    assert_raise ArgumentError, "muro_repr_table_new expects a binary, got: :a", fn ->
      mod.muro_repr_table_new([:a])
    end

    raw = <<255>>
    odd = mod.muro_repr_table_new([raw])
    assert mod.muro_repr_table_names(odd) == [raw]

    assert function_exported?(mod, :decode_bool, 1)
    assert function_exported?(mod, :decode_bool, 2)
    assert function_exported?(mod, :decode_nat, 1)
    assert function_exported?(mod, :decode_nat, 2)
    refute function_exported?(mod, :encode_bool, 1)
    refute function_exported?(mod, :encode_nat, 1)
    assert function_exported?(mod, :encode_bool, 2)
    assert function_exported?(mod, :encode_nat, 2)
    assert function_exported?(mod, :muro_repr_table_new, 0)
    assert function_exported?(mod, :muro_repr_table_new, 1)
    assert function_exported?(mod, :muro_repr_table_names, 1)

    assert mod.decode_bool(true) == {:ok, true, empty}
    assert mod.decode_bool(false, empty) == {:ok, false, empty}
    assert mod.decode_nat(3) == {:ok, peano(3), empty}
    assert mod.decode_nat(3, known) == {:ok, peano(3), known}
    assert mod.encode_nat(peano(3), known) == 3
    assert mod.encode_bool(false, empty) == false
    assert mod.decode_bool(mod.encode_bool(true, empty), empty) == {:ok, true, empty}

    for bad <- [
          %{},
          %{by_name: %{}},
          %{by_name: [], by_index: %{}},
          %{by_name: %{}, by_index: %{}, extra: 1},
          nil
        ] do
      assert_raise ArgumentError,
                   "decode_bool table must be %{by_name: %{}, by_index: %{}}",
                   fn -> mod.decode_bool(true, bad) end

      assert_raise ArgumentError,
                   "encode_nat table must be %{by_name: %{}, by_index: %{}}",
                   fn -> mod.encode_nat(0, bad) end
    end

    assert_raise ArgumentError,
                 "muro_repr_table_names table must be %{by_name: %{}, by_index: %{}}",
                 fn -> mod.muro_repr_table_names(%{}) end
  end

  test "a boolean repr emits the table helpers and no unused nat guard" do
    book =
      ok!("""
      data Bool : Type where
        true : Bool
        false : Bool
      repr Bool := boolean
      """)

    source = Emit.emit_module(ReprBoolOnly, book)
    assert source =~ "def muro_repr_table_new"
    assert source =~ "def muro_repr_table_names"
    refute source =~ "@muro_repr_nat_max"
    refute source =~ "muro_repr_decode_nat"
    refute source =~ "muro_repr_else"
    refute source =~ "muro_repr_map_of"
    refute source =~ "muro_repr_decode_interned"
    refute source =~ "muro_repr_bin_from"
    mod = compile_source(source, ReprBoolOnly)
    assert mod.decode_bool(true) == {:ok, true, mod.muro_repr_table_new()}
    refute function_exported?(mod, :encode_bool, 1)
  end

  test "interned names keep one index and both numeral targets" do
    mod = wide()
    empty = mod.muro_repr_table_new()

    assert mod.decode_key("*") == {:ok, :wild, empty}

    assert mod.decode_key("*", mod.muro_repr_table_new(["auth"])) ==
             {:ok, :wild, mod.muro_repr_table_new(["auth"])}

    {:ok, {:named, 0}, table} = mod.decode_key("auth")
    assert mod.muro_repr_table_names(table) == ["auth"]
    assert mod.encode_key({:named, 0}, table) == "auth"
    assert mod.encode_key(:wild, empty) == "*"

    {:ok, :wild, same} = mod.decode_key("*", table)
    assert same == table

    bad = <<255>>
    assert mod.decode_key(bad) == {:error, {[], {:not_string, bad}}}
    assert mod.decode_key(nil) == {:error, {[], {:no_variant, [:named, :wild], nil}}}
    assert mod.decode_wrap(nil) == {:error, {[], {:not_string, nil}}}
    assert mod.decode_wrap(1) == {:error, {[], {:not_string, 1}}}
    assert mod.decode_token(bad) == {:error, {[], {:not_string, bad}}}

    {:ok, {:wrap, 0}, blank} = mod.decode_wrap("")
    assert mod.muro_repr_table_names(blank) == [""]
    assert mod.encode_wrap({:wrap, 0}, blank) == ""

    assert_raise ArgumentError, "encode_wrap: no name for index 1", fn ->
      mod.encode_wrap({:wrap, {:suc, 0}}, empty)
    end

    reserved = mod.muro_repr_table_new(["*"])

    assert_raise ArgumentError,
                 ~s(encode_key: name "*" is reserved by a sibling constructor),
                 fn -> mod.encode_key({:named, 0}, reserved) end

    labels = Enum.map(0..20, fn i -> "n" <> Integer.to_string(i) end)
    {:ok, {:names, nat_list}, nat_table} = mod.decode_names(labels)
    assert muro_list(nat_list) == Enum.map(0..20, &peano/1)
    assert mod.muro_repr_table_names(nat_table) == labels
    assert mod.encode_names({:names, nat_list}, nat_table) == labels

    {:ok, {:codes, bit_list}, bit_table} = mod.decode_codes(labels)
    assert muro_list(bit_list) == Enum.map(0..20, &bin_term/1)
    assert bin_term(0) == :z
    assert bin_term(1) == {:d1, :z}
    assert bin_term(2) == {:d2, :z}
    assert bin_term(4) == {:d2, {:d1, :z}}
    assert mod.encode_codes({:codes, bit_list}, bit_table) == labels

    preset = mod.muro_repr_table_new(["a", "b", "c", "d", "e"])
    {:ok, {:token, term}, ^preset} = mod.decode_token("e", preset)
    assert term == bin_term(4)
    assert mod.encode_token({:token, term}, preset) == "e"

    {:ok, _, seen} = mod.decode_names(["b", "a", "b"])
    assert mod.muro_repr_table_names(seen) == ["b", "a"]

    start = mod.muro_repr_table_new(["a"])
    {:ok, _, kept} = mod.decode_names(["b", "a"], start)
    assert mod.muro_repr_table_names(kept) == ["a", "b"]

    {:ok, {:twin, 0, {:suc, 0}}, twin_table} = mod.decode_twin({"b", "a"})
    assert mod.muro_repr_table_names(twin_table) == ["b", "a"]
    assert mod.encode_twin({:twin, 0, {:suc, 0}}, twin_table) == {"b", "a"}

    first = %{"a" => "second", "z" => "first"}
    second = %{"z" => "first", "a" => "second"}
    {:ok, rec1, t1} = mod.decode_rec(first)
    {:ok, rec2, t2} = mod.decode_rec(second)
    assert rec1 == {:rec, 0, {:suc, 0}}
    assert rec1 == rec2
    assert t1 == t2
    assert mod.muro_repr_table_names(t1) == ["first", "second"]

    {:ok, {:link, {:cons, {0, {:suc, 0}}, nil}}, link_table} = mod.decode_link(%{"b" => "a"})
    assert mod.muro_repr_table_names(link_table) == ["b", "a"]

    assert mod.decode_link(%{"b" => "a"}) == mod.decode_link(%{"b" => "a"})
  end

  test "a new name past the nat guard is too many names" do
    mod = names_limit(2)
    {:ok, _, table} = mod.decode_names(["a", "b", "c"])
    assert mod.muro_repr_table_names(table) == ["a", "b", "c"]

    assert mod.decode_names(["a", "b", "c", "d"]) ==
             {:error, {[3], {:too_many_names, 2}}}
  end

  test "map_of sorts by host term order and refuses a colliding key" do
    mod = wide()
    empty = mod.muro_repr_table_new()

    assert mod.decode_bag(:no) == {:error, {[], {:not_map, :no}}}
    assert mod.decode_bag(nil) == {:error, {[], {:not_map, nil}}}
    assert mod.decode_bag(%{}) == {:ok, {:bag, nil}, empty}
    assert mod.encode_bag({:bag, nil}, empty) == %{}

    assert mod.decode_bag(%{1.0 => true}) ==
             {:error, {[{:key, 1.0}], {:not_integer, 1.0}}}

    assert mod.decode_bag(%{1 => "x"}) == {:error, {[1], {:not_boolean, "x"}}}

    {:ok, {:rows, {:cons, {:item, 0, true}, nil}}, ^empty} = mod.decode_rows(%{0 => true})
    assert mod.encode_rows({:rows, {:cons, {:item, 0, true}, nil}}, empty) == %{0 => true}

    {:ok, {:bag, {:cons, {0, false}, {:cons, {{:suc, 0}, true}, nil}}}, ^empty} =
      mod.decode_bag(%{1 => true, 0 => false})

    keys = Enum.to_list(0..40)

    host_a = Enum.reduce(keys, %{}, fn k, acc -> Map.put(acc, k, rem(k, 2) == 0) end)

    host_b =
      Enum.reduce(Enum.reverse(keys), %{}, fn k, acc -> Map.put(acc, k, rem(k, 2) == 0) end)

    {:ok, sorted_a, _} = mod.decode_bag(host_a)
    {:ok, sorted_b, _} = mod.decode_bag(host_b)
    assert sorted_a == sorted_b

    assert Enum.map(muro_list(elem(sorted_a, 1)), fn {k, v} -> {mod.encode_nat(k, empty), v} end) ==
             Enum.map(keys, fn k -> {k, rem(k, 2) == 0} end)

    labels = Enum.map(1..40, fn i -> "k" <> Integer.to_string(i) end)
    nat_a = Enum.reduce(labels, %{}, fn k, acc -> Map.put(acc, k, true) end)
    nat_b = Enum.reduce(Enum.reverse(labels), %{}, fn k, acc -> Map.put(acc, k, true) end)
    {:ok, nat_va, nat_ta} = mod.decode_nat_map(nat_a)
    {:ok, nat_vb, nat_tb} = mod.decode_nat_map(nat_b)
    assert nat_va == nat_vb
    assert mod.muro_repr_table_names(nat_ta) == Enum.sort(labels)
    assert nat_ta == nat_tb
    assert mod.encode_nat_map(nat_va, nat_ta) == nat_a

    {:ok, {:collide, collide_list}, _} = mod.decode_collide(%{1.0 => true, 1 => false})
    assert muro_list(collide_list) == [{peano(1), false}, {0, true}]

    assert mod.decode_collide(%{0 => true, 1.0 => false}) ==
             {:error, {[], {:keys_collide, 0, 1.0}}}

    duplicate = {:bag, {:cons, {0, true}, {:cons, {0, false}, nil}}}

    assert_raise ArgumentError, "encode_bag: duplicate map key 0", fn ->
      mod.encode_bag(duplicate, empty)
    end

    unsorted = {:bag, {:cons, {peano(2), true}, {:cons, {0, false}, nil}}}
    encoded = mod.encode_bag(unsorted, empty)
    assert encoded == %{2 => true, 0 => false}
    {:ok, ordered, ^empty} = mod.decode_bag(encoded)
    assert ordered == {:bag, {:cons, {0, false}, {:cons, {peano(2), true}, nil}}}
    assert ordered != unsorted
    assert mod.decode_bag(mod.encode_bag(ordered, empty), empty) == {:ok, ordered, empty}

    :rand.seed(:exsss, {7, 8, 9})

    for _ <- 1..40 do
      n = :rand.uniform(6) - 1

      host =
        if n == 0 do
          %{}
        else
          Map.new(Enum.map(1..n, fn _ -> {:rand.uniform(8) - 1, Enum.random([true, false])} end))
        end

      {:ok, v, table} = mod.decode_bag(host)
      assert table == empty
      assert mod.decode_bag(mod.encode_bag(v, table), table) == {:ok, v, table}
    end
  end

  test "a fallback replaces only an error at its own position" do
    mod = wide()
    empty = mod.muro_repr_table_new()

    assert mod.decode_fall({true}) == {:ok, {:fall, true}, empty}
    assert mod.decode_fall({false}) == {:ok, {:fall, false}, empty}
    assert mod.decode_fall({1}) == {:ok, {:fall, false}, empty}
    assert mod.decode_fall({nil}) == {:ok, {:fall, false}, empty}
    assert mod.decode_fall({"yes"}) == {:ok, {:fall, false}, empty}
    assert mod.decode_fall({%{}}) == {:ok, {:fall, false}, empty}
    assert mod.encode_fall({:fall, false}, empty) == {false}
    assert mod.decode_fall(mod.encode_fall({:fall, false}, empty)) == {:ok, {:fall, false}, empty}

    assert mod.decode_count({1}) == {:ok, {:count, {:suc, 0}}, empty}
    assert mod.decode_count({0}) == {:ok, {:count, 0}, empty}
    assert mod.decode_count({-1}) == {:ok, {:count, 0}, empty}
    assert mod.decode_count({"x"}) == {:ok, {:count, 0}, empty}
    assert mod.decode_count({nil}) == {:ok, {:count, 0}, empty}
    assert mod.decode_count({1_000_001}) == {:error, {[0], {:nat_too_large, 1_000_001}}}
    assert mod.encode_count({:count, 0}, empty) == {0}

    # A numeral fallback anywhere in the book keeps `{:nat_too_large, _}`.
    # A named fallback, in a book with no numeral fallback, replaces that
    # reason when it is reported at the fallback's own path.
    named = compile_book(ok!(named_nat_src()), ReprElseNamed)
    assert named.decode_hold({1_000_001}) == {:ok, {:hold, :zero}, empty}
    assert named.decode_hold({-1}) == {:ok, {:hold, :zero}, empty}
    assert {:ok, {:hold, {:count, two}}, ^empty} = named.decode_hold({2})
    assert named.encode_hold({:hold, {:count, two}}, empty) == {2}

    kept = compile_book(ok!(named_nat_src() <> numeral_box_src()), ReprElseKept)
    assert kept.decode_hold({1_000_001}) == {:error, {[0], {:nat_too_large, 1_000_001}}}
    assert kept.decode_box({1_000_001}) == {:error, {[0], {:nat_too_large, 1_000_001}}}
    assert kept.decode_box({-1}) == {:ok, {:box, 0}, empty}
    assert kept.decode_hold({2}) == {:ok, {:hold, {:count, two}}, empty}

    assert mod.decode_need(%{}) == {:error, {[], {:missing_key, "b"}}}
    assert mod.decode_need(%{"b" => 1}) == {:ok, {:need, false}, empty}
    assert mod.decode_need(%{"b" => nil}) == {:ok, {:need, false}, empty}
    assert mod.decode_need(%{"b" => "yes"}) == {:ok, {:need, false}, empty}
    assert mod.decode_need(%{"b" => true}) == {:ok, {:need, true}, empty}

    assert mod.decode_row(%{}) == {:ok, {:row, :nothing}, empty}
    assert mod.decode_row(%{"b" => true}) == {:ok, {:row, {:just, true}}, empty}
    assert mod.decode_row(%{"b" => false}) == {:ok, {:row, {:just, false}}, empty}
    assert mod.decode_row(%{"b" => nil}) == {:ok, {:row, {:just, false}}, empty}
    assert mod.decode_row(%{"b" => 1}) == {:ok, {:row, {:just, false}}, empty}
    assert mod.decode_row(%{"b" => "yes"}) == {:ok, {:row, {:just, false}}, empty}
    assert mod.encode_row({:row, {:just, false}}, empty) == %{"b" => false}
    assert mod.encode_row({:row, :nothing}, empty) == %{}

    assert mod.decode_row(mod.encode_row({:row, {:just, false}}, empty)) ==
             {:ok, {:row, {:just, false}}, empty}

    assert mod.decode_plain(%{}) == {:ok, {:plain, :nothing}, empty}
    assert mod.decode_plain(%{"b" => nil}) == {:error, {["b"], {:nil_not_allowed, nil}}}
    assert mod.decode_plain(%{"b" => 1}) == {:error, {["b"], {:not_boolean, 1}}}

    assert mod.decode_soft(nil) == {:ok, {:soft, :nothing}, empty}
    assert mod.decode_soft(true) == {:ok, {:soft, {:just, true}}, empty}
    assert mod.decode_soft(false) == {:ok, {:soft, {:just, false}}, empty}
    assert mod.decode_soft(1) == {:ok, {:soft, {:just, false}}, empty}
    assert mod.decode_soft("yes") == {:ok, {:soft, {:just, false}}, empty}
    assert mod.encode_soft({:soft, {:just, false}}, empty) == false
    assert mod.encode_soft({:soft, :nothing}, empty) == nil

    assert mod.decode_hold({nil}) == {:ok, {:hold, :no}, empty}
    assert mod.decode_hold({1}) == {:ok, {:hold, :no}, empty}
    assert mod.decode_hold({%{}}) == {:ok, {:hold, :no}, empty}
    assert mod.decode_hold({%{"n" => 1, "z" => 2}}) == {:ok, {:hold, :no}, empty}
    assert mod.decode_hold({%{"n" => "x"}}) == {:error, {[0, "n"], {:not_integer, "x"}}}

    assert mod.decode_hold({%{"n" => 1_000_001}}) ==
             {:error, {[0, "n"], {:nat_too_large, 1_000_001}}}

    assert mod.decode_hold({%{"n" => 2}}) == {:ok, {:hold, {:yes, peano(2)}}, empty}
    assert mod.encode_hold({:hold, :no}, empty) == {nil}
    assert mod.encode_hold({:hold, {:yes, peano(2)}}, empty) == {%{"n" => 2}}
  end

  test "the names example decodes the issue wire" do
    mod = names_example()
    empty = mod.muro_repr_table_new()

    wire = %{
      "*" => [%{"relation" => "*", "read" => true}],
      "auth" => [%{"relation" => "token", "read" => false}]
    }

    expected =
      {:template,
       {:cons, {:binding, :wild, {:cons, {:entry, :wild, {:just, true}}, nil}},
        {:cons,
         {:binding, {:named, 0}, {:cons, {:entry, {:named, {:suc, 0}}, {:just, false}}, nil}},
         nil}}}

    assert {:ok, got, table} = mod.decode_template(wire)
    assert got == expected
    assert mod.muro_repr_table_names(table) == ["auth", "token"]
    assert table.by_name == %{"auth" => 0, "token" => 1}
    assert table.by_index == %{0 => "auth", 1 => "token"}

    off =
      {:template,
       {:cons, {:binding, :wild, {:cons, {:entry, :wild, {:just, false}}, nil}},
        {:cons,
         {:binding, {:named, 0}, {:cons, {:entry, {:named, {:suc, 0}}, {:just, false}}, nil}},
         nil}}}

    reads_off = String.to_atom(Emit.elixir_base("reads-off"))
    count_entries = String.to_atom(Emit.elixir_base("count-entries"))
    assert apply(mod, reads_off, [expected]) == off
    assert apply(mod, count_entries, [expected]) == {:suc, {:suc, 0}}

    assert mod.encode_template(off, table) == %{
             "*" => [%{"relation" => "*", "read" => false}],
             "auth" => [%{"relation" => "token", "read" => false}]
           }

    assert mod.encode_template(expected, table) == wire

    assert mod.decode_template(mod.encode_template(expected, table), table) ==
             {:ok, expected, table}

    preset = mod.muro_repr_table_new(["token", "auth"])

    preset_term =
      {:template,
       {:cons, {:binding, :wild, {:cons, {:entry, :wild, {:just, true}}, nil}},
        {:cons,
         {:binding, {:named, {:suc, 0}}, {:cons, {:entry, {:named, 0}, {:just, false}}, nil}},
         nil}}}

    assert mod.decode_template(wire, preset) == {:ok, preset_term, preset}
    assert mod.muro_repr_table_names(preset) == ["token", "auth"]
    assert mod.encode_template(preset_term, preset) == wire

    for bad <- [1, nil, "yes"] do
      flagged = %{"*" => [%{"relation" => "*", "read" => bad}]}

      assert mod.decode_template(flagged) ==
               {:ok,
                {:template,
                 {:cons, {:binding, :wild, {:cons, {:entry, :wild, {:just, false}}, nil}}, nil}},
                empty}
    end

    missing = %{"*" => [%{"relation" => "*"}]}

    assert mod.decode_template(missing) ==
             {:ok,
              {:template,
               {:cons, {:binding, :wild, {:cons, {:entry, :wild, :nothing}, nil}}, nil}}, empty}

    strict = strict_names()

    assert strict.decode_template(%{"*" => [%{"relation" => "*", "read" => 1}]}) ==
             {:error, {["*", 0, "read"], {:not_boolean, 1}}}

    :rand.seed(:exsss, {4, 5, 6})

    for _ <- 1..20 do
      rels = ["*", "a", "b"]
      nkeys = :rand.uniform(4) - 1

      host =
        if nkeys == 0 do
          %{}
        else
          Map.new(1..nkeys, fn i ->
            nent = :rand.uniform(3) - 1

            entries =
              if nent == 0 do
                []
              else
                Enum.map(1..nent, fn _ ->
                  %{
                    "relation" => Enum.random(rels),
                    "read" => Enum.random([true, false, 1, nil])
                  }
                end)
              end

            {"k#{i}", entries}
          end)
        end

      case mod.decode_template(host) do
        {:ok, v, got} ->
          assert mod.decode_template(mod.encode_template(v, got), got) == {:ok, v, got}

        other ->
          flunk(inspect(other, limit: 8))
      end
    end
  end

  # `examples/repr_names.muro` with Entry opened. That book emits
  # `muro_repr_else/4` for `boolean else false` beside an open map.
  # Elixir ≥ 1.19 reports a head matching only `{:ambiguous_key, _}` as
  # never used. `compile_source/2` refuses the warning, as
  # `--warnings-as-errors` does.
  test "an open entry with boolean else compiles when warnings are errors" do
    src =
      File.read!("examples/repr_names.muro")
      |> String.replace(
        ~s|repr Entry := map { "relation" => Key, "read" => optional (boolean else false) }|,
        ~s|repr Entry := map open { "relation" => Key, "read" => optional (boolean else false) }|
      )

    book = ok!(src)
    source = Emit.emit_module(ReprElseOpen, book)
    mod = compile_source(source, ReprElseOpen)
    refute source =~ "defp muro_repr_else({:error, {_path, {:ambiguous_key, _}}}"
    assert source =~ "defp muro_repr_else({:error, {path, reason}} = err, at, incoming, fallback)"
    assert source =~ "{:ambiguous_key, _} ->"
    empty = mod.muro_repr_table_new()

    assert mod.decode_entry(%{"relation" => "*", "read" => true}) ==
             {:ok, {:entry, :wild, {:just, true}}, empty}

    assert mod.decode_entry(%{"relation" => "*", "read" => false}) ==
             {:ok, {:entry, :wild, {:just, false}}, empty}

    for bad <- [1, nil, "yes", %{}] do
      assert mod.decode_entry(%{"relation" => "*", "read" => bad}) ==
               {:ok, {:entry, :wild, {:just, false}}, empty}
    end

    assert mod.decode_entry(%{"relation" => "*"}) ==
             {:ok, {:entry, :wild, :nothing}, empty}

    assert mod.decode_entry(%{"relation" => "*", :read => false}) ==
             {:error, {[], {:ambiguous_key, :read}}}

    assert mod.decode_entry(%{"relation" => "*", "read" => true, :read => false}) ==
             {:error, {[], {:ambiguous_key, :read}}}

    assert mod.decode_entry(%{"relation" => "*", "read" => 1, :source => :preset}) ==
             {:ok, {:entry, :wild, {:just, false}}, empty}

    assert mod.decode_template(%{"*" => [%{"relation" => "*", "read" => 1}]}) ==
             {:ok,
              {:template,
               {:cons, {:binding, :wild, {:cons, {:entry, :wild, {:just, false}}, nil}}, nil}},
              empty}

    assert mod.decode_template(%{"*" => [%{"relation" => "*", :read => false}]}) ==
             {:error, {["*", 0], {:ambiguous_key, :read}}}

    assert mod.decode_template(%{
             "*" => [%{"relation" => "*", "read" => false, :read => true, "token_id" => 7}]
           }) == {:error, {["*", 0], {:ambiguous_key, :read}}}
  end

  test "a few thousand pairs and five hundred names stay within the guard" do
    mod = wide()
    names = Enum.map(0..499, fn i -> "n" <> Integer.to_string(i) end)

    case mod.decode_names(names) do
      {:ok, v, table} ->
        assert mod.muro_repr_table_names(table) == names
        assert mod.encode_names(v, table) == names

      other ->
        flunk("500 names failed: #{inspect(other, limit: 5)}")
    end

    bits = Enum.map(0..2047, fn i -> "k" <> Integer.to_string(i) end)
    host = Map.new(bits, &{&1, true})

    case mod.decode_dict(host) do
      {:ok, v, table} ->
        if mod.encode_dict(v, table) != host, do: flunk("binary-numeral map did not round-trip")
        assert mod.muro_repr_table_names(table) == Enum.sort(bits)

      other ->
        flunk("binary-numeral map failed: #{inspect(other, limit: 5)}")
    end

    ints = Map.new(0..1999, fn i -> {i, rem(i, 2) == 0} end)

    case mod.decode_bag(ints) do
      {:ok, v, table} ->
        if mod.encode_bag(v, table) != ints, do: flunk("integer-key map did not round-trip")

      other ->
        flunk("integer-key map failed: #{inspect(other, limit: 5)}")
    end
  end

  test "decode of the example never raises" do
    mod = example()

    for term <- odd_terms() do
      for fun <- [:decode_bool, :decode_entry, :decode_shape, :decode_outcome] do
        result = apply(mod, fun, [term])

        assert match?({:ok, _, _}, result) or
                 match?({:error, {path, _}} when is_list(path), result)
      end
    end
  end

  # Forty-odd atoms, none of them a declared key in the ambiguous-key book.
  # The sigil builds them at compile time, so the test does not call String.to_atom.
  @pad_atoms ~w(aa ab ac ad ae af ag ah ai aj ak al am an ao ap aq ar as at au av aw ax ay az ba bb bc bd be bf bg bh bi bj bk bl bm bn bo)a

  # The choice arm and the top-level map call the same decoder lines. Their
  # constructors differ because a book cannot repeat a name.
  defp same_arm({:ok, {:grant, payload}, table}, {:ok, {:choice_grant, payload}, table}),
    do: true

  defp same_arm({:error, err}, {:error, err}), do: true

  defp same_arm(left, right) do
    flunk("grant and its choice arm disagree:\n#{inspect(left)}\n#{inspect(right)}")
  end

  defp ambig_mod(mod) do
    book = ok!(ambig_src())
    source = Emit.emit_module(mod, book)
    {compile_source(source, mod), source}
  end

  defp ambig_shape(mod, src) do
    book = ok!(src)
    source = Emit.emit_module(mod, book)
    {compile_source(source, mod), source}
  end

  defp padded(collisions, order) do
    strings = for i <- 0..40, do: {"p#{i}", 0}
    atoms = for atom <- @pad_atoms, do: {atom, 0}

    pairs =
      case order do
        :strings_first -> strings ++ atoms ++ collisions
        :collisions_first -> collisions ++ strings ++ atoms
        :rev -> Enum.reverse(atoms) ++ Enum.reverse(strings) ++ Enum.reverse(collisions)
        :middle -> strings ++ collisions ++ atoms
      end

    Enum.reduce(pairs, %{}, fn {k, v}, acc -> Map.put(acc, k, v) end)
  end

  defp ambig_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A

    data Grant : Type where
      grant : Maybe Bool → Grant

    data ChoiceGrant : Type where
      choice_grant : Maybe Bool → ChoiceGrant
      choice_none : ChoiceGrant

    data AtomGrant : Type where
      atom_grant : Maybe Bool → AtomGrant

    data Both : Type where
      both : Bool → Bool → Both

    data Many : Type where
      many : Maybe Bool → Maybe Bool → Maybe Bool → Many

    data AtomMany : Type where
      atom_many : Maybe Bool → Maybe Bool → AtomMany

    data Child : Type where
      child : Maybe Bool → Child

    data Parent : Type where
      parent : Child → Parent

    data Grand : Type where
      grand : Parent → Grand

    data Kids : Type where
      kids : List Child → Kids

    data Closed : Type where
      closed : Maybe Bool → Closed

    data Bag : Type where
      bag : List (Nat × Bool) → Bag

    data Tag : Type where
      tag : Bool → Tag

    data AtomTag : Type where
      atom_tag : Bool → AtomTag

    data Node : Type where
      node_grant : Maybe Bool → Node
      node_none : Node

    data Hold : Type where
      hold : Node → Hold

    repr Bool := boolean
    repr Grant := map open { "read" => optional Bool }
    repr ChoiceGrant := choice_grant => map open { "read" => optional Bool } | choice_none => nil
    repr AtomGrant := map open { :read => optional Bool }
    repr Both := map open { "read" => Bool, :read => Bool }
    repr Many := map open { "read" => optional Bool, "write" => optional Bool, "admin" => optional Bool }
    repr AtomMany := map open { :write => optional Bool, :read => optional Bool }
    repr Child := map open { "read" => optional Bool }
    repr Parent := map open { "child" => Child }
    repr Grand := map open { "parent" => Parent }
    repr Kids := list Child
    repr Closed := map { "read" => optional Bool }
    repr Bag := map_of integer => boolean
    repr Tag := map open { "kind" => "circle", "ok" => Bool }
    repr AtomTag := map open { :kind => :yes, :ok => Bool }
    repr Node := node_grant => map open { "read" => optional Bool } | node_none => nil
    repr Hold := tuple { Node else node_none }
    """
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

    {compiled, diagnostics} =
      Code.with_diagnostics(fn ->
        Code.compile_string(source)
      end)

    warnings = for %{severity: :warning, message: message} <- diagnostics, do: message

    if warnings != [] do
      flunk("generated #{inspect(mod)} warned:\n" <> Enum.join(warnings, "\n"))
    end

    [{^mod, _bin}] = compiled

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

  defp names_example do
    assert {:ok, source} = Muro.emit_file("examples/repr_names.muro", HostReprNames)
    assert source =~ "def #{Emit.elixir_base("reads-off")}("
    assert source =~ "def #{Emit.elixir_base("count-entries")}("
    assert source =~ "def muro_repr_table_new"
    assert source =~ "muro_repr_decode_interned"
    assert source =~ "muro_repr_map_of_decode"
    assert source =~ "muro_repr_else"
    assert source =~ "@muro_repr_nat_max 1_000_000"
    refute source =~ "muro_repr_bin_from"
    compile_source(source, HostReprNames)
  end

  defp strict_names do
    src =
      File.read!("examples/repr_names.muro")
      |> String.replace(
        ~s|repr Entry := map { "relation" => Key, "read" => optional (boolean else false) }|,
        ~s|repr Bool := boolean\nrepr Entry := map { "relation" => Key, "read" => optional Bool }|
      )

    compile_book(ok!(src), HostReprStrict)
  end

  defp wide, do: compile_book(ok!(wide_src()), ReprWide)

  defp names_limit(max) do
    book = ok!(names_limit_src())
    source = Emit.emit_module(ReprNameLimit, book)
    needle = "@muro_repr_nat_max 1_000_000"
    assert source =~ needle

    source =
      String.replace(source, needle, "@muro_repr_nat_max #{Integer.to_string(max)}",
        global: false
      )

    compile_source(source, ReprNameLimit)
  end

  defp wide_src do
    """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A

    data Key : Type where
      named : Nat → Key
      wild : Key

    data Wrap : Type where
      wrap : Nat → Wrap

    data Names : Type where
      names : List Nat → Names

    data Twin : Type where
      twin : Nat → Nat → Twin

    data Rec : Type where
      rec : Nat → Nat → Rec

    data Link : Type where
      link : List (Nat × Nat) → Link

    data Item : Type where
      item : Nat → Bool → Item

    data Rows : Type where
      rows : List Item → Rows

    data Bag : Type where
      bag : List (Nat × Bool) → Bag

    data NatMap : Type where
      natmap : List (Nat × Bool) → NatMap

    data Fall : Type where
      fall : Bool → Fall

    data Count : Type where
      count : Nat → Count

    data Flag : Type where
      no : Flag
      yes : Nat → Flag

    data Hold : Type where
      hold : Flag → Hold

    data Row : Type where
      row : Maybe Bool → Row

    data Soft : Type where
      soft : Maybe Bool → Soft

    data Plain : Type where
      plain : Maybe Bool → Plain

    data Need : Type where
      need : Bool → Need

    data Collide : Type where
      collide : List (Nat × Bool) → Collide

    data Bit : Type where
      d1 : Bit → Bit
      z : Bit
      d2 : Bit → Bit

    data Token : Type where
      token : Bit → Token

    data Codes : Type where
      codes : List Bit → Codes

    data Dict : Type where
      dict : List (Bit × Bool) → Dict

    repr Bool := boolean
    repr Nat := integer
    repr Key := named => interned string | wild => "*"
    repr Wrap := interned string
    repr Names := list interned string
    repr Twin := tuple { interned string, interned string }
    repr Rec := map { "z" => interned string, "a" => interned string }
    repr Link := map_of interned string => interned string
    repr Rows := map_of integer => boolean
    repr Bag := map_of integer => boolean
    repr NatMap := map_of interned string => boolean
    repr Fall := tuple { boolean else false }
    repr Count := tuple { integer else 0 }
    repr Flag := no => nil | yes => map { "n" => integer }
    repr Hold := tuple { Flag else no }
    repr Row := map { "b" => optional (boolean else false) }
    repr Soft := nullable (boolean else false)
    repr Plain := map { "b" => optional Bool }
    repr Need := map { "b" => boolean else false }
    repr Collide := map_of (integer else 0) => boolean
    repr Token := interned string
    repr Codes := list interned string
    repr Dict := map_of interned string => boolean
    """
  end

  defp named_nat_src do
    """
    data Count : Type where
      count : Nat → Count
      zero : Count

    data Hold : Type where
      hold : Count → Hold

    repr Count := count => integer | zero => nil
    repr Hold := tuple { Count else zero }
    """
  end

  defp numeral_box_src do
    """
    data Box : Type where
      box : Nat → Box

    repr Box := tuple { integer else 0 }
    """
  end

  defp names_limit_src do
    """
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    data Names : Type where
      names : List Nat → Names
    repr Names := list interned string
    """
  end

  defp muro_list(nil), do: []
  defp muro_list({:cons, el, rest}), do: [el | muro_list(rest)]

  defp bin_term(0), do: :z
  defp bin_term(i) when rem(i, 2) == 1, do: {:d1, bin_term(div(i - 1, 2))}
  defp bin_term(i) when i > 0, do: {:d2, bin_term(div(i - 2, 2))}

  defp peano(n), do: peano(n, 0)
  defp peano(0, acc), do: acc
  defp peano(n, acc) when n > 0, do: peano(n - 1, {:suc, acc})

  # Compare the integer encode returns. Do not assert on the Peano term.
  defp assert_nat_integer(mod, n) when is_integer(n) and n >= 0 and n <= 10_000 do
    case mod.decode_nat(n) do
      {:ok, v, table} ->
        assert mod.encode_nat(v, table) == n

      other ->
        flunk("decode_nat(#{n}) failed: #{inspect(other, limit: 5)}")
    end
  end

  # A success is discarded. Inspecting `{:ok, nat}` is what exhausts memory.
  defp assert_nat_rejected(mod, value, path, reason, fun) do
    case apply(mod, fun, [value]) do
      {:ok, _, _} ->
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
