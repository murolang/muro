defmodule Muro.CheckTest do
  use ExUnit.Case, async: true

  alias Muro.{Ast, Check, Emit, Example, Parser}

  test "parse, check, and emit half_ok.muro" do
    src = File.read!("examples/half_ok.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.NatFromFile, book)
    assert out =~ ~r/\bdef plus\b/
    assert out =~ ~r/\bdef half\b/
    refute out =~ "half_ok"
    refute out =~ "IsEven"
    refute out =~ "plus_suc"
  end

  test "Muro.Check decides half_ok" do
    assert Check.check_sig(Example.book()) == :ok
  end

  test "run internal helper is defp" do
    assert {:ok, book} = Parser.parse(File.read!("examples/internal_ok.muro"))
    assert Check.check_sig(book) == :ok
    src = Emit.emit_module(Muro.InternalOk, book)
    assert src =~ ~r/\bdefp step\b/
    assert src =~ ~r/\bdef inc\b/
    refute src =~ ~r/\bdef step\b/
  end

  test "emit plus and half as def; omit spec and evidence" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    assert src =~ ~r/\bdef plus\b/
    assert src =~ ~r/\bdef half\b/
    refute src =~ "def half_ok"
    refute src =~ "def IsEven"
    refute src =~ "plus_suc"
  end

  test "affine duplication fails in evidence and is allowed in spec" do
    arrow = {:pi, :affine, :nat, "_", :nat}

    evid = %{
      name: "dup_evid",
      mode: :evidence,
      type: {:pi, :affine, arrow, "f", :nat},
      body:
        {:lam, :affine, arrow, "f",
         {:app, {:app, {:var, "plus"}, {:app, {:var, "f"}, :ze}}, {:app, {:var, "f"}, :ze}}}
    }

    spec = %{
      name: "dup_spec",
      mode: :spec,
      type: {:pi, :affine, :nat, "n", :typ},
      body:
        {:lam, :affine, :nat, "n",
         {:idt, :nat, {:app, {:app, {:var, "plus"}, {:var, "n"}}, {:var, "n"}}, {:var, "n"}}}
    }

    assert {:error, msg} = Check.check_sig([evid | Example.book()])
    assert msg =~ "affine"

    assert Check.check_sig([spec | Example.book()]) == :ok
  end

  test "spec never becomes evidence or a run" do
    as_run = %{
      name: "bad_run",
      mode: :run,
      export: true,
      type: {:pi, :affine, :nat, "n", :typ},
      body: {:def, "IsEven"}
    }

    as_evid = %{
      name: "bad_evid",
      mode: :evidence,
      type: {:pi, :affine, :nat, "n", :typ},
      body: {:def, "IsEven"}
    }

    assert {:error, r} = Check.check_sig([as_run | Example.book()])
    assert r =~ "promotion"

    assert {:error, e} = Check.check_sig([as_evid | Example.book()])
    assert e =~ "promotion"
  end

  test "evidence never becomes a run" do
    book = [
      %{
        name: "bad",
        mode: :run,
        export: true,
        type: :nat,
        body: {:def, "half_ok"}
      }
    ]

    assert {:error, msg} = Check.check_sig(book ++ Example.book())
    assert msg =~ "promotion"
  end

  test "a word other than the four tags is not a tag" do
    assert {:error, msg} = Parser.parse("def x : other Nat := 0")
    assert msg =~ "expected run, run internal, spec, or evidence"
  end

  test "emitted half of eight is four" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    Code.eval_string(src)
    eight = Enum.reduce(1..8, 0, fn _, n -> {:suc, n} end)
    assert call("NatLive", :half, [eight]) == {:suc, {:suc, {:suc, {:suc, 0}}}}
  end

  test "zeros.muro parses, checks, and emits only zeros" do
    src = File.read!("examples/zeros.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Zeros, book)
    assert out =~ ~r/\bdef zeros\b/
    refute out =~ "head-zeros"
    refute out =~ "head_zeros"
  end

  test "pair.muro: let (a, b) = e in t checks, emits a pattern match, and runs" do
    src = File.read!("examples/pair.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.PairLet, book)
    assert out =~ ~r/\bdef addPair\b/
    assert out =~ ~r/\{x1, x2\} = x0;/
    refute out =~ "swap-ok"
    Code.eval_string(out)

    assert call("PairLet", :addPair, [{{:suc, 0}, {:suc, {:suc, 0}}}]) ==
             {:suc, {:suc, {:suc, 0}}}

    assert call("PairLet", :swap, [{1, 2}]) == {2, 1}
  end

  test "higher_order.muro: a definition passed as a value or partially applied is a closure" do
    src = File.read!("examples/higher_order.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.HigherOrder, book)
    refute out =~ "ident()"
    refute out =~ "add2-ok"
    Code.eval_string(out)

    assert call("HigherOrder", :nats, []) |> Enum.take(3) == [0, {:suc, 0}, {:suc, {:suc, 0}}]

    assert call("HigherOrder", :add2, []) ==
             {:cons, {:suc, {:suc, 0}}, {:cons, {:suc, {:suc, {:suc, 0}}}, nil}}

    assert call("HigherOrder", :len_one, []) == {:suc, 0}
    assert call("HigherOrder", :adder, [{:suc, 0}, {:suc, 0}]) == {:suc, {:suc, 0}}
  end

  test "emit: extra arguments apply the result; an eta-reduced match body takes its binder" do
    src = """
    def ident : run Π (n : Nat) → Nat := λ (n : Nat) → n
    def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
      λ (n : Nat) → λ (m : Nat) →
        match n motive (λ _ → Nat)
          | 0 => m
          | suc p => suc (plus p m)
    def picker : run Π (n : Nat) → Π (_ : Nat) → Nat :=
      λ (n : Nat) → match n motive (λ _ → Π (_ : Nat) → Nat)
        | 0 => ident
        | suc p => plus p
    def pick : run Π (n : Nat) → Π (_ : Nat) → Nat := λ (n : Nat) → picker n
    def seven : run Nat := picker (suc (suc 0)) (suc (suc (suc (suc (suc (suc 0))))))
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    out = Emit.emit_module(Muro.EmitEta, book)
    Code.eval_string(out)

    assert call("EmitEta", :seven, []) ==
             {:suc, {:suc, {:suc, {:suc, {:suc, {:suc, {:suc, 0}}}}}}}

    assert call("EmitEta", :picker, [0, {:suc, 0}]) == {:suc, 0}
    assert call("EmitEta", :pick, [{:suc, 0}, {:suc, 0}]) == {:suc, 0}
  end

  test "a keyword is a whole word: successor, reflect, ttl, Natural, matcher are names" do
    src = """
    def successor : run Π (n : Nat) → Nat := λ (n : Nat) → suc(n)
    def reflect : run Nat := successor 0
    def ttl : run Nat := reflect
    def Natural : spec Type := Nat
    def matcher : run Π (n : Natural) → Nat := λ (n : Natural) → match n motive (λ _ → Nat) | 0 => ttl | suc m => m
    def rewriter : run Nat->Nat := matcher
    def Unity : spec Type := Unit
    def Emptiness : spec Type := Empty
    def Typed : spec Type := Natural
    def ok : evidence {rewriter (successor 0) ≡ 0 : Nat} := refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "conversion unfolds a definition that matches past a type parameter" do
    src = """
    def g : spec Π (R : Type) → Π (n : Nat) → Π (k : R) → R :=
      λ (R : Type) → λ (n : Nat) → λ (k : R) →
        match n motive (λ _ → R)
          | 0 => k
          | suc m => g R m k

    def closed : evidence {g Nat (suc 0) (suc 0) ≡ g Nat 0 (suc 0) : Nat} := refl

    def open : evidence Π (- m : Nat) → Π (- k : Nat) → {g Nat (suc m) k ≡ g Nat m k : Nat} :=
      λ (- m : Nat) → λ (- k : Nat) → refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    {:ok, bad} =
      Parser.parse(
        String.replace(src, "| suc m => g R m k", "| suc m => g R m (g R m k)") <>
          "\ndef no : evidence {g Nat (suc 0) (suc 0) ≡ g Nat 0 0 : Nat} := refl\n"
      )

    assert {:error, msg} = Check.check_sig(bad)
    assert msg =~ "no body: cannot convert"
  end

  test "a mutual block descends per member, and keeps the argument only into an earlier member" do
    finder = """
    def best-trace : run Π (+ s : Nat) → Π (+ k : Nat) → Nat :=
      λ (+ s : Nat) → λ (+ k : Nat) →
        match k motive (λ _ → Nat)
          | 0 => s
          | suc j => trace-action s (suc 0) j

    def trace-action : run Π (+ s : Nat) → Π (a : Nat) → Π (+ k : Nat) → Nat :=
      λ (+ s : Nat) → λ (a : Nat) → λ (+ k : Nat) → best-trace (suc s) k
    """

    three =
      "def three : evidence {best-trace 0 (suc (suc (suc 0))) ≡ suc (suc (suc 0)) : Nat} := refl\n"

    assert {:ok, book} = Parser.parse(finder <> three)
    assert Check.check_sig(book) == :ok

    [best, trace] = String.split(finder, "\n\n")
    assert {:ok, swapped} = Parser.parse(trace <> "\n" <> best)
    assert {:error, msg} = Check.check_sig(swapped)
    assert msg =~ "trace-action body: recursive call does not descend"

    parity = """
    def even : run Π (n : Nat) → Nat :=
      λ (n : Nat) → match n motive (λ _ → Nat) | 0 => suc 0 | suc p => odd 0 p
    def odd : run Π (b : Nat) → Π (n : Nat) → Nat :=
      λ (b : Nat) → λ (n : Nat) → match n motive (λ _ → Nat) | 0 => b | suc p => even p
    """

    assert {:ok, book} = Parser.parse(parity)
    assert Check.check_sig(book) == :ok

    for src <- [
          "def f : evidence Π (n : Nat) → Empty := λ (n : Nat) → g n\n" <>
            "def g : evidence Π (n : Nat) → Empty := λ (n : Nat) → f n\n",
          "def f : evidence Π (n : Nat) → Empty := λ (n : Nat) → f n\n"
        ] do
      assert {:ok, book} = Parser.parse(src)
      assert {:error, msg} = Check.check_sig(book)
      assert msg =~ "f body: recursive call does not descend on a smaller argument"
    end
  end

  test "a definition naming a type is that type in a run type" do
    src = """
    def R : spec Type := Nat
    def Pair : spec Type := Nat × R
    def inc : run Π (r : R) → R := λ (r : R) → suc r
    def swap : run Π (p : Pair) → Pair := λ (p : Pair) → let (a, b) = p in (b, a)
    def two : run R := inc (inc 0)
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.RunAliasEx, book)
    Code.eval_string(out)
    assert call("RunAliasEx", :two, []) == {:suc, {:suc, 0}}
    assert call("RunAliasEx", :swap, [{0, {:suc, 0}}]) == {{:suc, 0}, 0}

    {:ok, bad} =
      Parser.parse("""
      def Eq0 : spec Type := {0 ≡ 0 : Nat}
      def h : run Π (p : Nat × Eq0) → Nat := λ (p : Nat × Eq0) → let (a, b) = p in a
      """)

    assert {:error, msg} = Check.check_sig(bad)
    assert msg =~ "variable has a spec type"
  end

  test "refl is not a run term, so no proof reaches emitted code" do
    eq0 = "def Eq0 : spec Type := {0 ≡ 0 : Nat}\n"

    for body <- [
          "def f : run Π (p : Eq0) → Nat := λ (p : Eq0) → 0\ndef g : run Nat := f refl\n",
          "def k : run Nat := (λ (p : Eq0) → 0) refl\n"
        ] do
      assert {:ok, book} = Parser.parse(eq0 <> body)
      assert {:error, msg} = Check.check_sig(book)
      assert msg =~ "no promotion: refl in run mode"
    end

    # an erased argument is checked in spec, and evidence keeps refl
    ok =
      eq0 <>
        """
        def f : run Π (-p : Eq0) → Nat := λ (-p : Eq0) → 0
        def g : run Nat := f refl
        def e : evidence Eq0 := refl
        """

    assert {:ok, book} = Parser.parse(ok)
    assert Check.check_sig(book) == :ok
    out = Emit.emit_module(Muro.NoRunRefl, book)
    refute out =~ "refl"
  end

  test "a run definition has a run type, used or not" do
    eq0 = "def Eq0 : spec Type := {0 ≡ 0 : Nat}\n"

    for {name, body} <- [
          {"e", "def e : run Eq0 := refl\n"},
          {"h", "def h : run Π (n : Nat) → Nat × Eq0 := λ (n : Nat) → (n, refl)\n"},
          {"c", "def c : run Π (n : Nat) → {n ≡ n : Nat} := λ (n : Nat) → refl\n"},
          {"t", "def t : run Type := Nat\n"},
          {"s",
           "ν Stream (A : Type) : Type where\n  uncons : Stream A → A × Stream A\n" <>
             "def s : run Stream Eq0 := unfold 0 (λ (+ n : Nat) → (refl, n))\n"}
        ] do
      assert {:ok, book} = Parser.parse(eq0 <> body)
      assert {:error, msg} = Check.check_sig(book)
      assert msg =~ "#{name} type: no promotion: a run definition has a spec type"
    end

    # the domain is not read: a run argument of spec type is refused at its use
    dom = eq0 <> "def f : run Π (p : Eq0) → Nat := λ (p : Eq0) → 0\n"
    assert {:ok, book} = Parser.parse(dom)
    assert Check.check_sig(book) == :ok

    # an alias of Nat is a run type at the colon too
    alias_ok = "def R : spec Type := Nat\ndef two : run R := suc (suc 0)\n"
    assert {:ok, book} = Parser.parse(alias_ok)
    assert Check.check_sig(book) == :ok
  end

  test "result.muro: ok/error constructors are the Elixir tags" do
    src = File.read!("examples/result.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.ResultEx, book)
    Code.eval_string(out)
    assert call("ResultEx", :pred, [0]) == {:error, :tt}
    assert call("ResultEx", :pred, [{:suc, 0}]) == {:ok, 0}
    assert call("ResultEx", :orZero, [{:error, :tt}]) == 0
    assert call("ResultEx", :orZero, [{:ok, 3}]) == 3
  end

  test "fst and snd are let; head (tail s) infers through let" do
    src = """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A
    def natsFrom : run Π (n : Nat) → Stream Nat :=
      λ (n : Nat) → unfold n (λ (+ k : Nat) → (k, suc k))
    def second : run Π (s : Stream Nat) → Nat :=
      λ (s : Stream Nat) → head (tail s)
    def second-ok : evidence {second (natsFrom 0) ≡ suc(0) : Nat} := refl
    def first : run Π (p : Nat × Nat) → Nat := λ (p : Nat × Nat) → fst p
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    first = Enum.find(book, &(&1.name == "first"))
    assert {:ok, {:lam, _, _, _, {:letp, {:var, 0}, {:var, 1}}}} = Ast.to_db(first.body)

    out = Emit.emit_module(Muro.SecondEx, book)
    Code.eval_string(out)
    assert call("SecondEx", :second, [call("SecondEx", :natsFrom, [0])]) == {:suc, 0}
  end

  test "an application argument may be followed by a colon on the same line" do
    assert {:ok, _} = Parser.parse("def a : evidence {0 ≡ f x : Nat} := refl")
  end

  test "let opens an affine pair once; both projections use it twice" do
    plus =
      "def plus : run Π (n : Nat) → Π (m : Nat) → Nat := λ (n : Nat) → λ (m : Nat) → n\n"

    both_proj =
      plus <>
        "def f : run Π (p : Nat × Nat) → Nat := λ (p : Nat × Nat) → plus (fst p) (snd p)"

    assert {:ok, book} = Parser.parse(both_proj)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "affine variable used twice"

    with_let =
      plus <>
        "def f : run Π (p : Nat × Nat) → Nat := λ (p : Nat × Nat) → let (x, y) = p in plus x y"

    assert {:ok, book} = Parser.parse(with_let)
    assert Check.check_sig(book) == :ok

    # the components are affine too
    twice =
      plus <>
        "def f : run Π (p : Nat × Nat) → Nat := λ (p : Nat × Nat) → let (x, y) = p in plus x x"

    assert {:ok, book} = Parser.parse(twice)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "affine variable used twice"

    # let also infers: as the head of an application its body's type is
    # strengthened past the components
    head =
      plus <>
        "def f : run Π (p : (Π (n : Nat) → Nat) × Nat) → Nat := " <>
        "λ (p : (Π (n : Nat) → Nat) × Nat) → (let (g, y) = p in g) 0"

    assert {:ok, book} = Parser.parse(head)
    assert Check.check_sig(book) == :ok

    # ... unless that type mentions a component
    dep =
      "data Fin : Nat → Type where\n  fzero : Π (n : Nat) → Fin suc(n)\n" <>
        "def mkFin : run Π (n : Nat) → Fin suc(n) := λ (n : Nat) → fzero n\n" <>
        "def g : run Π (p : Nat × Nat) → Nat := " <>
        "λ (p : Nat × Nat) → uncons (let (x, y) = p in mkFin x)"

    assert {:ok, book} = Parser.parse(dep)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "mentions a component"

    # the scrutinee must be a product
    not_prod = plus <> "def f : run Π (n : Nat) → Nat := λ (n : Nat) → let (x, y) = n in x"
    assert {:ok, book} = Parser.parse(not_prod)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "expected ×"
  end

  test "nats.muro parses, checks, and emits natsFrom" do
    src = File.read!("examples/nats.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Nats, book)
    assert out =~ ~r/\bdef natsFrom\b/
    assert out =~ "Stream.unfold"
    Code.eval_string(out)

    assert call("Nats", :natsFrom, [0]) |> Stream.take(3) |> Enum.to_list() == [
             0,
             {:suc, 0},
             {:suc, {:suc, 0}}
           ]
  end

  test "non-guarded unfold fails in run and in evidence" do
    f = {:lam, :affine, :nat, "_", {:var, "bad"}}

    run = %{
      name: "bad",
      mode: :run,
      export: true,
      type: {:stream, :nat},
      body: {:unf, :ze, f}
    }

    evid = %{name: "bad", mode: :evidence, type: {:stream, :nat}, body: {:unf, :ze, f}}

    assert {:error, r} = Check.check_sig([run])

    assert r =~ "pair" or r =~ "unguarded" or r =~ "unfold" or r =~ "×" or r =~ "Stream" or
             r =~ "ν" or r =~ "convert" or r =~ "applied"

    assert {:error, e} = Check.check_sig([evid])

    assert e =~ "pair" or e =~ "unguarded" or e =~ "unfold" or e =~ "×" or e =~ "Stream" or
             e =~ "ν" or e =~ "convert" or e =~ "applied"
  end

  test "even_dec.muro checks; Dec and evenDec are not emitted" do
    src = File.read!("examples/even_dec.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.EvenBook, book)
    refute out =~ ~r/\bevenDec\b/
    refute out =~ ~r/\bdef Dec\b/
    refute out =~ ~r/\bdef IsEven\b/
  end

  test "run Either match emits left/right tags" do
    src = File.read!("examples/either_run.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.EitherRun, book)
    assert out =~ ~r/\bdef fromLeft\b/
    assert out =~ "{:left,"
    assert out =~ "{:right,"
    Code.eval_string(out)
    assert call("EitherRun", :fromLeft, [{:left, 0}]) == 0
    assert call("EitherRun", :fromLeft, [{:right, :tt}]) == 0
  end

  test "LEM for arbitrary P is rejected" do
    src = File.read!("examples/even_dec.muro")
    assert {:ok, book} = Parser.parse(src)

    lem = %{
      name: "lem",
      mode: :evidence,
      type: {:pi, :affine, :typ, "P", {:app, {:var, "Dec"}, {:var, "P"}}},
      body: {:lam, :affine, :typ, "P", {:app, {:var, "left"}, :one}}
    }

    assert {:error, msg} = Check.check_sig([lem | book])
    assert is_binary(msg)
  end

  test "affine refutation cannot be used twice in evidence" do
    src = File.read!("examples/even_dec.muro")
    assert {:ok, book} = Parser.parse(src)

    arrow = {:pi, :affine, {:app, {:var, "IsEven"}, :ze}, "_", :empty}

    dup = %{
      name: "dup_contra",
      mode: :evidence,
      type: {:pi, :affine, arrow, "c", {:prod, :empty, :empty}},
      body:
        {:lam, :affine, arrow, "c", {:pair, {:app, {:var, "c"}, :one}, {:app, {:var, "c"}, :one}}}
    }

    assert {:error, msg} = Check.check_sig([dup | book])
    assert msg =~ "affine"
  end

  test "always.muro checks; Always evidence is not emitted" do
    src = File.read!("examples/always.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.ZeroAlways, book)
    assert out =~ ~r/\bdef zeros\b/
    refute out =~ "always-zero"
  end

  test "unguarded Always evidence fails" do
    src = File.read!("examples/always.muro")
    assert {:ok, book} = Parser.parse(src)

    p = {:lam, :affine, :nat, "_", {:idt, :nat, :ze, :ze}}

    bad = %{
      name: "bad",
      mode: :evidence,
      type: {:always, :nat, p, {:var, "zeros"}},
      body: {:var, "bad"}
    }

    assert {:error, msg} = Check.check_sig(book ++ [bad])
    assert msg =~ "unfold" or msg =~ "ν" or msg =~ "unguarded" or msg =~ "applied"
  end

  test "Always of IsZero at natsFrom 0 is not proved by tt" do
    src = """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def natsFrom : run Π (n : Nat) → Stream Nat :=
      λ (n : Nat) → unfold n (λ (+ k : Nat) → (k, suc k))

    def bogus : evidence Always Nat (λ (n : Nat) → {n ≡ 0 : Nat}) (natsFrom 0) :=
      unfold tt (λ (_ : Unit) → (refl, tt))
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    refute msg =~ "unguarded"
  end

  test "natsFrom 0 ~ zeros is not proved by tt" do
    src = """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def zeros : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))

    def natsFrom : run Π (n : Nat) → Stream Nat :=
      λ (n : Nat) → unfold n (λ (+ k : Nat) → (k, suc k))

    def bogus : evidence natsFrom 0 ~ zeros :=
      unfold tt (λ (_ : Unit) → (refl, tt))
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    refute msg =~ "unguarded"
  end

  test "bisim.muro checks; evidence is not emitted" do
    src = File.read!("examples/bisim.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.BisimEx, book)
    assert out =~ ~r/\bdef zeros\b/
    assert out =~ ~r/\bdef zeros_\b/
    assert out =~ ~r/\bdef natsFrom\b/
    refute out =~ "zeros-bisim"
    refute out =~ "nats_tail_bisim"
  end

  test "dominance.muro: a declared ν family checks; the family is not emitted" do
    src = File.read!("examples/dominance.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.DominanceEx, book)
    assert out =~ ~r/\bdef zeros\b/
    assert out =~ ~r/\bdef natsFrom\b/
    refute out =~ ~r/\bdef Dom\b/
    refute out =~ "zeros_below"
  end

  test "a declared ν family: indices, positivity, the uncons shape, the step" do
    stream = "ν Stream (A : Type) : Type where\n  uncons : Stream A → A × Stream A\n"
    zeros = "def zeros : run Stream Nat := unfold 0 (λ (_ : Nat) → (0, 0))\n"

    refused = fn src, want ->
      assert {:ok, book} = Parser.parse(stream <> src)
      assert {:error, msg} = Check.check_sig(book)
      assert msg =~ want
    end

    # three indices, and a body with two recursive components
    ok = """
    ν Three (f : Stream Nat) (g : Stream Nat) (h : Stream Nat) : Type where
      uncons : Three f g h → {head f ≡ head g : Nat} × Three (tail f) (tail g) (tail h)
    ν Two (s : Stream Nat) : Type where
      uncons : Two s → Unit × (Two (tail s) × Two (tail (tail s)))
    #{zeros}
    def t3 : evidence Three zeros zeros zeros := unfold tt (λ (_ : Unit) → (refl, t3))
    def two : evidence Two zeros := unfold tt (λ (_ : Unit) → (tt, (two, two)))
    """

    assert {:ok, book} = Parser.parse(stream <> ok)
    assert Check.check_sig(book) == :ok

    refused.(
      "ν Bad (s : Stream Nat) : Type where\n  uncons : Bad s → (Π (_ : Bad s) → Empty) × Bad (tail s)\n",
      "not strictly positive"
    )

    # an unfold step is a pair, so a body that is not a product is refused
    refused.(
      "ν F (s : Stream Nat) : Type where\n  uncons : F s → Π (n : Nat) → F (tail s)\n",
      "ν body is not a product"
    )

    assert {:error, msg} =
             Parser.parse(
               "ν D (f : Stream Nat) (g : Stream Nat) : Type where\n  uncons : D g f → Unit × D (tail f) (tail g)\n"
             )

    assert msg =~ "uncons must take D applied to its indices in order"

    assert {:error, msg} = Parser.parse("ν Z : Type where\n  uncons : Z → Nat × Z\n")
    assert msg =~ "a ν family takes at least one index"

    fam =
      "ν Eqs (f : Stream Nat) (g : Stream Nat) : Type where\n  uncons : Eqs f g → {head f ≡ head g : Nat} × Eqs (tail f) (tail g)\n" <>
        zeros

    # the head obligation is checked
    refused.(
      fam <>
        "def bad : evidence Π (s : Stream Nat) → Eqs s zeros := λ (s : Stream Nat) → unfold tt (λ (_ : Unit) → (refl, bad (tail s)))\n",
      "convert"
    )

    # a call into the block is not a head
    refused.(
      fam <>
        "def bad : evidence Eqs zeros zeros := unfold tt (λ (_ : Unit) → (head bad, bad))\n",
      "unguarded recursive call"
    )
  end

  test "an unfold that calls itself in the head is refused" do
    src = """
    ν Count (n : Nat) : Type where
      uncons : Count n → Nat × Count (suc n)
    def bad : evidence Π (n : Nat) → Count n :=
      λ (n : Nat) → unfold tt (λ (_ : Unit) → (head (bad n), bad (suc n)))
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "unguarded recursive call"
  end

  test "a declared family unfold checks, and a stream tail wraps" do
    src = """
    ν Count (n : Nat) : Type where
      uncons : Count n → Nat × Count (suc n)
    def c : evidence Π (n : Nat) → Count n :=
      λ (n : Nat) → unfold tt (λ (_ : Unit) → (n, c (suc n)))
    def idu : run Π (_ : Unit) → Unit := λ (_ : Unit) → tt
    def s : run Stream Unit := unfold tt (λ (_ : Unit) → (tt, idu tt))
    def hs : evidence {head (tail s) ≡ tt : Unit} := refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "a ν-typed definition need not be an unfold when it does not call its block" do
    src = """
    def tabulate : run Π (+ f : Π (_ : Nat) → Nat) → Stream Nat :=
      λ (+ f : Π (_ : Nat) → Nat) → unfold 0 (λ (+ k : Nat) → (f k, suc k))
    def ident : run Π (n : Nat) → Nat := λ (n : Nat) → n
    def nats : run Stream Nat := tabulate ident
    def one : evidence {head (tail nats) ≡ suc 0 : Nat} := refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    assert {:ok, book} = Parser.parse("def s : run Stream Nat := s\n")
    assert {:error, _} = Check.check_sig(book)
  end

  test "unguarded ~ evidence fails" do
    src = File.read!("examples/bisim.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "bad",
      mode: :evidence,
      type: {:bisim, {:var, "zeros"}, {:app, {:var, "natsFrom"}, :ze}},
      body: {:var, "bad"}
    }

    assert {:error, msg} = Check.check_sig(book ++ [bad])

    assert msg =~ "unfold" or msg =~ "ν" or msg =~ "unguarded" or msg =~ "convert" or
             msg =~ "applied"
  end

  test "list.muro checks; evidence is not emitted; length runs" do
    src = File.read!("examples/list.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Lists, book)
    assert out =~ ~r/\bdef length\b/
    assert out =~ ~r/\bdef ones2\b/
    refute out =~ "length-ones2"
    Code.eval_string(out)
    assert call("Lists", :length, [call("Lists", :ones2, [])]) == {:suc, {:suc, 0}}
  end

  test "maybe.muro checks; fromMaybe runs" do
    src = File.read!("examples/maybe.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.MaybeEx, book)
    assert out =~ ~r/\bdef fromMaybe\b/
    refute out =~ "fromJust1"
    Code.eval_string(out)
    assert call("MaybeEx", :fromMaybe, [0, {:just, {:suc, 0}}]) == {:suc, 0}
    assert call("MaybeEx", :fromMaybe, [0, :nothing]) == 0
  end

  test "tree.muro checks; size descends on both children" do
    src = File.read!("examples/tree.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Trees, book)
    assert out =~ ~r/\bdef size\b/
    refute out =~ "size-t2"
    Code.eval_string(out)
    t2 = {:node, :leaf, {:node, :leaf, :leaf}}
    assert call("Trees", :size, [t2]) == {:suc, {:suc, 0}}
  end

  test "strict positivity rejects Bad" do
    src = """
    data Bad : Type where
      mk : (Bad → Nat) → Bad
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "positive"
  end

  test "vec.muro checks; lookup of fzero on a singleton" do
    src = File.read!("examples/vec.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Vecs, book)
    assert out =~ ~r/\bdef lookup\b/
    assert out =~ ~r/\bdef ones1\b/
    refute out =~ "lookup-ok"
    Code.eval_string(out)
    ones1 = {:vcons, 0, {:suc, 0}, :vnil}
    assert call("Vecs", :lookup, [{:fzero, 0}, ones1]) == {:suc, 0}
  end

  # The equation of a rewrite is evidence, or spec inside a spec term: a
  # type may rewrite along an erased equation; a run body may not.
  test "a spec rewrite reads a spec equation; a run rewrite still needs evidence" do
    vec = """
    data Vec (A : Type) : Nat → Type where
      vnil  : Vec A 0
      vcons : Π (n : Nat) → A → Vec A n → Vec A suc(n)
    """

    good =
      vec <>
        """
        def castLen : run Π (-A : Type) → Π (-n : Nat) → Π (-m : Nat) → Π (-e : {n ≡ m : Nat}) →
                            Π (xs : Vec A (rewrite e motive (λ _ → Nat) in m)) →
                            Vec A (rewrite e motive (λ _ → Nat) in m) :=
          λ (-A : Type) → λ (-n : Nat) → λ (-m : Nat) → λ (-e : {n ≡ m : Nat}) →
          λ (xs : Vec A (rewrite e motive (λ _ → Nat) in m)) → xs
        """

    assert {:ok, book} = Parser.parse(good)
    assert Check.check_sig(book) == :ok

    bad =
      vec <>
        """
        def castBad : run Π (-A : Type) → Π (-n : Nat) → Π (-m : Nat) → Π (-e : {n ≡ m : Nat}) →
                            Π (xs : Vec A m) → Vec A n :=
          λ (-A : Type) → λ (-n : Nat) → λ (-m : Nat) → λ (-e : {n ≡ m : Nat}) →
          λ (xs : Vec A m) → rewrite e motive (λ z → Vec A z) in xs
        """

    assert {:ok, book2} = Parser.parse(bad)
    assert {:error, msg} = Check.check_sig(book2)
    assert msg =~ "erased variable in evidence mode"
  end

  # A branch is typed at its constructor's own indices: nothing is
  # substituted for p. Without the equation in the motive, as : Vec A p is
  # not a Vec A m, and the recursive call lookup A p j as has j : Fin m
  # against Fin p.
  test "an indexed match branch does not learn the scrutinee's index by itself" do
    src = """
    data Fin : Nat → Type where
      fzero : Π (n : Nat) → Fin suc(n)
      fsuc  : Π (n : Nat) → Fin n → Fin suc(n)

    data Vec (A : Type) : Nat → Type where
      vnil  : Vec A 0
      vcons : Π (n : Nat) → A → Vec A n → Vec A suc(n)

    def lookup : run Π (-A : Type) → Π (-n : Nat) → Π (i : Fin n) → Π (xs : Vec A n) → A :=
      λ (-A : Type) → λ (-n : Nat) → λ (i : Fin n) → λ (xs : Vec A n) →
        (match i motive (λ (k : Nat) → λ (_ : Fin k) → Vec A k → A)
          | fzero m =>
              λ (ys : Vec A suc(m)) →
                (match ys motive (λ (k : Nat) → λ (_ : Vec A k) → A)
                  | vnil => 0
                  | vcons p a as => a)
          | fsuc m j =>
              λ (ys : Vec A suc(m)) →
                (match ys motive (λ (k : Nat) → λ (_ : Vec A k) → A)
                  | vnil => 0
                  | vcons p a as => lookup A p j as)) xs
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert is_binary(msg)
  end

  # Type is a sort. A kind (Π … → Type) is well-formed but is not a term of
  # type Type. Otherwise Type would be a retract of a small type (Girard).
  test "a kind is not a small type: Π, ×, and data fields" do
    pi_retract = """
    def U : spec Type := Π (_ : Unit) → Type
    """

    assert {:ok, book} = Parser.parse(pi_retract)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "Type has no type"

    prod_retract = """
    def U : spec Type := Type × Unit
    """

    assert {:ok, book} = Parser.parse(prod_retract)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "Type has no type"

    box_retract = """
    data Box : Type where
      box : Π (A : Type) → Box
    """

    assert {:ok, book} = Parser.parse(box_retract)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "Type has no type"
  end

  test "a type is recognised by its shape, not by what it reduces to" do
    src = """
    def U : spec (λ (x : Nat) → Type) 0 := Nat
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "Type has no type"
  end

  test "instantiating an evidence lemma does not consume its argument" do
    src = """
    def lem : evidence Π (n : Nat) → {n ≡ n : Nat} := λ (n : Nat) → refl
    def twice : evidence Π (n : Nat) → {n ≡ n : Nat} × {n ≡ n : Nat} :=
      λ (n : Nat) → (lem n, lem n)
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    # the argument is still checked in the mode of the application
    spec_arg = """
    def P : spec Type := Nat
    def lem : evidence Π (A : Type) → {A ≡ A : Type} := λ (A : Type) → refl
    def bad : evidence {P ≡ P : Type} := lem P
    """

    assert {:ok, book} = Parser.parse(spec_arg)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "no promotion"
  end

  test "kinds are well-formed as def types and binder domains" do
    src = """
    def IsEven : spec Π (n : Nat) → Type :=
      λ (n : Nat) →
        match n motive (λ _ → Type)
          | 0 => Unit
          | suc n1 => Empty
    def Fam : spec Π (F : Π (n : Nat) → Type) → Type :=
      λ (F : Π (n : Nat) → Type) → F 0
    def useFam : spec Fam IsEven := tt
    def Eq : spec Type := {IsEven ≡ IsEven : Π (n : Nat) → Type}
    def eqOk : evidence Eq := refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "indexed positivity rejects Bad" do
    src = """
    data Bad : Nat → Type where
      mk : Π (n : Nat) → (Bad n → Nat) → Bad n
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "positive"
  end

  test "wrong constructor target index fails" do
    src = File.read!("examples/vec.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "badnil",
      mode: :run,
      export: true,
      type: {:app, {:app, {:var, "Vec"}, :nat}, :ze},
      body: {:app, {:app, {:app, {:var, "vcons"}, :ze}, {:su, :ze}}, {:var, "vnil"}}
    }

    assert {:error, msg} = Check.check_sig(book ++ [bad])
    assert is_binary(msg)
  end

  test "constructor target missing an index fails" do
    src = """
    data Vec (A : Type) : Nat → Type where
      vnil : Vec A
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert is_binary(msg)
  end

  test "non-descending Vec recursion fails" do
    src = File.read!("examples/vec.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "loopV",
      mode: :run,
      export: true,
      type:
        {:pi, :erased, :typ, "A",
         {:pi, :affine, :nat, "n",
          {:pi, :affine, {:app, {:app, {:var, "Vec"}, {:var, "A"}}, {:var, "n"}}, "xs", :nat}}},
      body:
        {:lam, :erased, :typ, "A",
         {:lam, :affine, :nat, "n",
          {:lam, :affine, {:app, {:app, {:var, "Vec"}, {:var, "A"}}, {:var, "n"}}, "xs",
           {:app, {:app, {:app, {:var, "loopV"}, {:var, "A"}}, {:var, "n"}}, {:var, "xs"}}}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end

  # The fields of a computed scrutinee are not smaller than anything: this
  # `boom z` would unfold to itself, and `absurd` would be an evidence of
  # Empty. Same rule as `match` on Nat (scrut_ok).
  test "a field of a computed scrutinee is not smaller" do
    src = """
    data N : Type where
      z : N
      s : N → N

    def P : spec Π (x : N) → Type :=
      λ (x : N) →
        match x motive (λ _ → Type)
          | z => Unit
          | s _ => Empty

    def bump : run Π (n : N) → N :=
      λ (n : N) → s n

    def boom : evidence Π (n : N) → Empty :=
      λ (n : N) →
        match (bump n) motive (λ x → P x)
          | z => tt
          | s m => boom m

    def absurd : evidence Empty :=
      boom z
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "boom body"
    assert msg =~ "descend"

    # matching a λ-bound variable that is not an argument exposes nothing either
    lam_src = """
    data List (A : Type) : Type where
      nil  : List A
      cons : A → List A → List A

    def bad : run Π (xs : List Nat) → Nat :=
      λ (xs : List Nat) →
        (λ (ys : List Nat) →
          match ys motive (λ _ → Nat)
            | nil => 0
            | cons _ as => bad as) (cons 0 xs)
    """

    assert {:ok, book2} = Parser.parse(lam_src)
    assert {:error, msg2} = Check.check_sig(book2)
    assert msg2 =~ "descend"
  end

  # The self-call must descend at the position of the argument it descends
  # on; a smaller variable passed at another position is not descent
  # (f (1, 0) → f (2, 0) → f (2, 1) → … would diverge).
  test "a smaller variable at another position is not descent" do
    src = """
    def f : run Π (x : Nat) → Π (y : Nat) → Nat :=
      λ (x : Nat) → λ (y : Nat) →
        match x motive (λ _ → Nat)
          | 0 => y
          | suc xp => f (suc (suc y)) xp
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "f body"
    assert msg =~ "descend"
  end

  # The definition being checked may not be passed along unapplied.
  test "an unapplied self-reference is refused" do
    src = """
    def apply : run Π (f : Π (x : Nat) → Nat) → Π (x : Nat) → Nat :=
      λ (f : Π (x : Nat) → Nat) → λ (x : Nat) → f x

    def loop : run Π (n : Nat) → Nat :=
      λ (n : Nat) → apply loop n
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "loop body"
    assert msg =~ "applied"

    spec = """
    def selfSpec : spec Π (n : Nat) → Nat :=
      λ (n : Nat) → selfSpec n
    """

    assert {:ok, book2} = Parser.parse(spec)
    assert {:error, msg2} = Check.check_sig(book2)
    assert msg2 =~ "selfSpec body"
    assert msg2 =~ "descend"
  end

  test "a spec definition may not be its own negation" do
    src = """
    def X : spec Type := Π (+ x : X) → Empty
    def self-app : evidence X := λ (+ x : X) → x x
    def boom : evidence Empty := self-app self-app
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "X body"
    assert msg =~ "applied"
  end

  test "a spec definition may not be plainly its own body" do
    assert {:ok, book} = Parser.parse("def T : spec Type := T\n")
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "T body"
    assert msg =~ "applied"

    assert {:ok, book2} = Parser.parse("def n : spec Nat := n\n")
    assert {:error, msg2} = Check.check_sig(book2)
    assert msg2 =~ "applied"
  end

  test "a spec family may recurse on a match-bound predecessor" do
    src = """
    def Even : spec Π (n : Nat) → Type :=
      λ (n : Nat) →
        match n motive (λ _ → Type)
          | 0 => Unit
          | suc m =>
              match m motive (λ _ → Type)
                | 0 => Empty
                | suc k => Even k
    def two-even : evidence Even (suc (suc 0)) := tt
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  # The position a definition descends on is found by the checker; it need
  # not be the first argument.
  test "descent on a later argument" do
    src = """
    def plusFlip : run Π (m : Nat) → Π (n : Nat) → Nat :=
      λ (m : Nat) → λ (n : Nat) →
        match n motive (λ _ → Nat)
          | 0 => m
          | suc np => suc (plusFlip m np)

    def three : evidence {plusFlip suc(0) suc(suc(0)) ≡ suc(suc(suc(0))) : Nat} :=
      refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    # lookup with the length kept: it descends on i, the third argument
    vec = File.read!("examples/vec.muro")

    unerased =
      String.replace(vec, "Π (-n : Nat) → Π (i : Fin n)", "Π (n : Nat) → Π (i : Fin n)")
      |> String.replace("λ (-n : Nat) → λ (i : Fin n)", "λ (n : Nat) → λ (i : Fin n)")

    assert unerased != vec
    assert {:ok, book2} = Parser.parse(unerased)
    assert Check.check_sig(book2) == :ok
  end

  test "non-descending Maybe recursion fails" do
    src = File.read!("examples/maybe.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "loop",
      mode: :run,
      export: true,
      type:
        {:pi, :erased, :typ, "A",
         {:pi, :affine, {:app, {:var, "Maybe"}, {:var, "A"}}, "m",
          {:app, {:var, "Maybe"}, {:var, "A"}}}},
      body:
        {:lam, :erased, :typ, "A",
         {:lam, :affine, {:app, {:var, "Maybe"}, {:var, "A"}}, "m",
          {:app, {:app, {:var, "loop"}, {:var, "A"}}, {:var, "m"}}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end

  test "non-descending Tree recursion fails" do
    src = File.read!("examples/tree.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "loopT",
      mode: :run,
      export: true,
      type: {:pi, :affine, {:var, "Tree"}, "t", {:var, "Tree"}},
      body: {:lam, :affine, {:var, "Tree"}, "t", {:app, {:var, "loopT"}, {:var, "t"}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end

  test "non-descending list recursion fails" do
    src = File.read!("examples/list.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "badlen",
      mode: :run,
      export: true,
      type:
        {:pi, :erased, :typ, "A", {:pi, :affine, {:app, {:var, "List"}, {:var, "A"}}, "xs", :nat}},
      body:
        {:lam, :erased, :typ, "A",
         {:lam, :affine, {:app, {:var, "List"}, {:var, "A"}}, "xs",
          {:app, {:app, {:var, "badlen"}, {:var, "A"}}, {:var, "xs"}}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end

  test "nx_add.muro checks; emitted module runs Nx.add" do
    src = File.read!("examples/nx_add.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.NxAdd, book)
    assert out =~ ~r/\bdef addI\b/
    assert out =~ ~r/\bdef addT\b/
    assert out =~ "Nx.add"
    refute out =~ "defn"
    refute out =~ "@defn_compiler"
    Code.eval_string(out)

    t1 = call("NxAdd", :t1, [])
    assert %Nx.Tensor{} = t1
    assert Nx.to_flat_list(t1) == [1, 2]
    assert Nx.to_flat_list(call("NxAdd", :doubled, [])) == [2, 4]
    assert Nx.to_flat_list(call("NxAdd", :addT, [Nx.tensor([1, 2], type: :s64)])) == [2, 4]

    sum = call("NxAdd", :addI, [Nx.tensor(3, type: :s64), Nx.tensor(4, type: :s64)])
    assert %Nx.Tensor{} = sum
    assert Nx.to_number(sum) == 7
  end

  test "Peano Nat is not emitted as s64 except through toI64" do
    src = File.read!("examples/nx_add.muro")
    assert {:ok, book} = Parser.parse(src)
    out = Emit.emit_module(Muro.NxNatEmit, book)
    assert out =~ "{:suc,"
    assert out =~ "muro_nat_to_int"
  end

  test "kernel identity on F32 is refused" do
    src = """
    def bad : spec Π (x : F32) → Π (y : F32) → {x ≡ y : F32} :=
      λ (x : F32) → λ (y : F32) → refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "F32"
  end

  test "kernel identity on Tensor F32 is refused" do
    src = """
    def badT : spec Π (n : I64) → Π (x : Tensor F32 n) → Π (y : Tensor F32 n) → {x ≡ y : Tensor F32 n} :=
      λ (n : I64) → λ (x : Tensor F32 n) → λ (y : Tensor F32 n) → refl
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "F32"
  end

  test "running out of fuel is reported, not a verdict" do
    assert {:error, msg} = Check.check_sig(Example.book(), fuel: 1)
    assert msg =~ "out of fuel"
    refute msg =~ "cannot convert"
    assert Check.check_sig(Example.book(), fuel: Check.default_fuel()) == :ok
    assert Muro.check_file("examples/vec.muro", fuel: 10 * Check.default_fuel()) == :ok
  end

  test "mix muro.check --fuel" do
    assert {:error, msg} = Muro.check_file("examples/half_ok.muro", fuel: 2)
    assert msg =~ "out of fuel"

    assert_raise Mix.Error, ~r/out of fuel/, fn ->
      Mix.Tasks.Muro.Check.run(["--fuel", "2", "examples/half_ok.muro"])
    end

    assert_raise Mix.Error, ~r/positive/, fn ->
      Mix.Tasks.Muro.Check.run(["--fuel", "0"])
    end
  end

  test "check_sig reports every definition error, in book order" do
    src = """
    def a : run Nat := tt

    def ok : run Nat := 0

    def b : run Π (n : Nat) → Nat :=
      λ (n : Nat) → ?
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    [first, second] = String.split(msg, "\n\n")
    assert first =~ "a body"
    assert first =~ "Unit ≁ Nat"
    assert second =~ "b body"
    assert second =~ "unsolved hole"
    assert second =~ "expected: Nat"
    refute msg =~ "ok body"
  end

  test "parse errors carry line:col" do
    assert {:error, msg} = Parser.parse("def x : run Nat :=")
    assert msg =~ ~r/^\d+:\d+: /
  end

  test "a check error names the definition and prefixes line:col" do
    src = "def bad : run Nat := tt\n"

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ ~r/^1:1: bad body:/
    assert msg =~ "Unit ≁ Nat"
  end

  test "conversion prints surface types with binder names" do
    src = """
    def bad : evidence Π (n : Nat) → {n ≡ 0 : Nat} :=
      λ (n : Nat) → n
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "Nat ≁ {n ≡ 0 : Nat}"
    refute msg =~ "#0"
  end

  test "a hole fails with the expected type and the context" do
    src = """
    def gap : run Π (n : Nat) → Nat :=
      λ (n : Nat) → ?
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "unsolved hole"
    assert msg =~ "expected: Nat"
    assert msg =~ "n : Nat"
    assert msg =~ ~r/\d+:\d+: /
  end

  test "a hole in infer position still fails" do
    src = "def gap : run Nat := ? 0\n"

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "unsolved hole"
    assert msg =~ "expected: (none; infer)"
  end

  test "the prelude checks, and a file can use it" do
    assert Check.check_sig(Muro.Prelude.book()) == :ok
    assert Muro.check_file("examples/using_prelude.muro") == :ok

    assert {:ok, src} = Muro.emit_file("examples/using_prelude.muro", Muro.UsePrelude)
    assert src =~ "def before"
    assert src =~ "defp pred"
    refute src =~ "def plus"
    refute src =~ "defp plus"
  end

  test "a file definition replaces the prelude name and its dependents" do
    path = Path.join(System.tmp_dir!(), "muro_shadow_plus.muro")

    File.write!(path, """
    def plus : run Nat := 0
    def before : run Nat := pred (suc 0)
    """)

    assert Muro.check_file(path) == :ok
    assert {:ok, src} = Muro.emit_file(path, Muro.ShadowPlus)
    assert src =~ "def plus"
    assert src =~ "defp pred"
    refute src =~ "defp plus"

    bad = Path.join(System.tmp_dir!(), "muro_shadow_pred.muro")

    File.write!(bad, """
    def pred : run Nat := 0
    def bad : evidence {0 ≡ 0 : Nat} := inj-suc 0 0 refl
    """)

    assert {:error, msg} = Muro.check_file(bad)
    assert msg =~ "unknown constructor inj-suc"
  end

  test "half_ok keeps its own plus when emitted through the prelude" do
    assert {:ok, src} = Muro.emit_file("examples/half_ok.muro", Muro.HalfFromFile)
    assert src =~ "def plus"
    assert src =~ "def half"
    refute src =~ "defp pred"
    refute src =~ "defp plus"
  end

  test "a hole never checks, including in spec" do
    src = "def gap : spec Π (n : Nat) → Nat := λ (n : Nat) → ?\n"

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "unsolved hole"
    assert msg =~ "expected: Nat"
  end

  test "even and odd descend together" do
    src = File.read!("examples/even_odd.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "a spec alias does not hide a negative field" do
    src = """
    def Contra : spec Type := Bad → Empty
    data Bad : Type where
      roll : Contra → Bad
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "strictly positive"
  end

  test "a spec alias of Nat is a positive field" do
    src = """
    def N : spec Type := Nat
    data D : Type where
      mk : N → D
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "a negative occurrence through a second data type is refused" do
    src = """
    data Bad : Type where
      bad : (Wrap → Empty) → Bad
    data Wrap : Type where
      wrap : Bad → Wrap
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "strictly positive"
  end

  test "a negative occurrence through a second data type is refused in either order" do
    src = """
    data Wrap : Type where
      wrap : Bad → Wrap
    data Bad : Type where
      bad : (Wrap → Empty) → Bad
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "strictly positive"
  end

  test "two data types that store each other in a field still check" do
    src = """
    data Tree : Type where
      node : Forest → Tree
    data Forest : Type where
      nil : Forest
      cons : Tree → Forest → Forest
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "a data type inside its own argument is refused" do
    src = """
    data T (A : Type) (B : Type) : Type where
      node : A → T Empty (T A B → Empty) → T A B
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "strictly positive"
  end

  test "a negative field under a stuck match on Nat is refused" do
    src = """
    data Bad : Type where
      bad : (Π (n : Nat) → match n motive (λ _ → Type) | 0 => (Bad → Empty) | suc _ => Unit) → Bad
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "strictly positive"
  end

  test "a negative field under a stuck match on a data type is refused" do
    src = """
    data B : Type where
      t : B
      f : B
    data Bad : Type where
      bad : (Π (b : B) → match b motive (λ _ → Type) | t => (Bad → Empty) | f => Unit) → Bad
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "strictly positive"
  end

  test "a match that reduces is unfolded before positivity" do
    src = """
    data D : Type where
      mk : (Π (n : Nat) → match 0 motive (λ _ → Type) | 0 => Nat | suc _ => (D → Empty)) → D
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "a direct negative field is refused" do
    src = """
    data Bad : Type where
      roll : (Bad → Empty) → Bad
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "strictly positive"
  end

  test "mutual evidence of Empty is refused" do
    src = """
    def impossible : evidence Empty := helper
    def helper : evidence Empty := impossible
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "applied" or msg =~ "descend"
  end

  test "a mutual block with no shared descent position is refused" do
    src = """
    def ping : evidence Π (n : Nat) → Π (m : Nat) → {n ≡ 0 : Nat} :=
      λ (n : Nat) → λ (m : Nat) →
        match n motive (λ k → {k ≡ 0 : Nat}) | 0 => refl | suc p => pong p suc(p)
    def pong : evidence Π (n : Nat) → Π (m : Nat) → {m ≡ 0 : Nat} :=
      λ (n : Nat) → λ (m : Nat) →
        match m motive (λ k → {k ≡ 0 : Nat}) | 0 => refl | suc q => ping suc(q) q
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "descend"

    assert {:error, msg} = Muro.check_file("examples/bad_shared.muro")
    assert msg =~ "descend"
    assert Muro.check_file("examples/even_odd.muro") == :ok
  end

  test "mutual evidence of an absurd equation is refused" do
    src = """
    def ping : evidence Π (n : Nat) → {n ≡ suc(n) : Nat} :=
      λ (n : Nat) → pong n
    def pong : evidence Π (n : Nat) → {n ≡ suc(n) : Nat} :=
      λ (n : Nat) → ping n
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "descend"
  end

  test "mutual unguarded run is refused" do
    src = """
    def spin : run Nat := spin2
    def spin2 : run Nat := spin
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "applied" or msg =~ "descend"
  end

  test "a match branch must bind every constructor field" do
    src = """
    data P : Type where
      mk : Nat → Nat → P
    def g : run Π (p : P) → Nat :=
      λ (p : P) →
        match p motive (λ _ → Nat)
          | mk a => a
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "branch mk binds 1 variables, constructor has 2 fields"
  end

  test "too many match binders is an error, not a crash" do
    src = """
    data P : Type where
      mk : Nat → P
    def g : run Π (p : P) → Nat :=
      λ (p : P) →
        match p motive (λ _ → Nat)
          | mk a b => a
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "branch mk binds 2 variables, constructor has 1 fields"
  end

  test "uncons of an Always proof is the unfold step" do
    src = File.read!("examples/always.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "uncons of a bisimulation is the head equation and the tails" do
    src = File.read!("examples/bisim.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "two data types with one name are refused" do
    src = """
    data Foo : Nat → Type where
      foo : Foo 0
    data Foo : Nat → Type where
      bar : Foo suc(0)
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "duplicate name Foo"
  end

  test "a definition with a constructor's name is refused" do
    src = """
    data Vec (A : Type) : Nat → Type where
      vnil  : Vec A 0
      vcons : Π (n : Nat) → A → Vec A n → Vec A suc(n)
    def vnil : evidence Vec Nat suc(0) := vcons 0 0 vnil
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "duplicate name vnil"
  end

  test "two definitions with one name are refused" do
    src = """
    def x : run Nat := 0
    def x : run Nat := suc(0)
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "duplicate name x"
  end

  test "a constructor that reuses a prelude name is refused" do
    src = """
    data D : Type where
      plus : D
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(Muro.Prelude.for_check(book))
    assert msg =~ "duplicate name plus"
  end

  test "mix muro.check refuses a mutual Empty cycle" do
    assert {:error, msg} = Muro.check_file("examples/cycle_empty.muro")
    assert msg =~ "impossible"
    assert msg =~ "helper"
    assert msg =~ "recursive definition must be applied to its arguments"
    refute msg =~ "unknown"

    assert_raise Mix.Error, ~r/recursive definition must be applied to its arguments/, fn ->
      Mix.Tasks.Muro.Check.run(["examples/cycle_empty.muro"])
    end
  end

  test "mix muro.check refuses a negative field through another data type" do
    assert {:error, msg} = Muro.check_file("examples/bad_wrap.muro")
    assert msg =~ "constructor is not strictly positive"

    assert_raise Mix.Error, ~r/constructor is not strictly positive/, fn ->
      Mix.Tasks.Muro.Check.run(["examples/bad_wrap.muro"])
    end
  end

  test "mix muro.check refuses a repeated name" do
    assert {:error, msg} = Muro.check_file("examples/bad_dup.muro")
    assert msg =~ "duplicate name Foo"

    assert_raise Mix.Error, ~r/duplicate name Foo/, fn ->
      Mix.Tasks.Muro.Check.run(["examples/bad_dup.muro"])
    end
  end

  test "mix muro.check refuses a negative field under a stuck match" do
    assert {:error, msg} = Muro.check_file("examples/bad_stuck.muro")
    assert msg =~ "constructor is not strictly positive"

    assert_raise Mix.Error, ~r/constructor is not strictly positive/, fn ->
      Mix.Tasks.Muro.Check.run(["examples/bad_stuck.muro"])
    end
  end

  test "mix muro.check refuses a negative constructor field" do
    assert {:error, msg} = Muro.check_file("examples/bad_positive.muro")
    assert msg =~ "constructor is not strictly positive"

    assert_raise Mix.Error, ~r/constructor is not strictly positive/, fn ->
      Mix.Tasks.Muro.Check.run(["examples/bad_positive.muro"])
    end
  end

  test "mix muro.check unfolds a spec alias before positivity" do
    assert {:error, msg} = Muro.check_file("examples/bad_alias.muro")
    assert msg =~ "constructor is not strictly positive"
    refute msg =~ "BadAlias"
    refute msg =~ "unknown"

    assert_raise Mix.Error, ~r/constructor is not strictly positive/, fn ->
      Mix.Tasks.Muro.Check.run(["examples/bad_alias.muro"])
    end
  end

  test "mix muro.check refuses a cons branch with the wrong binder count" do
    assert {:error, msg} = Muro.check_file("examples/bad_cons.muro")
    assert msg =~ "branch cons binds 1 variables, constructor has 2 fields"
    assert msg =~ "branch cons binds 3 variables, constructor has 2 fields"

    assert_raise Mix.Error, ~r/branch cons binds 1 variables, constructor has 2 fields/, fn ->
      Mix.Tasks.Muro.Check.run(["examples/bad_cons.muro"])
    end

    assert Mix.Tasks.Muro.Check.run(["examples/list.muro"]) == :ok
    assert Mix.Tasks.Muro.Check.run(["examples/vec.muro"]) == :ok
    assert Mix.Tasks.Muro.Check.run(["examples/even_odd.muro"]) == :ok
    assert Mix.Tasks.Muro.Check.run(["examples/always.muro"]) == :ok
    assert Mix.Tasks.Muro.Check.run(["examples/bisim.muro"]) == :ok
  end

  test "a match on a two-field constructor reduces with both fields in place" do
    # The second field was substituted one variable too low, into whichever
    # binder came next: drop1 (cons y ys) reduced to zs, so the true equation
    # was refused and the false one checked.
    assert Muro.check_file("examples/second_field.muro") == :ok

    assert {:error, msg} = Muro.check_file("examples/bad_second_field.muro")
    assert msg =~ "drop1-other"
  end

  test "sort.muro checks; an atom is not a Nat; a missing arm names the atom" do
    assert Muro.check_file("examples/sort.muro") == :ok
    assert Muro.check_file("examples/list.muro") == :ok
    assert Muro.check_file("examples/vec.muro") == :ok

    sort_src = File.read!("examples/sort.muro")
    refute sort_src =~ "data List"
    assert {:ok, sort_book} = Parser.parse(sort_src)
    assert Enum.any?(sort_book, &(&1[:kind] == :import and &1.path == "list.muro"))
    refute Enum.any?(sort_book, &(&1[:kind] == :data and &1.name == "List"))

    assert {:ok, ex} = Muro.emit_file("examples/sort.muro", Sort)
    assert ex =~ ":asc"
    assert ex =~ ":desc"
    refute ex =~ "length-ones2"
    refute ex =~ "sort-two"

    assert {:ok, book} = Parser.parse("def bad : run Nat := :asc\n")
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "Atom"
    assert msg =~ "Nat"

    src = """
    def only : run Atom := :asc
    def bad : run Π (d : Atom) → Nat :=
      λ (d : Atom) →
        match d motive (λ _ → Nat)
          | :desc => 0
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "missing branch for :asc"

    plus = """
    def bad : run Π (+ d : Atom) → Atom :=
      λ (+ d : Atom) → d
    """

    assert {:ok, book} = Parser.parse(plus)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "Data"
  end

  test "Pi and lam are keywords only at a word boundary" do
    assert {:ok, [pickle]} = Parser.parse("def Pickle : run Nat := 0\n")
    assert pickle.name == "Pickle"
    assert Check.check_sig([pickle]) == :ok

    assert {:ok, [lambda]} = Parser.parse("def lambda : run Nat := 0\n")
    assert lambda.name == "lambda"
    assert Check.check_sig([lambda]) == :ok

    src = """
    def id : run Pi (x : Nat) → Nat :=
      lam (x : Nat) → x
    """

    assert {:ok, [id]} = Parser.parse(src)
    assert {:pi, :affine, :nat, "x", :nat} = id.type
    assert {:lam, :affine, :nat, "x", {:var, "x"}} = id.body
    assert Check.check_sig([id]) == :ok
  end

  test "import names a file, and a clash or a cycle is an error" do
    dir = Path.join(System.tmp_dir!(), "muro_imp_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    File.write!(Path.join(dir, "lemma.muro"), """
    def n : run Nat := 0
    def n-zero : evidence {n ≡ 0 : Nat} := refl
    """)

    use = Path.join(dir, "use.muro")

    File.write!(use, """
    import "lemma.muro"
    def use : evidence {n ≡ 0 : Nat} := n-zero
    """)

    assert Muro.check_file(use) == :ok
    assert {:ok, src} = Muro.emit_file(use, Use)
    assert src =~ "def n"
    refute src =~ "n-zero"

    missing = Path.join(dir, "miss.muro")

    File.write!(missing, """
    import "no-such.muro"
    def z : run Nat := 0
    """)

    assert {:error, msg} = Muro.check_file(missing)
    assert msg =~ "missing file"
    assert msg =~ "no-such.muro"

    File.cp!("examples/list.muro", Path.join(dir, "list.muro"))
    again = Path.join(dir, "again.muro")

    File.write!(again, """
    import "list.muro"
    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A
    def z : run Nat := 0
    """)

    assert {:error, msg} = Muro.check_file(again)
    assert msg =~ "duplicate name List"
    assert msg =~ "again.muro"
    assert msg =~ "list.muro"

    File.write!(Path.join(dir, "a.muro"), """
    import "b.muro"
    def z : run Nat := 0
    """)

    File.write!(Path.join(dir, "b.muro"), """
    import "a.muro"
    def z : run Nat := 0
    """)

    assert {:error, msg} = Muro.check_file(Path.join(dir, "a.muro"))
    assert msg =~ "import cycle"
    assert msg =~ "a.muro"
    assert msg =~ "b.muro"

    assert {:error, msg} = Parser.parse("import \"list\n")
    assert msg =~ "unclosed string"
  end

  test "a file reached by two imports is loaded once" do
    dir = Path.join(System.tmp_dir!(), "muro_dia_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    File.write!(Path.join(dir, "base.muro"), "def one : run Nat := suc 0\n")
    File.write!(Path.join(dir, "a.muro"), "import \"base.muro\"\ndef two : run Nat := suc one\n")

    top = Path.join(dir, "top.muro")

    File.write!(top, """
    import "a.muro"
    import "base.muro"
    def four : run Nat := suc (suc (suc one))
    def four-ok : evidence {four ≡ suc (suc (suc (suc 0))) : Nat} := refl
    """)

    assert Muro.check_file(top) == :ok
    assert {:ok, src} = Muro.emit_file(top, Dia)
    assert length(Regex.scan(~r/\bdef one\b/, src)) == 1

    File.write!(
      Path.join(dir, "b.muro"),
      "import \"base.muro\"\ndef three : run Nat := suc one\n"
    )

    File.write!(Path.join(dir, "other.muro"), "def one : run Nat := 0\n")
    clash = Path.join(dir, "clash.muro")
    File.write!(clash, "import \"a.muro\"\nimport \"b.muro\"\nimport \"other.muro\"\n")

    assert {:error, msg} = Muro.check_file(clash)
    assert msg =~ "duplicate name one"
    assert msg =~ "base.muro"
    assert msg =~ "other.muro"
  end

  test "a param is supplied by the declaration of that name in the importing file" do
    dir = Path.join(System.tmp_dir!(), "muro_param_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)

    File.write!(Path.join(dir, "lib.muro"), """
    param S : spec Type
    param step : run Π (+ s : S) → S
    param P : spec Π (s : S) → Type
    param keep : evidence Π (+ s : S) → Π (p : P s) → P (step s)

    def twice : run Π (+ s : S) → S := λ (+ s : S) → step (step s)

    def keep2 : evidence Π (+ s : S) → Π (p : P s) → P (twice s) :=
      λ (+ s : S) → λ (p : P s) → keep (step s) (keep s p)
    """)

    supply = """
    def S : spec Type := Nat
    def step : run Π (+ s : Nat) → Nat := λ (+ s : Nat) → suc s
    def P : spec Π (s : Nat) → Type := λ (s : Nat) → Unit
    def keep : evidence Π (+ s : Nat) → Π (p : Unit) → Unit := λ (+ s : Nat) → λ (p : Unit) → p
    """

    top = Path.join(dir, "top.muro")
    File.write!(top, "import \"lib.muro\"\n" <> supply <> "def two : run Nat := twice 0\n")

    assert Muro.check_file(top) == :ok
    assert {:ok, src} = Muro.emit_file(top, Muro.ParamEx)
    refute src =~ "param"
    Code.eval_string(src)
    assert call("ParamEx", :two, []) == {:suc, {:suc, 0}}

    assert {:error, msg} = Muro.check_file(Path.join(dir, "lib.muro"))
    assert msg =~ "lib.muro:1:1: param S is supplied by a file that imports this one"
    assert msg =~ "param keep is supplied"

    # A library that imports one with params passes them on.
    File.write!(Path.join(dir, "mid.muro"), """
    import "lib.muro"
    def four : run Π (+ s : S) → S := λ (+ s : S) → twice (twice s)
    """)

    via = Path.join(dir, "via.muro")
    File.write!(via, "import \"mid.muro\"\n" <> supply)
    assert Muro.check_file(via) == :ok
    assert {:error, msg} = Muro.check_file(Path.join(dir, "mid.muro"))
    assert msg =~ "lib.muro:2:1: param step is supplied"

    bad = Path.join(dir, "bad.muro")

    File.write!(
      bad,
      "import \"lib.muro\"\n" <> String.replace(supply, "step : run", "step : spec")
    )

    assert {:error, msg} = Muro.check_file(bad)
    assert msg =~ "bad.muro:3:1: step is spec; the param it supplies is run"
    assert msg =~ "lib.muro:2:1: param step : run"

    File.write!(
      bad,
      "import \"lib.muro\"\n" <>
        String.replace(
          supply,
          "Π (+ s : Nat) → Nat := λ (+ s : Nat) → suc s",
          "Π (s : Nat) → Nat := λ (s : Nat) → s"
        )
    )

    assert {:error, msg} = Muro.check_file(bad)
    assert msg =~ "lib.muro:2:1: step (param) body"

    # S is abstract in the library: without the instance, + s : S is not
    # known to be copyable. With S := Stream Nat it is not, and the
    # refusal is reported at the library's line.
    File.write!(
      bad,
      "import \"lib.muro\"\n" <>
        String.replace(supply, "S : spec Type := Nat", "S : spec Type := Stream Nat")
    )

    assert {:error, msg} = Muro.check_file(bad)
    assert msg =~ ~r/lib\.muro:6:1: twice \w+: \+ requires a copyable type/

    File.write!(
      Path.join(dir, "pick.muro"),
      "param T : spec Type\nparam t0 : run T\ndef t1 : run T := t0\n"
    )

    File.write!(
      bad,
      "import \"pick.muro\"\ndata T : Type where\n  a : T\n  b : T\ndef t0 : run T := b\n"
    )

    assert Muro.check_file(bad) == :ok

    File.write!(bad, "param S : spec Type\ndef S : spec Type := Nat\n")
    assert {:error, msg} = Muro.check_file(bad)
    assert msg =~ "duplicate name S"

    assert {:ok, book} = Parser.parse("param S : spec Type\ndef n : run Nat := 0\n")
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "1:1: param S is supplied by a file that imports this one"
  end

  test "a run definition named like a Kernel function of its arity is emitted" do
    src = """
    def max : run Π (m : Nat) → Π (n : Nat) → Nat :=
      λ (m : Nat) → λ (n : Nat) →
        match m motive (λ _ → Nat)
          | 0 => n
          | suc p => (match n motive (λ _ → Nat) | 0 => suc p | suc q => suc (max p q))
    def length : run Π (n : Nat) → Nat := λ (n : Nat) → n
    def min : run Π (- k : Nat) → Π (n : Nat) → Nat := λ (- k : Nat) → λ (n : Nat) → n
    def top : run Nat := max (length (suc 0)) (suc (suc 0))
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    out = Emit.emit_module(Muro.KernelNameEx, book)
    assert out =~ "import Kernel, except: [max: 2, length: 1]"
    Code.eval_string(out)
    assert call("KernelNameEx", :top, []) == {:suc, {:suc, 0}}
    assert call("KernelNameEx", :min, [0]) == 0
  end

  test "two names with one Elixir spelling do not collide on emit" do
    src = """
    def foo-bar : run Nat := 0
    def foo_bar : run Nat := suc 0
    def answer : run Nat := foo_bar
    """

    assert {:ok, book} = Parser.parse(src)
    assert :ok = Check.check_sig(book)
    out = Emit.emit_module(Muro.Collide, book)
    assert out =~ "def foo_bar do"
    assert out =~ "def foo_bar_2 do"
    assert out =~ "foo_bar_2()"
    Code.eval_string(out)
    assert call("Collide", :answer, []) == {:suc, 0}
    assert call("Collide", :foo_bar, []) == 0
    assert call("Collide", :foo_bar_2, []) == {:suc, 0}
  end

  test "a definition named like an Elixir reserved word emits a compilable module" do
    for word <- ~w(and or not when fn do end nil true false catch rescue after else) do
      src = """
      def #{word} : run Π (a : Nat) → Nat := λ (a : Nat) → a
      def use-#{word} : run Nat := #{word} 0
      """

      assert {:ok, book} = Parser.parse(src)
      assert :ok = Check.check_sig(book)
      mod = Module.concat(Muro, "Reserved#{word}")
      out = Emit.emit_module(mod, book)
      assert out =~ "def muro_#{word}("
      Code.eval_string(out)
      assert apply(mod, :"use_#{word}", []) == 0
    end
  end

  test "a function and a pair of Data are copyable at +" do
    plus =
      "def plus : run Π (n : Nat) → Π (m : Nat) → Nat := λ (n : Nat) → λ (m : Nat) → n\n"

    # a + function parameter is applied twice, and mapped over a list
    fns =
      plus <>
        """
        data List (A : Type) : Type where
          nil  : List A
          cons : A → List A → List A
        def twice : run Π (+ f : Π (_ : Nat) → Nat) → Π (n : Nat) → Nat :=
          λ (+ f : Π (_ : Nat) → Nat) → λ (n : Nat) → f (f n)
        def map : run Π (+ f : Π (_ : Nat) → Nat) → Π (xs : List Nat) → List Nat :=
          λ (+ f : Π (_ : Nat) → Nat) → λ (xs : List Nat) →
            match xs motive (λ _ → List Nat)
              | nil => nil
              | cons x rest => cons (f x) (map f rest)
        def both : run Π (+ p : Nat × Nat) → Nat :=
          λ (+ p : Nat × Nat) → plus (fst p) (snd p)
        def two : evidence {twice (plus (suc 0)) 0 ≡ suc 0 : Nat} := refl
        """

    assert {:ok, book} = Parser.parse(fns)
    assert Check.check_sig(book) == :ok

    # a closure over a reusable variable may be passed at +
    addn =
      "def addn : run Π (n : Nat) → Π (m : Nat) → Nat := λ (n : Nat) → λ (m : Nat) → plus n m\n"

    pass = fn q ->
      plus <>
        addn <>
        """
        def twice : run Π (+ f : Π (_ : Nat) → Nat) → Π (n : Nat) → Nat :=
          λ (+ f : Π (_ : Nat) → Nat) → λ (n : Nat) → f (f n)
        def g : run Π (#{q}n : Nat) → Nat :=
          λ (#{q}n : Nat) → twice (addn n) (suc 0)
        """
    end

    assert {:ok, book} = Parser.parse(pass.("+ "))
    assert Check.check_sig(book) == :ok

    # a closure over an affine variable is refused there: copying the
    # function would copy what it captured
    assert {:ok, book} = Parser.parse(pass.(""))
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "affine variable used as reusable"

    # the same rule at a + constructor field
    field = fn q ->
      plus <>
        addn <>
        """
        data Box : Type where
          box : Π (+ f : Π (_ : Nat) → Nat) → Box
        def use : run Π (b : Box) → Nat :=
          λ (b : Box) → match b motive (λ _ → Nat) | box f => f (f (suc 0))
        def g : run Π (#{q}n : Nat) → Box := λ (#{q}n : Nat) → box (addn n)
        """
    end

    assert {:ok, book} = Parser.parse(field.("+ "))
    assert Check.check_sig(book) == :ok
    assert {:ok, book} = Parser.parse(field.(""))
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "affine variable used as reusable"

    # a stream is not copyable, at a binder, a field, or a branch
    stream = "def f : run Π (+ s : Stream Nat) → Nat := λ (+ s : Stream Nat) → head s\n"
    assert {:ok, book} = Parser.parse(stream)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "+ requires a copyable type"

    sfield = "data W : Type where\n  w : Π (+ s : Stream Nat) → W\n"
    assert {:ok, book} = Parser.parse(sfield)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "+ requires a copyable type"

    spair = "def f : run Π (+ p : Nat × Stream Nat) → Nat := λ (+ p : Nat × Stream Nat) → fst p\n"
    assert {:ok, book} = Parser.parse(spair)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "+ requires a copyable type"
  end

  test "a + binder on an unfold step must be copyable" do
    src = """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A
    def dup-stream : run Π (s : Stream Nat) → Stream (Stream Nat × Stream Nat) :=
      λ (s : Stream Nat) → unfold s (λ (+ t : Stream Nat) → ((t, t), t))
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "+ requires a copyable type"
  end

  test "a + binder on an unfold step over a Data seed still checks" do
    src = """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A
    def nats : run Stream Nat :=
      unfold 0 (λ (+ n : Nat) → (n, suc n))
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
  end

  test "the predecessor of a reusable variable is reusable" do
    plus =
      "def plus : run Π (n : Nat) → Π (m : Nat) → Nat := λ (n : Nat) → λ (m : Nat) → n\n"

    body = fn q ->
      plus <>
        """
        def f : run Π (#{q}n : Nat) → Nat :=
          λ (#{q}n : Nat) →
            match n motive (λ _ → Nat)
              | 0 => 0
              | suc p => plus p p
        """
    end

    assert {:ok, book} = Parser.parse(body.("+ "))
    assert Check.check_sig(book) == :ok

    assert {:ok, book} = Parser.parse(body.(""))
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "affine variable used twice"

    # a computed scrutinee binds an affine predecessor, whatever n is
    computed =
      plus <>
        """
        def f : run Π (+ n : Nat) → Nat :=
          λ (+ n : Nat) →
            match plus n n motive (λ _ → Nat)
              | 0 => 0
              | suc p => plus p p
        """

    assert {:ok, book} = Parser.parse(computed)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "affine variable used twice"

    # the predecessor is still a smaller argument for descent
    twice =
      """
      def double : run Π (+ n : Nat) → Nat :=
        λ (+ n : Nat) →
          match n motive (λ _ → Nat)
            | 0 => 0
            | suc p => suc (suc (double p))
      def four : evidence {double (suc (suc 0)) ≡ suc (suc (suc (suc 0))) : Nat} := refl
      """

    assert {:ok, book} = Parser.parse(twice)
    assert Check.check_sig(book) == :ok

    # a constructor may declare a reusable field, and a branch binds it so
    seed =
      plus <>
        """
        data Seed : Type where
          at : Π (+ s : Nat) → Π (+ n : Nat) → Seed
        def both : run Π (p : Seed) → Nat :=
          λ (p : Seed) →
            match p motive (λ _ → Nat)
              | at s n => plus (plus s s) (plus n n)
        """

    assert {:ok, book} = Parser.parse(seed)
    assert Check.check_sig(book) == :ok
  end

  test "uncons of a Nat is not a ν step" do
    src = "def bad : run Nat := uncons 0\n"
    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "ν"
  end

  test "CSHRL checks in every environment, and its agents run" do
    assert {:error, msg} = Muro.check_file("examples/cshrl/lib/core.muro")
    assert msg =~ "is supplied by a file that imports this one"

    nat = fn
      _f, 0 -> 0
      f, {:suc, n} -> 1 + f.(f, n)
    end

    load = fn path, mod ->
      assert Muro.check_file(path) == :ok
      assert {:ok, src} = Muro.emit_file(path, Module.concat(Muro, mod))
      refute src =~ "CoindHomo"
      Code.eval_string(src)
    end

    take = fn mod, fun, start, k ->
      call(mod, fun, [start])
      |> Enum.take(k)
      |> Enum.map(fn {a, r} -> {a, nat.(nat, r)} end)
    end

    load.("examples/cshrl/envs/two_state.muro", "CshrlTwo")
    assert take.("CshrlTwo", :episode, :start, 3) == [go: 1, go: 1, go: 1]

    load.("examples/cshrl/envs/binary_sacrifice.muro", "CshrlSac")
    assert take.("CshrlSac", :episode, :start, 3) == [go_trap: 1, go_paradise: 0, go_paradise: 0]

    assert take.("CshrlSac", :successor_episode, :start, 3) ==
             [go_paradise: 0, go_paradise: 1, go_paradise: 1]

    load.("examples/cshrl/envs/skill_investment.muro", "CshrlSkill")
    assert take.("CshrlSkill", :episode, :novice, 3) == [work: 1, work: 1, work: 1]

    assert take.("CshrlSkill", :successor_episode, :novice, 5) ==
             [train: 0, train: 0, train: 0, work: 5, work: 5]

    assert call("CshrlSkill", :value, [:novice]) |> Enum.take(5) |> Enum.map(&nat.(nat, &1)) ==
             [1, 2, 3, 5, 5]

    assert Muro.check_file("examples/cshrl/envs/optimal.muro") == :ok
  end

  # The module exists only after Code.eval_string, so a literal remote call warns.
  defp call(mod, fun, args), do: apply(Module.concat(Muro, mod), fun, args)
end
