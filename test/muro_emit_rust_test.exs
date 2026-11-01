defmodule Muro.EmitRustTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "half and plus match the Nat NIF" do
    dir = tmp_dir()
    File.cp!("examples/half_ok.muro", Path.join(dir, "half_rs.muro"))
    source = File.read!(emit_rust!(dir, "half_rs"))
    assert source =~ "pub fn half(n: muro__Nat) -> muro__Nat"
    assert source =~ "pub fn plus(n: muro__Nat, m: muro__Nat) -> muro__Nat"
    refute source =~ "IsEven"
    refute source =~ "fn half_ok"

    capture_io(fn ->
      Mix.Tasks.Muro.Emit.run([Path.join(dir, "half_rs.muro"), "--backend", "c"])
    end)

    on_exit(fn ->
      :code.delete(:"Elixir.HalfRs")
      :code.purge(:"Elixir.HalfRs")
    end)

    Code.compile_file(Path.join(dir, "half_rs.ex"))
    half = fn n -> apply(:"Elixir.HalfRs", :half, [n]) end
    plus = fn n, m -> apply(:"Elixir.HalfRs", :plus, [n, m]) end

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let h = half_rs::muro__to_u64(&half_rs::half(half_rs::muro__from_u64(4)));
            let p = half_rs::muro__to_u64(&half_rs::plus(
                half_rs::muro__from_u64(2),
                half_rs::muro__from_u64(3),
            ));
            println!("{h} {p}");
        }
        """,
        ["half_rs"]
      )

    assert half.(4) == 2
    assert plus.(2, 3) == 5
    assert out == "#{half.(4)} #{plus.(2, 3)}\n"
  end

  test "a stream head, the next element, and a captured value are Nat" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "streams.muro"), """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def zeros : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))

    def natsFrom : run Π (n : Nat) → Stream Nat :=
      λ (n : Nat) →
        unfold n (λ (+ k : Nat) → (k, suc k))

    def prefix : run Π (n : Nat) → Stream Nat :=
      λ (n : Nat) →
        unfold 0 (λ (_ : Nat) → (n, 0))

    def hd : run Π (s : Stream Nat) → Nat :=
      λ (s : Stream Nat) → head s

    def second : run Π (s : Stream Nat) → Nat :=
      λ (s : Stream Nat) → head (tail s)
    """)

    emit_rust!(dir, "streams")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let z = streams::zzeros();
            let zh = streams::muro__to_u64(&streams::hd(z.clone()));
            let zs = streams::muro__to_u64(&streams::second(z));
            let ns = streams::natsFrom(streams::muro__from_u64(0));
            let nh = streams::muro__to_u64(&streams::hd(ns.clone()));
            let n2 = streams::muro__to_u64(&streams::second(ns));
            let pr = streams::prefix(streams::muro__from_u64(2));
            let ph = streams::muro__to_u64(&streams::hd(pr));
            println!("{zh} {zs} {nh} {n2} {ph}");
        }
        """,
        ["streams"]
      )

    assert out == "0 0 0 1 2\n"
  end

  test "length of two cons cells is 2 and sort orders them" do
    dir = tmp_dir()
    File.cp!("examples/list.muro", Path.join(dir, "list.muro"))
    File.cp!("examples/sort.muro", Path.join(dir, "sort.muro"))

    File.write!(Path.join(dir, "sorted.muro"), """
    import "sort.muro"

    def first : run Nat :=
      match sort :asc (cons (suc 0) (cons 0 nil)) motive (λ _ → Nat)
        | nil => 0
        | cons x _ => x

    def second : run Nat :=
      match sort :asc (cons (suc 0) (cons 0 nil)) motive (λ _ → Nat)
        | nil => 0
        | cons _ xs =>
            match xs motive (λ _ → Nat)
              | nil => 0
              | cons y _ => y
    """)

    emit_rust!(dir, "list")
    emit_rust!(dir, "sort")
    emit_rust!(dir, "sorted")
    rustc_lib!(dir, "sort")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let n = list::muro__to_u64(&list::length(list::ones2()));
            let a = sorted::muro__to_u64(&sorted::first());
            let b = sorted::muro__to_u64(&sorted::second());
            println!("{n} {a} {b}");
        }
        """,
        ["list", "sorted"]
      )

    assert out == "2 0 1\n"
  end

  test "a keyword constructor and an applied lambda run" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "kw.muro"), """
    data Bool : Type where
      true : Bool
      false : Bool

    def pick : run Π (b : Bool) → Nat :=
      λ (b : Bool) →
        match b motive (λ _ → Nat)
          | true => 0
          | false => suc 0

    def zero : run Nat := pick true
    def one : run Nat := pick false
    """)

    File.write!(Path.join(dir, "apply_lam.muro"), """
    def id : run Π (n : Nat) → Nat :=
      λ (n : Nat) → (λ (m : Nat) → suc m) n

    def snd : run Π (n : Nat) → Π (m : Nat) → Nat :=
      λ (n : Nat) → λ (m : Nat) → ((λ (x : Nat) → λ (y : Nat) → y) n) m

    def keep : run Π (n : Nat) → Nat :=
      λ (n : Nat) → (λ (- k : Nat) → n) 0
    """)

    emit_rust!(dir, "kw")
    emit_rust!(dir, "apply_lam")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let z = kw::muro__to_u64(&kw::zzero());
            let o = kw::muro__to_u64(&kw::one());
            let id = apply_lam::muro__to_u64(&apply_lam::id(apply_lam::muro__from_u64(3)));
            let snd = apply_lam::muro__to_u64(&apply_lam::snd(
                apply_lam::muro__from_u64(1),
                apply_lam::muro__from_u64(2),
            ));
            let keep = apply_lam::muro__to_u64(&apply_lam::keep(apply_lam::muro__from_u64(5)));
            println!("{z} {o} {id} {snd} {keep}");
        }
        """,
        ["kw", "apply_lam"]
      )

    assert out == "0 1 4 2 5\n"
  end

  test "a source run named step0 stays a Nat beside the unfold step" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "step0.muro"), """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def step0 : run Nat := suc 0

    def zeros : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))

    def hd : run Π (s : Stream Nat) → Nat :=
      λ (s : Stream Nat) → head s
    """)

    source = File.read!(emit_rust!(dir, "step0"))
    assert source =~ "pub fn step0() -> muro__Nat"
    assert source =~ "fn muro__step_0("
    refute source =~ "fn step0_2("

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let n = step0::muro__to_u64(&step0::step0());
            let z = step0::hd(step0::zzeros());
            println!("{} {}", n, step0::muro__to_u64(&z));
        }
        """,
        ["step0"]
      )

    assert out == "1 0\n"
  end

  test "an unfold step stays apart from a source run with the same binders" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "clash.muro"), """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def zeros : run Stream Nat :=
      unfold 0 (λ (n : Nat) → (0, n))

    def step0 : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc n

    def hd : run Π (s : Stream Nat) → Nat :=
      λ (s : Stream Nat) → head s

    def muro_step_0 : run Nat := suc (suc 0)

    def id : run Π (muro_step_0 : Nat) → Nat :=
      λ (muro_step_0 : Nat) → muro_step_0
    """)

    source = File.read!(emit_rust!(dir, "clash"))
    assert source =~ "pub fn step0(n: muro__Nat) -> muro__Nat"
    assert source =~ "fn muro__step_0("
    assert source =~ "pub fn murozustepzu0() -> muro__Nat"
    refute source =~ "fn step0_2("

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let n = clash::muro__to_u64(&clash::step0(clash::muro__from_u64(1)));
            let z = clash::muro__to_u64(&clash::hd(clash::zzeros()));
            let s = clash::muro__to_u64(&clash::murozustepzu0());
            let v = clash::muro__to_u64(&clash::id(clash::muro__from_u64(3)));
            println!("{n} {z} {s} {v}");
        }
        """,
        ["clash"]
      )

    assert out == "2 0 2 3\n"
  end

  test "a spec alias keeps the argument layout when a lambda is applied" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "alias_apply.muro"), """
    def R : spec Type := Nat
    def P : spec Type := Nat × Nat

    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def S : spec Type := Stream Nat

    def zeros : run Stream Nat :=
      unfold 0 (λ (n : Nat) → (0, n))

    data Box : Type where
      mk : Π (- e : Nat) → Nat → Box

    def one : run Nat := (λ (r : R) → suc r) 0
    def three : run Nat := (λ (r : R) → suc r) (suc (suc 0))
    def right : run Nat := (λ (p : P) → let (a, b) = p in b) (0, suc 0)
    def hd0 : run Nat := (λ (s : S) → head s) zeros

    def boxed : run Box := mk (suc 0) (suc (suc 0))

    def live : run Nat :=
      match boxed motive (λ _ → Nat)
        | mk _ n => n
    """)

    source = File.read!(emit_rust!(dir, "alias_apply"))
    assert source =~ "let r = muro__zero();"
    assert source =~ "let zu = muro__erase(());"
    refute source =~ "let r = muro__erase(());"

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let one = alias_apply::muro__to_u64(&alias_apply::one());
            let three = alias_apply::muro__to_u64(&alias_apply::three());
            let right = alias_apply::muro__to_u64(&alias_apply::right());
            let hd0 = alias_apply::muro__to_u64(&alias_apply::hd0());
            let live = alias_apply::muro__to_u64(&alias_apply::live());
            println!("{one} {three} {right} {hd0} {live}");
        }
        """,
        ["alias_apply"]
      )

    assert out == "1 3 1 0 2\n"
  end

  test "a shadowed parameter resolves to the inner binding" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "shadow.muro"), """
    def pick : run Π (x : Nat) → Π (x : Nat) → Nat :=
      λ (x : Nat) → λ (x : Nat) → x

    def third : run Π (x : Nat) → Π (y : Nat) → Π (x : Nat) → Nat :=
      λ (x : Nat) → λ (y : Nat) → λ (x : Nat) → x
    """)

    emit_rust!(dir, "shadow")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let p = shadow::muro__to_u64(&shadow::pick(
                shadow::muro__from_u64(1),
                shadow::muro__from_u64(2),
            ));
            let t = shadow::muro__to_u64(&shadow::third(
                shadow::muro__from_u64(1),
                shadow::muro__from_u64(2),
                shadow::muro__from_u64(3),
            ));
            println!("{p} {t}");
        }
        """,
        ["shadow"]
      )

    assert out == "2 3\n"
  end

  test "suc reveals an argument whose type is an alias of Nat" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "alias_nat.muro"), """
    def R : spec Type := Nat
    def inc : run Π (r : R) → R := λ (r : R) → suc r
    def two : run R := inc (inc 0)
    """)

    emit_rust!(dir, "alias_nat")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let two = alias_nat::muro__to_u64(&alias_nat::muro__reveal(alias_nat::two()));
            let n = alias_nat::muro__to_u64(&alias_nat::muro__reveal(alias_nat::inc(
                alias_nat::muro__erase(alias_nat::muro__from_u64(4)),
            )));
            println!("{two} {n}");
        }
        """,
        ["alias_nat"]
      )

    assert out == "2 5\n"
  end

  test "swap reveals a pair whose type is an alias" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "alias_pair.muro"), """
    def R : spec Type := Nat
    def Pair : spec Type := Nat × R
    def swap : run Π (p : Pair) → Pair := λ (p : Pair) → let (a, b) = p in (b, a)
    def left : run Nat := let (a, b) = swap (0, suc 0) in a
    def right : run Nat := let (a, b) = swap (0, suc 0) in b
    """)

    emit_rust!(dir, "alias_pair")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let fst = alias_pair::muro__to_u64(&alias_pair::left());
            let snd = alias_pair::muro__to_u64(&alias_pair::right());
            println!("{fst} {snd}");
        }
        """,
        ["alias_pair"]
      )

    assert out == "1 0\n"
  end

  test "a stream alias and a joined stream are read as streams" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "alias_stream.muro"), """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def S : spec Type := Stream Nat

    def zeros : run S :=
      unfold 0 (λ (_ : Nat) → (0, 0))

    def hd : run Π (s : S) → Nat :=
      λ (s : S) → head s

    def nats : run Π (n : Nat) → S :=
      λ (n : Nat) → unfold n (λ (+ k : Nat) → (k, suc k))

    def n1 : run Nat := head (tail (nats 0))

    data Bool : Type where
      true : Bool
      false : Bool

    def pick : run Π (b : Bool) → Nat :=
      λ (b : Bool) →
        head (
          match b motive (λ _ → Stream Nat)
            | true => unfold 0 (λ (_ : Nat) → (0, 0))
            | false => unfold tt (λ (_ : Unit) → (suc 0, tt))
        )

    def fromTrue : run Nat := pick true
    def fromFalse : run Nat := pick false
    """)

    emit_rust!(dir, "alias_stream")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let z = alias_stream::muro__to_u64(&alias_stream::hd(alias_stream::zzeros()));
            let n = alias_stream::muro__to_u64(&alias_stream::n1());
            let t = alias_stream::muro__to_u64(&alias_stream::fromTrue());
            let f = alias_stream::muro__to_u64(&alias_stream::fromFalse());
            println!("{z} {n} {t} {f}");
        }
        """,
        ["alias_stream"]
      )

    assert out == "0 1 0 1\n"
  end

  test "a Nat match on an alias reveals the pointer" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "alias_match.muro"), """
    def R : spec Type := Nat

    def pred : run Π (r : R) → R :=
      λ (r : R) →
        match r motive (λ _ → R)
          | 0 => 0
          | suc p => p

    def one : run R := pred (suc (suc 0))
    """)

    emit_rust!(dir, "alias_match")

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let n = alias_match::muro__to_u64(&alias_match::muro__reveal(alias_match::one()));
            println!("{n}");
        }
        """,
        ["alias_match"]
      )

    assert out == "1\n"
  end

  test "run internal is private and the examples that C accepts compile" do
    dir = tmp_dir()
    File.cp!("examples/internal_ok.muro", Path.join(dir, "internal_ok.muro"))
    source = File.read!(emit_rust!(dir, "internal_ok"))
    assert source =~ "pub fn inc(n: muro__Nat) -> muro__Nat"
    assert source =~ "fn step(n: muro__Nat) -> muro__Nat"
    refute source =~ "pub fn step"

    out =
      run_rust!(
        dir,
        """
        fn main() {
            println!("{}", internal_ok::muro__to_u64(&internal_ok::inc(internal_ok::muro__from_u64(4))));
        }
        """,
        ["internal_ok"]
      )

    assert out == "5\n"

    for name <- ~w(nats zeros always) do
      File.cp!("examples/#{name}.muro", Path.join(dir, "#{name}.muro"))
      emit_rust!(dir, name)
      rustc_lib!(dir, name)
    end
  end

  test "a tensor and a bare lambda are refused before a file is written" do
    dir = tmp_dir()
    nx = Path.join(dir, "nx_add.muro")
    File.cp!("examples/nx_add.muro", nx)

    assert_raise Mix.Error, ~r/c:machine/, fn ->
      Mix.Tasks.Muro.Emit.run([nx, "--backend", "rust"])
    end

    refute File.exists?(Path.join(dir, "nx_add.rs"))

    lam = Path.join(dir, "lam.muro")

    File.write!(lam, """
    def bad : run Π (f : Π (x : Nat) → Nat) → Nat :=
      λ (f : Π (x : Nat) → Nat) → f 0
    """)

    assert_raise Mix.Error, ~r/c:lambda/, fn ->
      Mix.Tasks.Muro.Emit.run([lam, "--backend", "rust"])
    end

    refute File.exists?(Path.join(dir, "lam.rs"))
  end

  test "muro_step, muro-step, and three unfolds are different functions" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "steps.muro"), """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def s0 : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))

    def s1 : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (suc 0, 0))

    def s2 : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (suc (suc 0), 0))

    def hd : run Π (s : Stream Nat) → Nat :=
      λ (s : Stream Nat) → head s

    def muro_step : run Nat := 0
    def muro-step : run Nat := suc 0
    """)

    source = File.read!(emit_rust!(dir, "steps"))
    bare = Muro.Emit.Rust.source_id("muro_step")
    dashed = Muro.Emit.Rust.source_id("muro-step")
    steps = step_fns(source)
    assert bare != dashed
    refute String.contains?(bare, "__")
    refute String.contains?(dashed, "__")
    assert length(steps) == 3
    refute bare in steps
    refute dashed in steps

    out =
      run_rust!(
        dir,
        """
        fn main() {
            assert_eq!(steps::muro__to_u64(&steps::#{bare}()), 0);
            assert_eq!(steps::muro__to_u64(&steps::#{dashed}()), 1);
            assert_eq!(steps::muro__to_u64(&steps::hd(steps::s0())), 0);
            assert_eq!(steps::muro__to_u64(&steps::hd(steps::s1())), 1);
            assert_eq!(steps::muro__to_u64(&steps::hd(steps::s2())), 2);
        }
        """,
        ["steps"]
      )

    assert out == ""
  end

  test "a-b, a_b, and a_b_2 are three functions" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "inj.muro"), """
    def a-b : run Nat := 0
    def a_b : run Nat := suc 0
    def a_b_2 : run Nat := suc (suc 0)
    def call : run Nat := a_b
    """)

    source = File.read!(emit_rust!(dir, "inj"))
    [ab, a_b, a_b_2] = ids = Enum.map(~w(a-b a_b a_b_2), &Muro.Emit.Rust.source_id/1)
    assert length(Enum.uniq(ids)) == 3
    Enum.each(ids, fn id -> refute String.contains?(id, "__") end)
    Enum.each(ids, fn id -> assert source =~ "pub fn #{id}(" end)

    out =
      run_rust!(
        dir,
        """
        fn main() {
            assert_eq!(inj::muro__to_u64(&inj::#{ab}()), 0);
            assert_eq!(inj::muro__to_u64(&inj::#{a_b}()), 1);
            assert_eq!(inj::muro__to_u64(&inj::#{a_b_2}()), 2);
            assert_eq!(inj::muro__to_u64(&inj::call()), 1);
        }
        """,
        ["inj"]
      )

    assert out == ""
  end

  test "a source run spelled like each generated name stays apart from it" do
    dir = tmp_dir()
    samples = Enum.uniq(Muro.Emit.Rust.generated_samples())
    File.write!(Path.join(dir, "forms.muro"), forms_book(samples))
    source = File.read!(emit_rust!(dir, "forms"))
    assert source =~ "fn muro__step_0("

    checks =
      samples
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {name, i} ->
        id = Muro.Emit.Rust.source_id(name)
        refute id == name
        refute String.contains?(id, "__")
        assert source =~ "pub fn #{id}("
        "assert_eq!(forms::muro__to_u64(&forms::#{id}()), #{i});"
      end)

    out =
      run_rust!(
        dir,
        """
        fn main() {
            assert_eq!(forms::muro__to_u64(&forms::muro__from_u64(4)), 4);
            assert_eq!(forms::muro__to_u64(&forms::hd(forms::flow())), 0);
        #{checks}
        }
        """,
        ["forms"]
      )

    assert out == ""
  end

  test "a binder is claimed against type names visible in its scope" do
    dir = tmp_dir()

    File.write!(Path.join(dir, "hide.muro"), """
    data Box : Type where
      mk : Π (Box : Nat) → R

    def R : spec Type := Box

    def pack : run Π (n : Nat) → Box :=
      λ (n : Nat) → mk n

    def wrap : run Π (Box : Nat) → Nat :=
      λ (Box : Nat) → suc Box

    def nest : run Π (n : Nat) → Nat :=
      λ (n : Nat) → (λ (Box : Nat) → Box) n

    def held : run Π (n : Nat) → Nat :=
      λ (n : Nat) →
        match (pack n) motive (λ _ → Nat)
          | mk Box => Box

    def opened : run Nat :=
      let (Box, k) = (suc 0, suc (suc 0)) in Box

    def answer : run Nat :=
      match (pack (suc (suc 0))) motive (λ _ → Nat)
        | mk k => k

    def nested : run Nat := nest (suc (suc (suc 0)))
    def bumped : run Nat := wrap (suc 0)
    def one : run Nat := held (suc 0)
    """)

    source = File.read!(emit_rust!(dir, "hide"))
    assert source =~ "pub struct Box("
    assert source =~ "fn mk(muro__a_0: muro__Nat) -> Box"
    assert source =~ "pub fn wrap(Box_2: muro__Nat) -> muro__Nat"
    assert source =~ "let Box_0 = n.clone();"
    assert source =~ "muro__node_Box::mk(Box_0) => Box_0.clone()"
    refute source =~ "pub fn wrap(Box:"

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let answer = hide::muro__to_u64(&hide::answer());
            let nested = hide::muro__to_u64(&hide::nested());
            let one = hide::muro__to_u64(&hide::one());
            let opened = hide::muro__to_u64(&hide::opened());
            let bumped = hide::muro__to_u64(&hide::bumped());
            println!("{answer} {nested} {one} {opened} {bumped}");
        }
        """,
        ["hide"]
      )

    assert out == "2 3 1 1 2\n"
  end

  defp forms_book(samples) do
    runs =
      samples
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {name, i} ->
        "def #{name} : run Nat := #{peano(i)}"
      end)

    """
    ν Stream (A : Type) : Type where
      uncons : Stream A → A × Stream A

    def flow : run Stream Nat :=
      unfold 0 (λ (_ : Nat) → (0, 0))

    def hd : run Π (s : Stream Nat) → Nat :=
      λ (s : Stream Nat) → head s

    #{runs}
    """
  end

  defp peano(0), do: "0"
  defp peano(n), do: "suc (" <> peano(n - 1) <> ")"

  defp step_fns(source) do
    ~r/fn (muro__step_\d+)\(/
    |> Regex.scan(source)
    |> Enum.map(fn [_, name] -> name end)
    |> Enum.uniq()
  end

  defp emit_rust!(dir, name) do
    path = Path.join(dir, "#{name}.muro")
    out = capture_io(fn -> Mix.Tasks.Muro.Emit.run([path, "--backend", "rust"]) end)
    rs = Path.join(dir, "#{name}.rs")
    assert out =~ rs
    assert File.regular?(rs)
    rs
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_rs_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp rustc_bin do
    path =
      System.find_executable("rustc") ||
        Path.join(System.user_home!(), ".cargo/bin/rustc")

    assert File.regular?(path), "rustc not found"
    path
  end

  defp rustc_lib!(dir, name) do
    {out, status} =
      System.cmd(
        rustc_bin(),
        [
          "--edition",
          "2021",
          "--crate-type",
          "lib",
          "--crate-name",
          name,
          "#{name}.rs",
          "-o",
          "lib#{name}.rlib"
        ],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
    refute out =~ "warning:", out
  end

  defp run_rust!(dir, main, crates) do
    File.write!(Path.join(dir, "main.rs"), main)
    Enum.each(crates, &rustc_lib!(dir, &1))

    args =
      ["--edition", "2021", "main.rs", "-o", "main"] ++
        Enum.flat_map(crates, fn name -> ["--extern", "#{name}=lib#{name}.rlib"] end)

    {compiled, status} =
      System.cmd(rustc_bin(), args, cd: dir, stderr_to_stdout: true)

    assert status == 0, compiled
    refute compiled =~ "warning:", compiled

    {ran, status} = System.cmd(Path.join(dir, "main"), [], stderr_to_stdout: true)
    assert status == 0, ran
    ran
  end
end
