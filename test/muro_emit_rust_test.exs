defmodule Muro.EmitRustTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "half and plus match the Nat NIF" do
    dir = tmp_dir()
    File.cp!("examples/half_ok.muro", Path.join(dir, "half_rs.muro"))
    source = File.read!(emit_rust!(dir, "half_rs"))
    assert source =~ "pub fn half(n: Nat) -> Nat"
    assert source =~ "pub fn plus(n: Nat, m: Nat) -> Nat"
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
            let h = half_rs::muro_to_u64(&half_rs::half(half_rs::muro_from_u64(4)));
            let p = half_rs::muro_to_u64(&half_rs::plus(
                half_rs::muro_from_u64(2),
                half_rs::muro_from_u64(3),
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
            let z = streams::zeros();
            let zh = streams::muro_to_u64(&streams::hd(z.clone()));
            let zs = streams::muro_to_u64(&streams::second(z));
            let ns = streams::natsFrom(streams::muro_from_u64(0));
            let nh = streams::muro_to_u64(&streams::hd(ns.clone()));
            let n2 = streams::muro_to_u64(&streams::second(ns));
            let pr = streams::prefix(streams::muro_from_u64(2));
            let ph = streams::muro_to_u64(&streams::hd(pr));
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
            let n = list::muro_to_u64(&list::length(list::ones2()));
            let a = sorted::muro_to_u64(&sorted::first());
            let b = sorted::muro_to_u64(&sorted::second());
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
            let z = kw::muro_to_u64(&kw::zero());
            let o = kw::muro_to_u64(&kw::one());
            let id = apply_lam::muro_to_u64(&apply_lam::id(apply_lam::muro_from_u64(3)));
            let snd = apply_lam::muro_to_u64(&apply_lam::snd(
                apply_lam::muro_from_u64(1),
                apply_lam::muro_from_u64(2),
            ));
            let keep = apply_lam::muro_to_u64(&apply_lam::keep(apply_lam::muro_from_u64(5)));
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
    assert source =~ "pub fn step0() -> Nat"
    assert source =~ "fn step0_2("

    out =
      run_rust!(
        dir,
        """
        fn main() {
            let n = step0::muro_to_u64(&step0::step0());
            let z = step0::hd(step0::zeros());
            println!("{} {}", n, step0::muro_to_u64(&z));
        }
        """,
        ["step0"]
      )

    assert out == "1 0\n"
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
            let p = shadow::muro_to_u64(&shadow::pick(
                shadow::muro_from_u64(1),
                shadow::muro_from_u64(2),
            ));
            let t = shadow::muro_to_u64(&shadow::third(
                shadow::muro_from_u64(1),
                shadow::muro_from_u64(2),
                shadow::muro_from_u64(3),
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
            let two = alias_nat::muro_to_u64(&alias_nat::muro_reveal(alias_nat::two()));
            let n = alias_nat::muro_to_u64(&alias_nat::muro_reveal(alias_nat::inc(
                alias_nat::muro_erase(alias_nat::muro_from_u64(4)),
            )));
            println!("{two} {n}");
        }
        """,
        ["alias_nat"]
      )

    assert out == "2 5\n"
  end

  test "run internal is private and the examples that C accepts compile" do
    dir = tmp_dir()
    File.cp!("examples/internal_ok.muro", Path.join(dir, "internal_ok.muro"))
    source = File.read!(emit_rust!(dir, "internal_ok"))
    assert source =~ "pub fn inc(n: Nat) -> Nat"
    assert source =~ "fn step(n: Nat) -> Nat"
    refute source =~ "pub fn step"

    out =
      run_rust!(
        dir,
        """
        fn main() {
            println!("{}", internal_ok::muro_to_u64(&internal_ok::inc(internal_ok::muro_from_u64(4))));
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
