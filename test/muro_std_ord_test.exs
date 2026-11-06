defmodule Muro.StdOrdTest do
  use ExUnit.Case, async: true

  # A strict walk of two equal unary Nats of this size overflows the C
  # stack. Elixir would tail-call it, so the Elixir check counts reductions.
  # Rust drops a Nat recursively, and that drop overflows before the walk
  # does, so the Rust nat stays under the drop limit. The emitted Rust
  # match is what shows the second comparison sits in the eq arm.
  @elixir_huge 200_000
  @c_huge 200_000
  @rust_huge 40_000
  @fast_us 100_000
  @fast_reds 5_000

  test "lexicographic compare is correct and skips unequal tails" do
    dir = tmp()
    path = Path.join(dir, "lex_probe.muro")
    File.write!(path, probe())
    assert Muro.check_file(path) == :ok

    elixir_fast!(path)
    c_fast!(dir, path)
    rust_fast!(dir, path)
  end

  defp elixir_fast!(path) do
    mod = Module.concat(LexProbe, "N#{System.unique_integer([:positive])}")
    {:ok, source} = Muro.emit_file(path, mod)
    refute source =~ "lex_step(compare("
    assert source =~ ":eq -> compare("
    [{^mod, _bin}] = Code.compile_string(source)
    lex = String.to_atom(Muro.Emit.elixir_base("lex-tag"))

    assert apply(mod, lex, [n(0), n(0), n(0), n(0)]) == n(1)
    assert apply(mod, lex, [n(0), n(1), n(0), n(0)]) == n(2)
    assert apply(mod, lex, [n(0), n(0), n(0), n(1)]) == n(0)
    assert apply(mod, lex, [n(1), n(0), n(0), n(5)]) == n(2)
    assert apply(mod, lex, [n(2), n(0), n(2), n(1)]) == n(0)
    assert apply(mod, lex, [n(2), n(1), n(2), n(1)]) == n(1)

    left = n(@elixir_huge)
    right = n(@elixir_huge)
    before = reductions()
    {us, tag} = :timer.tc(fn -> apply(mod, lex, [n(0), left, n(1), right]) end)
    spent = reductions() - before
    assert tag == n(0)
    assert us < @fast_us, "elixir walked the tails in #{us} us"
    assert spent < @fast_reds, "elixir spent #{spent} reductions on unequal heads"
  end

  defp c_fast!(dir, path) do
    assert {:ok, [header, source]} = Muro.emit_c(path, nif: false)
    c = File.read!(source)
    # lex-step is evidence. The second comparison is the eq arm of compare-lex.
    refute c =~ "#{Muro.Emit.C.source_id("lex-step")}(compare("
    assert c =~ "compare(b, d);"
    assert File.regular?(header)

    File.write!(Path.join(dir, "main.c"), c_main())

    {compiled, status} =
      System.cmd(
        "cc",
        ["-O0", "-fno-optimize-sibling-calls", "main.c", "lex_probe.c", "-o", "lex_bin"],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, compiled
    {out, status} = System.cmd(Path.join(dir, "lex_bin"), [], stderr_to_stdout: true)
    assert status == 0, out
    assert out =~ "huge"
  end

  defp rust_fast!(dir, path) do
    assert {:ok, [rs]} = Muro.emit_rust(path)
    rust = File.read!(rs)
    node = Muro.Emit.Name.gen("node_#{Muro.Emit.Rust.source_id("Ordering")}")
    eq = Muro.Emit.Rust.source_id("eq")
    refute rust =~ "#{Muro.Emit.Rust.source_id("lex-step")}(compare("
    assert rust =~ "#{node}::#{eq} => compare(b.clone(), d.clone())"

    File.write!(Path.join(dir, "main.rs"), rust_main())

    {lib_out, status} =
      System.cmd(
        rustc_bin(),
        [
          "--edition",
          "2021",
          "-C",
          "opt-level=0",
          "--crate-type",
          "lib",
          "--crate-name",
          "lex_probe",
          "lex_probe.rs",
          "-o",
          "liblex_probe.rlib"
        ],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, lib_out
    refute lib_out =~ "warning:", lib_out

    {bin_out, status} =
      System.cmd(
        rustc_bin(),
        [
          "--edition",
          "2021",
          "-C",
          "opt-level=0",
          "main.rs",
          "-o",
          "lex_rs",
          "--extern",
          "lex_probe=liblex_probe.rlib"
        ],
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, bin_out
    refute bin_out =~ "warning:", bin_out

    {out, status} = System.cmd(Path.join(dir, "lex_rs"), [], stderr_to_stdout: true)
    assert status == 0, out
    assert out =~ "huge"
  end

  defp probe do
    """
    import "std:ord.muro"

    def lex-tag : run Π (a : Nat) → Π (b : Nat) → Π (c : Nat) → Π (d : Nat) → Nat :=
      λ (a : Nat) → λ (b : Nat) → λ (c : Nat) → λ (d : Nat) →
        match (compare-lex (a, b) (c, d)) motive (λ _ → Nat)
          | lt => 0
          | eq => suc 0
          | gt => suc (suc 0)
    """
  end

  defp n(0), do: 0
  defp n(k) when k > 0, do: Enum.reduce(1..k, 0, fn _, acc -> {:suc, acc} end)

  defp reductions do
    {:reductions, n} = Process.info(self(), :reductions)
    n
  end

  defp c_main do
    nat = Muro.Emit.Name.gen("nat")
    tag = Muro.Emit.Name.gen("field_tag")
    suc = Muro.Emit.Name.gen("field_suc")
    fun = Muro.Emit.C.source_id("lex-tag")

    """
    #include "lex_probe.h"

    #include <stdio.h>
    #include <stdlib.h>
    #include <time.h>

    static #{nat} *from_u32(unsigned n) {
      #{nat} *p = malloc(sizeof *p);
      if (p == 0) abort();
      p->#{tag} = 0;
      p->#{suc} = 0;
      while (n > 0) {
        #{nat} *s = malloc(sizeof *s);
        if (s == 0) abort();
        s->#{tag} = 1;
        s->#{suc} = p;
        p = s;
        n--;
      }
      return p;
    }

    static unsigned to_u(#{nat} *n) {
      unsigned k = 0;
      while (n->#{tag} == 1) {
        n = n->#{suc};
        k++;
      }
      return k;
    }

    static int expect(const char *name, unsigned got, unsigned want) {
      if (got != want) {
        fprintf(stderr, "%s: got %u want %u\\n", name, got, want);
        return 1;
      }
      return 0;
    }

    int main(void) {
      #{nat} *z = from_u32(0);
      #{nat} *one = from_u32(1);
      #{nat} *two = from_u32(2);
      #{nat} *five = from_u32(5);
      int bad = 0;
      bad |= expect("eq", to_u(#{fun}(z, z, z, z)), 1);
      bad |= expect("gt-second", to_u(#{fun}(z, one, z, z)), 2);
      bad |= expect("lt-second", to_u(#{fun}(z, z, z, one)), 0);
      bad |= expect("first-gt", to_u(#{fun}(one, z, z, five)), 2);
      bad |= expect("eq-then-lt", to_u(#{fun}(two, z, two, one)), 0);
      bad |= expect("eq-eq", to_u(#{fun}(two, one, two, one)), 1);

      #{nat} *h1 = from_u32(#{@c_huge});
      #{nat} *h2 = from_u32(#{@c_huge});
      struct timespec a, b;
      clock_gettime(CLOCK_MONOTONIC, &a);
      unsigned tag = to_u(#{fun}(z, h1, one, h2));
      clock_gettime(CLOCK_MONOTONIC, &b);
      double ms = (b.tv_sec - a.tv_sec) * 1000.0 + (b.tv_nsec - a.tv_nsec) / 1e6;
      bad |= expect("huge-lt", tag, 0);
      if (ms > 1000.0) {
        fprintf(stderr, "huge compare took %.3f ms\\n", ms);
        bad = 1;
      }
      printf("huge %.3f ms\\n", ms);
      return bad == 0 ? 0 : 1;
    }
    """
  end

  defp rust_main do
    from = Muro.Emit.Name.gen("from_u64")
    to = Muro.Emit.Name.gen("to_u64")
    fun = Muro.Emit.Rust.source_id("lex-tag")

    """
    use std::process::exit;
    use std::time::Instant;

    fn tag(a: u64, b: u64, c: u64, d: u64) -> u64 {
        lex_probe::#{to}(&lex_probe::#{fun}(
            lex_probe::#{from}(a),
            lex_probe::#{from}(b),
            lex_probe::#{from}(c),
            lex_probe::#{from}(d),
        ))
    }

    fn expect(name: &str, got: u64, want: u64) -> bool {
        if got != want {
            eprintln!("{name}: got {got} want {want}");
            false
        } else {
            true
        }
    }

    fn main() {
        let mut ok = true;
        ok &= expect("eq", tag(0, 0, 0, 0), 1);
        ok &= expect("gt-second", tag(0, 1, 0, 0), 2);
        ok &= expect("lt-second", tag(0, 0, 0, 1), 0);
        ok &= expect("first-gt", tag(1, 0, 0, 5), 2);
        ok &= expect("eq-then-lt", tag(2, 0, 2, 1), 0);
        ok &= expect("eq-eq", tag(2, 1, 2, 1), 1);

        let h1 = lex_probe::#{from}(#{@rust_huge});
        let h2 = lex_probe::#{from}(#{@rust_huge});
        let start = Instant::now();
        let huge = lex_probe::#{to}(&lex_probe::#{fun}(
            lex_probe::#{from}(0),
            h1,
            lex_probe::#{from}(1),
            h2,
        ));
        let ms = start.elapsed().as_secs_f64() * 1000.0;
        ok &= expect("huge-lt", huge, 0);
        if ms > 1000.0 {
            eprintln!("huge compare took {ms:.3} ms");
            ok = false;
        }
        println!("huge {ms:.3} ms");
        if !ok {
            exit(1);
        }
    }
    """
  end

  defp rustc_bin do
    path =
      System.find_executable("rustc") ||
        Path.join(System.user_home!(), ".cargo/bin/rustc")

    assert File.regular?(path), "rustc not found"
    path
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_ord_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end
