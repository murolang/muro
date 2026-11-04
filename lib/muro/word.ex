defmodule Muro.Word do
  @moduledoc """
  Fixed-width words. U8, U32, and U64 are residues of ℕ modulo 2^w.
  I64 is two's complement on the same 64 bits: wrapping add, sub, and
  mul are the bit-pattern operations. Ordering, checked arithmetic, and
  division use the signed value.

  `toNat` returns the canonical residue, so `toNat` of I64 −1 is
  2^64−1. Shifts are total: an amount at or past the width yields the
  guarded value and is never a host shift. `div` and `rem` are `Opt`;
  signed `div` and `rem` are also empty for `INT64_MIN / −1`. Checked
  I64 arithmetic succeeds exactly when the result lies in
  [−2^63, 2^63−1]. A cast is the residue modulo the destination width.
  """

  import Bitwise

  @u8 256
  @u32 4_294_967_296
  @u64 18_446_744_073_709_551_616
  @half 9_223_372_036_854_775_808

  @kinds [:u8, :u32, :u64, :i64]

  def kinds, do: @kinds

  def modulus(:u8), do: @u8
  def modulus(:u32), do: @u32
  def modulus(:u64), do: @u64
  def modulus(:i64), do: @u64

  def bits(:u8), do: 8
  def bits(:u32), do: 32
  def bits(:u64), do: 64
  def bits(:i64), do: 64

  def word_ty(:i64), do: :i64
  def word_ty(k) when k in [:u8, :u32, :u64], do: {:word, {:ty, k}, []}

  def opt_ty(k), do: {:word, {:optk, k}, []}
  def bool_ty, do: {:word, :bool, []}

  def lit(k, n), do: {:word, {:lit, k, residue(k, n)}, []}
  def bool_tm(true), do: {:word, true, []}
  def bool_tm(false), do: {:word, false, []}
  def some_tm(k, n), do: {:word, :some, [lit(k, n)]}
  def none_tm, do: {:word, :none, []}

  def residue(k, n) when k in @kinds do
    m = modulus(k)
    r = rem(n, m)
    if r < 0, do: r + m, else: r
  end

  def of(k, n), do: residue(k, n)

  def add(k, x, y), do: residue(k, residue(k, x) + residue(k, y))
  def mul(k, x, y), do: residue(k, residue(k, x) * residue(k, y))

  def sub(k, x, y) do
    x = residue(k, x)
    y = residue(k, y)
    residue(k, x + (modulus(k) - y))
  end

  def band(k, x, y), do: residue(k, residue(k, x) &&& residue(k, y))
  def bnot(k, x), do: residue(k, modulus(k) - 1 - residue(k, x))
  def bor(k, x, y), do: bnot(k, band(k, bnot(k, x), bnot(k, y)))
  def bxor(k, x, y), do: bor(k, band(k, x, bnot(k, y)), band(k, bnot(k, x), y))

  def eq?(k, x, y), do: residue(k, x) == residue(k, y)

  def lt?(k, x, y) do
    x = residue(k, x)
    y = residue(k, y)

    case k do
      :i64 -> slt?(x, y)
      _ -> x < y
    end
  end

  def le?(k, x, y), do: eq?(k, x, y) or lt?(k, x, y)

  def shl(k, x, n) when is_integer(n) and n >= 0 do
    x = residue(k, x)
    if n < bits(k), do: residue(k, x * pow2(n)), else: 0
  end

  def shr(k, x, n) when is_integer(n) and n >= 0 do
    x = residue(k, x)

    case k do
      :i64 -> ashr(x, n)
      _ -> if n < bits(k), do: div(x, pow2(n)), else: 0
    end
  end

  def checked_add(k, x, y), do: checked(k, fits_add?(k, x, y), add_payload(k, x, y))
  def checked_sub(k, x, y), do: checked(k, fits_sub?(k, x, y), sub_payload(k, x, y))
  def checked_mul(k, x, y), do: checked(k, fits_mul?(k, x, y), mul_payload(k, x, y))

  def divide(k, x, y) do
    if bad_div?(k, x, y), do: :none, else: {:some, div_bits(k, x, y)}
  end

  def remainder(k, x, y) do
    if bad_div?(k, x, y), do: :none, else: {:some, rem_bits(k, x, y)}
  end

  def cast(k, n), do: residue(k, n)

  @doc """
  Reduce a word whose arguments are already values. `:stuck` means a
  redex is not ready. `{:error, :fuel}` means `toNat` would build a
  Peano numeral longer than the fuel.
  """
  def step(op, args, fuel \\ 2_000)

  def step({:of, k}, [t], _fuel) do
    case from_nat(t) do
      {:ok, n} -> {:ok, lit(k, n)}
      :error -> :stuck
    end
  end

  def step(:ton, [t], fuel) do
    case lit_arg(t) do
      {:ok, k, n} ->
        n = residue(k, n)

        if n > fuel do
          {:error, :fuel}
        else
          {:ok, to_nat(n)}
        end

      :error ->
        :stuck
    end
  end

  def step(:add, [x, y], _), do: on_lits(x, y, &add/3)
  def step(:sub, [x, y], _), do: on_lits(x, y, &sub/3)
  def step(:mul, [x, y], _), do: on_lits(x, y, &mul/3)
  def step(:and, [x, y], _), do: on_lits(x, y, &band/3)
  def step(:or, [x, y], _), do: on_lits(x, y, &bor/3)
  def step(:xor, [x, y], _), do: on_lits(x, y, &bxor/3)
  def step(:not, [x], _), do: on_un(x, &bnot/2)

  def step(:cadd, [x, y], _), do: on_opt(x, y, &checked_add/3)
  def step(:csub, [x, y], _), do: on_opt(x, y, &checked_sub/3)
  def step(:cmul, [x, y], _), do: on_opt(x, y, &checked_mul/3)
  def step(:div, [x, y], _), do: on_opt(x, y, &divide/3)
  def step(:rem, [x, y], _), do: on_opt(x, y, &remainder/3)

  def step(:eq, [x, y], _), do: on_cmp(x, y, &eq?/3)
  def step(:lt, [x, y], _), do: on_cmp(x, y, &lt?/3)
  def step(:le, [x, y], _), do: on_cmp(x, y, &le?/3)

  def step(:shl, [x, n], _), do: on_shift(x, n, &shl/3)
  def step(:shr, [x, n], _), do: on_shift(x, n, &shr/3)

  def step({:cast, k}, [t], _) do
    case lit_arg(t) do
      {:ok, _sk, n} -> {:ok, lit(k, n)}
      :error -> :stuck
    end
  end

  def step(:opt, [t], _) do
    case kind_of_ty(t) do
      {:ok, k} -> {:ok, {:word, {:optk, k}, []}}
      :error -> :stuck
    end
  end

  def step(_op, _args, _fuel), do: :stuck

  def kind_of_ty(:i64), do: {:ok, :i64}
  def kind_of_ty({:word, {:ty, k}, []}) when k in [:u8, :u32, :u64], do: {:ok, k}
  def kind_of_ty(_), do: :error

  def from_nat(:ze), do: {:ok, 0}

  def from_nat({:su, t}) do
    case from_nat(t) do
      {:ok, n} -> {:ok, n + 1}
      :error -> :error
    end
  end

  def from_nat(_), do: :error

  def to_nat(0), do: :ze
  def to_nat(n) when n > 0, do: {:su, to_nat(n - 1)}

  def lit_arg({:word, {:lit, k, n}, []}) when k in @kinds and is_integer(n), do: {:ok, k, n}
  def lit_arg(_), do: :error

  defp on_lits(x, y, f) do
    case {lit_arg(x), lit_arg(y)} do
      {{:ok, k, a}, {:ok, k, b}} -> {:ok, lit(k, f.(k, a, b))}
      _ -> :stuck
    end
  end

  defp on_un(x, f) do
    case lit_arg(x) do
      {:ok, k, a} -> {:ok, lit(k, f.(k, a))}
      :error -> :stuck
    end
  end

  defp on_cmp(x, y, f) do
    case {lit_arg(x), lit_arg(y)} do
      {{:ok, k, a}, {:ok, k, b}} -> {:ok, bool_tm(f.(k, a, b))}
      _ -> :stuck
    end
  end

  defp on_opt(x, y, f) do
    case {lit_arg(x), lit_arg(y)} do
      {{:ok, k, a}, {:ok, k, b}} ->
        {:ok,
         case f.(k, a, b) do
           {:some, n} -> some_tm(k, n)
           :none -> none_tm()
         end}

      _ ->
        :stuck
    end
  end

  defp on_shift(x, n, f) do
    case {lit_arg(x), from_nat(n)} do
      {{:ok, k, a}, {:ok, b}} -> {:ok, lit(k, f.(k, a, b))}
      _ -> :stuck
    end
  end

  defp slt?(x, y) do
    cond do
      x < @half and y < @half -> x < y
      x >= @half and y >= @half -> x < y
      true -> x >= @half
    end
  end

  defp pow2(0), do: 1
  defp pow2(n) when n > 0 and n <= 64, do: 1 <<< n

  defp ashr(x, n) when n >= 64 do
    if x < @half, do: 0, else: @u64 - 1
  end

  defp ashr(x, n) do
    q = div(x, pow2(n))
    if x < @half, do: q, else: rem(q + (@u64 - pow2(64 - n)), @u64)
  end

  defp to_z(n) do
    n = residue(:i64, n)
    if n < @half, do: n, else: n - @u64
  end

  defp from_z(z) when z >= 0, do: z
  defp from_z(z), do: z + @u64

  defp in_range?(z), do: z >= -@half and z <= @half - 1

  defp add_payload(:i64, x, y), do: from_z(to_z(x) + to_z(y))
  defp add_payload(k, x, y), do: residue(k, x) + residue(k, y)

  defp sub_payload(:i64, x, y), do: from_z(to_z(x) - to_z(y))
  defp sub_payload(k, x, y), do: residue(k, x) - residue(k, y)

  defp mul_payload(:i64, x, y), do: from_z(to_z(x) * to_z(y))
  defp mul_payload(k, x, y), do: residue(k, x) * residue(k, y)

  defp fits_add?(:i64, x, y), do: in_range?(to_z(x) + to_z(y))
  defp fits_add?(k, x, y), do: add_payload(k, x, y) < modulus(k)

  defp fits_sub?(:i64, x, y), do: in_range?(to_z(x) - to_z(y))
  defp fits_sub?(k, x, y), do: residue(k, y) <= residue(k, x)

  defp fits_mul?(:i64, x, y), do: in_range?(to_z(x) * to_z(y))
  defp fits_mul?(k, x, y), do: mul_payload(k, x, y) < modulus(k)

  defp checked(_k, true, n), do: {:some, n}
  defp checked(_k, false, _n), do: :none

  defp bad_div?(:i64, x, y) do
    x = residue(:i64, x)
    y = residue(:i64, y)
    y == 0 or (x == @half and y == @u64 - 1)
  end

  defp bad_div?(k, _x, y), do: residue(k, y) == 0

  defp div_bits(:i64, x, y), do: quot_bits(residue(:i64, x), residue(:i64, y))
  defp div_bits(k, x, y), do: div(residue(k, x), residue(k, y))

  defp rem_bits(:i64, x, y), do: rem_signed(residue(:i64, x), residue(:i64, y))
  defp rem_bits(k, x, y), do: rem(residue(k, x), residue(k, y))

  defp neg?(n), do: n >= @half

  defp neg_bits(0), do: 0
  defp neg_bits(n), do: @u64 - n

  defp abs_bits(n) do
    if n < @half, do: n, else: @u64 - n
  end

  defp quot_bits(x, y) do
    mag = div(abs_bits(x), abs_bits(y))
    if xor_sign?(x, y), do: neg_bits(mag), else: mag
  end

  defp rem_signed(x, y) do
    mag = rem(abs_bits(x), abs_bits(y))
    if neg?(x), do: neg_bits(mag), else: mag
  end

  defp xor_sign?(x, y), do: neg?(x) != neg?(y)
end
