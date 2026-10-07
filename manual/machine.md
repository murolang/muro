---
title: Machine numbers
slug: machine
order: 11
summary: I64, F32, Tensor, and Nx. Nat stays Peano.
---

# Machine numbers

In brief: `I64`, `F32`, and `Tensor D S` wrap `%Nx.Tensor{}`. Computed values are run. Nat stays Peano. The only map `Nat → I64` is `toI64`. Shape is one I64 dimension. Kernel identity on `F32` and `Tensor F32 S` is refused.

## Two number systems

Peano `Nat` is `0` / `suc`. Emit writes `0` and `{:suc, n}`. That is the type you prove things about.

`I64` and `F32` are machine scalars. They are spec formers; values computed at those types are run. Mix depends on `{:nx, "~> 0.9"}` only. Emit is ordinary `def` plus `Nx.add` / `Nx.stack` / `Nx.tensor`, not `defn`.

There is no second index language. A tensor shape is an `I64`, not a Peano `Nat`, and not a `Vec`.

## Operations

| Term | Meaning |
| --- | --- |
| `toI64 n` | Total on Peano. Examples use small values. |
| `addi x y` | I64 addition |
| `muli x y` | I64 multiplication |
| `addt t u` | Tensor addition |
| `packI x y` | Pack two I64s into a tensor whose shape is `toI64 suc(suc 0)` |
| `Tensor D S` | Tensor with dtype `D` and shape `S` |

`Tensor D S` is Data, so `+` is allowed on a tensor.

## The example

`examples/nx_add.muro`:

```
def addI : run Π (x : I64) → Π (y : I64) → I64 :=
  λ (x : I64) → λ (y : I64) → addi x y

def addT : run Π (- n : I64) → Π (+ t : Tensor I64 n) → Tensor I64 n :=
  λ (- n : I64) → λ (+ t : Tensor I64 n) → addt t t

def t1 : run Tensor I64 (toI64 suc(suc 0)) :=
  packI (toI64 suc 0) (toI64 suc(suc 0))

def doubled : run Tensor I64 (toI64 suc(suc 0)) :=
  addT (toI64 suc(suc 0)) t1
```

`n` is erased. `t` is reusable because `Tensor I64 n` is Data. `addT` doubles a tensor by adding it to itself.

```
{:ok, src} = Muro.emit_file("examples/nx_add.muro", Muro.NxAdd)
Code.eval_string(src)
Muro.NxAdd.doubled() |> Nx.to_flat_list()
# [2, 4]
```

`t1` packed `1` and `2`. Doubled is `[2, 4]`.

## What you cannot do

- Identity `{e₁ ≡ e₂ : F32}` or `{e₁ ≡ e₂ : Tensor F32 S}` in the kernel.
- Treat `I64` as `Nat`. There is no implicit coercion. `toI64` is the only map, and it is one way.
- Index a `Vec` by an `I64`. Lengths in [indexed data](indexed.md) are Peano.

Next: [Emit](emit.md).
