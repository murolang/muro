# Binary successor

Library code in [`binary.muro`](binary.muro). Inductive `Nat` stays the primary number type. This file does not replace it and does not change the core calculus.

`List Bit` is a binary numeral, least significant bit first (`O` / `I`). Leading zeros are allowed. The empty list is zero. `sucBit`, `sucBits`, and `sucBin` are a Mealy machine: the carry is the state, and `sucBin` starts that state at `I` (add one).

No host integer is used inside the Muro terms. There is no fixed width. The limit is the number of bits the runtime can store.

Call `sucBin` on a bit list. The bits of 11 become the bits of 12:

```
sucBin (cons I (cons I (cons O (cons I nil))))
```

That equation is `suc-11`. The correspondence with inductive successor is `sucBin-corresp`:

```
toNat (sucBin (toBits n)) ≡ suc n
```

Check and emit from the `muro` directory:

```
mix muro.check stdlib/binary.muro
mix muro.emit stdlib/binary.muro
```

From a neighbouring file, `import "binary.muro"` brings the definitions into scope. The path is relative to the importing file. `sucBin`, `toBits`, and `toNat` are the run definitions; the proofs are erased on emit.
