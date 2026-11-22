# P vs. NP

A Lean 4 and Mathlib workspace for formalizing results in computational complexity.

## Build

Install [Elan](https://lean-lang.org/install/manual/), then run these commands from
the repository root.

```sh
lake exe cache get Mathlib.Data.Finset.Card
lake build
```

The first command downloads precompiled Mathlib files for the starter proof.
For additional Mathlib imports, pass the corresponding module names to that
command, or run `lake exe cache get` to download the full cache.

Add modules under `PvsNP/` and import them from `PvsNP.lean` so `lake build`
checks them. `PvsNP/Basic.lean` contains a starter theorem using Mathlib's finite
sets.
