# Contributing

Issues and pull requests are welcome. The structure of the development and the open tasks are in
[`docs/PLAN.md`](docs/PLAN.md).

## Rules

- `Challenge.lean` is the public statement. Changing it changes what is proved; discuss it in an
  issue first. After any change run `python3 scripts/sync-statement.py`, which regenerates
  `TriangularLattice/Statement.lean` (CI checks that the two agree).
- Every Lean file uses the module system (`module`, `public import`).
- No `axiom`, `native_decide`, `implemented_by` or `Lean.ofReduceBool`. The only permitted axioms
  are `propext`, `Classical.choice` and `Quot.sound`.
- No `set_option maxHeartbeats` raises; split slow proofs into lemmas. Files stay under 1500 lines.
- Follow Mathlib naming and style, with a docstring on every public declaration.

## Building

```sh
lake exe cache get   # prebuilt Mathlib
lake build
```

Never run `lake clean`: it removes the Mathlib build.
