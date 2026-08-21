<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Contributing

This repository does **not** prove the Erdős–Straus conjecture. Do not
add a fake `theorem erdos_straus`. Do not add `sorry` on the QED line.

The record is meant to be usable by others: kernel-checked Lean, written
analytic claims labelled unverified, and closed routes written down so
they are not reopened as if undone. Negative results are contributions.

## Pins (please keep them)

Reproducible builds are part of the archive.

| Pin | File | Policy |
|---|---|---|
| Lean toolchain | `lean-toolchain` | `leanprover/lean4:v4.34.0-rc1` |
| Mathlib revision | `lakefile.toml` `rev` | SHA, not a moving branch |
| Transitive Lake lock | `lake-manifest.json` | **commit it** with any pin change |

Do not leave `lake-manifest.json` as uncommitted local churn. If you bump
Mathlib, bump `lakefile.toml` and regenerate the lock in the same commit:

```bash
lake update mathlib
lake exe cache get
lake build
```

Lake will warn if the lock is out of date. Do not ignore that on a PR.

## Build

```bash
lake exe cache get
lake build
```

Layer A (no Mathlib) can be checked with `lean` on the files listed in
`README.md`. Layer B needs the pinned Mathlib olean cache.

## Scope

Do not densify covering. Do not treat Bradford 2026, Bounded-A, or extra
covering slices as a QED path. Library files (`Leochlon.lean`,
`Stormer.lean`) are not progress toward `erdos_straus_of_interface`.

Programme notes in this directory are the source of those freezes.

## License

MIT. Copyright Riley Betts Ltd 2026. By opening a pull request you offer
your contribution under the same license.
