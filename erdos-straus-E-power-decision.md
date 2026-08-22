<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# E_power — decision (22 August 2026)

**Riley Betts Erdős–Straus programme.** Companion to
`erdos-straus-E-power.md`, `EPower.lean`, `e_power_fibre_moments.py`,
`e_power_residual_primes.py`. This file is a programme decision, not a
theorem. It does not prove the Erdős–Straus conjecture, does not empty
the box, and does not discharge `AnalyticSurvivorBound`.

---

## Decision

The immediate Lean target
`FiniteProductDensityBound` — finite product-space density
\(u(A)\le 2^{-\gamma k^2}\) assembled from
`HubExponentialHypothesis` and `FibreSuenHypothesis` at the
**prime-power hub** \(H=\operatorname{lcm}_i(s_i)\) — is
**withdrawn as the next object to inhabit**.

The 21 August one-stage write-up was already withdrawn. This withdraws
the 22 August *replacement target* at this hub, not the combinatorial
core and not the idea of a later density-to-count transfer.

Do not inhabit `HubExponentialHypothesis` or `FibreSuenHypothesis`.
Do not formalise Harris/FKG in order to reach them. Do not restore
one-stage CDL.

---

## What is not withdrawn

- Layer A cores in `EPower.lean`: hub \(q=s\ell\) with \(\gcd(s,\ell)=1\),
  fibre \(1/\ell\), residual reduction, empty-graph Suen, dependent pair
  mass, sequential Janson I counting (`janson_hit_lower`, `janson_step`),
  two-stage count identity, transfer *at a genuine period*.
- `finite_product_density_of`: the algebra “H1 and H2 imply density”
  remains a correct combination. The hypotheses are the part that this
  hub does not support.
- Unconditional deduplicated mass. \(\mu(A)/(\log A)^2\) still tracks
  toward \(H_5/4\). `DedupTwoLogMass` is the harmonic statement
  \(\mu(2^k)\ge k^2/\kappa\), uninhabited. Proving it does not revive
  density.

---

## Why

On surviving fibres the usable Janson mass is
\(\mu_\rho^2/(\mu_\rho+2\Delta_\rho)\), not \(\mu_\rho\) and not
\(\sum 1/q\).

At \(T=3\), that Titu mass tracks \(1.17\ln A\) through \(A=32\), while
\(k^2=(\log_2 A)^2\) is already larger at \(A=8\). Hub survival is
exactly \(2/3\) on every enumerated \(H=3^k\).

A grid \(T\in\{3,5,7,11\}\) at \(A=8,16,32\) does not repair both
sides. The first primes above \(T\) each divide a stable \(8\)–\(15\%\)
of \(T\)-rough parts and own \(\Delta_\rho\). Raising \(T\) moves that
tax to the next prime, or kills \(\Delta\) and residual \(\mu\)
together. Worst-fibre Titu at \(A=32\) is \(4.0\)–\(4.2\) for every
\(T\), against \(k^2=25\). Even \(T=11\) only reaches
\(-\log P/k^2\approx 0.07\) on thirty samples.

Harris upgrades \(\gamma\), not this mass. Growing \(T\) is not a
two-log schedule for this hub. These are finite-\(A\) measurements, not
a proof that Titu is \(o((\log A)^2)\). They are enough to stop
inhabiting H1/H2 here.

Numbers: `e_power_mass_growth.json`, `e_power_fibre_moments_A32.json`,
`e_power_residual_primes.json`.

---

## Revival test

A **different split** (not \(\operatorname{lcm}\) of the \(T\)-smooth
parts, or not this residual family) may put finite density back on the
queue. The same two numbers decide. On one schedule, through at least
\(A=32\):

| Number | Meaning | Present hub at \(A=32\) | Revive only if |
| --- | --- | --- | --- |
| \(-\log P(\mathrm{hub})/k^2\) | H1 | \(0.016\) at \(T=3\) (exact \(P=2/3\)); \(\approx 0.07\) at \(T=11\) (sample) | \(\ge 0.3\) at \(A=32\), and not falling from \(A=16\) to \(A=32\) |
| \(\min_\rho\,\mu_\rho^2/(\mu_\rho+2\Delta_\rho)\,/\,k^2\) | H2 (Titu) | \(0.16\)–\(0.17\) at every \(T\in\{3,5,7,11\}\), falling with \(A\) | \(\ge 0.3\) at \(A=32\), and not falling from \(A=16\) to \(A=32\) |

Both must pass on the **same** split. One-sided improvement is the
tradeoff already measured.

A coprime residual pack cannot supply the H2 number: pairwise-coprime
moduli have \(\sum 1/n_i\ll\log\log(\max n)\). Empty-graph Suen stays
a theorem and stays one-log.

If a split passes the table, *then* Harris/FKG (or a residue-class
substitute) is the first Lean inequality worth writing, and H1/H2 may
be restated for that split. Until then they stay uninhabited.

---

## Revival attempt 1 — failed, stop

**Split.** Largest-prime residual, cofactor hub (`e_power_lp_split.py`).
\(T\)-smooth \(q\) is still hub-forced. Otherwise \(\ell=P(q)^v\) and
\(s=q/\ell\) enters \(H\). Residual moduli are prime powers, so
\(\Delta\) lives only inside one largest prime.

**Result at \(A=8,16,32\), \(T=3,5,7\).** Every cell fails both
columns. Forty random hub residues; \(H\) is huge (\(\omega(H)=27\)
at \(A=32\)).

| \(A\) | \(T\) | \(-\log P/k^2\) | Titu\(/k^2\) | H1 | H2 |
| --- | --- | --- | --- | --- | --- |
| 8 | 3 | 0.048 | 0.262 | fail | fail |
| 8 | 5 | 0.077 | 0.262 | fail | fail |
| 8 | 7 | 0.154 | 0.228 | fail | fail |
| 16 | 3 | 0.025 | 0.218 | fail | fail |
| 16 | 5 | 0.037 | 0.218 | fail | fail |
| 16 | 7 | 0.054 | 0.191 | fail | fail |
| 32 | 3 | 0.016 | 0.195 | fail | fail |
| 32 | 5 | 0.020 | 0.195 | fail | fail |
| 32 | 7 | 0.048 | 0.195 | fail | fail |

Titu\(/k^2\) is the same order as the old split and is still falling.
H1 is unchanged in kind: \(P\approx 2/3\) at \(T=3\). Moving shared
rough primes into the hub deletes those events from the fibre
(incompatibility on a larger \(H\)) instead of turning them into
two-log residual mass. On some small-\(A\) worst fibres \(\Delta=0\)
and Titu equals \(\mu_\rho\), which is already one-log.

Per the revival rule: both numbers failed through \(A=32\). **Stop.**
Do not run a second split. Do not Harris. Record E_power density at
a two-stage hub of this kind as a negative on the measured range.

JSON: `e_power_lp_split.json`.

---

## If nothing revives (now in force)

Record E_power *density* as a negative at this hub. A one-log fibre
bound is a different theorem: exponent \(\sim\log A\) gives something
like \(A^{-c}\), which at \(A=\exp(c\sqrt{\log x})\) is
\(\exp(-c'\sqrt{\log x})\), not \(S_A\ll x^{1-\delta}\). Do not sell
that as the withdrawn two-stage target.

Transfer remains after a genuine finite density, not instead of one.
Vaughan is still the published comparison.

---

## Lean freeze

Do these:

- keep `EPower.lean` as the combinatorial core;
- keep `DedupTwoLogMass` harmonic and uninhabited.

Do not do these:

- inhabit `HubExponentialHypothesis`, `FibreSuenHypothesis`, or
  `FiniteProductDensityBound`;
- formalise Harris/FKG, fold `janson_step` into H2, or fake \(e^{-x}\);
- prove `DedupTwoLogMass` as a substitute for density;
- start residual-modulus transfer, restore one-stage CDL, densify
  covering, run \(x=10^{10}\), or discharge `AnalyticSurvivorBound`.

**Next.** The revival table was run on one alternative split and
failed. Stop. Do not inhabit H1/H2. Do not start a second split
unless a written argument says why both numbers would pass. This is
a recorded negative for two-stage density at a smooth/cofactor hub,
not a Lean queue.
