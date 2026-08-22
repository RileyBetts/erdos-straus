<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Acceptance Specification: Requirements for a Conjecture that Solves Erdős–Straus

**Riley Betts Ltd — Erdős–Straus programme, 19 August 2026.**
Companion to `erdos-straus-novel-structures-plan.md` (§§4a–4u),
`erdos-straus-road-to-lean-qed.md`, `erdos-straus-loughran-orbit.md`,
and the Lean repository (v0.23).

---

## Purpose

The programme's findings amount to an *acceptance specification* for the
load-bearing statement of any proof of the Erdős–Straus conjecture. Let C be
a candidate conjecture proposed as the final open input. C solves ES only if
it satisfies **all eight** requirements below. Each requirement is traceable
to a theorem, measurement, or refutation in the programme record; each has
already eliminated at least one proposed candidate.

Notation: hard classes = the six quadratic-residue classes mod 840; the
covering level A; the marginal constant κ ≈ 0.139 (measured); the divisor
form q ∣ p + 4a²d, q ≡ −1 (mod 4ad).

---

## The eight requirements

### R1. Verified sufficiency
C must imply `HardLandingHypothesis` — hence ES — through kernel-checked
implications.

- *Status of current interfaces:* `AnalyticSurvivorBound` and
  `DivisorLandingBound` satisfy R1 by construction
  (`hard_landing_of_interface`, `hard_landing_of_divisor_interface`,
  `erdos_straus_of_interface`); `TubEpHypothesis` satisfies it via
  `erdos_straus_of_tub_ep`.
- *Trace:* `ErdosStraus.lean` (ES.Covering), `ErdosStrausBLRoute.lean`.
- *Note:* this is the cheap requirement — the only one fully under the
  programme's control.

### R2. Independent content (not ES in disguise)
C must be attackable by methods that do not already amount to proving ES.
A certified equivalence is a translation, not a target; a statement is
admissible only if it has mathematical life beyond this one conjecture —
typically by quantifying over a *class* (all suitably split log K3 surfaces;
all structured divisor problems of a given shape).

- *Failures recorded:* `TubEpHypothesis` (equivalence, `tub_ep_iff_erdos_straus`
  — certified translation, zero strategic distance); the relocation risk for
  H_ES is the open instance of this test and must be put to experts early.
- *Trace:* plan §4k, §4q; conversation record on the equivalence trap.

### R3. Barrier evasion (the k-budget invariant)
C's proof must inject arithmetic input from **outside** the
interval-intrinsic class. The invariant (derived three independent ways)
caps every method consuming only interval-intrinsic randomness — sieves,
large sieve, k-wise-independence fooling, raw multi-scale renewal
bookkeeping — at sifted mass ≤ c·log(level), against a requirement > log x.
Admissible input classes identified:

1. spectral / bilinear arithmetic (Duke–Friedlander–Iwaniec-class
   equidistribution of quadratic-congruence roots; dispersion);
2. algebraic rigidity used non-statistically (the §4p character-coset
   structure, if reciprocity genuinely couples conditions across moduli);
3. genuinely global geometry (existence principles not routed through
   fibers).

Any C whose natural proof is "sieve harder" fails R3 before it starts.

- *Trace:* plan §§4h, 4k, 4l (the invariant), §4n (Bonferroni divergence at
  μ ≈ 2.2 — why exactness does not confer truncation), §4p–4r (rigidity as
  boundary layer).

### R4. Exceptional-set annihilation, with mandatory growth
ES is a for-all statement and density-one results are classical; C must kill
the exceptional set entirely. The programme fixes the geometry of this
requirement: **fixed parameter boxes provably leave ~x/(log x)^{1+c(D₀)}
exceptions** (half-rough shifted values — for a single (a,d), failure
density (log x)^{−1/φ(4ad)}, jointly compounding). Hence C must involve a
level/box growing with x, at rate log²(level) ≳ log x, i.e.
level = exp(c·√log x) with κc² > 1 — the marginal constant, proved
parametrization-invariant across the covering and divisor coordinates.

- *Eliminated by R4:* every fixed-identity and fixed-box proposal, including
  the advised fixed-D₀ LandingLemma (heuristically false; §4q).
- *Empirical anchor:* 161 d=1 escapees below 10⁶ at a ≤ 30; 100% of
  escapees have p + 4 free of 3-mod-4 factors (the a = 1 mechanism is
  exact).
- *Trace:* plan §4q, §4r; §4h / `erdos-straus-E-partial.md` (E_partial:
  Layer 0 is E_power, a recorded negative for the \(x^{1-\delta}\)
  covering-box bound (`erdos-straus-E-power.md`,
  `erdos-straus-E-power-decision.md`), not `AnalyticSurvivorBound`; Gate A forbids
  compiling a power-saving count as QED progress).

### R5. Splitness compatibility
C must locate the arithmetic where this surface actually keeps it: in
**integrality and divisors**, not in fiber-level local–global structure.
Kernel-checked facts: every conic fiber of the ES surface is split
((Ax − nt)(Ay − nt) = (nt)², A = 4t − n), and positive fiber points
correspond exactly — both directions, linear recovery — to divisor pairs of
(nt)² in the class −nt (mod A), for all n ≥ 2. Consequently:

- geometric form of R5: C must be a *global* principle robust to a totally
  split boundary triangle and interior 𝔾ₘ² (fiber-level methods — Cao–Xu
  toric strong approximation, Harpaz descent-fibration — provably cannot
  grip);
- analytic form of R5: C is naturally a statement about divisors of shifted
  values in prescribed progressions (the same requirement in dual
  coordinates).

- *Trace:* `ConicFiber.lean` (axioms: propext, Quot.sound only); plan §4m
  (Cao–Xu boundary break), §4t (Harpaz verdict; "too split" pattern).

### R6. Consistency with the known negatives
C must not prove too much. It must be compatible with:

1. **Markoff-type failures** — sibling log K3 surfaces fail the integral
   Hasse principle infinitely often (Ghosh–Sarnak; CTWX; LM); so C cannot be
   "Brauer–Manin suffices for log K3 integral points" in general;
2. **BL Theorem 1.9** — BM is not the only obstruction to strong
   approximation on the ES surfaces themselves;
3. **abelian insufficiency** — no finite set of congruence/character
   conditions covers the hard classes (Mordell-type QR obstruction; to be
   fenced formally with Mathlib Dirichlet); so C cannot be finitely-abelian
   in nature.

Surviving geometric shapes therefore involve *refined* frameworks
(semi-integral / orbifold obstruction sets) or new technology.

- *Trace:* plan §4m (Markoff comparison; Thm 1.9), roadmap §5; abelian
  insufficiency (roadmap §12, "parallel fence").

### R7. Effectivity
C must come with an **explicit threshold X₀**: the pipeline's finite half is
a certificate computation below X₀ (kernel `decide`, declared
`native_decide`, or Track C ZK attestation at scale). A Siegel-style
ineffective "all sufficiently large n" would establish ES as a truth while
leaving the machine-checked proof permanently uncompilable. Ineffective C is
admissible mathematics but fails the programme's QED contract.

- *Trace:* roadmap §11 (certificate lanes and axiom audit); README audit
  tables.

### R8. Statability now, in a published dialect
C must be:

1. formalizable as a kernel Prop today (both current interfaces are — this
   is what keeps the target drift-proof; quantifier and definition drift are
   documented failure modes, caught twice in this programme); and
2. phrased in a published dialect — bilinear
   forms in divisor problems (the dispersion school) or global existence
   principles for log K3 surfaces (the Bright–Loughran literature) — so that
   the statement has theorems to cite, not only ES.

- *Trace:* plan §4s (definition drift caught), §4q (quantifier vacuity
  caught); geometric note (the translation function of `tub_ep_consumed` and
  the DFI dictionary `dfi_dictionary_d1`).

---

## Scorecard of current candidates

| Requirement | `DivisorLandingBound` (growing bound) | Existence principle ⟹ TubEp (future) |
|---|---|---|
| R1 sufficiency | **✓ proved** | ✓ via `erdos_straus_of_tub_ep` (once C stated) |
| R2 independence | **open — the known risk** (relocation test needed) | ✓ if stated for a surface class |
| R3 barrier evasion | designed for input class 1 (DFI); unproven | ✓ automatic (not interval-bound) |
| R4 growth / exceptional set | **✓ built in** (level schedule exp(c√log x)) | must be engineered (uniformity in n) |
| R5 splitness | **✓ native** (it *is* the divisor form) | the hard design constraint (global method) |
| R6 negatives | ✓ (quantitative, not local–global) | **the hard design constraint** (Markoff-safe hypotheses) |
| R7 effectivity | plausible (dispersion proofs usually effective) | needs care |
| R8 statability/dialect | **✓ stated; dispersion school** | statable schema; Bright–Loughran literature |

Neither candidate currently satisfies all eight. **The requirements are
theorems; the statement meeting all eight is the discovery.**

---

## One-paragraph summary

A conjecture that solves Erdős–Straus must be a kernel-statable proposition
with mathematical life beyond ES, whose proof injects spectral, rigidity, or
global-geometric input outside the interval-intrinsic class, which
annihilates (not merely thins) the exceptional set through a parameter
growing like exp(c√log x) with κc² > 1, which respects the surface's total
splitness by living in divisor/integrality structure or in genuinely global
geometry, which is consistent with the Markoff failures, Theorem 1.9, and
abelian insufficiency, which names its threshold, and which is written in
a published dialect with existing theorems, not only ES. Everything short of
this is infrastructure — valuable, publishable, and already substantially
built — but not the keystone.

*Prepared as part of the Riley Betts Ltd Erdős–Straus programme, facilitated
by Martyn Riley (automation and high-level strategy; not a claim of
expertise in number theory, combinatorics, or geometry — see `README.md`).
The mathematical work is a collaboration of Anthropic agents, Grok 4.6, and
Cursor agents, with Lean 4, Mathlib, and numerical test resources. No proof
of the conjecture is claimed. Every claim above is traceable to a
kernel-checked theorem, a labelled measurement, or a recorded refutation in
the programme archive.*
