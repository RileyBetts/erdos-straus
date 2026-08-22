<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Erdős–Straus in Lean

> [!CAUTION]
> **No proof of the Erdős–Straus conjecture is claimed or achieved.**
> This repository does not prove `theorem erdos_straus`.
> Every novel result in the table below is **unverified**: not independently
> refereed, not a solution of the conjecture. Analytic rows are write-ups,
> not Lean.

> [!NOTE]
> **Project report (v0.2, 22 August 2026).** A compiled survey of this
> public archive is
> **[erdos-straus-programme-report-v0.2.pdf](erdos-straus-programme-report-v0.2.pdf)**.
> LaTeX source: [`erdos-straus-programme-report-v0.2.tex`](erdos-straus-programme-report-v0.2.tex).

## Novel results (unverified)

The archive is kept so the community can use this record. Negative
results are listed so closed routes are not reopened as if undone.
Lean kernel facts later in this file are machine-checked relative to
the stated axioms; they are still not a solution.

| Result | Kind | Status | Where |
| --- | --- | --- | --- |
| T(3)+ : S(3,x) ≪ (log x)^(−3/2). Matching lower bound open (stalls at q > x^(1/2)). | written claim | **unverified** | `erdos-straus-T-3.md` |
| T(A)+ at fixed A: aligned-prime Selberg bound. Γ-inflation o(log² A). Does not empty a QED-scale box. | written claim | **unverified** | `erdos-straus-T-A.md` |
| E_lane: d=1 floor ≪ x exp(−c′ √log x · log log x). Below Vaughan. | written claim | **unverified** | `erdos-straus-T-A.md` |
| E_power: covering-box S_A ≪ x^(1−δ) at A = exp(c √log x). Above Vaughan, below k-budget. Not `AnalyticSurvivorBound`. | written claim | **unverified** | `erdos-straus-E-power.md` |
| Dummy covering: extra slices with cond ≡ 1 do not cut. Live kill of a QED-scale ClassRough schedule. | written claim | **unverified** | `erdos-straus-E-partial.md` |
| No bilinear cell at the Bombieri–Vinogradov wall (M+N=1 and Q=1/2). | negative | **unverified** | `erdos-straus-T-3.md` |
| r_χ → Kloosterman range no-go at Q = x^(1/2+). | negative | **unverified** | `erdos-straus-T-3.md` |
| Zheng two-modulus range no-go on d1 ≈ d2 ≈ √x; uneven leftover dies on (0, 1/2, 1/2). | negative | **unverified** | `erdos-straus-T-2.md` |
| Joint δ-method Farey–k incompatibility at the BV wall. | negative | **unverified** | `erdos-straus-T-3-delta.md` |
| Gallant GKR / FKMS does not apply to the T(3) CRT kernel. | negative | **unverified** | `erdos-straus-T-3-monodromy.md` |
| Four T(3) looks fail at one varying-modulus correlation. | negative | **unverified** | `erdos-straus-varying-modulus-gap.md` |
| Geometry is not a QED path with existing tools (Harpaz split; Campana not C+; no Vieta; Thm 1.8 is not existence). Split fibres / no-Vieta / 9/5 are Lean; the rest is a reading. | negative | **unverified** (Lean parts machine-checked) | `ConicFiber.lean`, `NoVieta.lean`, `SchinzelSep.lean` |
| C7: no degree-1 Witness identity, modulus ≤ 30, coefficients ≤ 4, covers a hard class. | negative | **unverified** | `c7_bounded_coupling_search.py` |

## Role and how the work was done

**Martyn Riley, of Riley Betts Ltd**, is responsible for facilitating the
automation and the high-level strategy: strategic decisions that
encourage novel routes to be attacked, a scientific method of carefully
recording negative results, and a methodical documentation procedure for
the agents to follow. He makes no claim to expertise in number theory,
combinatorics, or geometry, though he is interested in these subjects.

The mathematical and formalization work in this archive is a
collaboration of Anthropic agents, Grok 4.6, and Cursor agents, with
access to Lean 4, Mathlib, and numerical test resources. It is not a
record of human coauthorship of the mathematics.

A layered formalization of covering-landing and the Bright–Loughran
geometry around the conjecture lives below. Programme notes (same
directory as this file):
`erdos-straus-programme.md` (v0.23 programme brief; geometry is theory-building, not QED),
`erdos-straus-gs-reformulation.md` (analytic-lane dictionary: G–S /
Heath-Brown; no new theorems),
`erdos-straus-novel-structures-plan.md` (research record, §4v joint-lane freeze),
`erdos-straus-road-to-lean-qed.md` (execution roadmap),
`erdos-straus-conjecture-spec.md` (acceptance requirements R1–R8 for a
load-bearing C),
`erdos-straus-candidate-conjectures.md` (candidate statements for C, v0.5:
C1–C11, C4_1 = T(A), NV, S1, S1_1, C3_1, C5_2, C7_1),
`erdos-straus-T-A.md` (working note for T(A): selection constant, not
the Euler factor \(0.91\); T(3) kernel `classRough_123_iff_certificates`;
T(3)\(^+\) and T(A)\(^+\) in `erdos-straus-T-3.md` / `erdos-straus-T-A.md`
(`c4_sieve_constant.py`); E_lane the \(d=1\) floor, below Vaughan;
certificate converse and dummy-covering checks in `c4_certificates.py`),
`erdos-straus-T-2.md` (Zheng two-modulus look: A2.2 no-go on
\(d_1\approx d_2\approx\sqrt{x}\); A2.3 uneven Type I leftover does not
cover \((0,1/2,1/2)\); not T(2)\(^+\) claimed; not T(3) progress;
`zheng-wellfactorable.md`, `t2_zheng_ranges.py`),
`erdos-straus-T-3.md` (T(3)\(^+\) claimed: \(S(3,x)\ll(\log x)^{-3/2}\);
three-step lower-bound plan, completion of \(q>x^{1/2}\) named as the
risk; \(r_\chi\to\) Kloosterman look a range no-go at the stall; joint
well-factorable CRT residue the frontier question; not Lean),
`erdos-straus-T-3-delta.md` (joint δ-method at the CRT modulus: Farey–\(k\)
incompatibility at the BV wall; \((0,1/2,1/2)\) is not that identity;
not T(3) progress; `t3_delta_ranges.py`),
`erdos-straus-T-3-monodromy.md` (FKMS gallant GKR does not apply to the
joint CRT kernel; not T(3) progress; `t3_monodromy_ranges.py`),
`erdos-straus-varying-modulus-gap.md` (four T(3) completion looks fail
by distinct mechanisms at the same varying-modulus correlation; not
T(3) progress),
`erdos-straus-sieve-desk.md` (analytic worklist: T(A)\(^+\) /
\(C_{\mathrm{sieve}}(A)\); E_lane; E_power; T(3) completion; do not densify covering),
`erdos-straus-E-partial.md` (Gate A: E_power is the paper; still not
`AnalyticSurvivorBound`),
`erdos-straus-E-power.md` (claimed: \(S_A(x,2x)\ll x^{1-\delta}\), below
the k-budget, above Vaughan; Lemma SM; second-moment check through
\(A=2000\)),
`erdos-straus-loughran-orbit.md` (geometric questions: the class
statement, what is not a proof path),
`erdos-straus-prior-archive.md` (prior Track-1 archive as library,
not a merge),
`erdos-straus-bradford-lemma3.md` (Bradford 2026 is not QED; Lemma 3
forbids finite-parameter Type I/II catalogues),
`erdos-straus-leochlon.md` (Type-II dictionary into `ES.IsES`),
`CONTRIBUTING.md` (pins, lockfile, scope for later public contribution).

## Layers

**Layer A (core):** `ErdosStraus.lean`, `BrightLoughran.lean`, `ConicFiber.lean`,
`TwistDescent.lean`, `SchinzelSep.lean`, `SchinzelDecide.lean`,
`NoVieta.lean` — bare Lean,
Lean ≥ 4.33.0, no imports; axioms: `propext`, `Quot.sound`, plus
`Lean.ofReduceBool` for the `native_decide` instances (see
[audit](#audit-layer-a-axioms)).
`classRough_of_certifies` is the exact direction: a real odd character
mod \(4a\) certifying the prime factors of \(p+4a^2\) implies
`ClassRough`. `oddRealChar_four` inhabits the structure at \(a=1\)
(\(\chi_4\), `classRough_of_chi4`). The converse is a theorem at
\(a=1,2,3\): `classRough_123_iff_certificates` (T(3) kernel; not the
Wirsing asymptotic).

**Layer B (Mathlib):** `ErdosStrausQR.lean`, `ErdosStrausBLRoute.lean`,
`Leochlon.lean` (Type-II dictionary; not a covering merge), `Stormer.lean`
(consecutive smooth numbers; Apache 2.0, Mathlib PR #42040; library only)
— build via `lake build` against the pinned Mathlib; discharge the Layer-A
reciprocity interface and develop the BL route.

Layer A isolates quadratic reciprocity as the named field
`BL.InvariantData.reciprocity`; Layer B discharges it from Mathlib.
The elementary spine can be checked with no extra infrastructure before
deciding whether to trust the larger build.

`archive/ErdosStraus-core.lean` is a frozen snapshot of an earlier covering
file, not a Lake root; `archive/ErdosStraus-mathlib-project.lean` is a
duplicate of `ErdosStraus.lean`. See `archive/README.md`.

## Build

### Layer A

```bash
lean ErdosStraus.lean
lean BrightLoughran.lean
lean ConicFiber.lean
lean TwistDescent.lean
lean SchinzelSep.lean
lean SchinzelDecide.lean
lean NoVieta.lean
```

Requires Lean ≥ 4.33.0.  No Mathlib, no `lake`.

### Layer B

Pinned toolchain: `leanprover/lean4:v4.34.0-rc1` (`lean-toolchain`; a
release candidate, not a moving nightly).
Mathlib is a git dependency of
[mathlib4](https://github.com/leanprover-community/mathlib4) at
`1a0ef26d9624d64a1ad11853d17c30b8c32f2a10` (`lakefile.toml`,
`lake-manifest.json`).  The first `lake build` clones that revision;
no local `../mathlib4` checkout is required.  Fetch the Mathlib olean
cache before building — otherwise Lake compiles Mathlib from source.

The lockfile `lake-manifest.json` is part of the archive. Commit it with
any toolchain or Mathlib bump; see `CONTRIBUTING.md`.

```bash
lake exe cache get
lake build
```

If Lake warns that the manifest is out of date, run `lake update mathlib`
once, then `lake exe cache get` and `lake build` again, and commit the
updated `lake-manifest.json`.

GitHub Actions (`.github/workflows/ci.yml`) runs the same Layer B build.

## Audit (Layer A axioms)

Checked on Lean 4.33.0 (`#print axioms`).  The kernel-checked spine is:

| Theorem | Axioms |
|---|---|
| `witness_sound` | `propext`, `Quot.sound` |
| `es_1009` | `propext`, `Quot.sound` |
| `bl_thm12_prime_anatomy` | `propext`, `Quot.sound` |
| `primes_below_100_covered_kernel` | none (`decide`) |
| `lemma38_check_true` | none (`decide`) |
| `conditional_qed_hard` | `propext`, `Quot.sound`, `Classical.choice` |
| `lemma32` | `propext`, `Quot.sound`, `Classical.choice` |
| `ConicFiber.fiber_identity` | `propext`, `Quot.sound` |
| `ConicFiber.fiber_to_divisor` | `propext`, `Quot.sound` |
| `ConicFiber.divisor_to_fiber` | `propext`, `Quot.sound` |
| `TwistDescent.descent` | none |
| `TwistDescent.naive_cover_empty` | `propext`, `Quot.sound` |
| `TwistDescent.lift` | `propext`, `Quot.sound`, `Classical.choice` |
| `TwistDescent.twist_real_iff` | `propext` |
| `TwistDescent.t_fiber_section_cleared` | `propext` |
| `TwistDescent.u1_fiber_section_cleared` | `propext` |
| `TwistDescent.u1_fiber_twist` | `propext` |
| `SchinzelSep.signed_9_5` | none |
| `SchinzelSep.no_pos_9_5` | `propext`, `Quot.sound` |
| `SchinzelDecide.sep_9_5` | none (`decide`) |
| `SchinzelDecide.sep_13_7` | none (`decide`) |
| `SchinzelDecide.pos_4_5` | none (`decide`) |
| `SchinzelDecide.decideCplus_sound` | `propext`, `Quot.sound` |
| `SchinzelDecide.decideCplus_complete` | `propext`, `Quot.sound` |
| `SchinzelDecide.no_pos_9_5` | `propext`, `Classical.choice`, `Quot.sound` |
| `SchinzelDecide.no_pos_13_7` | `propext`, `Classical.choice`, `Quot.sound` |
| `NoVieta.unique_x` | `propext`, `Quot.sound` |
| `NoVieta.es_unique_x` | `propext`, `Classical.choice`, `Quot.sound` |

`native_decide` theorems add a generated reduction axiom
(`Lean.ofReduceBool` / `._native.native_decide.ax_1_1` on 4.33.0):

| Theorem | File |
|---|---|
| `primes_below_10000_covered` | `ErdosStraus.lean` |
| `hard_primes_below_10000_covered` | `ErdosStraus.lean` |
| `okay_below_100000` | `ErdosStraus.lean` |
| `thm12_instance_1009` | `BrightLoughran.lean` |
| `witness_fingerprint_1009` | `BrightLoughran.lean` |

## What's in Lean

Route 2 (Bright–Loughran geometry) is recorded in plan §4s, not only in
source comments.  Proved, not the conjecture:

- **ℤ-model** — `IsESZ`, `esZ_nonempty`, mixed-sign occupancy
- **Box** — `schinzelZ_min_le` / `esZ_min_le` (BL Lemma 3.10)
- **Reciprocity** — `hilbert_reciprocity_*`, `thm12_discharged`
- **TUB-EP** — `TubEpHypothesis`; implication `erdos_straus_of_tub_ep` proved,
  hypothesis not discharged
- **Conic fibration** — `ConicFiber.lean`: the fibers of the ES surface are
  the split conics uv = (nt)²; `fiber_to_divisor` / `divisor_to_fiber` prove
  positive fiber points correspond exactly to divisor pairs of (nt)² in the
  class −nt (mod 4t−n), for all n ≥ 2.  Consequence recorded in plan §4t:
  Harpaz's descent-fibration theorem (JEMS 2019) does not apply — the ES
  surface is too split for fiber-level local-global methods.
- **Twist descent (C5_1 Gate 2)** — `TwistDescent.lean`: a positive-locus
  point of \(V_{n,d}\) (`w² = d·u₁u₃`) projects to \(U_n\cap C_+\); every
  \(C_+\) point lifts to some twist; the naive cover `w² = −u₁u₃` is empty
  over \(C_+\).  Does not produce a point of \(V_{n,d}\).
  Gate 3: the t-fibration of \(V_{n,d}\) has an explicit rational section
  (`t_fiber_section_cleared`); Harpaz Theorem 1.0.1 does not apply to it.
  Autopsy: the same curve is a section of \(\pi=u_1\) and \(\pi=w\)
  (`u1_fiber_section_cleared`).
- **Schinzel separator (S1)** — `SchinzelSep.lean`: 9/5 has a mixed-sign
  integer point (`signed_9_5`). Ordered no-positive is `no_pos_9_5`.
  `SchinzelDecide.lean`: soundness+completeness for a positive-octant
  decision procedure; `no_pos_9_5` / `no_pos_13_7` unordered. Does not
  claim the BL 1.8 analogue; S1_1 is a hand adelic sketch, not Lean.
- **No Vieta (NV)** — `NoVieta.lean`: the affine equation is linear in each
  coordinate; unique \(x\) given \((y,z)\) (`unique_x`, `es_unique_x`).
  No Markoff-type second-root involution. Closes the geometric mechanism
  inventory (plan §4v). Does not produce a point of \(C_+\).
- **T(3) kernel** — `classRough_123_iff_certificates`: ClassRough on
  \(a=1,2,3\) is exactly a \(1\times 2\times 2\) union of character
  certificates. Research note T(3)\(^+\): \(S(3,x)\ll(\log x)^{-3/2}\)
  (`erdos-straus-T-3.md`); not Lean; matching lower bound not claimed
  (three-step plan; stalls at \(q>x^{1/2}\)). T(A)\(^+\): uniform
  Selberg, \(\Gamma(\beta+1)e^{\gamma\beta}=\exp(o(\log^2 A))\)
  (`erdos-straus-T-A.md`, `c4_sieve_constant.py`).

## What this does not claim

- Unconditional `ErdosStraus`
- `TubEpHypothesis` (the implication `erdos_straus_of_tub_ep` is proved)
- Bright–Loughran Theorem 1.8 as existence of a positive-octant point
- Harpaz’s conic-log-K3 theorem as existence on ES fibers (inapplicable; split)
- Harpaz Theorem 1.0.1 as existence on the t-fibers of \(V_{n,d}\) (Gate 3: those fibers are split)
- Mitankin–Uhlemann semi-integral Hasse as a \(\mathbb{Z}\)-point of \(C_+\) (C3_1)
- Vieta dynamics / Bourgain–Gamburd–Sarnak on ES surfaces (`NoVieta.lean`: no second root)
- Bradford 2026 as a proof; Bounded-A / L8–L9 covering from the prior
  Track-1 archive as a merge. Those artifacts live here as
  library/docs (`erdos-straus-prior-archive.md`). Do not densify covering.

## Bibliography

Literature the Lean and the plan actually use.  None of these papers proves the
conjecture; Bright–Loughran Theorem 1.8 is a non-obstruction statement, not
existence of a positive-octant point.  Narrative annotations live in
`erdos-straus-novel-structures-plan.md` §5.

### Conjecture, covering, identities

- P. Erdős, *Az \(1/x_1+\cdots+1/x_n=a/b\) egyenlet egész számú megoldásairól*, Mat. Lapok **1** (1950), 192ff.
- W. Sierpiński, *Sur les décompositions de nombres rationnels en fractions primaires*, Mathesis **65** (1956), 16ff.
- A. Schinzel, *Sur quelques propriétés des nombres \(3/n\) et \(4/n\), où \(n\) est un nombre impair*, Mathesis **65** (1956), 219–222.
- N. Nakayama, *On the decomposition of a rational number into “Stammbrüche”*, Tôhoku Math. J. **46** (1939), 1ff.
- L. A. Rosati, *Sull’equazione diofantea \(4/n=1/x_1+1/x_2+1/x_3\)*, Boll. Un. Mat. Ital. (3) **9** (1954), 59ff.
- A. Aigner, *Brüche als Summe von Stammbrüchen*, J. Reine Angew. Math. **214/215** (1964), 174ff.
- K. Yamamoto, *On the Diophantine equation \(4/n=1/x+1/y+1/z\)*, Mem. Fac. Sci. Kyushu Univ. Ser. A **19** (1965), 37–47. [doi:10.2206/kyushumfs.19.37](https://doi.org/10.2206/kyushumfs.19.37)
- L. J. Mordell, *Diophantine Equations*, Academic Press, London, 1969, Chapter 30.
- A. Schinzel, *On sums of three unit fractions with polynomial denominators*, Funct. Approx. Comment. Math. **28** (2000), 187–194. [doi:10.7169/facm/1538186694](https://doi.org/10.7169/facm/1538186694)
- T. F. Bloom, *Egyptian fractions*, arXiv:[2210.04496](https://arxiv.org/abs/2210.04496) (covering equivalence, Theorem 1).
- M. A. Lopez, *A complete congruence system for the Erdős–Straus conjecture*, arXiv:[2404.01508](https://arxiv.org/abs/2404.01508) (Type A/B).
- M. Bello-Hernández, M. Benito, E. Fernández, *A divisor parametrization for the Erdős–Straus conjecture*, arXiv:[2606.10922](https://arxiv.org/abs/2606.10922).
- M. Bello Hernández, M. Benito, E. Fernández, *On the equation \(4/p=1/n+1/m+1/k\)*, arXiv:[1010.2035](https://arxiv.org/abs/1010.2035) (Lemma 3: finite-parameter Type I/II catalogues miss an AP).
- K. Bradford, *An elementary proof of the Erdős–Straus conjecture*, arXiv:[2602.11774](https://arxiv.org/abs/2602.11774) (not a proof; `erdos-straus-bradford-lemma3.md`).
- C. Størmer, *Quelques théorèmes sur l’équation de Pell \(x^2-Dy^2=\pm 1\) et leurs applications*, Videnskabsselskabets Skrifter I Math.-Nat. Kl. **2** (1897) (consecutive smooth numbers; `Stormer.lean`, Apache 2.0, Mathlib PR #42040, library only).

### Bright–Loughran geometry (Route 2)

- M. Bright, D. Loughran, *Brauer–Manin obstruction for Erdős–Straus surfaces*, Bull. Lond. Math. Soc. **52** (2020), no. 4, 746–761; arXiv:[1908.02526](https://arxiv.org/abs/1908.02526). [doi:10.1112/blms.12374](https://doi.org/10.1112/blms.12374)
- J.-P. Serre, *Cours d’arithmétique*, Presses Universitaires de France, Paris, 1970; English: *A Course in Arithmetic*, GTM **7**, Springer, 1973 (Hilbert symbols; Layer A implements these formulae).
- S. Lang, A. Weil, *Number of points of varieties in finite fields*, Amer. J. Math. **76** (1954), 819–827 (input to Bright–Loughran Theorem 1.9).
- J. Jahnel, D. Schindler, *On integral points on degree four del Pezzo surfaces*, Israel J. Math. **222** (2017), 21–62; arXiv:[1602.03118](https://arxiv.org/abs/1602.03118). [doi:10.1007/s11856-017-1581-0](https://doi.org/10.1007/s11856-017-1581-0) (weak/strong obstruction at infinity; the box).
- Y. Harpaz, *Integral points on conic log K3 surfaces*, J. Eur. Math. Soc. **21** (2019), 627–664; arXiv:[1511.04876](https://arxiv.org/abs/1511.04876). [doi:10.4171/jems/846](https://doi.org/10.4171/jems/846) (plan §4t: inapplicable — split fibers).
- H. Uppal, *Integral points on affine surfaces fibered over* \(\mathbb{A}^1\), arXiv:[2307.06638](https://arxiv.org/abs/2307.06638) (norm-1-torus extension of Harpaz; not a theorem about ES fibers).
- J.-L. Colliot-Thélène, O. Wittenberg, *Groupe de Brauer et points entiers de deux familles de surfaces cubiques affines*, Amer. J. Math. **134** (2012), 1303–1327. [doi:10.1353/ajm.2012.0036](https://doi.org/10.1353/ajm.2012.0036)
- Y. Cao, F. Xu, *Strong approximation with Brauer–Manin obstruction for toric varieties*, Ann. Inst. Fourier **68** (2018), 1879–1908. [doi:10.5802/aif.3199](https://doi.org/10.5802/aif.3199) (honest toric SA; *not* a theorem about the ES octant).
- J.-L. Colliot-Thélène, F. Xu, *Brauer–Manin obstruction for integral points of homogeneous spaces and representation by integral quadratic forms*, Compos. Math. **145** (2009), 309–363. [doi:10.1112/S0010437X0800376X](https://doi.org/10.1112/S0010437X0800376X)

### Markoff comparison (does not move mixed-sign ES points into \(C_+\))

- J. Bourgain, A. Gamburd, P. Sarnak, *Markoff triples and strong approximation*, C. R. Math. Acad. Sci. Paris **354** (2016), 131–135; arXiv:[1505.06411](https://arxiv.org/abs/1505.06411). [doi:10.1016/j.crma.2015.12.006](https://doi.org/10.1016/j.crma.2015.12.006)
- J. Bourgain, A. Gamburd, P. Sarnak, *Markoff surfaces and strong approximation: 1*, arXiv:[1607.01530](https://arxiv.org/abs/1607.01530).
- A. Ghosh, P. Sarnak, *Integral points on Markoff type cubic surfaces*, Invent. Math. **229** (2022), 689–749; arXiv:[1706.06712](https://arxiv.org/abs/1706.06712). [doi:10.1007/s00222-022-01114-z](https://doi.org/10.1007/s00222-022-01114-z)
- D. Loughran, V. Mitankin, *Integral Hasse principle and strong approximation for Markoff surfaces*, Int. Math. Res. Not. IMRN **2021**, no. 18, 14086–14122; arXiv:[1807.10223](https://arxiv.org/abs/1807.10223). [doi:10.1093/imrn/rnz114](https://doi.org/10.1093/imrn/rnz114)
- J.-L. Colliot-Thélène, D. Wei, F. Xu, *Brauer–Manin obstruction for Markoff surfaces*, Ann. Sc. Norm. Super. Pisa Cl. Sci. (5) **21** (2020), 1257–1313; arXiv:[1808.01584](https://arxiv.org/abs/1808.01584). [doi:10.2422/2036-2145.201810_002](https://doi.org/10.2422/2036-2145.201810_002)
- V. Mitankin, J. Uhlemann, *Local–global principles for semi-integral points on Markoff orbifold pairs*, J. Lond. Math. Soc. **112** (2025), no. 6, e70363; arXiv:[2411.02629](https://arxiv.org/abs/2411.02629). [doi:10.1112/jlms.70363](https://doi.org/10.1112/jlms.70363)
- S. Jang, *Tropical dynamics of Markov surfaces*, arXiv:[2306.11357](https://arxiv.org/abs/2306.11357).

### Analytic exceptional set and sieve

- R. C. Vaughan, *On a problem of Erdős, Straus and Schinzel*, Mathematika **17** (1970), 193–198. [doi:10.1112/s0025579300002886](https://doi.org/10.1112/s0025579300002886)
- W.-C. S. Suen, *A correlation inequality and a Poisson limit theorem for nonoverlapping balanced subgraphs of a random graph*, Random Structures Algorithms **1** (1990), 231–242. [doi:10.1002/rsa.3240010210](https://doi.org/10.1002/rsa.3240010210)
- S. Janson, *Poisson approximation for large deviations*, Random Structures Algorithms **1** (1990), 221–229. [doi:10.1002/rsa.3240010209](https://doi.org/10.1002/rsa.3240010209)
- C. Elsholtz, T. Tao, *Counting the number of solutions to the Erdős–Straus equation on unit fractions*, J. Aust. Math. Soc. **94** (2013), 50–105. [doi:10.1017/s1446788712000468](https://doi.org/10.1017/s1446788712000468)
- T. Tao, [On the number of solutions to \(4/p = 1/n_1+1/n_2+1/n_3\)](https://terrytao.wordpress.com/2011/11/19/on-the-number-of-solutions-to-4p-1n1-1n2-1n3/) (blog, 2011; Mordell reciprocity, 3-fold lift).
- P. Shiu, *A Brun–Titchmarsh theorem for multiplicative functions*, J. Reine Angew. Math. **313** (1980), 161–170.
- M. Nair, *Multiplicative functions of polynomial values in short intervals*, Acta Arith. **62** (1992), 257–269. [doi:10.4064/aa-62-3-257-269](https://doi.org/10.4064/aa-62-3-257-269)
- M. Nair, G. Tenenbaum, *Short sums of certain arithmetic functions*, Acta Math. **180** (1998), 119–144. [doi:10.1007/bf02392880](https://doi.org/10.1007/bf02392880)
- K. Henriot, *Nair–Tenenbaum bounds uniform with respect to the discriminant*, Math. Proc. Cambridge Philos. Soc. **152** (2012), 405–424; erratum **157** (2014); arXiv:[1102.1643](https://arxiv.org/abs/1102.1643). [doi:10.1017/s0305004111000752](https://doi.org/10.1017/s0305004111000752)
- J. B. Friedlander, H. Iwaniec, B. Mazur, K. Rubin, *The spin of prime ideals*, Invent. Math. **193** (2013), 697–749.
- H. Halberstam, H.-E. Richert, *Sieve Methods*, Academic Press, London, 1974.
- J. Friedlander, H. Iwaniec, *Opera de Cribro*, AMS Colloquium Publications **57**, 2010.
- K. K. Norton, *On the number of restricted prime factors of an integer. I*, Illinois J. Math. **20** (1976), 681–705. [doi:10.1215/ijm/1256049659](https://doi.org/10.1215/ijm/1256049659) (Lemma 6.3: Mertens constants in arithmetic progressions).
- A. Languasco, A. Zaccagnini, *A note on Mertens' formula for arithmetic progressions*, J. Number Theory **127** (2007), 37–46. [doi:10.1016/j.jnt.2006.12.015](https://doi.org/10.1016/j.jnt.2006.12.015)
- A. Granville, K. Soundararajan, *The distribution of values of \(L(1,\chi_d)\)*, Geom. Funct. Anal. **13** (2003), 992–1028. [doi:10.1007/s00039-003-0438-3](https://doi.org/10.1007/s00039-003-0438-3)
- H. Iwaniec, *Primes represented by quadratic polynomials in two variables*, Acta Arith. **24** (1973/74), 435–459.
- H. Iwaniec, *The half dimensional sieve*, Acta Arith. **29** (1976), 69–95.
- J. Brüdern, É. Fouvry, *Lagrange's four squares theorem with almost prime variables*, J. Reine Angew. Math. **454** (1994), 59–96.
- J. Brüdern, É. Fouvry, *Le crible à vecteurs*, Compositio Math. **102** (1996), 337–355.
- G. Harman, *Prime-detecting sieves*, LMS Monographs **33**, Princeton, 2007.
- Ju. V. Linnik, *An asymptotic formula in an additive problem of Hardy–Littlewood*, Izv. Akad. Nauk SSSR Ser. Mat. **24** (1960), 629–706.
- Z. Zheng, *Primes in simultaneous arithmetic progressions*, arXiv:[2512.22798](https://arxiv.org/abs/2512.22798).
- E. Bombieri, J. B. Friedlander, H. Iwaniec, *Primes in arithmetic progressions to large moduli*, Acta Math. **156** (1986), 203–251. [doi:10.1007/BF02399204](https://doi.org/10.1007/BF02399204)
- D. R. Heath-Brown, *Hybrid bounds for Dirichlet \(L\)-functions*, Invent. Math. **47** (1978), 149–170. [doi:10.1007/BF01578069](https://doi.org/10.1007/BF01578069)
- L. Grimmelt, J. Merikoski, *Twisted correlations of the divisor function via discrete averages of \(\mathrm{SL}_2(\mathbb{R})\) Poincaré series*, arXiv:[2404.08502](https://arxiv.org/abs/2404.08502).
- J.-M. Deshouillers, H. Iwaniec, *Kloosterman sums and Fourier coefficients of cusp forms*, Invent. Math. **70** (1982/83), 219–288. [doi:10.1007/BF01390728](https://doi.org/10.1007/BF01390728)
- É. Fouvry, H. Iwaniec, *Gaussian primes*, Acta Arith. **79** (1997), 249–287. [doi:10.4064/aa-79-3-249-287](https://doi.org/10.4064/aa-79-3-249-287)
- É. Kowalski, P. Michel, W. Sawin, *Bilinear forms with Kloosterman sums and applications*, Ann. of Math. **186** (2017), 413–500. [doi:10.4007/annals.2017.186.2.2](https://doi.org/10.4007/annals.2017.186.2.2)
- V. Blomer, D. Milićević, *The second moment of twisted modular \(L\)-functions*, Geom. Funct. Anal. **25** (2015), 453–516. [doi:10.1007/s00039-015-0318-7](https://doi.org/10.1007/s00039-015-0318-7)
- I. D. Shkredov, *Modular hyperbolas and bilinear forms of Kloosterman sums*, J. Number Theory **220** (2021), 182–211. [doi:10.1016/j.jnt.2020.11.008](https://doi.org/10.1016/j.jnt.2020.11.008)
- A. Pascadi, *Non-abelian amplification and bilinear forms with Kloosterman sums*, Geom. Funct. Anal., accepted; arXiv:[2511.08445](https://arxiv.org/abs/2511.08445).
- D. Milićević, Y. Qin, H. Wu, *Bilinear forms with Kloosterman sums and moments of twisted \(L\)-functions*, arXiv:[2511.07550](https://arxiv.org/abs/2511.07550).
- V. Blomer, A. Pascadi, *Bilinear forms with Kloosterman sums via quadratic characters*, arXiv:[2607.24311](https://arxiv.org/abs/2607.24311).
- K. Nath, L. Xie, *Almost primes and primes that are sums of two squares plus one*, arXiv:[2501.16723](https://arxiv.org/abs/2501.16723); Acta Arith. 2025. [doi:10.4064/aa250227-19-11](https://doi.org/10.4064/aa250227-19-11).
- E. Fuchs, C. Hsu, J. Rickards, D. Schindler, K. E. Stange, *Primes represented by shifted quadratic forms: on primitivity and congruence classes*, arXiv:[2504.20289](https://arxiv.org/abs/2504.20289); Acta Arith. **222** (2026), 371–391.
- C. Maire, *Genus theory and governing fields*, New York J. Math. **24** (2018), 1056–1067.

### Computation

- S. E. Salez, *The Erdős–Straus conjecture: new modular equations and checking up to \(N=10^{17}\)*, arXiv:[1406.6307](https://arxiv.org/abs/1406.6307).

## License

Copyright (c) 2026 Riley Betts Ltd. This repository is released under the
MIT License; see `LICENSE`. Lean, Python, and the programme notes carry
the same notice in their file headers.

`Stormer.lean` is adapted from Mathlib PR #42040 and remains under the
Apache License 2.0, Copyright Alexander Benjamin Worth Burns and Ravi
Bajaj; see `LICENSE-APACHE`. It is library only, not a proof of the
conjecture.

Contributions: `CONTRIBUTING.md`. Pins live in `lean-toolchain`,
`lakefile.toml`, `lake-manifest.json`, and `requirements.txt`.
