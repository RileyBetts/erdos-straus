<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Programme brief — Erdős–Straus archive v0.23

**21 August 2026.** This file is the front door of the zip. It is not a
theorem. **No proof of the Erdős–Straus conjecture is claimed or
achieved.** The archive is public so that the mathematical community can
use the record.

**Martyn Riley, of Riley Betts Ltd**, facilitates the automation and the
high-level strategy (novel routes, recorded negative results, documentation
procedure for the agents). He makes no claim to expertise in number
theory, combinatorics, or geometry. Details: `README.md`.

The mathematical and formalization work is a collaboration of Anthropic
agents, Grok 4.6, and Cursor agents, with Lean 4, Mathlib, and numerical
test resources. It is not a record of human coauthorship of the mathematics.

We have a Lean formalization of the elementary Bright–Loughran arithmetic
and of several negative tests (split fibres; Campana packaging does not
reach the positive octant; mixed-sign occupancy does not imply a positive
point; the affine equation has no Vieta involution). The remaining
geometric question is occupancy of **one real component** of a surface that
already has integral points in the other.
Bright–Loughran Theorem 1.8 is treated as a non-obstruction statement, not
as existence of a positive-octant integral point.

**Postscript (v0.23).** Joint monodromy independence (FKMS
arXiv:2511.09459, gallant GKR) does not apply to
\(\chi_2(d_2)\chi_3(d_3)K(\,\cdot\,;D)\): not a sheaf on a fixed
\(\mathbf{F}_q\); after switching a prime modulus cannot exceed
\(\sqrt{x}\); composite \(D\) has \(\mathbf{SO}_4\)-type monodromy, not
gallant. Not T(3) progress. Write-up:
`erdos-straus-T-3-monodromy.md`. Range check: `t3_monodromy_ranges.py`.
The four T(3) completion looks (Zheng, \(\delta\)-symbol, FKMS, and the
Maynard near-BV slab) fail by distinct mechanisms at the same
varying-modulus correlation: `erdos-straus-varying-modulus-gap.md`.

**Postscript (v0.22).** Joint Heath-Brown δ-expansion at the CRT
modulus does not avoid the BV-wall degeneracy: Farey \(Q_\delta\) cannot
both open \((m,\nu)\)-bilinear and complete the AP index \(k\) when
\(Q_D\ge 1/2\). At \((0,1/2,1/2)\) that identity does not apply (\(k\)
absent; additive characters already bilinear). No bound is claimed up
to \(D\sim x\) or \(x^{3/2}\). Not T(3) progress. Write-up:
`erdos-straus-T-3-delta.md`. Range check: `t3_delta_ranges.py`.

**Postscript (v0.21).** Uneven Zheng bookkeeping (leave one kernel
Type I / polylog, apply Theorem 1.1 to a sub-pair) does not move the
T(2) plane union BV \(\cup\) Zheng (\(0.518\)). The T(3) cube table
shifts at leftover \(\varepsilon=7/36\) (covered \(0.181\to 0.331\)),
but the stall cells \((1/2)^3\) and \((0,1/2,1/2)\) stay uncovered.
The covering-witness 91% at \(a,m\le\log^2 p\) is not \(r_\chi\) mass.
Not T(3) progress. Write-up: `erdos-straus-T-2.md` §A2.3.

**Postscript (v0.20).** T(2) via Zheng arXiv:2512.22798 is a range
no-go on the symmetric cell \(d_1\approx d_2\approx\sqrt{x}\)
(Theorems 1.1 and 1.2 both miss it; \(d_1\approx d_2\approx x^{1/4}\)
is ordinary BV). Well-factorability of \(\chi\) is a transfer lemma,
not Def. 1.1 for \(\chi\cdot 1_{d\le D}\). Squarefree support is not
in Lean; isolate the powerful part. Not T(2)\(^+\) claimed; not T(3)
progress; Part B excluded. Write-up: `erdos-straus-T-2.md`,
`zheng-wellfactorable.md`. Range check: `t2_zheng_ranges.py`. Do not
densify covering.

**Postscript (v0.19).** The stall obstruction is a one-line lemma, not
a grid artefact: if \(M+N=1\) and \(Q=\tfrac12\) (log-exponents), then
\(M<Q\) and \(N<Q\) cannot both hold. At the Bombieri–Vinogradov wall
there is no bilinear cell; at least one Type II factor folds. Write-up:
`erdos-straus-T-3.md`. Do not densify covering.

**Postscript (v0.18).** The \(r_\chi\) rewrite was reduced to an
explicit Kloosterman bilinear/trilinear form (Deshouillers–Iwaniec /
Fouvry–Iwaniec / FIMR template) and tested against Pascadi
Cor. 1.4/7.5, MQW Thm 1.1, and Blomer–Pascadi Thm 1.1. **No-go at the
stall** \(Q=x^{1/2+}\): dual lengths sit below the saving windows
(first genuine Blomer–Pascadi saving at \(Q\gtrsim x^{0.87}\)). Phase 0
ranked Blomer–Pascadi first (quadratic characters, all moduli); that
did not change the gate. Not a third escape; not a T(3) matching lower
bound. The joint well-factorable CRT-residue question is unchanged.
Write-up: `erdos-straus-T-3.md`. Range check:
`t3_kloosterman_ranges.py`. Do not densify covering.

**Postscript (v0.17).** The T(3) completion stall is now a sharp
question in the same genuinely hard frontier as roadmap §9's
Brauer-\(\alpha\) fusion (plan §4w): does a joint well-factorable
weight framework exist for a CRT residue that depends on the summed
triple, and if not, can one be built for the three-kernel case?
Existing BFI/Maynard machinery beats \(x^{1/2}\) only for a *fixed*
residue; the joint remainder moves with \((d_1,d_2,d_3)\). Not C1, not
H_ES, not the next compute step. Write-up: `erdos-straus-T-3.md`. The
analytic worklist is `erdos-straus-sieve-desk.md`; the geometric
questions are `erdos-straus-loughran-orbit.md`. Do not mix the two
lanes in one note. Do not densify covering.

**Postscript (v0.16).** E_power's second-moment lemma is proved
(Lemma SM, `erdos-straus-E-power.md`): \(\Delta\ll\mu^2/T\) plus
remainders that are \(o(\mu^2/T)\) on \(T=\mu/\eta\), by an elementary
divisor-in-AP bound. The implied constant is checked on Lean cells
through \(A=2000\) (`e_power_suen_moments_large.py`): \(R_\Delta\)
settles at \(0.13\) along \(T/\mu\approx 5\), \(R_\delta=O(1)\), Suen
loss \(<0.15\,\mu\). v0.15 remains the \(A\le 240\) check. Not Lean.
Do not densify covering.

**Postscript (v0.15).** E_power's second-moment gate is checked on the
Lean covering cells at \(A=24\to 240\) (`e_power_suen_moments.py`).
\(R_\Delta=T\sum\mu_\ell^2/\mu^2\) **falls** (OLS slope \(\approx-0.013\)
at fixed \(T\le 53\); flat at \(T=97\)). Along the schedule
\(T/\mu\approx 4.5\), \(R_\delta\) is flat and the Suen loss stays
\(<0.15\,\mu\). The \(A=48\) extrapolation does not fail at the first
decade of growth. Remaining at that stamp: \(A>240\), and the written
implied-constant lemma (now Lemma SM). Not Lean. Do not densify covering.

**Postscript (v0.14).** **E_power claimed:**
\(S_A(x,2x)\ll x^{1-\delta}\) for \(A=\exp(c\sqrt{\log x})\), effective
constants, via hub-conditioned Suen/Janson plus a small-\(c\) count
transfer (`erdos-straus-E-power.md`). This is roadmap §6 / Gate A's
paper: a power of \(x\), strictly stronger than Vaughan (1970), and
independently publishable if the programme stops here. It sits below
the k-budget ceiling and does not empty the box. Gate A still forbids
`AnalyticSurvivorBound` in Lean. E_lane remains the \(d=1\) ClassRough
floor, below Vaughan. Dummy covering remains the live kill of a
QED-scale ClassRough schedule. Not Lean. Do not densify covering. Do
not run \(x=10^{10}\).

**Postscript (v0.13).** **E_lane claimed:**
\(x\exp(-c'\sqrt{\log x}\,\log\log x)\) as the \(d=1\) floor, below
Vaughan, effective constants, one dimension-uniform FL lemma
(`erdos-straus-T-A.md`). T(A)\(^+\) at fixed \(A\) is claimed; growing
\(A\) needs that lemma. Selberg does not re-create the covering law:
the \(\Gamma\)-inflation is \(o(\log^2 A)\) as a theorem, so the
schedule's upper-bound half survives unconditionally at the
combinatorial constant. Expected \(B(A)=O(\log A)\). The §4h full-box
\(x^{1-c}\) remains Gate A. Dummy covering remains the live kill. Not
Lean. Do not densify covering. Do not run \(x=10^{10}\).

**Postscript (v0.12).** T(3) kernel is a theorem:
`classRough_123_iff_certificates`. **T(3)\(^+\) is claimed:**
\(S(3,x)\ll(\log x)^{-3/2}\) (`erdos-straus-T-3.md`). T(1) by citation
(Iwaniec, Acta Arith. **24**, plus Fuchs et al.). The T(3) lower bound
is a three-step plan: Iwaniec per slice; Brüdern–Fouvry to combine;
completion of \(q>x^{1/2}\) (named risk, beyond BV). Two escapes for
the paper's outlook: weaker \(c_-\), or the \(r_\chi\)-detector.
T(A)\(^+\) — uniform Selberg at fixed \(A\) (`erdos-straus-T-A.md`,
`c4_sieve_constant.py`). Measurement has saturated (\(c'\) still
climbing at \(10^9\); collision \(\sim 10^{24}\)). Defect layer: exact
iff \(\lambda(4a)\mid 2\).

**Postscript (v0.11).** Certificate lemma inhabited (`oddRealChar_four`,
\(\chi_4\)). Converse is an \(\omega\)-gap (\(84.6\%\) at \(x=10^6\),
\(A\le 40\)), not a near-equivalence. Shared-certificate dummy covering
does not fire. Working note: `erdos-straus-T-A.md`; measurement:
`c4_certificates.py`. Do not densify covering. The analytic worklist
(`erdos-straus-sieve-desk.md`) is a question list, not the next compute
step.

**Postscript (v0.10).** T(A) scans, Gate A, and the analytic worklist are
in this archive (`erdos-straus-T-A.md`, `erdos-straus-E-partial.md`,
`erdos-straus-sieve-desk.md`). Do not densify covering.

**Postscript (same day as v0.9).** A triage of this package: the geometric
and analytic lanes are one lane. Existing geometric tools reduce to the
divisor / joint-roughness problem; there is no Vieta dynamics
(`NoVieta.lean`). The questions below remain the right questions for
**class-theory and an effectivity framework** — genuinely worth answering,
and not a request for a proof of occupancy with Harpaz, Cao–Xu, or
Theorem 1.8. The technical main effort on our side is now T(A) (candidates C4_1:
the joint density at fixed covering width, with \(C(A)\) as a sequence
in \(A\)), not a further fibration
and not a pair asymptotic. The analytic worklist for T(A) is
`erdos-straus-sieve-desk.md`; do not densify covering.

This brief is the programme archive front door. Keep
the geometric lane (`erdos-straus-loughran-orbit.md`) separate from the
analytic covering / DFI lane.

---

## Open geometric questions (numbered)

Each item is a bounded mathematical question. Lean is optional; nothing
below requires a formalization.

### 1. Notation for “no integral BM obstruction against a real component”

Define
\[
U(\mathbb{A}_{\mathbb{Z}})^{C_+} \;:=\; C_+ \times \prod_p U(\mathbb{Z}_p),
\qquad
\bigl(U(\mathbb{A}_{\mathbb{Z}})^{C_+}\bigr)^{\mathrm{Br}}.
\]
Is this the right formalization of that phrase, in the integral-model
conventions of Bright–Loughran 2020? Does Theorem 1.8 amount to its
nonemptiness for the Erdős–Straus pairs \(\mathcal{U}_n\)?

We read Theorem 1.8 as exactly
\(\bigl(U_n(\mathbb{R})_+\times\prod_p\mathcal{U}_n(\mathbb{Z}_p)\bigr)^{\mathrm{Br}}\neq\emptyset\),
and as an obstruction to strong approximation, not to existence. Algebraic
Brauer is \(\operatorname{Br}\mathbb{Q}\), so the pairing is against the
transcendental quaternion \(\alpha=(-u_1/u_3,-u_2/u_3)\). Open: whether
this notation matches Bright–Loughran 2020.

### 2. The 9/5 separator: confirm or refute an adelic sketch

The Schinzel surface \(9/5=1/x+1/y+1/z\) has mixed-sign integer points and
**no** positive integer points (kernel: `SchinzelSep.lean`,
`SchinzelDecide.lean`). We do **not** claim a Brauer–Manin computation in
Lean.

Hand sketch (candidates doc S1_1; **not kernel-checked**):

- \((1,-5,1)\) is a \(\mathbb{Z}\)-point; \(\alpha=(-1,5)\);
  Hilbert symbol \((-1,5)_2=+1\); \(\operatorname{inv}_\infty=+1\).
- \((9/11,45/11,3)\) lies on the surface over \(\mathbb{Q}\) and in
  \(\mathbb{Z}_2^3\) (11 is a 2-adic unit); \(\alpha=(-3/11,-15/11)\);
  Hilbert symbol at 2 is \(-1\).
- Glueing \(C_+\) at infinity to the finite places of the mixed-sign
  global point is **not** a proof: \(\operatorname{inv}_\infty\) flips.
  Retune \(p=2\) with the second point; take any real \(C_+\) point at
  infinity (\(\operatorname{inv}_\infty=-1\)). Product of invariants
  \(+1\).

**Open:** are those two 2-adic Hilbert symbols correct, and is this the
analogue of Theorem 1.8 on the 9/5 \(\mathbb{Z}\)-model (Remark 1.10)?
Treat this as a computation to confirm or refute, not as a claimed result.

### 3. Do refined obstructions see finite empty trees?

On the separators, \(C_+\) fails because the Archimedean box makes the
positive search tree finite and empty (Bright–Loughran 1.9’s finiteness
promoted from approximation-failure to existence-failure). Ordinary BM
does not encode that. Mitankin–Uhlemann Campana/Darmon Hasse holds on
Markoff orbifolds while integral points fail, so those sets do not see it
either.

**Open:** does any refined obstruction in the semi-integral literature
detect “the positive tree is finite and empty”? If yes, the extra
Archimedean hypothesis below may collapse into a single obstruction
hypothesis. If no, the phenomenon lives in effectivity / integrality,
not in cohomology.

### 4. The wide regime (where Erdős–Straus actually lives)

The Schinzel class splits:

- **Narrow** (\(m/n\) bounded below, e.g. \(1<m/n<3\)): the \(C_+\) tree
  is finite; existence is a decision procedure (`SchinzelDecide.lean`).
- **Wide** (\(m/n\to 0\)): the tree widens like \(n/2\) for \(m=4\).
  This is the Erdős–Straus regime.

A “wide-tree separator” **cannot** appear in the narrow band. The honest
kill test for a class principle is a pair with \(0<m/n\le 1\), mixed-sign
yes, positive no. For \(m=4\) that search *is* Erdős–Straus.

**Open:** does a class-level framework in this literature assert anything
in the **wide** regime? If so, what is its Erdős–Straus instance? (Not:
prove occupancy for \(4/n\).)

### 5. TUB-EP as a class statement — recognise, reject, or refine

Working formulation (not claimed): a flat affine \(\mathbb{Z}\)-model of
a log K3, distinguished component \(C_+\), torus \(\mathbb{G}_m^2\) whose
action need not extend, Brauer generator separating the real components,
\(U(\mathbb{Z})\) nonempty and finite, BM set in \(C_+\) nonempty
\(\implies\) \(U(\mathbb{Z})\cap C_+\neq\emptyset\).

For \(\{U_n\}\) the hypotheses are Bright–Loughran (box, mixed-sign,
Theorems 1.2/1.5/1.8) and the conclusion is Erdős–Straus. If the only
member of the class is \(\{U_n\}\), this is the conjecture relocated.

The separators show that mixed-sign occupancy plus a box is **not**
enough. A refined schema (C11) adds Archimedean non-degeneracy
(\(m/n\to 0\) along the family). That hypothesis is necessary in the
narrow band; it is not an engine.

**Open:** is TUB-EP, or C11, something the literature would recognise,
reject, or refine as a class? A named extra hypothesis, or a named
counterexample in Schinzel’s family, would settle the question.

---

## What these questions are not

- Prove the Erdős–Straus conjecture, or treat Theorem 1.8 as a point of
  \(C_+\).
- Apply Harpaz (JEMS 2019) or Cao–Xu. Every conic fibre of \(U_n\) is the
  **split** conic \((Ax-nt)(Ay-nt)=(nt)^2\), \(A=4t-n\)
  (`ConicFiber.fiber_identity`). The real-compatible twist \(V_{n,d}\) is
  still split along \(\pi=u_1,u_2,w\) (`TwistDescent.lean`). Even a
  matching Harpaz 1.0.1 would be \(S\)-integral with \(2\in S\).
- Why ES models have integral points when Markoff models do not.
  \(U_n(\mathbb{Z})\) is never empty (`esZ_nonempty`). Markoff emptiness
  is emptiness of *all* integral points. Campana Hasse on Markoff
  orbifolds does not move a mixed-sign ES point into \(C_+\`.
- Densify the analytic covering, produce an explicit \(X_0\) from an
  ineffective Hasse principle, or formalize Theorem 1.8 in Lean.
- Merge Bounded-A / L8–L9 covering from the prior `erdosstrauss`
  archive, or treat Bradford 2026 as QED. Selected artifacts from that
  tree are library/docs only (`erdos-straus-prior-archive.md`).

Effectivity (an explicit threshold) is a second conversation. This
repository can absorb an explicit \(X_0\); it cannot absorb
“sufficiently large”.

---

## Kernel facts (one line each)

| Fact | Where |
|---|---|
| Mixed-sign points for every \(n\ge 2\); box \(\min\|u_i\|\le 3n/4\) | `esZ_nonempty`, `esZ_min_le` |
| \(\operatorname{inv}_\infty\alpha=-1\) exactly on \(C_+\) | Bright–Loughran Lemma 3.1; Lean `lemma31` |
| Split-fibre identity and divisor correspondence, all \(n\ge 2\) | `ConicFiber.lean` |
| Twist \(w^2=d\,u_1u_3\) still split along \(u_1,u_2,w\) | `TwistDescent.lean` |
| `TubEpHypothesis` \(\Leftrightarrow\) `ErdosStraus`; implication proved, hypothesis not discharged | `ErdosStrausBLRoute.lean` |
| 9/5 signed point; 9/5 and 13/7 have no positive point | `SchinzelSep.lean`, `SchinzelDecide.lean` |
| Theorem 1.8 not claimed as a point of \(C_+\) | this file; candidates C11 |

---

## How to read the zip

Start here, then:

1. Analytic: `erdos-straus-E-power.md` (Gate A's paper: \(S_A\ll x^{1-\delta}\);
   second-moment check \(A=24\to 240\)).
   `erdos-straus-T-A.md` (T(A) working note, including the
   certificate measurements).    `erdos-straus-E-partial.md` (Gate A).
   `erdos-straus-sieve-desk.md` is the vector-sieve question list
   (T(A)\(^+\) / \(C_{\mathrm{sieve}}(A)\); E_lane; E_power; T(3)
   completion; not a request to densify covering).
   `erdos-straus-T-3.md` is the T(3)
   statement, upper-bound argument, three-step lower-bound plan, the
   \(r_\chi\to\) Kloosterman range no-go, and the joint well-factorable
   CRT-residue question (frontier, with roadmap §9).
   `erdos-straus-T-2.md` is the Zheng two-modulus look: range no-go on
   \(d_1\approx d_2\approx\sqrt{x}\), not a T(2)\(^+\) claim.
2. Geometry: `erdos-straus-loughran-orbit.md` — the same five questions
   at length, with what not to treat as a proof path.
3. `erdos-straus-candidate-conjectures.md` — C4_1 = T(A); S1, **S1_1**,
   C11, C3_1, C5_2. Scoring ticks on C11 are withdrawn; S1_1 is a sketch.
4. `README.md` — build; Layer A axiom table.
5. Prior archive as library, not a merge:
   `erdos-straus-prior-archive.md`, `erdos-straus-bradford-lemma3.md`,
   `erdos-straus-leochlon.md`; Lean `Leochlon.lean`, `Stormer.lean`.
6. Lean, if wanted: `lean ErdosStraus.lean` (T(3) kernel:
   `classRough_123_iff_certificates`); `lean ConicFiber.lean TwistDescent.lean SchinzelSep.lean SchinzelDecide.lean NoVieta.lean`
   (Lean ≥ 4.33, no Mathlib). Full build: `lake exe cache get && lake build`
   against the pinned Mathlib in `lakefile.toml`.

The research record (`erdos-straus-novel-structures-plan.md`) and the
analytic roadmap (`erdos-straus-road-to-lean-qed.md`) are included for
completeness. They are the diary, not the open-question list. The
covering / DFI lane is compiled and is a different workstream.

This archive is **v0.23** of the working tree. It does not prove
`theorem erdos_straus`. There are no `sorry`s on the QED line; do not
add a fake one.
