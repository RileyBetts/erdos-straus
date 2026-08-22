<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Candidates for C: Statements That May Meet the Acceptance Specification
## v0.5 — 20 Aug 2026

*(v0.5: C4_1 is T(A), not a pair asymptotic. Growing \(A\) at
\(x=10^9\), \(A\le 200\): \(\mathrm{cond}\to 1\),
\(\log\hat C\sim 0.104\log^2 A<\kappa\). The x-scan at A∈{40,80},
x=10^5→10^9, returns compounding e(a)−1, not Mertens drift. v0.4 was the
joint-lane freeze: geometry reduces to the same analytic core;
`NoVieta.lean`; G–S memo. v0.3 added S1_1 and `SchinzelDecide.lean`. C3
frozen at C3_1; C5 line closed at C5_2; C7 first search recorded at
C7_1. Scoring ticks on C11 remain withdrawn. The 1.8 analogue is **not**
kernel-checked. Geometric QED with existing tools is not the technical
main effort — plan §4v.)*

**Riley Betts Erdős–Straus programme, 19 August 2026.**
Companion to `erdos-straus-conjecture-spec.md` (requirements R1–R8).
Status legend: each candidate lists its R3 input class (1 = spectral/bilinear,
2 = algebraic rigidity, 3 = global geometry), the requirements it plausibly
passes, and its **primary risk** — the requirement most likely to kill it.
None is asserted true; several are expected to fail. That is what a candidate
list is for.

---

### C1 — Structured-Modulus Dispersion (the reference candidate)
**Statement.** For the growing divisor family (a, d ≤ exp(c√log x), κc² > 1),
the shifted values p + 4a²d over hard primes p ≤ x admit level of
distribution 1 in the dispersion sense: bilinear forms in the divisor
condition q ∣ p + 4a²d, q ≡ −1 (mod 4ad) exhibit square-root cancellation
uniformly in the family, after removal of the explicit character-coset main
terms.
**Input class:** 1 (DFI/Kloosterman; Bombieri–Friedlander–Iwaniec).
**Passes:** R1 (wired), R4 (schedule built in), R5 (native divisor form),
R7 (dispersion proofs are effective), R8 (dispersion school's dialect).
**Primary risk: R2** — full compounded dispersion at this level may be ES
relocated; the relocation test (put it to an expert early) is mandatory.
This is H_ES in its most attackable dress.

### C2 — Reciprocity Coupling (rigidity super-multiplicativity)
**Statement.** The character conditions forced by survival (the §4p
square-coset exclusions) are, via quadratic reciprocity, jointly equivalent
to ≫ log²A multiplicatively independent conditions on the survivor; hence
the level-A survivor set in [x, 2x] has size ≪ x · 2^{−κ′ log²A} with
effective κ′ > 0 — character conditions compounding *beyond* their raw
covering mass.
**Input class:** 2.
**Passes:** R1 (feeds AnalyticSurvivorBound), R4 (if κ′ real), R5, R8
(statable now; classical language).
**Primary risk: R3 itself** — §4r measured the character layer as a
*boundary* layer whose aggregate equals the deterministic exclusions; C2
asserts reciprocity makes it strictly more. May be bookkeeping. Cheap to
probe further (extend §4r to cross-moduli correlations of forced symbols).
**Measured 20 Aug, C2 does not fire.** `c4_c2_symbols.py`, \(x=10^9\),
\(A\le 80\), 564 ClassRough survivors. Cross-covariance of Jacobi
\((p/q_1)(p/q_2)\) on survivors is noise: mean \(|z|\) is \(0.73\) on
covering pairs (\(q\equiv 3\pmod{4}\)) and \(0.89\) on inert pairs
(\(q\equiv 1\pmod{4}\)) at \(A=80\), against \(E|z|\approx 0.80\) for
independent coins. Flagship \((p/11)(p/19)\): \(z=-0.23\). Covering
symbols are independent square-coset exclusions (large marginals,
product of means). Inert \(q\equiv 1\pmod{4}\) cannot serve a \(d=1\)
slice; a few small ones (\(13,17\)) pick up \(O(1)\) bias — a small
compositum, not \(\gg\log^2 A\) extra bits. C2 as extra shrinkage also
has the **wrong sign** for \(\hat C\): extra independent characters
would make \(S/\prod\rho<1\); measured \(\hat C(80)=2.69\).
**Do not:** treat C2 as the source of the \(\log^2 A\) selection
constant. The leftover is still dummy slices / \(c'\) vs \(\kappa\).

### C3 — Triangle-Boundary Semi-Integral Existence Principle
**Statement.** Let (X, D) be a log K3 pair over ℚ with D a *totally split
triangle of lines* and interior containing 𝔾ₘ². Then semi-integral
(Campana/orbifold) points satisfy the Hasse principle with semi-integral
Brauer–Manin as the only obstruction, effectively; and the ES pairs satisfy
the hypotheses with empty obstruction (the semi-integral lift of BL Thm 1.8).
**Input class:** 3.
**Passes:** R2 (a class statement with independent life), R3 (not
interval-bound), R5 (global by design), **R6 by construction** — the Markoff
boundary is an irreducible conic, not a triangle; the triangle hypothesis is
the first natural Markoff-excluding condition the programme has identified.
**Primary risk: R6 residual + R7** — some *other* triangle-boundary
counterexample may exist; and orbifold methods are not yet effective. The
strongest geometric candidate on the list; the right question for the
Loughran orbit.
*(Status: frozen 20 Aug 2026 — see C3_1. The triangle does not exclude
Markoff; Campana Hasse does not imply a \(\mathbb{Z}\)-point of \(C_+\).
The live geometric statement remains TUB-EP, which is equivalent to ES.)*

### C3_1 — Freeze of C3 (three checks)
*(Examination record, 20 Aug 2026. C3 above is preserved as stated. This
section is the freeze: hypotheses, the Campana-to-\(C_+\) bridge, and
whether a named theorem \(T\) exists.)*

**Check 1 — do the ES pairs have a totally split triangle with interior
\(\mathbb{G}_m^2\)?** Yes. Bright–Loughran compute \(\operatorname{Br} U_n/\operatorname{Br}\mathbb{Q}\)
on the desingularization \(\widetilde{U}_n\), whose complement of three
boundary lines is a torus \(\mathbb{G}_m^2\) (\(\operatorname{Pic}=\mathbb{Z}\);
plan §4m). That is the geometry C3 names. It is a paper fact this
programme already uses; it is not a new Lean theorem.

**Check 2 — what would Campana/semi-integral Hasse produce, and does it
reach \(C_+\)?** Semi-integral points (Campana or Darmon) interpolate
between rational points of \(X\) and integral points of \(U=X\setminus D\).
Weights \(\omega_i=\infty\) recover \(\mathcal{U}(\mathbb{Z})\); finite
weights allow controlled meeting of the boundary. Occupying \(C_+\) is
`TubEpHypothesis`: a point of \(U_n(\mathbb{Z})\) with \(u_1,u_2,u_3>0\).
That is strictly stronger than a Campana point, and strictly stronger
than a *strict* Campana point (a rational point of \(U_n\) with orbifold
integrality). There is no lemma in this repository, and none in the
cited literature, converting a Campana point of an ES pair into a
positive-octant integral point.

The pattern is already in print on the comparison family. Mitankin–Uhlemann
(JLMS 2025; arXiv:2411.02629) prove that Markoff orbifold pairs
**satisfy the semi-integral Hasse principle**, and that they often have
strict semi-integral points while \(\mathcal{U}_m(\mathbb{Z})=\emptyset\).
Remark 1.5 there: Campana/Darmon points “do not behave in the way that
\(\mathcal{U}_m(\mathbb{Z})\) does”. So a class-level Campana Hasse
principle, even with empty obstruction, does **not** imply integral
points, hence does not imply `TubEpHypothesis`. C3 as written fails the
bridge to R1.

**Check 3 — is there a named \(T\)?** No. Mitankin–Uhlemann is a theorem
about Markoff orbifolds, not ES, and it is a theorem that Campana Hasse
*holds while integral points fail*. Bright–Loughran Theorem 1.8 is the
absence of a Brauer–Manin obstruction to ES, not existence in \(C_+\)
(already recorded: `tub_ep_iff_erdos_straus`; README “does not claim”).
No numbered result of Harpaz, Campana, or the Loughran orbit supplies
effective existence of a \(\mathbb{Z}\)-point of \(C_+\) on the ES pairs.
C3 is a research question, not \(C\).

**The claimed R6 discriminator is false.** C3 scored “R6 by construction”
because “the Markoff boundary is an irreducible conic, not a triangle”.
The compactification Mitankin–Uhlemann actually use is
\(X_m\subset\mathbb{P}^3\),
\(x_0(x_1^2+x_2^2+x_3^2)-x_1x_2x_3=m x_0^3\), whose boundary
\(D=X_m\setminus U_m\) has three irreducible components
\(D_i=\{x_0=x_i=0\}\) — a triangle of lines. Markoff, in the model the
orbifold literature uses, **has a triangle**. The triangle hypothesis
does not exclude the known negatives. The genuine ES-specific feature is
the split \(\mathbb{G}_m^2\) interior (with toric action not extending;
Cao–Xu does not apply). That feature is already in the TUB-EP packaging
and does not by itself produce a point of \(C_+\).

**Re-score.** R1: fail until a bridge from the output of \(T\) to
`TubEpHypothesis` exists. R2: the only statement that currently implies
ES through the kernel is TUB-EP itself, which is equivalent to ES.
A class-level *integral* Hasse principle for log K3s with split
\(\mathbb{G}_m^2\) interior would have independent life — and would
have to exclude Markoff by something other than a triangle. R6: not
cleared. R7: no explicit \(X_0\). R8(a): no numbered \(T\).

**Bounded next actions.** C3 as Campana packaging is not the QED line.
After plan §4v, an integral Hasse principle in \(C_+\) remains the
geometric *translation* of ES (`TubEpHypothesis`), not a proof path with
existing tools. Its honest geometric role is class-theory and an
effectivity framework (`erdos-straus-loughran-orbit.md`), not a Lean grind. Do not
write a C3_2 that replaces Campana by “strict Campana” without a lemma
that strict Campana points of the ES pair are integral points in \(C_+\).

### C4 — Simultaneous Shift-Roughness (no totally-compliant primes)
**Statement.** For D(x) → ∞ suitably slowly, no hard prime p ≤ x (above an
explicit X₀) has p + 4a²d simultaneously avoiding all prime factors
q ≡ −1 (mod 4ad) for every a, d ≤ D(x): quantitatively, the joint
half-roughness event has correlation structure forcing density
≪ x^{−δ}/x — i.e., emptiness.
**Input class:** 1 (shifted-convolution / sums-of-two-squares-with-primes
technology: Fouvry–Iwaniec, Friedlander–Iwaniec lineage).
**Passes:** R1 (it *is* DivisorLandingBound restated), R4, R5, R8 (additive
number theory literature; independent interest: joint norm-form values at prime shifts).
**Primary risk: R4's teeth** — the joint event's positive correlations
(shifts share structure) may keep the density above 1/x forever; the §4r
escapee statistics are the place to measure the correlation matrix first.
*(Status 20 Aug, late: this is the analytic core, not a side-candidate.
The first theorem is T(A) = C4_1. Pairs were the wrong moment. Plan §4v.)*

### C4_1 — T(A): the joint density at fixed A (the first theorem)
**Statement.** For each fixed \(A\ge 1\),
\[
S(A,x)
\;=\;
\mathbb{P}\bigl(p+4a^2\text{ is class-rough for all }1\le a\le A
\bigm| p\le x\text{ hard}\bigr)
\;=\;
C(A)\prod_{a=1}^{A}\rho_a(x)\cdot\bigl(1+o(1)\bigr),
\]
with \(C(A)\) explicit. The ingredients are Wirsing /
Landau–Selberg–Delange Tauberian analysis for the joint multiplicative
condition, compositum densities for the shared-modulus layer
(\(C_{\mathrm{euler}}(80)=0.911\) in the \(1/q\) normalisation, flat
in \(A\); `c4_euler_factor.py`), and a selection constant — that
constant is the theorem's content. The programme's central exposure is
not “independence” and not “Suen's \(\Delta\) is small”, but
**\(C(A)\) grows sub-critically**: \(\log C(A)=o(\log^2 A)\), or at
least \(\limsup\log C(A)/\log^2 A<\kappa\). Working note:
`erdos-straus-T-A.md`. Opening case T(3): kernel exactness is
`classRough_123_iff_certificates`; T(3)\(^+\) is claimed
(\(S(3,x)\ll(\log x)^{-3/2}\)); the matching lower bound is a three-step
plan with named risk at \(q>x^{1/2}\) (`erdos-straus-T-3.md`); the
sharp remaining question is a joint well-factorable weight for the
moving CRT residue of the triple (plan §4w); the \(r_\chi\to\)
Kloosterman look is a range no-go at the stall. T(A)\(^+\)
uniform Selberg: \(\Gamma(\beta+1)e^{\gamma\beta}=\exp(o(\log^2 A))\)
as a theorem; expected \(B(A)=O(\log A)\) (`c4_sieve_constant.py`).
**E_lane claimed:** \(x\exp(-c'\sqrt{\log x}\,\log\log x)\) as the
\(d=1\) floor, below Vaughan. **E_power:** one-stage
\(S_A\ll x^{1-\delta}\) withdrawn; two-stage hub density is a
recorded negative through \(A=32\)
(`erdos-straus-E-power.md`, `erdos-straus-E-power-decision.md`).

**Why this, not pairs.** Pair ratios \(\rho_{ab}/(\rho_a\rho_b)\) stay
\(1.000\) out to \(A=120\) (`c4_two_shift_probe.py`,
`c4_growing_box_probe.py`). Quasi-independence of pairs can hold while
the \(A\)-fold intersection drifts. The object the level schedule uses
is \(S\), and \(S/\prod\rho_a\) is already \(2.69\) at \(A=80\) and
\(6.92\) at \(A=200\) when \(x=10^9\).

**Definitions (prerequisite).** Lean `ClassRough p a`: \(p+4a^2\) has
**no divisor** \(q\ge 3\) with \(q\equiv -1\pmod{4a}\) — composites
included, not only aligned primes. Then
\[
\rho_a(x)=\mathbb{P}(\mathrm{ClassRough}(p,a)\mid p\le x\text{ hard}),
\qquad
e(a)=\frac{\mathbb{P}(R_a\mid R_1,\ldots,R_{a-1})}{\rho_a}
=\frac{S(a,x)/S(a-1,x)}{\rho_a(x)},
\]
with \(S(0)=1\). The Mertens/LSD totient \(\sum_{a\le A}1/\varphi(4a)\)
(2.53 at \(A=40\), 2.97 at \(A=80\)) is the exponent for the
**prime-aligned** condition only. A prime-only control matches it to
15–18% (\(\beta=-2.91,-3.51\) on \(x\ge 10^6\)). ClassRough’s extra
composite layer is the genuine-extra Euler product
\(\Pi_{\mathrm{gen}}(a,\sqrt{x})\) (`c4_composite_layer.py`): composites
\(q\equiv -1\pmod{4a}\) with no aligned prime factor, cutoff \(\sqrt{x}\).
The \(A=40\) product of \(\rho^{\mathrm{CR}}/\rho^{\mathrm{prime}}\)
matches \(\prod\Pi_{\mathrm{gen}}\) to \(3\%\) at \(x=10^6,10^8,10^9\).
The slope ratio 0.86 compares two ClassRough quantities; the
\(2.7\)–\(3.0\) totient inflation is this product misread as a Mertens
exponent.

**x-scan and e(a) scaling, 20 Aug.** `c4_S_xscan.py`, \(x=10^5\to 10^9\)
(1,587,581 hard primes; 16 minutes). The slope plot remains a straight
line (\(R^2=0.997\) on \(x\ge 10^6\)), but that line is not yet an
exponent-level theorem: \(\mathrm{d}\log\hat C/\mathrm{d}\ln\ln x=\beta_S-\beta_{\prod}\)
identically, so “deficit” and “\(\hat C\) still climbing” are the same
fact. The discriminator with a kill in it is whether \(e(a)-1\) decays
as \(1/\ln\ln x\) (Mertens error term of T(A); schedule intact) or is
\(x\)-independent (compounds as \(C(A)\sim e^{\gamma A}\); dead at
QED-scale \(A\)).

Recorded, honest window \(10^6\to 10^9\) (lever arm of width 0.41;
564 survivors at \(A=80\), \(x=10^9\)):
- mean\((e-1)\) for \(a=10..80\): \(0.0094\to 0.0141\to 0.0168\), not
  falling.
- \((e-1)\cdot\ln\ln x\): \(0.025\to 0.041\to 0.051\), so not
  \(1/\ln\ln x\).
- \(\log\hat C(A)/A\) at \(x=10^9\) sits at \(\approx 0.012\) for
  \(A=40..80\), i.e. \(\hat C(A)\sim e^{0.012 A}\).
- \(\hat C(80)\): \(1.57\) (\(10^6\)) \(\to 2.23\) (\(10^8\)) \(\to 2.69\)
  (\(10^9\)), still climbing.
- OLS \(\beta_S/\beta_{\prod\rho}=0.868\) at both \(A=40\) and \(A=80\)
  on \(x\ge 10^6\).

The extra decade did not reverse the compounding in \(x\). Growing
\(A\) at the same \(x=10^9\) (`c4_growing_A.py`, \(A\le 200\), 15
minutes) splits that into two facts:
- \(\mathrm{cond}(a)\to 1\): \(0.995\) at \(a=80\), mean \(0.993\) on
  \(a=161..200\). The 564 survivors at \(A=80\) become 155 at \(A=200\)
  (retention \(0.275\)) against \(\prod_{81}^{200}\rho_a=0.107\). Extra
  \(d=1\) slices are mostly dummy.
- \(\log\hat C\) is not linear in \(A\). On \(A\ge 40\),
  \(\log\hat C\sim 0.104\,\log^2 A\) (\(R^2=0.998\)) against
  \(\kappa=0.139\). The local slope \(\log\hat C/A\approx 0.012\) on
  \(A\le 80\) was a small-\(A\) artefact; by \(A=200\) it has fallen to
  \(0.0097\), and \(\hat C(200)=6.92<\exp(\kappa\log^2 200)\approx 49\).
  Sub-critical, thin margin \(\kappa_{\mathrm{eff}}\approx 0.035\).

T(A) has to produce this \(\log^2 A\) selection constant (ClassRough
union, composites included), not a totient product with \(C\approx 1\)
and not the prime-aligned Euler factor \(C_{\mathrm{euler}}\approx 0.91\)
(flat in \(A\); zero residue collisions for \(A\le 200\)).
The d=1 box is not empty at \(A=200\).

**Literature (T(2) templates, one-day pass).** Partial precedent for
simultaneous factor-restrictions on several shifts:
- C. Hooley, *On the intervals between numbers that are sums of two
  squares: II*, J. Number Theory **5** (1973), 215–217 — infinitely
  many \(n\) with \(n\), \(n+h\), \(n+k\) all sums of two squares
  (ternary quadratic forms). Existence on \(\mathbb{Z}\), not an
  asymptotic at primes, not class-roughness of \(p+4a^2\).
- Hooley / Indlekofer pair correlation of the S2 indicator on integers
  (order \(x/\log x\) times a singular series) — T(2) for S2 on
  \(\mathbb{Z}\).
- H. Iwaniec, primes represented by shifted binary quadratic forms
  (half-dimensional sieve, 1972/1976) — one S2-type condition, not two
  simultaneous class-rough shifts of a prime.

No off-the-shelf T(2) for class-roughness of two shifts of primes
turned up. Any existing two-slice theorem is still the template for
T(2).

**Measured lemma, not the theorem.** For fixed distinct \(a,b\le 120\),
\(\rho_{ab}/(\rho_a\rho_b)=1.000\pm 0.05\) (433/435 pairs in
\([0.95,1.05]\) at \(A=30\), \(x=10^6\)). Keep this as a check on the
shared-prime main term of T(A); do not put it back in the title.

**Input class:** 1 (Wirsing / LSD; compositum / Chebotarev for the
shared-modulus layer; Fouvry–Iwaniec / Friedlander–Iwaniec for the
transfer to primes).
**Passes:** R1 (it is C4 at fixed \(A\)), R5, R8 (a genuine paper
without QED pretence).
**Primary risk: R4, renamed** — \(C(A)\) super-critical in \(\log^2 A\)
(\(c'\ge\kappa\)), or cond\(\equiv 1\) making extra covering fictitious
out to QED-scale \(A\). Growing \(A\) to 200 at \(x=10^9\) gave
\(c'=0.104<\kappa=0.139\) and cond\(\approx 1\). Not a completed kill;
the margin is thin.
**Do not:** jump from T(A) to H_ES; the invariant still caps a direct
assault on the full level statement. Do not revive the pair asymptotic
as the first theorem.

### C5 — Descent Through α: Harpaz on the Torsor
**Statement.** Descent through the quaternion class α (the generator of
Br Uₙ/Br ℚ) replaces Uₙ by a torsor Tₙ on which α trivializes; the induced
conic fibrations on Tₙ are **non-split** (the splitness that blocked Harpaz
lives exactly in α), satisfy Harpaz-type descent-fibration hypotheses for
n in the hard classes, and integral points on Tₙ in the correct real
component descend to positive-octant points on Uₙ.
**Input class:** 3 (with class-1 ingredients inside Harpaz's method).
**Passes:** R2 (torsor statements generalize), R3, **R5 evaded by design** —
this is the only candidate that converts the split-fiber no-go into a
constructive move: the obstruction class *is* the de-splitting twist.
R8 (precisely Harpaz/Uppal technology).
**Primary risk: unexamined mathematics** — whether Tₙ's fibrations actually
satisfy the independence hypotheses, and whether the real-component
bookkeeping (octant selection is exactly α's real invariant, BL Thm 1.2/1.5)
closes, is genuinely open; also R6 (check the Markoff torsor analogue does
not falsify the pattern). Programme-native, elegant, and the single most
concrete new mathematical question this list contains.
*(Status: examined 19 Aug 2026 — the statement above is FALSE as written;
see C5_1 for the refutation and the derivation of the corrected object.
C5_2 closes the named t-fibration: still split, not C.)*

### C5_1 — How the Corrected C5 Was Derived, and Why
*(Examination record, 19 Aug 2026; overclaims in the first scoring pass
corrected 20 Aug 2026. C5 above is preserved as stated so that the
refutation and repair remain auditable; this section is the derivation.
C5_2 closes the named t-fibration.)*

**Step 1 — the spec killed the naive version.** The octant invariant
(BL Theorems 1.2/1.5; `invInfES`) contradicts C5's real-place bookkeeping.
For a positive-octant point P, inv_∞ α(P) = −1 — and that is *precisely
the statement* that any α-trivializing object has no real points over C₊.
Concretely: α trivializes on the cover w² = −u₁u₃; but u₁u₃ > 0 on the
positive octant, so the trivializing cover is real-empty exactly where
points are needed. The Brauer class does not merely obstruct — it walls
its own trivialization off from the octant. C5's "correct real component"
does not exist. Because the dichotomy is a kernel theorem in the
repository, this refutation was a one-line check rather than a month's
confusion: the formalization paid for itself here.

**Step 2 — the failure dictated the repair.** The refutation is
sign-specific, so the repair is too: replace the α-trivializing cover by
the **real-compatible twists** w² = d·u₁u₃ for squarefree d > 0, which have
real points over C₊ by construction (u₁u₃ > 0 there). Every positive
solution lifts to exactly one twist — d = the squarefree part of u₁u₃ — so
existence on Uₙ ∩ C₊ becomes existence on *some* member of the twist
family. The box (`esZ_min_le`) bounds |uᵢ|, hence bounds that d by O(n²);
the family therefore *grows with n*. A finite list of d independent of n
is the fixed-box proposal R4 already eliminated. **C5-corrected
(working statement):** for every hard n above an explicit X₀, some twist
V_{n,d} with squarefree d = O(n²) has an integral point in the positive
real locus; the descent V_{n,d} → Uₙ ∩ C₊ is polynomial; and *if* a
numbered, unconditional theorem of Harpaz (or Swinnerton–Dyer) applies to
this family uniformly in n, it supplies the point. The "if" is not part
of what has been checked.

**Step 3 — computing the corrected object showed why it is better, not
merely fixed.** On the twists, a paper calculation gives pulled-back
quaternion data of the shape (−d, −u₂u₃). That calculation is not
kernel-checked, and does not by itself prove Harpaz's independence
hypotheses. Even if the fibers of V_{n,d} are non-split, the arithmetic
has not left the divisor problem. Fibering the d = 1 cover by u₂ = t and
rationalizing (u₁ = wz) gives u₁ = nt(z² + 1)/(4t − n), so integrality
becomes **(4t − n)q² ∣ nt(p² + q²)** — the divisor problem on norm-form
values; general d replaces p² + q² by norms from ℚ(√−d). That is the
analytic form of R5, restated, not evaded. Two consequences, one
sobering and one enabling:

1. *Conservation of difficulty (R2):* the twist family corresponds to
   the per-slice splitting conditions of §4p–§4r — the a = 1 escapee
   condition ("p + 4 is a sum of two squares") is the d = 1 twist's shadow,
   and the full slice family is the full twist family. The cover represents
   the analytic core faithfully; it does not evade it. The relocation risk
   is real for the corrected C5 too.
2. *Toolkit gain:* the problem now lives over ℤ[√−d] — imaginary-quadratic
   factorization, class-field structure, and Chebotarev machinery become
   available in coordinates the ℤ-formulation did not use. Comparing
   Selmer structures across quadratic twist families *is* Swinnerton-Dyer's
   engine; whether *this* family is in that engine's hypotheses is the
   open geometric question, not a theorem. (C5_2 closed it in the
   negative for the t-fibration named in this step.)

**Step 4 — re-scoring against the spec (corrected).** Neither a tick nor
a double-tick is earned yet.

- **R1.** The implication "integral point of V_{n,d} in the positive real
  locus ⇒ point of Uₙ ∩ C₊" is `TwistDescent.descent` (Gate 2). It does
  not imply `HardLandingHypothesis` until something produces the twist
  point.
- **R2.** Open — relocation risk as in (1) above. The quadratic-twist
  packaging has independent life as a class statement only after it is
  stated for a class, not solely for ES.
- **R3.** Fail for the named fibration — Harpaz 1.0.1 does not apply
  (Gate 3). A Schinzel-conditional route would also fail the QED contract
  (R7).
- **R4.** A d-family independent of n fails R4. Growth d = O(n²) from the
  box is necessary and not yet shown to be enough.
- **R5.** Analytic form: native (the displayed divisor/norm-form
  condition). Geometric form: **fail for the named t-fibration** — split
  (`t_fiber_section_cleared`). "R5 evaded by design" remains withdrawn.
- **R6.** Open — Markoff test unrun. If the same pattern applies to
  x² + y² + z² = 3xyz, C5-corrected is false.
- **R7.** Fail until an explicit X₀ exists.
- **R8.** Dialect: yes (Harpaz / Swinnerton–Dyer / Loughran orbit).
  Kernel Prop: no. "Harpaz-type hypotheses" is definition drift until a
  numbered theorem is named.

**Open, and where the corrected C5 died on the named fibration:** R5
geometric / R3 (Gate 3: split t-fibers). Remaining death sites if a
*new* fibration is proposed: R4 (uniformity / growth) and R6 (Markoff).
R1 cheap half is now kernel-checked (`descent`); R7 and R8(a) still wait
on a named \(T\) that applies.

**Bounded next actions:** closed as a candidate line by C5_2 (Gate 3
negative on the named t-fibration). The 20 Aug autopsy split \(\pi=u_1\)
and \(\pi=w\) on the same curve (`u1_fiber_section_cleared`). Gate 2
remains as infrastructure. A new fibration of \(V_{n,d}\) would restart
at the section test.

**Why this section exists.** The acceptance specification refuted its own
list's most attractive candidate within one careful pass, and the repair
the refutation forced contains sharper mathematics than the original idea.
Recording the derivation — not just the corrected endpoint — is the point:
failed candidates and their repairs are the programme's method made
visible, and the next person who has the naive idea finds both the
refutation and the road onward waiting.

### C5_2 — Gate-3 Failure of the C5_1 Fibration (Refutation Record)
*(20 Aug 2026. The corrected C5 of C5_1 fails at its named fibration; the
failure is kernel-recorded. C5_1 is preserved above as the derivation;
this section closes that line.)*

**The named theorem.** The relevant Harpaz result is Theorem 1.0.1 (JEMS
21 (2019) 627–664; arXiv:1511.04876; special case of 3.1.16). It is
**unconditional** as a theorem about \(S\)-integral points — its input is
Green–Tao–Ziegler, not Schinzel. It does **not** resolve R7 for this
programme: \(2\in S\), so the output is not a \(\mathbb{Z}\)-point of
\(C_+\). It requires a pencil of affine conics \(f x^2 + g y^2 = 1\)
whose linear factors supply seven independent classes in
\(\mathbb{Q}^*/(\mathbb{Q}^*)^2\), with fibers that are non-split
norm-1 tori.

**The failure.** The fibration C5_1 actually named — \(\pi : V_{n,d} \to \mathbb{A}^1\),
\(u_2 = t\) — has a rational section over \(\mathbb{Q}(t)\): with \(A = 4t - n\),

    \(u_1 = nt(d+1)/A\),   \(u_3 = nt(d+1)/(Ad)\),   \(w = nt(d+1)/A\),   \(u_2 = t\),

satisfying both defining equations identically (kernel identity
`t_fiber_section_cleared` in `TwistDescent.lean`; axioms: `propext`).
The generic fiber is therefore **split for every \(d\)**: the same
obstruction as §4t on \(U_n\), reproduced one level up the tower. Harpaz's
engine does not run; the \(\Delta_{ij}\) independence test is moot (the
pencil has only two \(t\)-linear forms, \(t\) and \(4t-n\), not four); and
even a formally matching theorem would deliver \(S\)-integral points with
\(2 \in S\), not \(\mathbb{Z}\)-points in \(C_+\) — an additional gate any
future claim must clear.

**The interpretive lesson.** C5_1's own derivation contained the
refutation unrecognized: the "rationalization \(u_1 = wz\)" presented
there as revealing the norm-form divisor condition is a rational
parametrization of the fiber — i.e., the proof of splitness. A conic that
rationalizes has a point. The gate, not the first write-up, caught it.

**Status of the twist idea.** The splitness of \(U_n\) is *conserved*
under the real-compatible twists along this fibration — the "too split"
pattern now stands on three data points (Cao–Xu at the boundary, §4t;
Harpaz on \(U_n\), §4t; Harpaz on \(V_{n,d}\), here). A different map
\(V_{n,d} \to \mathbb{P}^1\) with genuinely non-split fibers would be a
**new claim requiring new evidence, not a pass of this gate** — and any
such claim faces the standing procedural rule this episode establishes:
**run the section test first.** Before any Selmer or descent architecture
is discussed for any fibration of any object in this programme, exhibit
either a \(\mathbb{Q}(t)\)-section (closing the route) or a proof of
non-splitness of the generic fiber (opening it). C5/C5_1/C5_2 is closed
as a candidate line pending such a proof. The cheap autopsy of 20 Aug
(same rational curve, reparametrized) produced sections of \(\pi=u_1\)
and \(\pi=w\) as well (`u1_fiber_section_cleared`); changing the linear
projection does not open the line. The geometric lane's remaining
content is the integral principle in \(C_+\) already named as
`TubEpHypothesis` (C3_1: Campana packaging does not reach it).

### Gates used on C5_1

C5_1 would have been \(C\) only if one frozen statement passed all eight
requirements. The working statement, the eight gates, and their status
after C5_2:

1. **Freeze a kernel Prop (R8a).** Name \(T\). **Done for the named line:**
   Harpaz 1.0.1. Schinzel-conditional \(T\) remains forbidden.
2. **Descent lemma (R1, cheap half).** **Done** in `TwistDescent.lean`
   (`descent`, `lift`, `naive_cover_empty`). Certifies the cover; does
   not produce a twist point.
3. **Fibration data versus \(T\).** **Done, negative** — see C5_2.
4. **Growth of \(d\) (R4).** Moot for the closed line; live if a new
   fibration is proposed.
5. **Markoff discriminator (R6).** Unrun; live only for a new fibration.
6. **Relocation test (R2).** Live for a class-level rewrite, not for the
   closed t-fibration.
7. **Effectivity (R7).** Even a matching Harpaz 1.0.1 is \(S\)-integral
   with \(2\in S\), not an explicit \(\mathbb{Z}\) threshold.
8. **Close R1 in the kernel.** Not reached: there is no \(T\) that applies
   to the named fibration.

In-house now on the geometric lane: S1/C11 (9/5 is kernel-checked;
widen only in the \(m/n\le 1\) band). A new fibration of \(V_{n,d}\)
restarts at the section test, not at Selmer. C7 is the in-house
computation (see C7_1).

### C6 — Theory-4 Flatness (conditioned spectral residual)
**Statement.** The Selberg-L² residual of the survivor indicator at level Aⱼ
is εⱼ-flat against the (j+1)-st covering shell, with Σεⱼ < ∞ along the
annulus schedule (the boxed target of roadmap §8), the structured component
being exactly computable.
**Input class:** 1-adjacent (new equidistribution theory for explicitly
CRT-structured sets; rungs 1–3b built).
**Passes:** R1, R4, R5, R8-(a) (already near-statable formally).
**Primary risk: R2/R3** — at asymptotic scale flatness may be H_ES
relocated; the invariant's applicability to the *residual after designed
projection* is the unresolved crack (spec R3, input-class boundary). The
right home is the theory-4 paper, with the relocation question on page one.

### C7 — Bounded-Coupling Covering Family (the searchable one)
**Statement.** There exists an Egyptian-fraction identity family, beyond the
classical m-box, whose covering congruences deliver total mass
≥ (1+δ) log x at coupling degree O(1) per scale — breaking the Poisson
coupling law measured for the classical family — so that Suen-type
conditioning alone annihilates the survivor set.
**Input class:** none post-discovery (the discovery is combinatorial; the
sieve then suffices *because* R3's premise is voided for this family).
**Passes:** R1, R4, R5, R7; **R8 uniquely strongly** — falsifiable by
machine search in this archive, this quarter.
**Primary risk: probably false** — the coupling anatomy may be universal
across identity families (the programme's own conjecture). But it is the
only candidate whose truth-value can be attacked in-house, and disconfirming
it cleanly would itself harden R3 into a broader theorem.
*(Status: first search 20 Aug 2026 — see C7_1. No degree-1 identity in the
searched box covers a hard class; bounded-omega Type-I mass does not
break the coupling law at toy scale. Not a theorem; C7 remains probably
false.)*

### C7_1 — First in-house search
*(20 Aug 2026. Script: `c7_bounded_coupling_search.py`. Not a refutation
of C7 as an asymptotic statement; a bounded computation against the
search the candidate promised.)*

**Identities.** Degree-1 Witness identities \(n=qt+r\) with \(2\le q\le 30\),
coefficients of \(a(t),d(t),m(t)\) at most 4, and \(c\in\{1,2,3,4\}\):
193 identities, 92 distinct arithmetic progressions. All lie in the
classical easy classes (including reparametrizations of the Mordell
suite already in `ErdosStraus.lean`). None meets a hard residue class
mod 840; none has its AP contained in the hard classes. A polynomial
identity that killed a hard class would have shown up in this box if
its modulus were \(\le 30\) and its coefficients small. Schinzel (2000)
already says no single polynomial identity covers all \(n\); this search
says none of small linear type covers even one hard class.

**Coupling mass (Type-I, \(c=1\), \(q=4ad-1\), \(a,d\le A\)).** Total mass
grows like \(\log^2 A\) (two parameters). At \(A\le 64\) the
\(\omega(q)\le 2\) slice is still \(\sim 95\%\) of the mass, because
\(q\le 4A^2\) is small and \(\log\log\) has not grown — the same
limitation plan §4k recorded. The prime-modulus slice (\(\omega=1\))
grows slower than the total (1.54 → 3.06 against total 2.02 → 5.82
from \(A=8\) to \(A=64\)). Bounded-omega classes do not deliver an
independent extra \(\log x\) in this range.

**Verdict.** C7 is not confirmed. The searchable prediction — a new
identity family concentrating covering mass at coupling degree \(O(1)\)
— did not appear. The k-budget invariant still says a family of this
shape cannot reach mass \(>\log x\) at bounded fan-in. Widen the
coefficient box or the modulus only if a *named* new identity family
is proposed; do not grind larger random boxes as a QED lane.

### C8 — Thin-Exception Mop-Up (two-stage hybrid)
**Statement.** (i) The exceptional set at level A is contained, provably, in
an explicitly Frobenius-thin set: exceptions are totally character-compliant
in the §4r sense, with the compliance conditions growing with A. (ii) An
effective Chebotarev/Linnik-type bound shows the thin set is empty above an
explicit X₀.
**Input class:** 1 + 2 combined.
**Passes:** R1, R5, R7 (Linnik-type effectivity is the point), R8.
**Primary risk: the for-all gap at R4** — thinness arguments historically
deliver density zero, not emptiness; stage (ii) is where 78 years of
"almost all" results have always stalled. Included because the *structure*
of the exceptions (100% forced at a = 1; measured biases) is sharper here
than in any classical treatment, and sharp structure is what emptiness
proofs feed on.

### C9 — Discriminant-Uniform Spectral Equidistribution (theta route)
**Statement.** Roots of ν² ≡ −pd (mod q) equidistribute, DFI-style, with
power-saving error *uniform in the p-dependent discriminant* over the ES
family, at a strength sufficient to detect one root meeting the divisor
constraint q ≡ −1 (mod 4ad) per growing box — the class-group/theta-series
formulation of C1.
**Input class:** 1 (spectral theory of GL(2)/metaplectic forms;
Duke–Friedlander–Iwaniec, Toth).
**Passes:** R2 well (independent life: Heegner-point and class-group
equidistribution in thin p-dependent families), R4, R5, R8.
**Primary risk: uniformity** — fixed-discriminant DFI is a landmark;
p-dependent uniformity at this level is precisely beyond current spectral
technology, and R3-compliance does not make it near.

### C10 — Effective Uniform Log-Manin for the ES Cox Ring
**Statement.** The universal torsor of Ũₙ (Pic = ℤ; the Cox-ring equation is
essentially the witness equation cn + a + m = 4acdm) satisfies an effective
Manin-type *positivity* statement: the count of positive-octant integral
points of height ≤ B is ≥ 1 uniformly for all n ≤ B^θ, some explicit θ > 0,
with polynomial dependence — existence via counting on the torsor.
**Input class:** 3/1 mix (torsor parametrization + circle-method/lattice
counting).
**Passes:** R1, R2 (log-Manin for split surfaces is a live program), R5
(the torsor *is* the witness algebra — programme-native), R8.
**Primary risk: R4-uniformity in n** — the entire ES difficulty reappears
as the uniformity range θ; heuristic counts (Elsholtz–Tao log³-growth) say
the statement *should* hold, which is exactly what they have said about ES
itself since 1948.
*(Status 20 Aug, evening: not a second lane. The Cox ring / universal
torsor *is* the witness equation, so this count is the Elsholtz–Tao count,
whose all-\(n\) lower bound is the divisor-dispersion problem — C1/C4
again. Plan §4v.)*

### NV — No Vieta (mechanism inventory closed)
*(Lemma, 20 Aug 2026. Not a candidate for C. `NoVieta.lean`.)*

The affine equation \(mxyz=n(xy+yz+zx)\) is linear in each coordinate.
Given \((y,z)\) with fibre denominator nonzero, there is at most one \(x\)
(`unique_x`; ES instance `es_unique_x`). There is no second root, hence no
Markoff-type Vieta involution \(x\mapsto 3yz-x\), hence no correspondence
orbit. The Bourgain–Gamburd–Sarnak playbook does not apply. This is the
structural reason the week's geometric no-gos are one fact, not five:
split fibres, conserved splitness under twists, Campana \(\neq C_+\), no
C5_3, and C10 = Elsholtz–Tao = divisor dispersion. Option 4 of the plan
was already killed as an investigation; it is now a kernel lemma.

### S1 — The Schinzel separator suite
*(Computation record, 20 Aug 2026. Script: `s1_schinzel_separators.py`.
Question: can \(C_+\) fail while mixed-sign integer points exist?
Answer: yes, on an explicit infinite family and on 86 reduced pairs in
the band \(1 < m/n < 3\), \(n\le 40\).)*

**Flagship family.** For \((m,n)=(2z-1,z)\) with \(z\notin\{3,4,6\}\),
the signed point \((1,1,-z)\) satisfies
\(1+1+1/(-z)=(2z-1)/z\). Positive solvability requires \((z-2)\mid 4\),
hence fails. At \(z=5\) this is **9/5**: kernel
`SchinzelSep.signed_9_5` (no axioms) and ordered
`SchinzelSep.no_pos_9_5` (axioms: `propext`, `Quot.sound`; \(x\le y\le z\)).
The unordered form is `SchinzelDecide.no_pos_9_5` (axioms: `propext`,
`Classical.choice`, `Quot.sound`), via the decision procedure below.
At \(z=7\): `SchinzelDecide.no_pos_13_7` (same axioms).

**Sweep.** In lowest terms, \(1 < m/n < 3\), \(n\le 40\): **86
separators** — mixed-sign witness found, positive search empty
(complete: leading denominator \(x\le 3n/m\)). Reproduced by
`s1_schinzel_separators.py`. A further 666 pairs in the band fail both
positive and a *bounded* signed search (\(|\mathrm{coords}|\le 60\));
that 666 is bound-sensitive and is not a kernel statement. Every
separator in the 86 has an explicit tiny signed witness. The 86 are
*not* all kernel-certified; only 9/5 (signed + positive) and 13/7
(positive) have been evaluated in Lean.

**The mechanism.** These are not finite-place Brauer–Manin failures we
have *kernel-checked*. For \(m/n\) bounded below 3 and above 1, the \(C_+\)
search tree is \(O(1)\)-branching (admissible leading denominators
\(\sim 3n/m = O(1)\)), and failure is those finitely many integrality
checks losing while \(\mathbb{Z}\)-solutions live outside the positive
octant. That is BL Theorem 1.9's finiteness mechanism promoted from
approximation-failure to existence-failure: the obstruction is
Archimedean-integral. It is consistent with C3_1: the question is
integral, not orbifold.

**What ES has that these separators lack.** For \(4/n\) with \(n\ge 5\),
\(m/n\to 0\) and the leading-denominator range grows like \(n/2\). The
86 live in the *narrow-tree* band \(1<m/n<3\). They do not, by themselves,
kill a principle that assumes Archimedean non-degeneracy.

**What S1 does not claim.** Mixed-sign occupancy and a box are kernel
or script facts. The TUB-EP consumable “no integral BM obstruction
against \(C_+\)” (the 1.8 analogue) is **not** kernel-checked; S1_1
sketches an adelic construction for \(\alpha\) on 9/5, not a Lean
pairing. If that analogue fails on 9/5, then 9/5 is not a TUB-EP
separator — it fails a hypothesis. If it holds, naive TUB-EP as a
class principle is already false, and C11's extra hypothesis is
necessary. That dichotomy is still C11's R8 gap until the pairing is
checked in their conventions.

**R6.** Any candidate existence principle for the Schinzel class must
fail on the 9/5-surface. Run that **before** a Markoff check. This
retires triangle-versus-conic discriminators of the kind C3 claimed.

### S1_1 — Regime split, decision procedure, and a 9/5 adelic sketch
*(20 Aug 2026. Lean: `SchinzelDecide.lean`. The Downloads v0.3 heading
“Beyond-BM, verified” is withdrawn: the construction below is a hand
sketch, not a kernel pairing.)*

**The decision procedure.** `decideCplus m n` searches \(x\le 3n\),
\(y\le 2nx\), recovers \(z\) from \(z\cdot D=nxy\). Soundness
(`decideCplus_sound`) and completeness (`decideCplus_complete`) are
proved (axioms: `propext`, `Quot.sound`). Boolean evaluations
`sep_9_5`, `sep_13_7`, `pos_4_5` are axiom-free (`decide`, not
`native_decide`). Completeness is a theorem about *each fixed*
\((m,n)\); it does not decide the 86 as a class, and it is not a
practical procedure for ES \(4/n\) at large \(n\).

**The regime split.** The Schinzel class splits:

- **Narrow** (\(m/n\) bounded below): Jahnel–Schindler at infinity plus
  integrality make the \(C_+\) tree finite. Existence is a computation.
  No existence *principle* is needed here beyond a decision procedure.
- **Wide** (\(m/n\to 0\)): the tree widens; existence is an asymptotic
  question. **This is where ES lives** (width \(\sim n/2\)).

C11's extra hypothesis is the boundary of that split, not a second
obstruction. Its honest kill domain is the **wide band** \(0<m/n\le 1\).
A “wide-tree separator in \(1<m/n<3\)” cannot exist by construction
(that earlier next-action was a test-design error). For \(m=4\) the
wide-band question is ES itself (searched past \(10^{17}\)). For
\(m=5,6,\ldots\) the computational literature (Sierpiński, Schinzel,
and later tables) has not produced a counterexample; that is literature
evidence, not an in-repo sweep.

**Adelic sketch for 9/5 (not kernel).** The 2-adic fibre is split, so
both values of \(\operatorname{inv}_2\alpha\) are attainable on
\(\mathbb{Z}_2\)-points. Explicit points on the surface:

- \((1,-5,1)\): mixed-sign \(\mathbb{Z}\)-point; \(\alpha=(-1,5)\);
  Hilbert symbol \((-1,5)_2=+1\); \(\operatorname{inv}_\infty=+1\).
- \((9/11,45/11,3)\): on the surface over \(\mathbb{Q}\)
  (\(11/9+11/45+1/3=9/5\)); 11 is a 2-adic unit, so a \(\mathbb{Z}_2\)-point;
  \(\alpha=(-3/11,-15/11)\); Hilbert symbol at 2 is \(-1\).

Assemble: global mixed-sign point at \(p\neq 2\), the second point at
\(p=2\), any real \(C_+\) point at \(\infty\) (Hilbert-at-infinity:
both arguments of \(\alpha\) negative, so \(\operatorname{inv}_\infty=-1\)).
Product \(+1\): the \(\alpha\)-pairing on this \(C_+\)-restricted integral
adele vanishes. Architecture matches BL §3.8 (cannot glue \(C_+\) to the
finite places of the mixed-sign global point; must retune a surjective
place — here \(p=2\)).

**What this does not settle.** Hilbert symbols at 2 are a hand computation,
not Lean. Bright–Loughran Remark 1.10 already says Schinzel surfaces are
\(\mathbb{Q}\)-isomorphic, so Theorem 1.6 still applies: \(\operatorname{Br} U/\operatorname{Br}\mathbb{Q}\)
is still \(\mathbb{Z}/2\) generated by \(\alpha\). The Downloads caveat
“Br \(U\) for \(m=9\) is not in the literature” is therefore the wrong
caveat; the real gap is that the *integral-model* pairing is not
kernel-checked and has not been confirmed in their \(\mathbb{Z}_p\)
conventions. “Obstruction shopping is closed” is too strong: \(\alpha\)
does not obstruct this sketched adele; that is not a theorem that no
refined integral obstruction exists. Ask the orbit to confirm the sketch
as the 1.8 analogue, rather than to define the set from scratch.

**Sharpened orbit question.** The narrow regime is decidable, and the
sketch says its failures are invisible to \(\alpha\). Does their
framework assert anything in the **wide** regime, and if so what is its
ES-instance?

### C11 — TUB-EP-refined (principle schema)
**Statement (Schinzel class).** Mixed-sign occupancy + box + no integral
Brauer–Manin obstruction against the positive component \(C_+\) (the
BL Theorem 1.8 condition, in its integral-against-a-component form) +
**Archimedean non-degeneracy** (the real-admissible leading-denominator
range unbounded in \(n\); equivalently \(m/n\to 0\) along the family)
\(\implies\) positive-octant integral existence.

**Why the fourth hypothesis.** S1 proves it necessary in the narrow
band: drop it and \((2z-1)/z\) refutes the principle. Markoff results
guard a “BM suffices for all log K3s” reading at the class boundary.
ES satisfies non-degeneracy for \(n\ge 3\) (width \(\sim n/2\); \(n=2\)
is \(1+1/2+1/2\) directly). The refined schema still delivers ES
*if* it is proved — it is not proved.

**Honest scoring.** Neither a tick nor a double-tick.

- **R1.** The ES instance of the conclusion is `TubEpHypothesis`, already
  wired. C11 as a schema is not a kernel implication from named
  hypotheses to `ErdosStraus` until those hypotheses are Props.
- **R2.** Better than raw TUB-EP: S1 gives class content (it *predicts*
  the separators fail). Sufficiency of “\(m/n\to 0\)” for the whole
  Schinzel class still relocates generalized Egyptian 3-fractions
  (\(4/n\), \(5/n\), …). Independent life is not yet earned.
- **R3.** Fail until a mechanism is named. C11 specifies what must be
  true and what would falsify it, not the engine that proves it.
- **R4.** Non-degeneracy is growth in Archimedean clothing; necessary,
  not shown sufficient.
- **R6.** Testable in-family (S1) and cross-family (Markoff). Not
  passed: the test suite exists, the principle is unproved.
- **R7.** No explicit \(X_0\).
- **R8(a).** The second hypothesis needs a precise definition of
  “integral BM obstruction against a real component.” The literature
  has this only in fragments. That is the well-posed question for the
  geometric worklist, not a tick.

**Bounded next actions.** (i) **Done** for the flagship: `SchinzelSep.lean`
(signed 9/5) and `SchinzelDecide.lean` (decision procedure; 9/5 and 13/7
positive-empty). (ii) A “wide-tree separator” **cannot** appear in the
band \(1<m/n<3\) — leading denominators are \(O(1)\) there by construction.
Extending that sweep does not test C11's sufficiency. The honest kill
test is the ES-like band \(0<m/n\le 1\): a single pair with small ratio,
mixed-sign yes, positive no, refutes C11 as a class statement. For
\(m=4\) that is ES itself (already searched far beyond \(n=200\)). For
\(m=5,6,\ldots\) it is a bounded generalized-Egyptian search, worth a
short sweep, not a QED lane. (iii) The component-integral BM definition
remains C11's R8 gap. S1_1 sketches that \(\alpha\) does not obstruct a
\(C_+\)-restricted 9/5 adele; that sketch is not kernel and is not a
substitute for their confirmation. Do not treat S1_1 as discharging
hypothesis 2.

---

## Reading the list

**One lane.** Fibrations, the universal torsor, and Vieta/Markoff dynamics
all reduce to the same analytic core (plan §4v; `NoVieta.lean`;
`ConicFiber.lean`). Geometric candidates C3/C5/C10/C11 are class-theory
and an effectivity framework, not a proof path with existing tools.

**Attackable in-house now, in order:** (i) T(A) = C4_1, constant-tracking
of the ClassRough selection sequence (`erdos-straus-T-A.md`). The
prime-aligned Euler factor is done (\(C_{\mathrm{euler}}(80)=0.911\),
flat, zero collisions); the ClassRough composite marginals are
\(\Pi_{\mathrm{gen}}(\sqrt{x})\), matching the \(A=40\) CR/prime product
to \(3\%\). Empirical shadow: growing \(A\) at \(x=10^9\) gave
\(c'=0.104<\kappa=0.139\) and \(\mathrm{cond}\to 1\);
(ii) C2's cross-moduli symbol-correlation computation (done: does not
fire); (iii)
E_partial written as the vehicle for (i)–(ii)
(`erdos-straus-E-partial.md`; Gate A forbids discharging
`AnalyticSurvivorBound`; dummy covering, not \(c'\) vs \(\kappa\),
is the live kill). G–S dictionary:
`erdos-straus-gs-reformulation.md`, now attached specifically to \(S\).
Certificate checks done (`c4_certificates.py`): converse is an
\(\omega\)-gap, not a near-equivalence; shared \(\chi\) does not explain
\(\mathrm{cond}\to 1\). T(3) kernel is a theorem
(`classRough_123_iff_certificates`); T(3)\(^+\) is claimed
(\(S(3,x)\ll(\log x)^{-3/2}\); `erdos-straus-T-3.md`); the T(3) lower
bound is a three-step plan (stall at \(q>x^{1/2}\)); T(A)\(^+\) tracks
\(C_{\mathrm{sieve}}(A)\) (`c4_sieve_constant.py`); **E_lane** is the
\(d=1\) floor from T(A)\(^+\) plus the dimension-uniform fundamental
   lemma. **E_power** is a recorded negative for the covering-box
\(x^{1-\delta}\) (`erdos-straus-E-power.md`,
`erdos-straus-E-power-decision.md`). Measurement has saturated: evaluate certificate Euler
products, not \(x=10^{10}\).
**Do not:** further C7 identity search; any Selmer/descent on any
fibration of this family; orbifold repackagings; a direct assault on
H_ES; \(x=10^{10}\).

**Open questions, by literature:** T(A) working note
`erdos-straus-T-A.md`. The analytic worklist
(`erdos-straus-sieve-desk.md`) names T(A)\(^+\), E_lane as
written claims, E_power as a recorded negative, and the T(3) completion step as the remaining
question. Do not densify covering. Then C2 + the G–S memo as a dictionary
in the Granville–Soundararajan / Lamzouri / Heath-Brown dialect, on the joint
lower-tail that \(S\) is. Geometry (C3/C11/S1_1) in the Bright–Loughran
literature as **foundations and effectivity**, not as QED — briefing
`erdos-straus-loughran-orbit.md`, programme brief `erdos-straus-programme.md`.
**Theory to write:** whether \(c'\) stays below \(\kappa\) uniformly in
\(A\), and whether \(\mathrm{cond}\to 1\) makes extra covering mass
fictitious at QED-scale \(A\); C6 as growing-moment flatness of \(S\)
after T(A) lives or dies; geometric effectivity framework for its own
sake.

Portfolio note: C1/C4/C4_1/C6/C9/C10 are one object. They die together
if \(C(A)\) is super-critical in \(\log^2 A\) (\(c'\ge\kappa\)) or if
cond\(\equiv 1\) makes extra covering fictitious at QED-scale \(A\).
Growing \(A\) to 200 did not see super-critical; cond\(\to 1\) is live.
C3/C5/C11 can still have
independent life as class-theory; they cannot substitute for T(A). C2
and C7 die on their own measurements (C7 already has a null in-box).

*Every candidate above is a conjecture. None is claimed proved, evidenced
beyond the cited measurements, or safe from its listed risk. The list's
purpose is to convert "a new idea is needed" from a lament into a menu.*
