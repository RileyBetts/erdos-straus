<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Geometric questions in the Bright–Loughran literature

**Riley Betts Erdős–Straus programme, 20 August 2026.**
Companion to `erdos-straus-candidate-conjectures.md` (C3_1, C5_2, C7_1, S1, S1_1, C11),
`erdos-straus-conjecture-spec.md` (R1–R8), plan §§4m–4u, and the Lean
kernel (`ConicFiber.lean`, `TwistDescent.lean`, `ErdosStrausBLRoute.lean`).

This note is the geometric worklist. It is not a theorem, not a request to
prove the Erdős–Straus conjecture, and not a claim that TUB-EP has
independent life until a class larger than `{U_n}` is exhibited. The
programme brief is `erdos-straus-programme.md` (the same five questions, short). The
\(r_\chi\to\) Kloosterman range no-go at the T(3) stall is the analytic
worklist, not this note. The Zheng T(2) look is analytic as well.

---

## Where the in-house line sits (20 Aug)

Three candidate lines were closed or frozen this week.

| Line | Result | Kernel / computation |
|---|---|---|
| C5 / C5_1 / C5_2 | Named t-fibration of the real-compatible twist \(V_{n,d}\) is **split**. Harpaz 1.0.1 does not apply. | `t_fiber_section_cleared` |
| C5 autopsy | \(\pi=u_1\) and \(\pi=w\) are the **same rational curve**, reparametrized. No C5_3. | `u1_fiber_section_cleared` |
| C3 | ES pairs *do* have a split triangle and interior \(\mathbb{G}_m^2\). Campana Hasse does **not** imply a \(\mathbb{Z}\)-point of \(C_+\). The triangle does **not** exclude Markoff. | C3_1; Mitankin–Uhlemann Remark 1.5 |
| C7 | No degree-1 Witness identity with modulus \(\le 30\) and coefficients \(\le 4\) covers a hard class. | `c7_bounded_coupling_search.py` |
| S1 | Mixed-sign occupancy does not imply \(C_+\). Infinite family \((2z-1)/z\); 86 separators in \(1<m/n<3\), \(n\le 40\). Flagship 9/5 signed + positive; 13/7 positive. | `SchinzelSep.lean`, `SchinzelDecide.lean`, `s1_schinzel_separators.py` |
| S1_1 | Narrow band is decidable; wide band is where ES lives. Hand adelic sketch: \(\alpha\) does not obstruct a \(C_+\)-restricted 9/5 adele. Not kernel. | candidate list S1_1 |
| NV | Affine equation linear in each variable; no Vieta involution; Markoff/BGS playbook does not apply. Mechanism inventory closed. | `NoVieta.unique_x` |
| C4_1 | T(A): joint density at fixed \(A\). Dies if \(c'\ge\kappa\) or \(\mathrm{cond}\equiv 1\) to QED-scale \(A\). Growing \(A\): \(c'=0.104<\kappa\), cond\(\to 1\). | candidates C4_1; plan §4v |

The analytic covering lane remains compiled (k-budget invariant; do not
densify). After plan §4v the two lanes are one lane: every geometric
mechanism inventoried reduces to joint roughness / divisor dispersion.
Geometry's honest role is class-theory and an effectivity framework (the
questions below), not a proof path with existing tools.
The only geometric statement that implies ES through the kernel is
`TubEpHypothesis`, and that is **equivalent** to ES
(`tub_ep_iff_erdos_straus`). Equivalence is a translation, not a target
(spec R2). The first theorem is T(A) = C4_1.

---

## The geometric literature

### Papers

Martin Bright and Daniel Loughran wrote the paper this programme
is built on: *Brauer–Manin obstruction for Erdős–Straus surfaces*, Bull.
LMS 52 (2020). Around that paper sits a literature on integral points
of log K3 / affine cubic surfaces: Loughran–Mitankin (Markoff integral
Hasse), Colliot-Thélène–Wei–Xu (Markoff BM), Mitankin–Uhlemann (Markoff
Campana points; cites BL), Harpaz (conic log K3s; JEMS 2019), Uppal
(norm-1 tori over \(\mathbb{A}^1\)), Jahnel–Schindler (strong obstruction
at infinity), Colliot-Thélène–Wittenberg (affine cubics).

That is the literature this note calls the Loughran orbit. The five
questions are in `erdos-straus-programme.md`. They are open mathematical questions,
not a correspondence.

### What the question is not

It is not “why do ES surfaces always have integral points when Markoff
surfaces don’t?”

\(U_n(\mathbb{Z})\) is **never empty**. Mixed-sign points exist for every
\(n\ge 2\) (`esZ_nonempty`). Markoff emptiness is emptiness of *all*
integral points, for a positive-density set of \(m\). Comparing those two
facts confuses two different problems. Mitankin–Uhlemann restoring Campana
Hasse on Markoff orbifolds does not move a mixed-sign ES point into the
positive octant.

It is not “apply Harpaz / Cao–Xu / Theorem 1.8.” Those three
mismatches are now kernel-recorded or paper-recorded:

- **Harpaz.** Every conic fiber of \(U_n\) is split:
  \((Ax-nt)(Ay-nt)=(nt)^2\), \(A=4t-n\) (`ConicFiber.fiber_identity`).
  The real-compatible twist \(V_{n,d}\) is still split along \(\pi=u_2\),
  \(\pi=u_1\), and \(\pi=w\). Split fibers have no Selmer structure to
  compare. Even a matching Harpaz 1.0.1 would produce \(S\)-integral
  points with \(2\in S\), not a \(\mathbb{Z}\)-point of \(C_+\).
- **Cao–Xu.** \(\widetilde{U}_n\) contains a torus \(\mathbb{G}_m^2\)
  whose action does **not** extend (BL Remark 3.12). Cao–Xu is a theorem
  about toric varieties, and does not force a point into a prescribed
  real component.
- **Theorem 1.8.** Nonempty Brauer–Manin set in the positive-octant
  adelic space. Kills BM as a *disproof* of ES. Does not produce a point
  of \(U_n(\mathbb{N})\).

### What the question is

The conjecture is occupancy of **one real component** of a surface that
already has integral points in the other.

Bright–Loughran proved that the transcendental quaternion
\(\alpha=(-u_1/u_3,-u_2/u_3)\) is \(-1\) on the positive octant and \(+1\)
on the complement, and that there is no BM obstruction to a positive
point. The remaining arithmetic lives in **integrality**, not in
fiber-level local–global structure: positive points on a split conic
fiber are exactly divisor pairs of \((nt)^2\) in the class \(-nt\pmod{A}\)
(`fiber_to_divisor` / `divisor_to_fiber`, all \(n\ge 2\)).

**Question for the orbit.** Is there a global (not fibration-based) method
that, for a class of affine log K3 surfaces over \(\mathbb{Q}\) that are
strongly obstructed at infinity, with two real components separated by a
transcendental quaternion, produces an integral point in the
Brauer-allowed component, given that the complementary component is
already occupied and the BM adelic set in the allowed component is
nonempty?

If the only member of that class is \(\{U_n\}_{n\ge 2}\), the statement is
ES relocated (R2). If the class is larger, the statement can have
independent life. The first stress test is already in their paper
(Remark 1.10): Schinzel’s family \(m/n=1/u+1/v+1/w\) — same Brauer group,
analogues of Theorems 1.2, 1.5, 1.8, 1.9, **different \(\mathbb{Z}\)-models**.

A working formulation of the class statement (TUB-EP, not claimed) is:

Let \(U/\mathbb{Z}\) be a flat affine model of a log K3 over \(\mathbb{Q}\),
\(C_+\) a distinguished component of \(U(\mathbb{R})\). Assume
(i) a desingularisation contains a Zariski-open torus \(T\cong\mathbb{G}_m^2\)
whose action need not extend; (ii) a generator of \(\operatorname{Br} U/\operatorname{Br}\mathbb{Q}\)
is constant on each real component and separates \(C_+\); (iii) \(U(\mathbb{Z})\)
is nonempty and finite (a real height bound); (iv) the BM set
\((C_+\times\prod U(\mathbb{Z}_p))^{\operatorname{Br}}\) is nonempty.
Then \(U(\mathbb{Z})\cap C_+\neq\emptyset\).

For the family \(U_n\), (iii) is Lemma 3.10 plus mixed-sign existence,
(ii) is Theorems 1.2/1.5, (iv) is Theorem 1.8, and the conclusion is ES.
The question is whether (i)–(iv) describe a class their methods can touch,
or only this family.

**Question (component-integral obstruction).** Define the \(C_+\)-restricted
integral adelic set
\(U(\mathbb{A}_{\mathbb{Z}})^{C_+} := C_+ \times \prod_p U(\mathbb{Z}_p)\)
and the obstruction set \((U(\mathbb{A}_{\mathbb{Z}})^{C_+})^{\mathrm{Br}}\),
pairing against the full \(\operatorname{Br} U\) including the transcendental
class \(\alpha\). Three sub-questions.

(i) Is this the right formalization of “no integral Brauer–Manin obstruction
against a real component,” and does BL Theorem 1.8 amount to its
nonemptiness for the ES pairs?

(ii) For the separator surface \(m/n = 9/5\) (positive-octant points
provably absent, integer points present, both machine-checked), compute
this set: we expect it nonempty — in which case the separators are
beyond-BM failures at the component level, and the Archimedean-integral
mechanism (finite forced tree, BL 1.9’s finiteness promoted to
existence-failure) is invisible to component-BM.

(iii) Does any refined obstruction in the semi-integral literature see
the narrow-tree failures? If so, hypotheses 2 and 3 of the refined
principle may merge into a single refined-obstruction hypothesis — the
cleanest form the principle could take.

If the separators pass hypothesis 2, that is not a threat to C11: it is
the necessity proof working as designed, since hypothesis 3 is what
excludes them. And (iii) is the genuinely open door: if the orbit’s
frameworks can detect narrow trees obstruction-theoretically, C11
collapses into a class-level existence principle in that literature,
which is the best possible fate for it.

**Status of (i)–(iii).** Do not claim (ii) as computed.

- **(i).** Yes, as a reading of the paper. Theorem 1.8 is exactly
  \(\bigl(U_n(\mathbb{R})_+\times\prod_p\mathcal{U}_n(\mathbb{Z}_p)\bigr)^{\mathrm{Br}}\neq\emptyset\),
  and also that this set is a proper subset (obstruction to strong
  approximation, not to existence). Algebraic Brauer is \(\operatorname{Br}\mathbb{Q}\)
  (Pic \(=\mathbb{Z}\)), so pairing against “full \(\operatorname{Br} U\)”
  is pairing against \(\alpha\). Open: whether the notation matches the
  2020 integral-model conventions.
- **(ii).** Construction **sketched** in S1_1, not kernel-checked.
  Glueing \(C_+\) at infinity to the finite places of the global point
  \((-5,1,1)\) is **not** a proof of nonemptiness:
  \(\operatorname{inv}_\infty\alpha=+1\) on mixed-sign points and \(-1\)
  on \(C_+\), so that hybrid has product of invariants \(-1\). The sketch
  retunes \(p=2\): \((1,-5,1)\) has \(\operatorname{inv}_2=+1\);
  \((9/11,45/11,3)\) is a \(\mathbb{Z}_2\)-point with
  \(\operatorname{inv}_2=-1\) (Hilbert symbols at 2 computed by hand).
  Product with a real \(C_+\) point is \(+1\). Open: whether those two
  2-adic symbols are correct and whether this is the 1.8 analogue on the
  9/5 \(\mathbb{Z}\)-model. Do not record “beyond-BM verified.”
- **(iii).** Unknown, and the right question. Ordinary BM does not encode
  “the positive search tree is finite and empty.” Mitankin–Uhlemann
  Campana/Darmon Hasse holds while integral points fail, so those
  obstruction sets do not see narrow-tree emptiness either. The geometric
  fact that sees it is already named: strong obstruction at infinity
  (Jahnel–Schindler) with a box small enough that the tree terminates.
  Whether that is packaged as a refined obstruction in the semi-integral
  literature is open. Follow-up, if the 9/5 sketch holds: does any
  framework in that literature assert anything in the **wide** regime
  (\(m/n\to 0\)), ES-instance?

### What would kill it

A \(\mathbb{Z}\)-model of the same \(\mathbb{Q}\)-surface (or of Schinzel’s
family) with finite nonempty \(U(\mathbb{Z})\), nonempty BM set in a
distinguished real component, and that component empty. Different models
of the same \(U_1/\mathbb{Q}\) already change the integral problem (BL,
p. 748). If such a model exists, TUB-EP needs an extra hypothesis that
isolates the ES models — for example a positivity condition on the torus
characters. Until a class or a counterexample is named, TUB-EP is a
research question, not \(C\).

---

## Open geometric questions (literature)

The five questions are in `erdos-straus-programme.md`. Kernel facts already in
the archive:

- Lean formalization of the elementary Bright–Loughran arithmetic
  (Lemmas 3.1/3.5/3.6/3.8, Hilbert reciprocity for the explicit symbols,
  the box, mixed-sign occupancy, octant invariant). Theorem 1.8 is not
  formalized and is not treated as existence.
- Every conic fiber is split; the identity is
  `(Ax − nt)(Ay − nt) = (nt)²`. Positive fiber points ↔ divisor pairs of
  `(nt)²`. Harpaz does not apply; the twist family was checked too.
- Campana packaging does not reach \(C_+\); that is a reading of
  Mitankin–Uhlemann Remark 1.5.
- Open: the Schinzel stress test and the three sub-questions on the
  component-integral obstruction. For (ii): an explicit 2-adic sketch
  (not kernel). For (iii): if that sketch holds, whether any framework
  asserts anything in the wide regime.
- Open: whether TUB-EP as a *class* is recognisable, rejectable, or
  refinable in that literature — not whether ES is proved.

### Next geometric computation, if the 9/5 sketch holds

Whether Schinzel’s \(\mathbb{Z}\)-models satisfy (i)–(iv) and whether
\(C_+\) can fail there. S1 already shows \(C_+\) can fail with mixed-sign
occupancy; S1_1 sketches that \(\alpha\) need not explain that failure.
The missing piece is the 1.8 analogue on 9/5. That is the R2/R8 test. A
counterexample to the analogue, or an extra hypothesis that isolates ES
(C11's non-degeneracy), would be the first honest refinement of TUB-EP.

Jahnel–Schindler (strong/weak obstruction at infinity) is the language
this should be written in.

### What not to mix

- Harpaz or Uppal descent-fibration on ES or on \(V_{n,d}\). The section
  test is already negative. Matching Theorem 1.0.1 to the statement is a
  literature check, not a proof path.
- Whether Campana points of ES pairs occupy \(C_+\). Mitankin–Uhlemann
  Remark 1.5 is the reason that question is the wrong strength.
- The dispersion school (C1/C9) in the same note. That is a different
  literature, a different risk (H_ES relocated), and a different paper.
- Densifying covering, producing an explicit \(X_0\) from an ineffective
  Hasse principle, or treating Theorem 1.8 as QED.

### Adjacent literature, later and separate

| Literature | Question | When |
|---|---|---|
| Jahnel–Schindler; CT–Wittenberg | Is “strongly obstructed at \(\infty\), two real components, complementary component occupied” a known existence regime for affine cubics? | After the dialect of (i)–(iii) is fixed |
| Mitankin–Uhlemann | Confirmation that ES Campana points are not the integral octant problem; possibly whether *strict* Campana on ES is interesting for its own sake | Not as \(C\) |
| Dispersion / DFI (Friedlander–Iwaniec lineage) | **Not C1.** The bounded question is the T(3) three-kernel CRT weight (plan §4w; `erdos-straus-T-3.md`): joint well-factorable weights for a residue that moves with the triple. The \(r_\chi\to\) Kloosterman bilinear look is a range no-go at \(Q=x^{1/2+}\). C1/H_ES remains relocated-risk and is not this note. | The analytic worklist, never this one |
| Schinzel 2000 / polynomial identities | Independent check that no small polynomial identity covers a hard class (C7_1 is the archive box) | Literature check, not a joint project |

Effectivity (spec R7) is a second constraint in every geometric
statement: even a true class-level Hasse principle typically has no
explicit \(X_0\). The finite certificate in this repository can absorb an
explicit threshold; it cannot absorb “sufficiently large”. An
ineffective theorem is not QED.

---

## How to proceed (recommended)

**This quarter, technical main effort (analytic):** T(A) = C4_1.
Working note: `erdos-straus-T-A.md`. Certificate checks done
(`c4_certificates.py`): converse is an \(\omega\)-gap; shared \(\chi\)
does not explain dummy covering. The analytic worklist
(`erdos-straus-sieve-desk.md`) is a question list, not the next
compute step. E_partial is written
(`erdos-straus-E-partial.md`, `erdos-straus-E-power.md`): Gate A vehicle
and the \(x^{1-\delta}\) covering-box paper, not QED. Do not densify
covering.
C2's cross-moduli probe did not fire (covering symbols independent;
extra shrinkage has the wrong sign for \(\hat C>1\)). Dictionary:
`erdos-straus-gs-reformulation.md` (attached to \(S\); if cond sticks at
1, the object is a conditioned pretentious tail). Die condition:
\(c'\) vs \(\kappa\), and dummy slices if cond\(=1\). Growing \(A\) at
\(x=10^9\) gave \(c'=0.104<\kappa=0.139\) and cond\(\approx 1\). Do not
assault H_ES directly.

**This quarter, geometry:** class-theory and an effectivity framework for
strongly-obstructed log K3s, not a request for a proof path. Everything
that looks like Selmer, descent, or Campana as \(C_+\) waits forever.

**This quarter, do not:** start C5_3, grind larger C7 boxes, densify
covering, formalize Harpaz, construct `InvariantData` by setting
`invP = -1`.

**If the class is just ES:** that is compatible with §4v. The proof path
is then analytic (T(A) first), or a stop.

**If a larger class or a missing hypothesis is named:** that becomes
geometric theory-building under the same eight-requirement spec. It does
not postpone T(A).

Kernel facts, in one line each:

- Mixed-sign points for every \(n\ge 2\); box \(\min|u_i|\le 3n/4\).
- \(\operatorname{inv}_\infty\alpha=-1\) exactly on \(C_+\).
- Split-fiber identity and divisor correspondence, all \(n\ge 2\).
- Twist \(w^2=d\,u_1u_3\) still split along \(u_1,u_2,w\).
- `TubEpHypothesis` \(\Leftrightarrow\) `ErdosStraus`; implication proved,
  hypothesis not discharged.
- Theorem 1.8 not claimed as a point of \(C_+\).
- No Vieta: unique \(x\) given \((y,z)\) (`NoVieta.unique_x`).
