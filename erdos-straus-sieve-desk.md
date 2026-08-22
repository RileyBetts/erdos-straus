<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# The analytic worklist

**Riley Betts Erdős–Straus programme, 20 August 2026.**
Companion to `erdos-straus-T-A.md` (T(A)\(^+\)), `erdos-straus-T-3.md`
(T(3)\(^+\) claimed; three-step lower-bound plan), candidates C4_1,
`erdos-straus-E-partial.md` (Gate A), `erdos-straus-E-power.md`
(E_power repaired; one-stage claim withdrawn), `erdos-straus-gs-reformulation.md`
(dictionary of the joint lower-tail, not this note).

This note is the analytic question list. It is not a theorem, not a
request to prove the Erdős–Straus conjecture, and not a request
to densify covering or to discharge `AnalyticSurvivorBound`. The
geometric questions are in `erdos-straus-loughran-orbit.md`. Do not mix
the two lanes. Artifacts from the prior Track-1 archive are
library/docs, not a Bounded-A merge (`erdos-straus-prior-archive.md`).

---

## Where the in-house line sits

The first theorem is **T(3)\(^+\)** (upper bound of the right order,
claimed in `erdos-straus-T-3.md`). The in-house theorems are
**T(A)\(^+\)** (uniform Selberg, \(C_{\mathrm{sieve}}(A)\) tracked
against \(\log^2 A\)) and **E_lane** (the \(d=1\) floor, below Vaughan),
both in `erdos-straus-T-A.md`. The T(3) matching lower
bound is a three-step plan with a named stall at completion; the
sharp remaining question is the joint well-factorable CRT residue
(plan §4w). The \(r_\chi\to\) Kloosterman bilinear look is a range
no-go at the stall, not a request to cite Linnik past \(\sqrt{x}\).
Zheng arXiv:2512.22798 on two simultaneous APs is a range no-go on
\(d_1\approx d_2\approx\sqrt{x}\) (`erdos-straus-T-2.md`); an uneven
Type I leftover still dies on \((0,1/2,1/2)\); a joint δ-method look
(`erdos-straus-T-3-delta.md`) does not avoid the BV-wall identity and
does not bound \(D\) up to \(x\) or \(x^{3/2}\); joint monodromy
independence (`erdos-straus-T-3-monodromy.md`) does not apply to the
CRT kernel; the four completion looks are named as one gap in
`erdos-straus-varying-modulus-gap.md`; not T(2)\(^+\)
claimed, not T(3) progress.
For each *fixed* covering width \(A\), the joint ClassRough density
among hard-class primes is to be trapped as
\[
c_-(A)\,(\log x)^{-\beta(A)}
\;\le\;
S(A,x)
\;\le\;
c_+(A)\,(\log x)^{-\beta(A)},
\]
equivalently \(S(A,x)\asymp C(A)\prod_{a=1}^{A}\rho_a(x)\) with
\(C(A)\) a tracked sequence. An asymptotic
\(S=C\prod\rho_a\cdot(1+o(1))\) is more than the programme needs.
Proving that \(C(A)\) exists at each fixed \(A\) does not save the
Erdős–Straus schedule. The exposure is the sequence \(C(A)\) against
the covering law \(\exp(\kappa\log^2 A)\) with \(\kappa=0.139\), and
whether extra slices still cut.

Euler pieces of the product are computed and are **not** the theorem:

| Piece | Status |
|---|---|
| Pair ratios \(\rho_{ab}/(\rho_a\rho_b)\) | \(1.000\) to \(A=120\). Lemma. |
| Prime-aligned \(C_{\mathrm{euler}}(A)\) | \(0.91\), flat \(A=40\to 200\); zero residue collisions. |
| ClassRough composites \(\Pi_{\mathrm{gen}}(a,\sqrt{x})\) | Matches \(\rho_{\mathrm{CR}}/\rho_{\mathrm{prime}}\) at \(A=40\) to \(3\%\). Lives in the *marginals* \(\rho_a\). |
| C2 covering Jacobi symbols | Does not fire. Extra shrinkage has the wrong sign for \(\hat C>1\). |

Leftover at \(x=10^9\): \(\hat C(80)=2.69\), \(\hat C(200)=6.92\),
\(\log\hat C\sim 0.104\log^2 A\) on \(A\ge 40\), and
\(\mathrm{cond}(a)=P(R_a\mid\mathrm{prefix})\to 1\) past \(a=80\)
(\(155\) survivors at \(A=200\)). Details: `erdos-straus-T-A.md`.

**Two partials of \(\log S\)** (`c4_surface_fit.py`):

| \(x\) | \(c'(x)\) | \(R^2\) | \(\hat C(80)\) |
|------:|----------:|--------:|---------------:|
| \(10^6\) | 0.063 | 0.92 | 1.57 |
| \(10^8\) | 0.076 | 0.99 | 2.23 |
| \(10^9\) | 0.094 | 0.99 | 2.69 |

The \(x\)-slope deficit at \(A=80\) is \(13.2\%\) of \(\beta_{\prod\rho}\)
(\(\kappa_{\mathrm{eff}}\approx 0.121\)). The \(A\)-curvature at
\(x=10^9\) is \(c'=0.104\) on \(A\ge 40\) (\(\kappa_{\mathrm{eff}}\approx 0.035\)).
They are different derivatives. \(c'(x)\) is still climbing; a linear
hit of \(\kappa=0.139\) extrapolates to \(\sim 10^{24}\) and is not a
reason to run \(10^{10}\). Measurement has saturated: further scans
refine constants inside this window without touching \(c'(\infty)\).

**First theorem, half claimed: T(3)\(^+\).** At \(a=1,2,3\) the
certificate converse is exact (kernel: `classRough_123_iff_certificates`).
A dimension-\(3/2\) Selberg sieve on hard primes gives
\(S(3,x)\ll(\log x)^{-3/2}\) (`erdos-straus-T-3.md`). T(1) is
\(S(1,x)\asymp(\log x)^{-1/2}\) by Iwaniec, Acta Arith. **24**, plus
Fuchs et al. The matching lower bound is a three-step plan: (a) Iwaniec
per slice exists; (b) Brüdern–Fouvry combines them (Nath–Xie is the
two-component template); (c) completion of factors \(q>x^{1/2}\) sits
beyond BV and can stall. Two escapes for the paper's outlook: weaker
\(c_-\), or the \(r_\chi\)-detector (Linnik). Calibrated against
\(\hat C(3)\approx 0.975\) at \(x=10^9\).

**In-house next, done as T(A)\(^+\); E_lane the floor.** Uniform Selberg
(`c4_sieve_constant.py`): \(\beta(A)=\sum 1/\varphi(4a)\sim 0.66\log A\),
\(C_{\mathrm{sieve}}=\Gamma(\beta+1)\exp(\gamma\beta-B(A))\). The
\(\Gamma\)-factor is \(\exp(o(\log^2 A))\) as a theorem; expected
\(B(A)=O(\log A)\) (Norton; typical \(M(q,a)\) in the
Granville–Soundararajan circle). Selberg does not re-create the
covering law. **E_lane claimed:** one dimension-uniform FL lemma
gives \(E_{\mathrm{lane}}(x)\ll x\exp(-c'\sqrt{\log x}\,\log\log x)\),
the \(d=1\) aligned-prime floor, below Vaughan. **E_power repaired:** the one-stage \(S_A\ll x^{1-\delta}\) claim is
withdrawn (`erdos-straus-E-power.md`). Two-stage finite density is
the Lean target; transfer is separate. Lemma SM is a surrogate-mass
input (checked through \(A=2000\)), not fibre Suen. Dummy covering
remains the live kill of a QED ClassRough schedule. Details:
`erdos-straus-T-A.md`, `erdos-straus-E-power.md`.

Gate A (`erdos-straus-E-partial.md`): Layer 1 is T(A)\(^+\) / E_lane.
Layer 0 is E_power, written, not `AnalyticSurvivorBound`. Dummy
covering, not \(c'\) vs \(\kappa\), is what stops a retuned QED
schedule. Do not densify covering.

---

## Literature lineage

Not Bright–Loughran (geometry: class-theory and effectivity).

Not Granville–Soundararajan / Lamzouri / Heath-Brown *first* — that is
the dictionary in `erdos-straus-gs-reformulation.md`, with the C2 null,
of the joint lower-tail that \(S\) is. This note comes before that one.

This note is the **half-dimensional / vector-sieve** worklist: jointly
restricted values of \(p+4a^2\), \(p\) prime in six classes mod 840,
each slice a ker-character condition of sum-of-two-squares shape.
Lineage already checked and *not* T(A) as an asymptotic:

- Hooley, JNT **5** (1973), 215–217 — three S2 values on \(\mathbb{Z}\).
- Hooley / Indlekofer — pair correlation of the S2 indicator on integers.
- Iwaniec, Acta Arith. **24** (1973/74) — primes represented by a quadratic
  polynomial in two variables; \(\#\{p=m^2+n^2+1\}\asymp x/(\log x)^{3/2}\).
- Iwaniec, Acta Arith. **29** (1976), 69–95 — the half-dimensional sieve;
  kernel-type conditions; two-sided bounds of the right order, not
  asymptotics.

The active template, and the intended instrument:

- K. Nath, L. Xie, arXiv:[2501.16723](https://arxiv.org/abs/2501.16723)
  (Acta Arith. 2025) — vector sieve with a semi-linear sieve and a
  linear sieve in conjunction with Iwaniec's argument, to detect
  primes of the form \(m^2+n^2+1\).
- E. Fuchs, C. Hsu, J. Rickards, D. Schindler, K. E. Stange,
  arXiv:[2504.20289](https://arxiv.org/abs/2504.20289) — Iwaniec's
  sieve for shifted quadratic forms, extended to primitivity and
  congruence conditions.

None is class-roughness of several shifts of a hard prime. The relevant
published dialect is the half-dimensional / vector-sieve literature on
ker-character conditions at primes — in particular the active
\(m^2+n^2+1\) papers. Keep this lane separate from the geometric questions.

---

## What the question is not

It is not “prove Erdős–Straus.”

It is not “prove H_ES / empty the box at \(A=\exp(c\sqrt{\log x})\).”
Gate A forbids that as the first paper, and the k-budget invariant says
interval-intrinsic sieves cannot buy it.

It is not “sieve harder / add more covering moduli.” Densifying covering
is closed. Extra \(d=1\) slices already fail to cut
(\(\mathrm{cond}\to 1\)). Adding more of them is not mass.

It is not “the pair asymptotic.” Pairs stay \(1.000\). The object is the
\(A\)-fold intersection \(S\).

It is not “compute \(C_{\mathrm{euler}}\).” That is \(0.91\) and flat.
A paper that only produces it has tracked the wrong constant.

It is not “run \(x=10^{10}\).”

---

## What the question is

Lean `ClassRough p a`: \(p+4a^2\) has **no divisor** \(q\ge 3\) with
\(q\equiv -1\pmod{4a}\) (composites included). Hard primes: the six
quadratic-residue classes modulo \(840\). Then \(\rho_a\) is the
one-slice density and \(S(A,x)\) is the joint.

**T(A).** For each fixed \(A\), write a two-sided bound
\[
c_-(A)\,(\log x)^{-\beta(A)}
\;\le\;
S(A,x)
\;\le\;
c_+(A)\,(\log x)^{-\beta(A)}
\]
with \(c_\pm(A)\) tracked as a sequence in \(A\), equivalently
\(S(A,x)\asymp C(A)\prod_{a\le A}\rho_a(x)\) with \(C(A)\) trapped.
An asymptotic \(S=C\prod\rho_a\cdot(1+o(1))\) is more than the
programme needs and is open-hard for kernel-type conditions at primes.
Architecture: ClassRough
is (exactly, one direction) a certificate
by a real odd character \(\chi\) mod \(4a\) — every coprime prime
factor of \(p+4a^2\) lies in \(\ker\chi\). Kernel:
`classRough_of_certifies`. The converse is a theorem at \(a=1,2,3\)
(`classRough_123_iff_certificates`) and a measured \(\omega\)-gap for
general \(A\)
(\(P(\exists\chi\mid\mathrm{ClassRough})=0.846\) at \(x=10^6\),
\(A\le 40\); \(100/90/66/35\%\) at \(\omega=1..4\); \(0\) reverse
mismatches), not a near-equivalence (`c4_certificates.py`). Each assignment
\((\chi_a)_{a\le A}\) is a
multi-shift semi-linear vector-sieve problem of the classical
ker-character type; Hooley 1973 is T(2) of that decomposition on
\(\mathbb{Z}\); Iwaniec 1976 is the sieve. After
\(C_{\mathrm{euler}}(A)\) and \(\Pi_{\mathrm{gen}}\) are divided out of
the prime-aligned joint and the ClassRough marginals respectively, what
remains is a **selection** sequence. That sequence is the theorem.

**Opening case T(3).** T(3)\(^+\) claimed in `erdos-straus-T-3.md`:
\(S(3,x)\ll(\log x)^{-3/2}\) on the exact slice \(\{1,2,3\}\). The
two-sided bracket is the three-step plan there; completion of
\(q>x^{1/2}\) is the named risk. Calibrated against
\(\hat C(3)\approx 0.975\).

**Exposure, two die conditions.**

1. \(\limsup_{A\to\infty}\log C(A)/\log^2 A \ge \kappa=0.139\)
   (super-critical; covering law cancelled). Measured \(c'=0.104\) at
   \(x=10^9\), \(A\le 200\). Thin, not a completed kill.
2. \(\mathrm{cond}(a)\equiv 1\) out to QED-scale \(A\) (dummy covering:
   extra factors in \(\prod\rho_a\) are fictitious). Measured past
   \(a=80\). This is the live kill of a retuned schedule.

A theorem that \(C(A)\) exists at each fixed \(A\), with no control as a
sequence in \(A\), is an asymptotic at the wrong moment. A bracket with
\(c_\pm\) tracked in \(A\) is Layer 1 and is what the exposure needs.
It is not QED.

---

## Open questions (numbered)

Each item is a bounded mathematical question. Lean is optional.

### 1. Does the T(3) lower bound stall only at completion?

The upper bound \(S(3,x)\ll(\log x)^{-3/2}\) is claimed in-house
(T(3)\(^+\), `erdos-straus-T-3.md`). The plan for \(c_->0\) is
three steps (`erdos-straus-T-3.md`):

- (a) Iwaniec's half-dimensional lower bound per slice (\(\kappa=1/2<1\)).
- (b) Brüdern–Fouvry vector-sieve inequality to combine three
  components (Nath–Xie 2025 is the two-component template).
- (c) Completion: at most three large prime factors per shift;
  kernel-membership of \(q>x^{1/2}\) sits beyond BV.

Is (c) the only stall, or does (b) already fail for three semi-linear
factors on a prime sequence? If (c) stalls, a weaker \(c_-\) (positive
proportion of the expected order, or almost-certificates) is still a
bracket; that is escape 1, and per-slice BFI at well-factorable level
\(x^{4/7}\) or \(x^{3/5}\) can feed it because each residue
\(-4,-16,-36\) is fixed.

The genuine second lane is not “cite Linnik past \(\sqrt{x}\)”. A look
(21 Aug 2026; `erdos-straus-T-3.md`, frontier section) found that
existing dispersion/BFI machinery beats \(x^{1/2}\) only for a **fixed**
residue and well-factorable weights. The joint remainder is a **moving**
CRT class \(\alpha(d_1,d_2,d_3)\). **Sharp question:** does a joint
well-factorable weight framework exist for a CRT residue that depends
on the summed triple, and if not, can one be built for this specific
three-kernel case? A look reduced the \(r_\chi\) rewrite to Kloosterman
bilinear forms and tested Pascadi / MQW / Blomer–Pascadi: **no-go at
the stall** \(Q=x^{1/2+}\) (`erdos-straus-T-3.md`). Not a third escape.
That is the analytic sibling of roadmap §9's Brauer-\(\alpha\) fusion:
the genuinely hard frontier, not in-house next, not C1/H_ES, not an
LSD asymptotic.

### 1b. Ker-character form, general \(A\)

Is the same bracket standard when ClassRough is replaced by “some real
odd \(\chi\) mod \(4a\) certifies every coprime prime factor of
\(p+4a^2\)”? That is the classical “shifted values with all prime
factors in a prescribed index-2 subgroup” problem; Hooley 1973 is the
integer T(2); Iwaniec 1976 is the sieve. The exact implication
certificate \(\Rightarrow\)
ClassRough is kernel. The converse is a theorem at \(a=1,2,3\) and a
measured \(\omega\)-gap for general \(A\)
(\(84.6\%\) at \(x=10^6\), \(A\le 40\); exact at \(\omega=1\);
\(100/90/66/35\%\) at \(\omega=1..4\)), not a
near-equivalence (`c4_certificates.py`). Shared-certificate inheritance does not
explain \(\mathrm{cond}\to 1\). The defect layer
(\(a\notin\{1,2,3,6\}\)) is a smaller-exponent correction, not an
obstruction to the kernel main term.

Does the vector sieve apply to the certificate indicators themselves,
and do its constants track in \(A\) well enough to bound
\(\log C(A)/\log^2 A\)? The in-house form of that question is T(A)\(^+\):
the Selberg constant \(C_{\mathrm{sieve}}(A)\), next.

### 1c. Growth of \(C_{\mathrm{sieve}}(A)\) — computed

T(A)\(^+\) (`erdos-straus-T-A.md`, `c4_sieve_constant.py`): for each
fixed \(A\),
\[
S(A,x)\;\ll\; C_{\mathrm{sieve}}(A)\,(\log x)^{-\beta(A)},
\]
with \(\beta(A)=\sum_{a\le A}1/\varphi(4a)\) and
\(C_{\mathrm{sieve}}(A)=\Gamma(\beta+1)\exp(\gamma\beta-B(A))\).
The \(\Gamma\)-factor is \(\exp(o(\log^2 A))\) unconditionally.
\(B(A)\in[0.32,0.47]\) on \(A\le 200\), Q-stable at \(10^6\) and
\(10^7\). A raw OLS of \(\log C\) against \(\log^2 A\) on \(A=40..200\)
has slope \(0.128\), next to \(\kappa=0.139\): that is the finite-\(Q\)
artefact (late-start deficit \(\sum\log\log(4a)/\varphi(4a)\)), and
the ratio \(\log C/\log^2 A\) is already falling. Expected
\(B(A)=O(\log A)\) (Norton, Illinois J. Math. **20** (1976);
Languasco–Zaccagnini, J. Number Theory **127** (2007);
Granville–Soundararajan, Geom. Funct. Anal. **13** (2003)). The
schedule's upper-bound half survives on the Selberg side. Confirm or
correct the identification of \(B(A)\) with the Mertens-constant sum
of the sifting set. E_lane (`erdos-straus-T-A.md`) is the \(d=1\)
floor from this bound plus FL; E_power (`erdos-straus-E-power.md`) is
the covering-box count. Do not densify covering in response.

### 2. Confirm the Euler table is not \(C(A)\)

Prime-aligned
\[
C_{\mathrm{euler}}(A)=\prod_q\frac{1-k_q/(q-1)}{(1-1/(q-1))^{m_q}}
\]
equals \(0.91\) and is flat in \(A\) (\(0.914\) at \(40\) to \(0.910\)
at \(200\); zero residue collisions for \(A\le 200\)). ClassRough
marginals are that times \(\Pi_{\mathrm{gen}}(a,\sqrt{x})\), matched at
\(A=40\) to \(3\%\).

Is that the complete local main term of the *product of marginals*?
If a named factor is missing, say so. Do not treat \(0.91\) as the
selection constant \(\hat C(200)=6.92\).

### 3. What kind of object is leftover \(\hat C=S/\prod\rho_a\)?

Empirically \(\log\hat C\sim 0.104\log^2 A\) on \(A\ge 40\) at
\(x=10^9\). Pairs contribute \(1\). \(C_{\mathrm{euler}}\) is flat.
C2 (reciprocity among covering Jacobi symbols) does not fire.

Is a \(\log^2 A\) selection sequence a known LSD / pretentious leftover
after Euler factors, or is it a signal that the product formula is
already failing as \(A\) grows at this \(x\)? In particular: can
\(\mathrm{cond}(a)\to 1\) with \(\rho_a\) bounded away from \(1\) occur
in a genuine \(x\to\infty\) limit at fixed \(A\), or is that an
\(A\)-growing-with-\(x\) artefact of \(x=10^9\)?

### 4. Dummy covering as a theorem

If \(\mathrm{cond}(a)\equiv 1\) for all \(a\ge A_0\), then
\(S(A,x)=S(A_0,x)\) for \(A\ge A_0\) and extra covering width is
fictitious. Is there a criterion (sieve dimension, dependence graph,
saturation of a Chebotarev condition) that would prove this for
ClassRough, or prove it fails as \(x\to\infty\)?

A yes that it saturates kills the QED schedule without densifying
anything. A no that it is an \(x=10^9\) artefact puts the exposure back
on \(c'\) vs \(\kappa\).

### 5. What control on \(C(A)\) as a sequence is realistic?

The programme needs \(\limsup\log C(A)/\log^2 A<\kappa\), uniformly in
the sense of a theorem about the sequence, not a computation at
\(A\le 200\). Bounded \(C(A)\) would be more than enough and is
probably false given \(\hat C(200)=6.92\). Sub-critical with an explicit
\(c'<\kappa\) would keep a retuned schedule *if* dummy covering fails.

The \(A\)-dependence of the vector-sieve constants \(c_\pm(A)\) is the
theoretical shadow of the measured \(c'\). Which of a T(3) bracket,
an upper-bound sieve with \(c_+\) tracked in \(A\), and a matching
lower bound, is in reach with the 2025 template, and which requires
letting \(A\) grow with \(x\) (and is therefore not this paper)?

---

## What these questions are not

- A proof, sketch, or programme for emptying the box at
  \(A=\exp(c\sqrt{\log x})\).
- A proposal to densify covering, add \(d>1\) as a QED move, or grind
  larger identity boxes.
- A pair-asymptotic paper with T(A) as a remark.
- An Euler-product paper whose main theorem is \(C_{\mathrm{euler}}\approx 0.91\).
- An LSD / Wirsing *asymptotic* as the first paper. The genre delivers
  brackets; that is enough.
- A request for \(x=10^{10}\) data.
- Geometry (Harpaz, Cao–Xu, Campana, Theorem 1.8, occupancy of \(C_+\)).

If the answer to (1) is that (a) and (b) run and (c) is the only stall,
record the two escapes in the T(3) outlook. T(A)\(^+\) is written
(question 1c): the \(\Gamma\)-inflation is \(o(\log^2 A)\). E_lane is
the \(d=1\) floor. T(3)\(^+\) is already that paper's upper half.

If the answer to (4) is that dummy covering is the shape of the tail,
that is the valuable result. Do not densify in response.

---

## How this note relates to the others

| Note | File | Question |
|---|---|---|
| This one | `erdos-straus-sieve-desk.md` | T(3) joint well-factorable CRT residue; \(C_{\mathrm{sieve}}(A)\); leftover \(\hat C\); dummy covering |
| Statement | `erdos-straus-T-3.md` | T(3)\(^+\) claimed; three-step plan; frontier question |
| Working | `erdos-straus-T-A.md` | T(A)\(^+\) uniform Selberg; E_lane the \(d=1\) floor |
| Gate A paper | `erdos-straus-E-power.md` | one-stage claim withdrawn; two-stage density + separate transfer |
| Second, analytic | `erdos-straus-gs-reformulation.md` | Dictionary of the joint lower-tail; C2 is a **null**; conditioned pretentious tail if cond sticks |
| Geometric | `erdos-straus-loughran-orbit.md` | Class-theory and effectivity; not a proof path |

This note is a written question list. The theorems already in the archive
are T(A)\(^+\) (\(C_{\mathrm{sieve}}(A)\)) and E_lane (the \(d=1\) floor);
E_power is a repaired two-stage programme, not a compiled
\(x^{1-\delta}\) count; the T(3) lower bound is the
three-step plan with named risk. Companions:
`erdos-straus-T-A.md` and `erdos-straus-T-3.md`.
Do not mix this with the geometric questions.

---

## Status paragraph

> We have the upper bound \(S(3,x)\ll(\log x)^{-3/2}\) (T(3)\(^+\):
> kernel exactness plus Selberg of dimension \(3/2\) on hard primes).
> The matching lower bound is a three-step plan: Iwaniec per slice;
> Brüdern–Fouvry to combine; completion of factors \(q>x^{1/2}\).
> Existing BFI/Maynard machinery beats \(x^{1/2}\) only for a *fixed*
> residue. The joint remainder is a moving CRT class
> \(\alpha(d_1,d_2,d_3)\). The \(r_\chi\to\) Kloosterman bilinear look
> is a range no-go at the stall (Pascadi / MQW / Blomer–Pascadi). The
> sharp question: does a joint well-factorable weight framework exist
> for that residue, and if not, can one be built for this three-kernel
> case? That sits with roadmap
> §9's Brauer-\(\alpha\) fusion as the genuinely hard frontier, not
> in-house next. If it stalls: weaker \(c_-\) / almost-certificates
> (per-slice well-factorable level still applies). Uniform Selberg
> T(A)\(^+\) is written:
> \(S(A,x)\ll C_{\mathrm{sieve}}(A)\,(\log x)^{-\beta(A)}\) with
> \(\beta\sim 0.66\log A\) and \(\Gamma(\beta+1)e^{\gamma\beta}=
> \exp(o(\log^2 A))\); expected \(B(A)=O(\log A)\). Selberg does not
> re-create the covering law. E_lane:
> \(x\exp(-c'\sqrt{\log x}\,\log\log x)\) as the \(d=1\) floor, below
> Vaughan. E_power: one-stage \(S_A\ll x^{1-\delta}\) withdrawn; the
> live target is two-stage finite density plus transfer
> (`erdos-straus-E-power.md`).
> Dummy covering remains the live kill of a QED ClassRough schedule.
> Pairs factor; the prime-aligned Euler
> factor is \(0.91\) and flat; leftover \(\hat C=S/\prod\rho_a\) grows
> like \(\exp(0.104\log^2 A)\) at \(x=10^9\); cond\(\to 1\) past
> \(a=80\). Both partials of \(\log S\) are measured: \(c'(x)\) climbs
> \(0.063\to 0.094\) on \(10^6\to 10^9\); the \(A\)-curvature is
> \(c'=0.104\) against \(\kappa=0.139\), unconverged, collision
> \(\sim 10^{24}\). Do not densify the covering, do not upgrade
> T(3) to an LSD asymptotic, do not run \(x=10^{10}\), and do not treat
> this as a request to prove Erdős–Straus.

Working notes: `erdos-straus-T-A.md`, `erdos-straus-T-3.md`.

