<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# T(3) — does the δ-symbol avoid the (0, 1/2, 1/2) degeneracy?

**Riley Betts Erdős–Straus programme, 21 August 2026.**
Companion to `erdos-straus-T-3.md` (Phase 1 reduction),
`erdos-straus-T-2.md` (A2.2/A2.3 closed), `zheng-wellfactorable.md`.
Primary references: D. R. Heath-Brown, J. Reine Angew. Math. **481**
(1996), 149–206; W. Duke, J. B. Friedlander, H. Iwaniec, Invent. Math.
**128** (1997), 23–43; D. R. Heath-Brown, L. B. Pierce, J. Reine Angew.
Math. **727** (2017), 85–143. Flag only: S. Bettin, V. Chandee, Adv. Math.
**328** (2018), 1234–1262.

This file **does not prove** the Erdős–Straus conjecture, does not claim
T(3) progress, and does not reopen Zheng or leg-sacrifice. Not Lean. Do
not densify covering. Do not discharge `AnalyticSurvivorBound`.

**Dies if (BV wall).** Heath-Brown’s dissection parameter \(Q_\delta\)
cannot both open an \((m,\nu)\)-bilinear cell and complete the AP index
\(k\) whenever the arithmetic modulus satisfies \(Q_D\ge 1/2\). The
Phase 1 identity reappears as that incompatibility. Range check:
`t3_delta_ranges.py`.

**Does not die of that identity at \((0,1/2,1/2)\).** There the AP index
is absent (\(D\ge x\)), so the stall lemma is the wrong obstruction.
Additive characters already give a bilinear cell. No bound is claimed
up to \(D\sim x\) or \(D\sim x^{3/2}\).

---

## Object

The weighted count is
\[
W(x)
=\sum_{\substack{p\le x\\ p\text{ hard}}}
\prod_{a=1}^{3}r_{\chi_a}(p+4a^2)
=\sum_{d_1,d_2,d_3}
\chi_1(d_1)\chi_2(d_2)\chi_3(d_3)
\sum_{\substack{p\le x\\ p\text{ hard}}}
\mathbf{1}_{p\equiv\alpha(d_1,d_2,d_3)\pmod{D}},
\]
with \(D=\mathrm{lcm}(d_1,d_2,d_3)\asymp d_1 d_2 d_3\) and \(\alpha\) the
moving CRT residue. After switching, each \(d_a\le\sqrt{x}\). Bombieri–
Vinogradov covers \(D\le x^{1/2}\). The tail runs up to \(D\sim x^{3/2}\).

Three cells, kept distinct:

| Cell | \((\alpha_1,\alpha_2,\alpha_3)\) | \(Q_D=\sum\alpha_a\) | AP index \(k\sim x/D\) |
|---|---|---|---|
| BV wall (Phase 1 stall) | product just past \(x^{1/2}\) | \(1/2\) | \(K=1/2\) |
| Uneven A2.3 | \((0,1/2,1/2)\) | \(1\) | absent |
| Symmetric | \((1/2)^3\) | \(3/2\) | absent |

Zheng A2.2/A2.3 are closed and are not re-derived. The Phase 1 lemma
(no bilinear cell at \(\delta=0\)) is: if \(M+N=1\) and \(Q=1/2\), then
\(M<Q\) and \(N<Q\) cannot both hold. That lemma is for a *combined
modulus* \(Q=D\) (additive characters, or any method that presents Type II
as \(mn\equiv\alpha\pmod{D}\)). The question here is whether the
δ-method’s own Farey order is a genuinely extra parameter.

---

## Joint δ-expansion, not sequential legs

Heath-Brown’s identity, for a parameter \(Q=Q_\delta\),
\[
\delta(n)
=c_Q\,Q^{-2}
\sum_{q=1}^\infty
\sum_{\substack{a=1\\(a,q)=1}}^q
e_q(an)\,
h\Bigl(\frac{q}{Q},\frac{n}{Q^2}\Bigr),
\]
with \(h(x,y)\) negligible unless \(q\lesssim Q\) and \(|n|\lesssim Q^2\).
Detect the congruence *jointly*:
\[
\mathbf{1}_{n\equiv\alpha\pmod{D}}
=\sum_{k}\delta(n-\alpha-Dk).
\]
Do not disperse \(d_1\), then \(d_2\), then \(d_3\). Insert Vaughan /
Heath-Brown on \(\Lambda(n)\). Type II is \(n=m\nu\) with log-exponents
\(M+N=1\), \(N\le 1/2\le M\). The resulting phase is
\[
e\bigl(a(m\nu-\alpha-Dk)/q\bigr),
\qquad q\lesssim Q_\delta.
\]
The Kloosterman / Farey modulus is \(q\), not \(D\). That is the extra
degree of freedom, if it survives the \(k\)-sum.

Lengths, in log-exponents: \(K=\max(1-Q_D,0)\). The \(k\)-sum is absent
when \(Q_D\ge 1\) (at most one representative in \([1,x]\)). It is
complete when \(K\ge Q_\delta>0\), incomplete when \(0<K<Q_\delta\).
The \((m,\nu)\) form is bilinear (both incomplete) iff \(M<Q_\delta\)
and \(N<Q_\delta\); otherwise at least one Type II factor folds (Type I /
Weil).

---

## Lemma (Farey–\(k\) incompatibility)

If \(M+N=1\) and \(Q_D\ge 1/2\), then one cannot have both

1. \((m,\nu)\)-bilinear versus Farey: \(Q_\delta>\max(M,N)\ge 1/2\),
2. \(k\)-complete: \(Q_\delta\le K=1-Q_D\le 1/2\).

Proof: (1) forces \(Q_\delta>1/2\); (2) forces \(Q_\delta\le 1/2\).
(`t3_delta_ranges.py`, `lemma_no_complete_k_bilinear_at_wall`.)

At the BV wall this is the Phase 1 identity with the arithmetic modulus
replaced by the dissection parameter, plus the observation that the extra
parameter cannot be spent twice. Completing \(k\) forces \(q\) to see
\(D\) (geometric sum / Ramanujan condition on \(aD/q\)), which collapses
Farey back onto the combined modulus. Opening bilinear forces \(Q_\delta>1/2\ge K\), so \(k\) is incomplete: a short third dual, not a bilinear
cell with a free \(Q_\delta\).

**At the BV wall the δ-symbol does not avoid the degeneracy.** It
repackages it. Dual lengths after opening bilinear at \(Q_\delta=1/2+\)
are \(I=J=Q_\delta-1/2\to 0\), the same short duals as Phase 2 at
\(\delta\to 0^+\). Weil’s range \(I\sim Q_\delta/2\) needs \(Q_\delta=1\).
Pascadi / Blomer–Pascadi savings remain far from the wall (Phase 2–3 of
`erdos-straus-T-3.md`). Not a partial increment past \(x^{1/2}\) in \(D\).

---

## The cell \((0,1/2,1/2)\)

Here \(Q_D=1\), so \(K=0\). There is no AP index to complete. The
incompatibility lemma is vacuous. The stall identity \(M+N=1\), \(Q=1/2\)
was never the obstruction of this cell: that identity is the BV wall.
A2.3 died because Zheng’s \(q\)-slot wants \(\theta\le 7/36\), not because
a bilinear cell is missing.

Additive characters already use modulus \(D\sim x\), hence \(Q_D=1>1/2\),
and balanced Type II is bilinear. The δ-method with \(Q_\delta>1/2\)
opens the same cell against Farey moduli, with duals \(I=Q_\delta-1/2\).
Those duals are short until \(Q_\delta\sim 1\). The remaining sum is
\[
\sum_{m,\nu}\alpha_m\beta_\nu
\sum_{d_2,d_3}\chi_2(d_2)\chi_3(d_3)
\,e\bigl(a(m\nu-\alpha(d_2,d_3))/q\bigr),
\]
\(\alpha\) the CRT of two large moduli. That is a moving-CRT Kloosterman
of two \(\sqrt{x}\)-moduli against a Farey \(q\), not DFI’s
\(e(a\overline{m}/n)\) and not Zheng Theorem 1.1.

**Range reached:** none past \(D\le x^{1/2}\) is proved. Bilinear
*existence* at this cell is not a saving theorem up to \(D\sim x\), and
not up to \(D\sim x^{3/2}\). The joint well-factorable CRT residue
(Phase 4 / plan §4w) is the same object in different clothing.

The symmetric cell \((1/2)^3\) is the same story with \(Q_D=3/2\) and a
three-factor CRT phase.

---

## Two-dimensional Kloosterman (Heath-Brown–Pierce)

Heath-Brown–Pierce treat *two quadratic forms* in \(k\ge 5\) variables.
The 2-dimensional Kloosterman refinement is a minor-arc \(L^2\) bound
after Parseval, using 2D Dirichlet boxes (a given \((\alpha_1,\alpha_2)\)
may lie in many boxes; they accept overlap because they only need an
upper bound). Their “Type I / Type II primes” (§2.3 of arXiv:1309.6767)
are good/bad primes for the pencil, not Vaughan’s Type I / Type II.

The T(3) system, after eliminating \(p\), is *two linear equations*
\[
d_1 n_1-d_2 n_2=12,\qquad d_1 n_1-d_3 n_3=32,
\]
plus \(p=d_1 n_1-4\) prime. Two δ-symbols (orders \(Q_1,Q_2\)) match the
dimensionality of HBP’s circle. They do **not** replace Type II for the
prime. That still wants a third δ on \(d_1 n_1-m\nu=4\), whose order
\(Q_3\) is the \(Q_\delta\) of the previous sections. Incomplete Poisson
in \(n_1\sim\sqrt{x}\) needs \(Q_1+Q_2>1/2\), which is cheap and does not
open the \((m,\nu)\) cell. HBP does not generalize to three simultaneous
linear APs by adding a third quadratic form: the hardness is primality
in a moving CRT class, not representation by a pair of quadrics in five
variables.

---

## Bettin–Chandee (flag only)

Bettin–Chandee bound trilinear forms with Kloosterman *fractions*
\(B(M,N,A)\), an extra averaging variable \(a\in A\) on the DFI phase
\(e(a\overline{m}/n)\). That is not three residue moduli \(d_1,d_2,d_3\).
Not transferred.

DFI Theorems 1–3 themselves are bilinear forms \(e(a\overline{m}/n)\)
with denominator \(n\sim N\), not Farey \(q\) against a CRT phase
\(\alpha(d_1,d_2,d_3)\). Off-the-shelf DFI does not estimate the sum in
the \((0,1/2,1/2)\) paragraph above.

---

## What is not claimed

- T(3) progress, a matching lower bound, or a partial increment of \(D\)
  past \(x^{1/2}\). Bilinear *existence* at \(Q_D\ge 1\) is not a bound.
- That \(\chi(d)1_{d\le D}\) is well-factorable of every level.
- A 3-parameter Heath-Brown–Pierce theorem.
- Anything in Lean.

**Next.** The BV-wall stall is unchanged. The uneven cell is not that
stall; covering it still wants a joint estimate for a moving CRT residue
of two large moduli (or escape 1). That object is named in
`erdos-straus-varying-modulus-gap.md`. Do not densify covering.
