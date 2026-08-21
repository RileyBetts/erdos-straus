<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# T(3) — a two-sided bracket, not an asymptotic

**Riley Betts Erdős–Straus programme, 20 August 2026.**
Opening case of T(A). Companion to `erdos-straus-T-A.md`,
`erdos-straus-sieve-desk.md`, `ErdosStraus.lean`
(`classRough_123_iff_certificates`). This file **does not prove**
the Erdős–Straus conjecture.

**Claimed here:** the upper bound of the right order,
\(S(3,x)\ll(\log x)^{-3/2}\). **Not claimed:** the matching lower bound. The two-sided bracket
remains open at the completion step (kernel-membership of factors
\(q>x^{1/2}\), beyond BV). A three-step plan with that named risk,
and two escapes for the paper's outlook, is written below.
Kernel exactness is Lean; the upper bound is a Selberg sieve of
dimension \(3/2\) on hard primes, written below.

---

## Statements

Let \(p\) run over primes in the six hard classes modulo 840. Write
\[
S(3,x)=\mathbb{P}\bigl(\mathrm{ClassRough}(p,a)\text{ for }a=1,2,3
\bigm| p\le x\text{ hard}\bigr).
\]

**Theorem T(3)\(^+\) (claimed).**
\[
S(3,x)\;\ll\;(\log x)^{-3/2}\qquad(x\to\infty).
\]
Proof in the next section. The implied constant is effective and
factors through the four assignment Euler products of
`c4_t3_euler.py`.

**T(3) (bracket, not claimed).** There exist explicit
\(0<c_-\le c_+<\infty\) such that
\[
\frac{c_-}{(\log x)^{3/2}}
\;\le\;
S(3,x)
\;\le\;
\frac{c_+}{(\log x)^{3/2}}.
\]
The upper half is T(3)\(^+\). The lower half is the three-step plan
below: Iwaniec per slice, Brüdern–Fouvry to combine, completion of
large factors. Completion is the named risk. Calibration: \(\hat C(3)\approx 0.960\) at
\(x=10^6\), \(\approx 0.975\) at \(x=10^9\).

**T(1) (claimed, by citation).** ClassRough at \(a=1\) is the
\(\chi_4\)-certificate (`classRough_iff_chi4`). For hard \(p\equiv 1
\pmod{4}\), \(p+4\) is odd, so this is \(p=x^2+y^2-4\). Iwaniec, Acta
Arith. **24** (1973/74), 435–459, plus the congruence layer of
Fuchs–Hsu–Rickards–Schindler–Stange, arXiv:2504.20289, give
\[
S(1,x)\;\asymp\;(\log x)^{-1/2}.
\]
This is one slice, not the joint. It calibrates the exponent
\(\kappa=1/2\) per certificate.

---

## Kernel (proved)

`classRough_123_iff_certificates` in `ErdosStraus.lean`: ClassRough on
\(a=1,2,3\) is exactly the \(1\times 2\times 2\) union of character
certificates.

| \(a\) | \(4a\) | odd characters | kernels |
|---:|---:|---|---|
| 1 | 4 | \(\chi_4\) | \(\{1\}\bmod 4\) |
| 2 | 8 | \(\chi_4\), \(\chi_4\chi_8\) | \(\{1,5\}\), \(\{1,3\}\bmod 8\) |
| 3 | 12 | \(\chi_4\), \(\chi_4\chi_3\) | \(\{1,5\}\), \(\{1,7\}\bmod 12\) |

The exactness locus is \(\{1,2,3,6\}\) (\(\lambda(4a)\mid 2\)). T(3)
is the consecutive covering-width opening. At \(x=10^6\): 656
ClassRough on all three slices, 656 certificate-union, match.

---

## Proof of T(3)\(^+\)

By the kernel theorem it is enough to bound each of the four
certificate assignments and take the union. Fix an assignment
\((H_1,H_2,H_3)\), where \(H_a\) is an index-2 kernel in
\((\mathbb{Z}/4a\mathbb{Z})^*\). Write \(\mathcal{A}\) for the set of
hard primes \(p\le x\), and \(\mathcal{P}\) for the set of primes \(q\)
that lie outside at least one \(H_a\) (coprime to \(4a\)). For such a
\(q\), let \(k_q\) be the number of distinct forbidden residues
\[
p\equiv -4a^2\pmod{q}
\quad\text{over those \(a\in\{1,2,3\}\) with \(q\notin H_a\).}
\]
Then \(0\le k_q\le 3\), and \(k_q=0\) if \(q\) lies in every relevant
kernel.

Let \(S(\mathcal{A},\mathcal{P},z)\) be the number of \(p\in\mathcal{A}\)
with no prime factor from \(\mathcal{P}\) dividing any of \(p+4\),
\(p+16\), \(p+36\) below \(z\). The full certificate is the case
\(z=\infty\): every prime factor of each shift lies in the prescribed
kernel. Hence the counting function of the assignment is
\(\le S(\mathcal{A},\mathcal{P},z)\) for every \(z\).

Take \(z=x^{1/4}(\log x)^{-B}\) with \(B\) large enough for
Bombieri–Vinogradov. Selberg's upper-bound sieve
(Halberstam–Richert, *Sieve Methods*, Thm. 5.1; Friedlander–Iwaniec,
*Opera de Cribro*, Thm. 7.1) gives
\[
S(\mathcal{A},\mathcal{P},z)
\;\ll\;
X\prod_{q<z}\Bigl(1-\frac{k_q}{q-1}\Bigr)
\;+\;
\sum_{\substack{d<z^2\\ d\mid P(z)}}|R_d|,
\]
where \(X=\#\mathcal{A}\sim(6/\varphi(840))\,x/\log x=x/(32\log x)\) and
\(R_d\) is the remainder for hard primes in the CRT progressions
modulo \(840d\).

**Density.** For the assignment \((\chi_4,\chi_4,\chi_4)\), one has
\(k_q=0\) if \(q\equiv 1\pmod{4}\) and \(k_q=3\) if \(q\equiv 3\pmod{4}\),
except at the finitely many \(q\) dividing \(12\), \(20\), or \(32\)
(residue collisions among \(-4,-16,-36\)). Thus
\[
\sum_{q<z}\frac{k_q}{q}
\;=\;
\frac32\log\log z+O(1),
\]
so the sieve has dimension \(\kappa=3/2\) and
\[
\prod_{q<z}\Bigl(1-\frac{k_q}{q-1}\Bigr)
\;\asymp\;
(\log z)^{-3/2}
\;\asymp\;
(\log x)^{-3/2}.
\]
The mixed assignments have the same Mertens exponent: each slice
forbids a density-\(1/2\) set of \(q\), and the three densities sum to
\(3/2\) up to \(O(1)\) collisions. The assignment Euler products of
`c4_t3_euler.py` (\(0.84\)–\(1.81\) at \(q\le 10^6\)) are the
constant factors in this product.

**Remainders.** \(z^2\le x^{1/2}(\log x)^{-2B}\). Bombieri–Vinogradov
on primes in arithmetic progressions, restricted to the six hard
classes modulo \(840\) and moduli \(840d\) with \(d\mid P(z)\)
coprime to \(840\), yields
\[
\sum_{d<z^2}|R_d|
\;\ll\;
\frac{x}{(\log x)^A}
\]
for any \(A\), by taking \(B=B(A)\). (Siegel–Walfisz handles the
\(q\mid 840\) Euler factors, which are absorbed in the constant.)

Therefore each assignment contributes \(\ll x/(\log x)^{1+3/2}\), and
dividing by \(\#\mathcal{A}\sim x/(32\log x)\) gives
\(S(3,x)\ll(\log x)^{-3/2}\).

(The same argument with \(z=x^{1/2-}\) would also bound the *full*
kernel condition directly for the upper bound: a prime factor
\(q>x^{1/2}\) of \(p+4a^2\le x+O(1)\) occurs at most once, and
Selberg at \(z=x^{1/2-}\) is available for an *upper* bound because
the remainder is estimated trivially or by BV at a smaller level
after a combinatorial truncation. Dimension \(3/2\) Selberg does not
require reaching a sifting limit.)

---

## T(3) lower bound — three-step plan (not claimed)

The matching lower bound is not a citation. It is a three-step
argument with a named stall. Steps (a) and (b) are on the shelf.
Step (c) is where it can fail.

**(a) Per-slice component.** Iwaniec's half-dimensional sieve
(Acta Arith. **29** (1976), 69–95) has a lower bound. That is its
celebrated feature: at dimension \(\kappa=1/2<1\) the sifting limit
does not obstruct a matching lower bound of order \(V(z)\). Each
certificate kernel is this sieve. T(1) is the \(a=1\) case, already
claimed by citation (Iwaniec, Acta Arith. **24**, plus Fuchs et al.).

**(b) Combine the three components.** The Brüdern–Fouvry vector-sieve
inequality (J. Reine Angew. Math. **454** (1994), 59–96; Compositio
Math. **102** (1996), 337–355) multiplies lower-bound weights without
requiring both factors to be positive at once. Nath–Xie,
arXiv:2501.16723 (Acta Arith. 2025), is the two-component template of
exactly this: one semi-linear factor and one linear factor, written
as a fundamental lemma for two beta sieves (their Prop. 3.10; cf.
Harman, *Prime-detecting sieves*, Lemma 10.1, and Heath-Brown–Li,
J. Number Theory **169** (2016)). Three simultaneous kernels of
dimension \(1/2\) are the same inequality with three factors. This
step produces a lower bound for \(S(\mathcal{A},\mathcal{P},z)\),
i.e. no bad prime factor below \(z\).

**(c) Completion — named risk.** Passing from “no bad factors below
\(z\)” to the full certificate means controlling the large prime
factors of each shift \(p+4a^2\le x+O(1)\). There are at most three
such factors per shift (the rest of the mass is \(<z\), already
sifted). Kernel-membership of a factor \(q>x^{1/2}\) sits beyond
Bombieri–Vinogradov: there is no averaged remainder at moduli larger
than \(x^{1/2}\). That is where the argument can stall. It is the
same shape as Chen's theorem versus twin primes — the almost-prime
lower bound is (b); the last large factor's kernel-membership is not
an averaged congruence.

**Two escapes, both for the paper's outlook.**

1. *Weaker \(c_-\).* A positive proportion of the expected order still
   delivers the bracket: \(S(3,x)\gg(\log x)^{-3/2-\varepsilon}\) or
   \(\gg(\log x)^{-3/2}/(\log\log x)^{O(1)}\) is T(3) for the
   exposure. Accepting almost-certificates (large factors unrestricted,
   or restricted only to \(q\le x^{1/2}\)) is this lane.
2. *Switch detectors.* Replace the kernel indicator by the divisor-sum
   detector \(r_\chi(n)=\sum_{d\mid n}\chi(d)\). The \(r\)-weighted T(3)
   is a three-shift Linnik / Hardy–Littlewood problem: expand
   \(\sum_{p\text{ hard}}\prod_{a=1}^{3}r_{\chi_a}(p+4a^2)\) as a
   character-weighted prime sum in simultaneous progressions.
   Dispersion-method territory (Linnik, Izv. Akad. Nauk SSSR Ser. Mat.
   **24** (1960), 629–706; Motohashi, Acta Arith. **16** (1969/70);
   Iwaniec, Acta Arith. **24**), with a fifty-year unconditional
   pedigree. The weighted count is not \(S(3,x)\), but a positive
   weighted main term plus a comparison of \(r\) to the indicator is a
   second path to \(c_->0\).

Neither escape is claimed here. Both belong in the T(3) paper's
outlook. Do not cite Nath–Xie as if it were three semi-linear
components on a prime sequence.

---

## Frontier: joint well-factorable weights (look, 21 Aug 2026)

This is the analytic sibling of roadmap §9 / plan §4m (Brauer-\(\alpha\)
fusion). Both are the **genuinely hard frontier**: named, not this
quarter's in-house compute, not a citation. It is not C1, not H_ES, and
not a request to densify covering.

**What existing machinery actually beats \(x^{1/2}\).**
Bombieri–Vinogradov with absolute values remains at \(x^{1/2}\). Past
that barrier the tradition has a *weaker* mean value: a **fixed** residue
\(a\), **well-factorable** weights \(\lambda(q)\). Bombieri–Friedlander–Iwaniec,
Acta Math. **156** (1986), Thm 10: \(Q=x^{4/7-\varepsilon}\). Maynard
arXiv:2006.07088: \(x^{3/5}\) or \(x^{7/12}\) under stronger
factorability. Linnik's dispersion method (Izv. Akad. Nauk **24**, 1960)
solves *binary* additive problems (Titchmarsh \(\sum_p\tau(p-a)\);
Hardy–Littlewood \(p=x^2+y^2+n\)). Once BV exists, the Titchmarsh main
term no longer needs past \(\sqrt{x}\): switch \(d\leftrightarrow(p-a)/d\).
Fouvry / BFI past \(\sqrt{x}\) buy a secondary term, not existence of
the main term.

**One kernel is finished, and not by beating BV.** Iwaniec, Acta Arith.
**24**, is T(1): residue \(-4\) fixed. A single \(r_\chi(p+4)\) is
Titchmarsh with conductor \(4\), a BV theorem. Fouvry–Iwaniec, Acta
Arith. **79** (1997), adds a linear condition on one Gaussian coordinate,
still one \(\chi_4\).

**Two kernels is the shelf, and it still does not complete.** Nath–Xie
(arXiv:2501.16723) is one semi-linear kernel plus one linear almost-prime.
Heath-Brown–Li, J. Number Theory **169** (2016), is Chen plus a third
almost-prime. Both stop at \(P_r\). They do not put a leftover factor
\(q>x^{1/2}\) into an index-2 subgroup.

**Why step (c) is not a BFI citation.** BFI needs the residue independent
of the modulus. Separately, \(p\equiv -4,-16,-36\pmod{d_a}\) *are* fixed,
so well-factorable remainders can be used **one slice at a time** (this
feeds escape 1: almost-certificates, Chen-type). The *joint* remainder
is the CRT class
\[
\alpha(d_1,d_2,d_3)\bmod\mathrm{lcm}(d_1,d_2,d_3)
\]
solving those three congruences at once. That residue **moves with the
triple**. After switching each \(d_a\le\sqrt{x}\), the lcm is as large as
\(x^{3/2}\), past Elliott–Halberstam. Linnik is binary; the product of
three \(r_\chi\) is ternary Titchmarsh, which is not on the shelf.

**The sharp question.** Does a joint well-factorable weight framework
exist for a CRT residue that depends on the summed triple
\((d_1,d_2,d_3)\mapsto\alpha(d_1,d_2,d_3)\)? If not, can one be built
for this specific three-kernel case (conductors \(4,8,12\); residues
\(-4,-16,-36\); hard primes)?

A yes is a theorem in the BFI/Maynard dialect and would complete (c),
or a weighted \(c_->0\) via \(r_\chi\). A no leaves escape 1 as the
outlook (weaker \(c_-\) / almost-certificates, possibly with per-slice
level \(4/7\) or \(3/5\)). Neither answer is in-house next, and neither
is H_ES.

---

## Look: \(r_\chi\) to Kloosterman bilinear forms (21 Aug 2026)

This section carries out the reduction from escape 2's detector to an
explicit bilinear/trilinear Kloosterman-sum instance, then tests the
resulting lengths against Pascadi, Milićević–Qin–Wu, and
Blomer–Pascadi. It does not prove a matching T(3) lower bound. \(A=3\)
is fixed (conductors \(4,8,12\)); this is not E_power's growing \(A\).

### Phase 0 — Blomer–Pascadi is the primary tool

Blomer–Pascadi, arXiv:2607.24311, Theorem 1.1 bounds
\(\sum\sum\alpha_m\beta_n S(am,n;c)\) for **all** moduli \(c\), by a
new connection to quadratic character sums (the fourth-moment
discriminant becomes a Legendre symbol; §1.4). In the square-root
range \(N=\sqrt{c}\) the saving is \(c^{-1/32}\), doubling
Kowalski–Michel–Sawin. The bound is nontrivial for
\(N\in(c^{13/28+\varepsilon},\,c^{7/12-\varepsilon})\).

That is the same quadratic-character language as the T(3) kernels
(\(\chi_4,\chi_8,\chi_3\)). Pascadi arXiv:2511.08445 is strongest for
composite \(c=pq,p^2\) (saving \(c^{-1/12}\) at \(|I|,|J|\sim\sqrt{c}\))
and weakest on primes; MQW arXiv:2511.07550 is a product-argument
kernel \(\mathrm{Kl}_2(cmn;q)\), the Voronoi/GL2 shape. Phase 0
therefore ranks **Blomer–Pascadi first**, Pascadi Cor. 1.4/7.5 as the
modulus-averaging form, MQW as the complementary single-modulus retry.

### Phase 1 — the reduction

Write \(r_\chi(n)=\sum_{d\mid n}\chi(d)\). The weighted count is
\[
W(x)=\sum_{\substack{p\le x\\ p\text{ hard}}}
\prod_{a=1}^{3} r_{\chi_a}(p+4a^2)
=\sum_{d_1,d_2,d_3}\chi_1(d_1)\chi_2(d_2)\chi_3(d_3)
\sum_{\substack{p\le x\\ p\text{ hard}}}
\mathbf{1}_{d_1\mid p+4}\,\mathbf{1}_{d_2\mid p+16}\,\mathbf{1}_{d_3\mid p+36}.
\]
The inner system is \(p\equiv-4\pmod{d_1}\), \(\equiv-16\pmod{d_2}\),
\(\equiv-36\pmod{d_3}\). Compatibility forces
\(\gcd(d_1,d_2)\mid 12\), \(\gcd(d_1,d_3)\mid 32\),
\(\gcd(d_2,d_3)\mid 20\), so the pairwise gcds are \(O(1)\) and
\(D:=\mathrm{lcm}(d_1,d_2,d_3)\asymp d_1 d_2 d_3\). When compatible
there is a unique residue \(\alpha(d_1,d_2,d_3)\bmod D\). The hard-class
constraint is a fixed set of residues mod \(840\), absorbed into
\(\mathrm{lcm}(D,840)\).

Each \(r_\chi(p+4a^2)\) with \(p+4a^2\sim x\) may be switched
\(d\leftrightarrow(p+4a^2)/d\), so every \(d_a\le\sqrt{x}\). The BV
range is then \(D\le x^{1/2}\). The named stall is the tail
\[
x^{1/2}<D\le x^{3/2},\qquad d_a\le x^{1/2}.
\]
Dyadically \(D\sim Q=x^{1/2+\delta}\) with \(\delta\in(0,1]\). The
first increment past BV is \(\delta\to 0^+\).

Detect \(p\equiv\alpha\pmod{D}\) by additive characters and apply
Heath-Brown/Vaughan to the prime sum (Deshouillers–Iwaniec Invent.
Math. **70**; Fouvry–Iwaniec Acta Arith. **79**; Friedlander–Iwaniec–Mazur–Rubin
Invent. Math. **193** — already in the bibliography). Type II is
\(mn\sim x\) against the congruence \(mn\equiv\alpha\pmod{D}\). For
\(\gcd(m,D)=1\) this is \(n\equiv\alpha\overline{m}\pmod{D}\). Poisson
summation in \(n\) produces the inverse-linear phase
\(e(A\overline{m}/D)\); Cauchy–Schwarz / completing the \(m\)-sum
opens a Kloosterman sum \(S(\,\cdot\,,\,\cdot\,;D)\). Twisted
multiplicativity in \(D\asymp d_1 d_2 d_3\) makes the form trilinear
in three Kloosterman sums of coprime moduli.

**Parameters, in terms of \(x\).** Let the Type II split be
\(N=x^{\theta}\), \(M=x^{1-\theta}\) with \(\theta\le 1/2\). The Poisson
dual interval lengths (Pascadi's \(|\mathcal{I}|,|\mathcal{J}|\)) are
\[
|\mathcal{I}|\asymp Q/M,\qquad |\mathcal{J}|\asymp Q/N,
\]
provided both Type II factors are strictly shorter than \(Q\) (otherwise
that variable folds to a complete residue system mod \(Q\), a Type I
sum, Weil's regime). The modulus-averaging parameters in Pascadi
Cor. 1.4/7.5 are \(C\asymp Q\) and a dyadically frozen
\(q=d_1 d_2\) with \(q\mid c\), \(c\sim C\), factorable as
\(q=dd'e\) with \(d'\mid d\), \((d,e)=1\). For the balanced split
\(\theta=1/2\),
\[
M=N=x^{1/2},\qquad
|\mathcal{I}|=|\mathcal{J}|=x^{\delta},\qquad
C=q_{\mathrm{avg}}\asymp x^{1/2+\delta}.
\]

**Lemma (no bilinear cell at \(\delta=0\)).**
If \(M+N=1\) and \(Q=\tfrac12\) (log-exponents: Type II \(mn\sim x\),
modulus \(D\sim x^{1/2}\)), then \(M<Q\) and \(N<Q\) cannot both hold.
Proof: otherwise \(M+N<2Q=1\).

A bilinear cell therefore exists only for \(\delta>0\). At the
Bombieri–Vinogradov wall at least one Type II factor folds, and the
form is Type I (Weil). This is an identity, not a grid artefact;
`t3_kloosterman_ranges.py` records it as `lemma_no_bilinear_cell_at_wall`.

### Phase 2 — go/no-go against Pascadi

Pascadi Cor. 1.4 requires \(|\mathcal{I}|,|\mathcal{J}|\ll C^{1/2+o(1)}\).
For the balanced split this is \(x^{\delta}\ll x^{1/4+\delta/2}\), i.e.
\(\delta\le 1/2\), which holds throughout the tail. **The length
constraint is satisfied near the stall. The saving is not.**

Cor. 1.4 / Thm 1.2 save against the Pólya–Vinogradov bound
\(\|\alpha\|\|\beta\|C\), which matches Weil at
\(|\mathcal{I}|,|\mathcal{J}|\sim\sqrt{C}\). Just past BV the duals are
of length \(x^{\delta}\) with \(\delta\) small, far below
\(\sqrt{C}=x^{1/4+\delta/2}\). Weil
\(\|\alpha\|\|\beta\|\sqrt{|\mathcal{I}||\mathcal{J}|C}\) is then the
relevant trivial bound, and Pascadi's \(C^{1}\) term is worse than
Weil. Thm 7.1 beats Weil for \(M\asymp N\) only when
\(N>c^{2/5}\) (Example 7.2, best factorisation \(c=pq\)): for
balanced duals this is \(\delta>1/3\), i.e. \(Q>x^{5/6}\).

The factorization \(q=dd'e\) can be arranged in dyadic boxes
(two of the three \(d_a\) frozen), and \(c=pq\) of similar prime
factors is Pascadi's *good* case (\(c^{-1/12}\)). That saving still
lives at \(|\mathcal{I}|,|\mathcal{J}|\sim\sqrt{c}\), not at the stall.

**Phase 2 verdict: no-go.** The match is structurally suggestive
(moving CRT \(\to\) Kloosterman of composite modulus) and misses the
admissible *saving* range in the T(3) regime. It does not reach past
\(x^{1/2}\); it reproduces the existing barrier in different notation.

### Phase 3 — MQW and Blomer–Pascadi

**MQW Theorem 1.1** is \(\sum\sum\alpha_m\beta_n\mathrm{Kl}_2(cmn;q)\),
conditions \(M\le Nq^{1/4}\), \(M^{7/5}N<q^{3/2}\), \(MN\le q^{5/4}\).
The kernel is the product-argument (Voronoi) shape, not the
AP-Poisson inverse-linear shape of Phase 1. Even forcing the
identification \(q=Q\), \(MN=x\) needs \(Q\ge x^{4/5}\) to enter
(1.2). Complementary, not a stall tool.

**Blomer–Pascadi Theorem 1.1** is the right kernel \(S(am,n;c)\) and
applies to prime moduli. Both dual intervals must lie under a common
\(N\in(c^{13/28},c^{7/12})\). For balanced Type II this is
\(\delta>13/30\), i.e. \(Q>x^{14/15}\). An unbalanced split can put
\(\max(|\mathcal{I}|,|\mathcal{J}|)\) in the interval-window at smaller
\(\delta\), but then \(\min\ll\max\) and Weil already wins: the
three-term bound of (1.3) exceeds \(\sqrt{|\mathcal{I}||\mathcal{J}|c}\).
The first cell where (1.3) actually beats Weil with balanced duals is
\(\delta\approx 0.37\), \(Q\approx x^{0.87}\). At \(\delta=0\) there is
no bilinear cell at all (lemma above).

Range check: `t3_kloosterman_ranges.py` (exponents in units of
\(\log x\); output `t3_kloosterman_ranges.json`). Stall slice
\(\delta=0\): no bilinear cell (lemma). First genuine Blomer–Pascadi saving
\(\delta\approx 0.367\); first Pascadi 7.1 Weil-beating
\(\delta=0.4\); first MQW (1.2) \(\delta=0.3\) (wrong kernel).

### Phase 4 — k-budget and the named stall

No genuine saving emerges in the T(3) regime \(Q=x^{1/2+}\). A power
saving \(c^{-1/32}\) at \(Q\sim x\) (the two-large-divisors corner,
both \(d_a\sim\sqrt{x}\)) would be a secondary-term improvement of an
error, echoing Fouvry/BFI: past \(\sqrt{x}\) buys a secondary term, not
existence of the main term. The gap \(x^{1/2}<Q<x^{5/6}\) is untouched.
The k-budget invariant is a different object (QED mass versus
\(\log x\)); this look does not move H_ES and does not empty the box.

**What remains.** The sharp question of the previous section is
unchanged: a joint well-factorable weight for the moving CRT residue,
or escape 1. Zheng, the joint \(\delta\)-symbol, and FKMS gallant GKR
are not a third escape; they fail by distinct mechanisms and terminate
at the same varying-modulus correlation
(`erdos-straus-varying-modulus-gap.md`). Per-slice BFI still feeds
almost-certificates.

---


## Defect layer (not in T(3))

For \(a\notin\{1,2,3,6\}\), ClassRough is certificate-union plus a
defect: \(-1\) lies in the subgroup generated by the prime residues
but is not a subset product (`c4_defect_layer.py`). T(3) has no
defect.

---

## What this note does not do

- It does not prove the two-sided T(3) bracket, T(A), or Erdős–Straus.
- It does not ask for an LSD asymptotic.
- It does not densify covering, assault H_ES, or run \(x=10^{10}\).

**Next, in order.** T(A)\(^+\) and E_lane are written
(`erdos-straus-T-A.md`); E_power is written (`erdos-straus-E-power.md`):
the \(\Gamma\)-inflation
is \(\exp(o(\log^2 A))\); expected \(B(A)=O(\log A)\); E_lane is the
\(d=1\) floor, below Vaughan; E_power is the covering-box count, above
Vaughan. The T(3) lower bound follows the three-step plan above. The
\(r_\chi\to\) Kloosterman look is a range no-go at the stall; the sharp
remaining question is still the joint well-factorable CRT residue, in
the same frontier bucket as roadmap §9's Brauer-\(\alpha\) fusion.
A separate two-modulus look (Zheng arXiv:2512.22798) is a range no-go
on \(d_1\approx d_2\approx\sqrt{x}\) (`erdos-straus-T-2.md`); an uneven
Type I leftover still dies on \((0,1/2,1/2)\). A joint δ-method look
(`erdos-straus-T-3-delta.md`) does not avoid the BV-wall identity and
does not bound \(D\) up to \(x\) or \(x^{3/2}\). Joint monodromy
independence (`erdos-straus-T-3-monodromy.md`) does not apply to the
CRT kernel. The four completion looks are one gap: a correlation whose
modulus is jointly growing (`erdos-straus-varying-modulus-gap.md`).
That is not T(3) progress. The analytic worklist remains
`erdos-straus-sieve-desk.md`.
