<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# T(2) via Zheng — range no-go on the symmetric cell

**Riley Betts Erdős–Straus programme, 21 August 2026.**
Companion to `zheng-wellfactorable.md`, `erdos-straus-T-3.md`,
`erdos-straus-E-power.md` (style, not a claim of the same strength).
Primary reference: Zongkun Zheng, *Primes in Simultaneous Arithmetic
Progressions*, arXiv:2512.22798 (28 Dec 2025). Supporting: Bombieri–
Friedlander–Iwaniec, Acta Math. **156** (1986); Deshouillers–Iwaniec,
Invent. Math. **70** (1982/83); Heath-Brown, Invent. Math. **47** (1978);
Grimmelt–Merikoski, arXiv:2404.08502 (Zheng §12.1, independent route).

This file **does not prove** the Erdős–Straus conjecture, does not claim
T(2)\(^+\), and does not claim T(3) progress. It is Part 0 + Part A of a
Zheng look (well-factorability, translation, range check, composition),
plus an A2.3 reroute that leaves one kernel Type I and applies Zheng to
a sub-pair. Part B (three-modulus) is excluded. Not Lean. Do not densify
covering. Do not discharge `AnalyticSurvivorBound`.

**Dies if (A2.2).** The symmetric cell \(d_1\approx d_2\approx\sqrt{x}\)
lies in neither Theorem 1.1 nor Theorem 1.2. The cell
\(d_1\approx d_2\approx x^{1/4}\) is ordinary Bombieri–Vinogradov. Zheng
does not cover the two-modulus switching ceiling.

**Dies if (A2.3).** Leaving one kernel Type I / polylog converts T(3) into
T(2) on the remaining pair. The cell \((0,1/2,1/2)\) is still uncovered:
the pair is the A2.2 ceiling. The switched-plane union BV \(\cup\) Zheng
does not move. Not T(3) progress.

---

## Object

Let \(p\) run over primes in the six hard classes modulo \(840\). The
two-kernel weighted count is
\[
W_2(x)
=\sum_{\substack{p\le x\\ p\text{ hard}}}
r_{\chi_1}(p+4)\,r_{\chi_2}(p+16)
=\sum_{d_1,d_2}\chi_1(d_1)\chi_2(d_2)
\,\#\{p\le x\text{ hard}:p\equiv-4\pmod{d_1},\;p\equiv-16\pmod{d_2}\},
\]
with \(\chi_1\) mod \(4\) and \(\chi_2\) mod \(8\) as in
`oddRealChar_four` / `oddRealChar_eight_*`. After switching each divisor
against \(p+4a^2\sim x\), one has \(d_1,d_2\le\sqrt{x}\). Write
\(d_1\sim x^{\alpha}\), \(d_2\sim x^{\beta}\) with
\((\alpha,\beta)\in[0,1/2]^2\). Ordinary BV covers the CRT modulus
\(\mathrm{lcm}(d_1,d_2)\asymp d_1 d_2\) when \(\alpha+\beta\le 1/2\).

T(2) itself is ClassRough at \(a=1,2\): kernel exactness is
`classRough_iff_chi4` and `classRough_a2_iff_certificates`. A matching
lower bound would need the indicator, or a comparison of \(r_\chi\) to
the indicator. This note tests whether Zheng supplies the two-modulus
mean value for the \(r_\chi\) expansion past BV. It does not, on the
cell that matters.

---

## A1. Translation against Theorem 1.1

Zheng, Theorem 1.1. Let \(\varepsilon>0\) and \(0\le\theta\le 7/36\).
Suppose \(|a_1|\le\log^B x\), \(|a_2|\le x\), \(a_1\neq a_2\). Let
\(\gamma=(\gamma_q)\), \(\lambda=(\lambda_d)\) be divisor-bounded,
supported on \(q\sim x^{\theta}\), \(d\le x^{\mathcal{L}(\theta)-\varepsilon}\),
with \((d,a_1)=(q,a_2)=\mu^2(d)=\mu^2(q)=1\), and \(\lambda\)
well-factorable of level \(x^{\mathcal{L}(\theta)-\varepsilon}\). Then
\[
\sum_{(q,d)=1}\gamma_q\lambda_d
\Bigl(\sum_{\substack{p\le x\\ p\equiv a_1\pmod{d}\\ p\equiv a_2\pmod{q}}}1
-\frac{\pi(x)}{\varphi(qd)}\Bigr)
\ll\frac{x}{\log^A x},
\]
for \(\mathcal{L}(\theta)\) the piecewise function in the paper (reproduced
in `t2_zheng_ranges.py`).

ES substitution, with \(q\leftrightarrow d_2\) and \(d\leftrightarrow d_1\):

| Hypothesis | ES value | Holds? |
|---|---|---|
| \(a_1\neq a_2\) | \(a_1=-4\), \(a_2=-16\) | Yes (his stated case) |
| \(\lvert a_1\rvert\le\log^B x\) | \(\lvert a_1\rvert=4\) | Yes |
| \(\lvert a_2\rvert\le x\) | \(16\) | Yes |
| \(\gamma_q\) divisor-bounded | \(\chi_2(d_2)\) | Yes (`zheng-wellfactorable.md`) |
| \(\lambda_d\) well-factorable of level \(x^{\mathcal{L}-\varepsilon}\) | \(\chi_1(d_1)\) | **Not for free.** Complete multiplicativity transfers well-factorability from an Iwaniec weight onto \(\chi\lambda\); \(\chi\cdot 1_{d\le D}\) is not itself well-factorable of every level (Def. 1.1 is a convolution). |
| \((d,a_1)=(q,a_2)=1\) | coprime to \(4\) and \(16\) | Yes: \(\chi_4,\chi_8\) vanish on evens; matches `gcd_eq_one_of_aligned` |
| \(\mu^2(d)=\mu^2(q)=1\) | squarefree support | **Not in Lean.** Isolate the powerful part by a trivial bound (`zheng-wellfactorable.md` Task 0.2) |
| \(q\sim x^{\theta}\), \(\theta\le 7/36\) | after assigning the shorter leg to \(q\) | Only when \(\min(\alpha,\beta)\le 7/36\) |
| \(d\le x^{\mathcal{L}(\theta)}\) | longer leg | Only when \(\max(\alpha,\beta)\le\mathcal{L}(\theta)\) |

Hard-class restriction is a fixed set of residues modulo \(840\), absorbed
into \(\mathrm{lcm}(d_1,d_2,840)\) at no power of \(x\). Compatibility of
the CRT is \(\gcd(d_1,d_2)\mid 12\), so pairwise gcds are \(O(1)\).

---

## A2. Range check

Theorem 1.1 is asymmetric: \(q\) is locked to a dyadic \(x^{\theta}\) with
\(\theta\le 7/36\approx 0.194\), while \(d\) may run up to
\(x^{\mathcal{L}(\theta)}\), and \(\mathcal{L}(\theta)\le 7/13\approx 0.538\)
only as \(\theta\to 0\). Assign the shorter switched divisor to \(q\).

**Lemma.** At \(\theta=7/36\),
\(\mathcal{L}(\theta)=151/288-9\cdot(7/36)/8=151/288-63/288=88/288=11/36\).
Thus \(\mathcal{L}(7/36)=11/36>7/36=\theta\). On the whole interval,
\(\mathcal{L}\) falls from \(7/13\) to \(11/36\), both strictly larger than
\(7/36\ge\theta\), so \(\theta=\mathcal{L}(\theta)\) never occurs.
(`t2_zheng_ranges.py`, `lemma_L_exceeds_theta_at_endpoint`.)

That does **not** put the switching ceiling into the window. The object
after pairing is the square \([0,1/2]^2\), and the dangerous diagonal is
\(\alpha\approx\beta\approx 1/2\), not \(\alpha\approx\beta\approx\theta\)
for \(\theta\le 7/36\).

Script: `t2_zheng_ranges.py` (grid of \(181^2\) points on the switched
plane; output `t2_zheng_ranges.json`). Fractions of the plane:

| Region | Fraction of \([0,1/2]^2\) |
|---|---|
| Ordinary BV (\(\alpha+\beta\le 1/2\)) | \(0.503\) |
| Zheng Theorem 1.1 | \(0.494\) |
| Zheng 1.1 past BV | \(0.015\) |
| Uncovered by both | \(0.482\) |

**Symmetric cell \(d_1\approx d_2\approx\sqrt{x}\)
(\(\alpha=\beta=1/2\)).** Not BV (product \(x\)). Not Theorem 1.1
(\(\min=1/2>7/36\)). Not Theorem 1.2 (\(q\sim x^{\theta}\) still has
\(\theta\le 2/23\approx 0.087\)).

**Symmetric cell \(d_1\approx d_2\approx x^{1/4}\)
(\(\alpha=\beta=1/4\)).** Ordinary BV (product \(x^{1/2}\)). Not
Theorem 1.1 (\(\min=1/4>7/36\)). Zheng adds nothing new on this cell;
it is the existing barrier in different notation.

Theorem 1.2 is a quadrilinear Type II form (\(mn\sim x\),
\(\beta_n\) Siegel–Walfisz, \(P^-(n)>\log^C x\)), with three cases
\(\theta\le 1/60\), \(\theta\le 1/30\), and \(1/60\le\theta\le 2/23\).
The largest \(d\)-exponent that occurs is \(\mathcal{L}(\theta,\nu)=3/5\)
at \(\theta=0\), \(\nu=1/5\). Complementary for a Heath-Brown remainder,
not a second window on the \((d_1,d_2)\) plane of \(W_2\). It does not
reach \(\sqrt{x}\) in the \(q\)-aspect.

**Uncovered trivial bound.** The uncovered set has harmonic measure about
half the switched plane. On a dyadic cell of exponents \((\alpha,\beta)\)
the pointwise bound is \(\ll x^{\alpha+\beta}+x^{1-\alpha-\beta}\). At
\(\alpha=\beta=1/2\) this is \(\ll x\), which swamps any main term of
size \(x/(\log x)^{1}\) for T(2). Cancellation from \(\chi_1\chi_2\) is
exactly what Zheng would have supplied, and it is not available on that
cell.

Grimmelt–Merikoski (arXiv:2404.08502), as cited in Zheng §12.1, is an
ongoing independent route to the same two-modulus problem, possibly with
a better exponent. It is not a dependency here and was not used as a
substitute window.

---

## A2.3. Uneven switch: Type I leftover, Zheng on a sub-pair

A2.2 forces both legs into \([0,1/2]\) before asking whether
\((\sqrt{x},\sqrt{x})\) sits in Zheng's window. Theorem 1.1 is already
asymmetric (\(q\sim x^{\theta}\), \(\theta\le 7/36\), longer leg up to
\(x^{\mathcal{L}(\theta)}\)). For T(3) nothing forces a 3-way balanced
switch. The reroute is: leave one kernel in a Type I / polylog slot,
assign the shorter of the other two to \(q\), and quote Theorem 1.1 on
that pair. Bookkeeping in `t2_zheng_ranges.py` (`reroute_tables`); output
in `t2_zheng_ranges.json` under `reroute`.

**The 91% figure is the wrong mass.** Plan mass-concentration (“91% of
witnesses have \(a\le\log^2 p\)”; 40/40 hard primes tested have a witness
with \(a,m\le\log^2 p\)) is covering-cell mass, not \(r_\chi\) divisor
mass. Harmonic measure of a polylog Type I slice is \(\asymp\log\log x\)
against \(\tfrac12\log x\) on the switched range. It does not put 91% of
\(W_3\) on the \(\alpha=0\) face. The prime-aligned Euler factor
\(C_{\mathrm{euler}}\approx 0.91\) is a third, unrelated constant.

**Native box, no pairing.** On the unswitched unit square, Theorem 1.1
occupies fraction \(0.127\). The long leg past \(\sqrt{x}\) (up to
\(7/13\)) is fraction \(0.0007\). Pairing sends a long leg in
\((1/2,7/13]\) to a complementary switched divisor in \([6/13,1/2]\);
with a polylog short leg that cell is already BV. Not switching does not
buy a new cell past the A2.2 ceiling.

**T(2) plane.** Union BV \(\cup\) Zheng on \([0,1/2]^2\) is \(0.518\)
with or without a Type I leftover of width \(\varepsilon\in\{0,1/78,1/40,7/36\}\).
The Type I \(\times\) Zheng slab is contained in the existing window.
The \(\sqrt{x}\) cell stays uncovered.

| Leftover \(\varepsilon\) | Type I \(\times\) Zheng | Union BV \(\cup\) Zheng | \(\sqrt{x}\) cell |
|---|---|---|---|
| \(0\) (polylog face) | \(0.011\) | \(0.518\) | no |
| \(1/78\) | \(0.054\) | \(0.518\) | no |
| \(1/40\) | \(0.107\) | \(0.518\) | no |
| \(7/36\) | \(0.494\) | \(0.518\) | no |

**T(3) cube** \([0,1/2]^3\), leftover on any one coordinate, Zheng or
pair-BV on the complementary pair (union of three slabs). Three-modulus
BV is \(\alpha+\beta+\gamma\le 1/2\).

| Leftover \(\varepsilon\) | 3-BV | Zheng slab | any | \((1/2)^3\) | \((0,1/2,1/2)\) |
|---|---|---|---|---|---|
| \(0\) | \(0.180\) | \(0.038\) | \(0.181\) | no | no |
| \(1/40\) | \(0.180\) | \(0.073\) | \(0.184\) | no | no |
| \(7/36\) | \(0.180\) | \(0.306\) | \(0.331\) | no | no |

The cube table *does* shift: at \(\varepsilon=7/36\) the covered fraction
nearly doubles, because a short leftover plus a Zheng pair can have
three-modulus product past \(x^{1/2}\). That is the 1.5% “Zheng past BV”
lifted to a slab. It is not the stall. The cell \((0,1/2,1/2)\) fails
3-BV (sum \(1\)), fails pair-BV (sum \(1\)), and fails Theorem 1.1
(\(\min=1/2>7/36\)). Cor. 11.2 with \(\mathscr{T}=o(1)\) absorbs a
polylog leftover into the well-factorable slot and does not enlarge the
pair window (A3).

**Dies if (A2.3).** An uneven rule converts the ternary count into the
T(2)-via-Zheng setup with a free choice of short leg. The remaining pair
still dies on the A2.2 ceiling. Not T(3) progress, not T(2)\(^+\).

---

## A3. Composition with the sieve architecture

Zheng Corollary 11.2: if \(\rho=(\rho_t)\) is divisor-bounded, supported
on \(t\le x^{\mathscr{T}(\theta)}\), squarefree and coprime to \(da_1\),
and \(\mathscr{T}(\theta)\le\mathcal{L}(\theta)\), then
\(\lambda*\rho\) is well-factorable of the combined level (Fouvry–Grupp
1989, Lemma 5) and Theorem 1.1 still applies provided the *sum*
\(\mathcal{L}+\mathscr{T}\) stays on the same piecewise graph. This is
his Chen-prime application in §11: an extra prime factor \(p_1\) is
recombined into the well-factorable slot.

For T(2) the extra condition \(p\) hard is periodic modulo \(840\). That
is \(\mathscr{T}=0\), so \(\mathscr{T}\le\mathcal{L}\) is vacuous. Lean
`ES.Covering` / `covering_sound` is a growing box of width \(A\), which
is the QED covering architecture, not the two-kernel object. A covering
width \(A=\exp(c\sqrt{\log x})\) would be \(x^{o(1)}\) as a modulus
level, hence still \(\mathscr{T}=o(1)\le\mathcal{L}\) on the cells
Theorem 1.1 already covers — and those cells exclude the symmetric
\(\sqrt{x}\) diagonal. Composition does not enlarge the \((d_1,d_2)\)
window. It is not a repair of A2.

---

## What is not claimed

- T(2)\(^+\): no two-sided bracket and no new upper bound. The Selberg
  upper bound \(S(2,x)\ll(\log x)^{-1}\) is the \(A=2\) case of T(A)\(^+\),
  already written, and does not use Zheng.
- T(3) progress. Three moduli as a genuine Zheng theorem are Part B,
  excluded. The A2.3 reroute (Type I leftover, Zheng on a sub-pair) is
  bookkeeping on Part A and dies on \((0,1/2,1/2)\).
- That \(\chi(d)1_{d\le D}\) is well-factorable of every level.
- Anything in Lean. Gate A still applies before any
  compilation. E_power is a recorded negative, not a compiled count.

**Next.** The two-modulus barrier after switching sits at
\(\min(\alpha,\beta)>7/36\) with \(\alpha+\beta>1/2\), including the
ceiling \(\alpha=\beta=1/2\). An uneven Type I leftover does not move
that barrier. Together with the \(\delta\)-symbol and FKMS looks it is
one of four routes to the same varying-modulus gap
(`erdos-straus-varying-modulus-gap.md`). Escape 1 for T(3)
(almost-certificates, per-slice BFI) is untouched. Do not densify
covering.
