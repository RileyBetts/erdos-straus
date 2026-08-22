<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# T(A) — tracking the selection constant of joint class-roughness

**Riley Betts Erdős–Straus programme, 20 August 2026.**
Working note for the first paper. Companion to candidates C4_1, plan §4v,
`erdos-straus-gs-reformulation.md`. Opening case: `erdos-straus-T-3.md`.
This file **does not prove** the
Erdős–Straus conjecture and does not claim T(A) as a two-sided
theorem. T(A)\(^+\) (fixed \(A\)) is claimed; E_lane is claimed as the
\(d=1\) floor. E_power (`erdos-straus-E-power.md`) is the covering-box
\(x^{1-\delta}\) count, not this note. The \(\Gamma\)-inflation is \(o(\log^2 A)\) as a
theorem; expected \(B(A)=O(\log A)\) by typical \(M(q,a)\).

T(A) is **constant-tracking**: write \(C(A)\) as an explicit sequence in
the covering width \(A\), and decide whether that sequence is
sub-critical against the covering law \(\exp(\kappa\log^2 A)\) with
\(\kappa=0.139\). Proving that \(C(A)\) *exists* for each fixed \(A\)
does not save the schedule.

---

## Statement (conjectural)

Let \(p\) run over primes in the six hard classes modulo 840. Lean
`ClassRough p a` (`ErdosStraus.lean`): \(p+4a^2\) has **no divisor**
\(q\ge 3\) with \(q\equiv -1\pmod{4a}\) — composites included. Write
\[
\rho_a(x)=\mathbb{P}(\mathrm{ClassRough}(p,a)\mid p\le x\text{ hard}),
\qquad
S(A,x)=\mathbb{P}\bigl(\mathrm{ClassRough}(p,a)\text{ for all }1\le a\le A
\bigm| p\le x\text{ hard}\bigr).
\]
**T(A).** For each fixed \(A\ge 1\), trap
\[
c_-(A)\,(\log x)^{-\beta(A)}
\;\le\;
S(A,x)
\;\le\;
c_+(A)\,(\log x)^{-\beta(A)}
\]
with \(c_\pm(A)\) explicit as a sequence in \(A\), equivalently
\(S(A,x)\asymp C(A)\prod_{a=1}^{A}\rho_a(x)\). An asymptotic
\(S=C\prod\rho_a\cdot(1+o(1))\) is stronger than the exposure needs
and is open-hard for kernel-type conditions at primes. The ingredients
are Iwaniec's half-dimensional sieve (vector arrangement) for the
joint ker-character condition, compositum densities for the
shared-modulus layer, and a selection constant — that constant, tracked
in \(A\), is the theorem's content.

**Exposure.** \(\limsup_{A\to\infty}\log C(A)/\log^2 A<\kappa\).
Existence of \(C(A)\) at each fixed \(A\) is not the exposure.

---

## Certificate architecture

ClassRough is composite-inclusive because the witness cofactor makes a
composite aligned divisor land a prime too: the kernel definition is
the faithful one. The analytic structure that definition carries is a
**certificate**.

A real odd character \(\chi\) mod \(4a\) *certifies* \(N=p+4a^2\) if
every prime factor of \(N\) coprime to \(4a\) lies in \(\ker\chi\).
Complete multiplicativity then forbids every divisor \(\equiv-1\pmod{4a}\),
since such a divisor is coprime to \(4a\) and would have
\(\chi=-1=\chi(-1)\). This direction is now kernel:

`classRough_of_certifies` in `ErdosStraus.lean` (`OddRealChar`).
It welds the character strand (`survivor_legendre_three` in Layer B)
to the roughness core. The structure is inhabited at \(a=1\) by
`oddRealChar_four` (\(\chi_4\), `classRough_of_chi4`): ClassRough of
\(p+4\) is 3-mod-4-freeness of its odd prime factors.

The converse — ClassRough implies some certificate — is **not** a
theorem. It is now a measurement (`c4_certificates.py`), not a
claimed-theorem figure. At \(x=10^6\), \(A\le 40\) (2{,}370 hard primes,
94{,}800 slots):

- certificate \(\Rightarrow\) ClassRough is exact in the data
  (0 reverse mismatches), as the lemma requires;
- \(P(\exists\chi\mid\mathrm{ClassRough})=0.846\), not 98–100%;
- the gap is one-directional (rough without certificate) and
  grows with \(\omega(N)\) among primes coprime to \(4a\):
  \(\omega=1\) is 100%, \(\omega=2\) is 90%, \(\omega=3\) is 66%,
  \(\omega=4\) is 35%. Exact at \(a=1,2,3,6\) (\(\lambda(4a)\mid 2\));
  the gap opens at \(a=4\).

At \(a=1,2,3\) the converse is now a theorem, not a measurement:
`classRough_iff_chi4`, `classRough_a2_iff_certificates`,
`classRough_a3_iff_certificates`, and the joint
`classRough_123_iff_certificates` in `ErdosStraus.lean`. An aligned
divisor is \(-1\) in \((\mathbb{Z}/4a\mathbb{Z})^*\); for \(a=2\) that
is a \(7\)-prime or a \(3\times 5\) product, for \(a=3\) an \(11\)-prime
or a \(5\times 7\) product, and in both cases the group is elementary
abelian \(2\), so ClassRough is exactly a finite union of kernels.
This is the T(3) kernel. It is not the Wirsing asymptotic.

T(A)'s proof architecture, once the converse is granted as a main-term
identification: \(S(A,x)\) is an inclusion–exclusion over certificate
assignments \((\chi_a)_{a\le A}\), each term a multi-shift semi-linear
vector-sieve problem of the classical type “all prime factors of shifted
values lie in prescribed index-2 subgroups.” Hooley, JNT **5** (1973),
is T(2) of this decomposition on \(\mathbb{Z}\); Iwaniec, Acta Arith.
**29** (1976), is the sieve; Nath–Xie 2025 is the vector arrangement.
The 15% uncertified roughness at this \(x\) is a main-term error if one
replaces ClassRough by the union of certificates for general \(A\);
at \(A=3\) there is no such error. An LSD asymptotic is more than the
programme needs.

The G–S memo then has its exact object: mean values of character-kernel
multiplicative indicators.

**Shared certificates as dummy covering.** On the 154 primes that
survive \(a\le 10\), later ClassRough is already \(\approx 0.95\)–\(0.98\)
(cond near 1). Inherited certificates from divisors \(a'\mid a\) with
\(a'\le 10\) cover only \(\approx 0.73\) of those primes on average;
\(\chi_4\) alone covers \(\approx 0.65\). The leftover is a mix of
*new* characters and uncertified roughness, not the same \(\chi\)
working again. Shared-certificate dummy covering **does not fire**.
\(\mathrm{cond}\to 1\) remains the large-modulus rarity of an aligned
divisor, not inheritance. Do not densify covering.

**Predicted formula for \(C(A)\).** If leftover selection were the raw
union-count inflation \(\prod_a n_\chi(a)\), then \(\log\hat C\) would
track \(\sum_{a\le A}\log n_\chi(a)\sim A\), not \(\log^2 A\). The
global partition function of consistent assignments \((\chi_a)\) along
the divisibility poset is a single Kronecker character of
\((\mathbb{Z}/4\mathrm{lcm}[1..A]\mathbb{Z})^*\). Oddness constraints
are vacuous: \(p\mid a\) implies \((p/(4a-1))=+1\) by reciprocity, so
the GF(2) rank is 0 and \(Z_{\mathrm{global}}(A)=2^{1+\pi_{\mathrm{odd}}(A)}\)
for \(A\ge 2\). At \(x=10^9\), \(A\ge 40\):

| predictor | OLS vs \(\log\hat C\) | \(R^2\) |
|---|---|---|
| \(\log^2 A\) | \(c'=0.104\) | **0.998** |
| \(\sum\log n_\chi/a\) | slope \(0.719\) | 0.996 |
| \(\log Z_{\mathrm{global}}\) | slope \(0.065\) | 0.986 |
| \(\sum\log n_\chi\) | slope \(0.0066\) | 0.976 |

\(\log Z_{\mathrm{global}}\sim\pi(A)\log 2\) is 32 at \(A=200\) against
\(\log\hat C=1.93\): right smoothness, wrong scale. The Mertens weight
\(\sum\log n_\chi/a\) is in the same ballpark as \(\log\hat C\) but the
ratio drifts \(0.15\to 0.38\) from \(A=40\) to \(200\), so it is not a
constant multiple. \(\log^2 A\) remains the fit; the constant's formula
is open. Do not treat \(\prod n_\chi\) or \(Z_{\mathrm{global}}\) as
\(C(A)\). The partition-function prediction was tested at three levels
and is the wrong scale at all of them.

---

## T(3) kernel (proved), T(3)\(^+\) (claimed), bracket (not)

`classRough_123_iff_certificates`: ClassRough on \(a=1,2,3\) is
exactly the \(1\times 2\times 2\) union of certificate assignments.
Characters: \(\chi_4\) at \(a=1\) (ker \(\{1\}\bmod 4\)); \(\chi_4\)
and \(\chi_4\chi_8\) at \(a=2\) (kers \(\{1,5\}\) and \(\{1,3\}\bmod 8\));
\(\chi_4\) and \(\chi_4\chi_3\) at \(a=3\) (kers \(\{1,5\}\) and
\(\{1,7\}\bmod 12\)). At \(x=10^6\), 2{,}370 hard primes: 656 ClassRough
on all three slices, 656 certificate-union, **match**. Occupancy of the
four assignments is 478 / 239 / 267 / 282 (they overlap; mean \(\approx 1.93\)
certificates per survivor).

This is the elementary exactness that makes T(3) a three-component
semi-linear vector sieve. **T(3)\(^+\) is claimed:**
\(S(3,x)\ll(\log x)^{-3/2}\) by a dimension-\(3/2\) Selberg sieve on
hard primes, with Bombieri–Vinogradov remainders at \(z=x^{1/4-}\)
(`erdos-straus-T-3.md`). **T(1) is claimed by citation:** ClassRough at
\(a=1\) is \(\chi_4\), hence \(p=x^2+y^2-4\), and Iwaniec, Acta Arith.
**24**, plus Fuchs et al., give \(S(1,x)\asymp(\log x)^{-1/2}\).
The two-sided T(3) bracket is **not** claimed: the matching lower bound
follows a three-step plan (Iwaniec per slice; Brüdern–Fouvry; completion
of \(q>x^{1/2}\)), with a named stall at (c) (`erdos-straus-T-3.md`).
Calibrated against
\(\hat C(3)\approx 0.975\) at \(x=10^9\) (\(S\approx 0.169\),
\(n_{\mathrm{alive}}=268{,}409\)) and \(\hat C(3)\approx 0.960\) at
\(x=10^6\). At this \(x\), \(\rho_1\approx 0.50\) still looks like a
coin-flip (\(\sqrt{\log x}\approx 4.5\); it was \(0.59\) at \(10^6\));
the log-power is the sieve main term.

Certificate Euler products (`c4_t3_euler.py`, \(q\le 10^6\)): the local
selection constant of each assignment (joint / product of three
ker-marginals) is \(O(1)\),

| assignment | \(C\) | \(C_{1/q}\) |
|---|---:|---:|
| \(\chi_4,\chi_4,\chi_4\) | 1.609 | 1.280 |
| \(\chi_4,\chi_4,\chi_4\chi_3\) | 1.811 | 1.388 |
| \(\chi_4,\chi_4\chi_8,\chi_4\) | 0.836 | 0.882 |
| \(\chi_4,\chi_4\chi_8,\chi_4\chi_3\) | 1.246 | 1.187 |

These are not \(\hat C(3)\): the four events overlap and the sieve
dimensions add. They are the Euler layer the analysis has to
evaluate, and they sit in the same \(O(1)\) window as the measured
\(\hat C(3)\approx 0.97\). Compute now evaluates this layer, not
another \(x\)-scan. Do not run \(x=10^{10}\).

---

## Defect layer (\(a\ge 4\))

Squarefree model: \(\omega\) residues in \(G=(\mathbb{Z}/4a\mathbb{Z})^*\).
ClassRough = no nonempty subset product \(\equiv-1\). Certificate =
\(-1\notin\langle\text{residues}\rangle\). These coincide iff \(G\) is
an elementary \(2\)-group, i.e. \(\lambda(4a)\mid 2\), which holds
exactly for \(a\in\{1,2,3,6\}\). Measured converse is exact on those
four slices (including \(a=6\), not only \(1,2,3\)) and opens at
\(a=4\).

The defect is combinatorial: \(-1\) lies in the subgroup generated by
the prime residues but is not a subset product. First appearance
\(a=4\), \(\omega=2\): uniform model gives \(P(\mathrm{CR})=0.672\),
\(P(\chi)=0.484\), defect \(0.188\). Certificate still decays as
\(2^{-\omega}\) per character; the defect is smaller mass with its own
(smaller) exponent. Uniform-\(a\) pooling does **not** reproduce the
measured \(100/90/66/35\) rates — those mix the class distribution of
real factors, not Haar measure on \(G\) — but the exactness locus and
the \(\omega\)-direction are derived, not fitted (`c4_defect_layer.py`).
Do not treat the \(\omega\)-gap as a reason that T(3) is approximate:
T(3) has no defect layer.

---

## What the scans already force on the introduction

Two measurements, both at the same hard-prime population
(\(1{,}587{,}581\) primes, \(x=10^9\)).

**In \(x\), at fixed \(A\in\{40,80\}\)** (`c4_S_xscan.py`).
\(\log S\) vs \(\ln\ln x\) is a straight line (\(R^2=0.997\) on
\(x\ge 10^6\)). The slope ratio \(\beta_S/\beta_{\prod\rho}=0.868\) at
both \(A\). Mean\((e(a)-1)\) for \(a=10..80\) rises
\(0.0094\to 0.0168\) from \(x=10^6\) to \(x=10^9\); it is not a
Mertens shadow of size \(1/\ln\ln x\). \(\hat C(80)\) rises
\(1.57\to 2.69\). Do not run \(x=10^{10}\).

**In \(A\), at fixed \(x=10^9\)** (`c4_growing_A.py`, \(A\le 200\)).
Two facts, not one:

- \(\mathrm{cond}(a)=P(R_a\mid R_1,\ldots,R_{a-1})\to 1\): \(0.995\) at
  \(a=80\), mean \(0.993\) on \(a=161..200\). Retention \(80\to 200\) is
  \(0.275\) against \(\prod_{81}^{200}\rho_a=0.107\). Extra \(d=1\)
  slices are mostly dummy covering mass.
- \(\log\hat C\sim 0.104\,\log^2 A\) on \(A\ge 40\) (\(R^2=0.998\)),
  against \(\kappa=0.139\). Local \(\log\hat C/A\approx 0.012\) on
  \(A\le 80\) was a small-\(A\) artefact; \(\hat C(200)=6.92\),
  \(\log\hat C/A=0.0097\). Sub-critical, thin
  (\(\kappa_{\mathrm{eff}}\approx 0.035\)). The box is not empty
  (\(155\) survivors); \(S(200)\approx 9.8\times 10^{-5}\) against a
  QED-scale target \(\lesssim 6\times 10^{-7}\) at this \(x\).

Pair ratios \(\rho_{ab}/(\rho_a\rho_b)=1.000\) out to \(A=120\) remain a
**lemma**, not the theorem (`c4_two_shift_probe.py`).

**The two partials of \(\log S\), fitted from the JSON dumps**
(`c4_surface_fit.py`). The x-slope deficit at \(A=80\) is \(13.2\%\) of
\(\beta_{\prod\rho}\) (\(\kappa_{\mathrm{eff}}\approx 0.121\)). The
A-curvature at \(x=10^9\) is \(c'=0.104\) on \(A\ge 40\)
(\(\kappa_{\mathrm{eff}}\approx 0.035\)). They are different derivatives.
Reconstructing \(\hat C(A,x)\) on the x-scan grid (\(A=40..80\)):

| \(x\) | \(c'(x)\) | \(R^2\) | \(\hat C(80)\) |
|------:|----------:|--------:|---------------:|
| \(10^6\) | 0.063 | 0.92 | 1.57 |
| \(10^8\) | 0.076 | 0.99 | 2.23 |
| \(10^9\) | 0.094 | 0.99 | 2.69 |

So \(c'(x)\) is **still growing** on the window we have. OLS of \(c'\)
against \(\ln\ln x\) (\(x\ge 10^6\)) has slope \(+0.052\) and only
\(R^2=0.65\). A linear hit of \(\kappa\) would sit near \(x\sim 10^{24}\);
that extrapolation is not a theorem and is not a reason to run
\(10^{10}\). Measurement has saturated: further scans refine constants
inside the same window without touching \(c'(\infty)\). The kill branch
\(c'(x)\to\kappa\) is **watchable** and **not fired**. Until \(c'(\infty)\)
is known, the comfortable x-reading
\(\kappa_{\mathrm{eff}}\approx 0.12\) is the partial at fixed \(A\),
and the steep A-reading \(0.035\) is a snapshot at \(x=10^9\). Dummy
covering remains the live schedule risk at this \(x\). The remaining
access to \(c'(\infty)\) is the Euler layer of the certificate
expansion, not a larger scan.

Convention: \(\sum_{a\le A}1/\varphi(4a)\) (\(2.53\) at \(A=40\),
\(2.97\) at \(A=80\)) is the Mertens exponent for the **prime-aligned**
condition only. A prime-only control matches it to \(15\)–\(18\%\).
ClassRough's composite layer is the \(2.7\)–\(3.0\) factor. The slope
ratio \(0.86\) compares two ClassRough quantities.

---

## The local Euler factor is \(0.91\), and it is not \(C(A)\)

Per prime \(q\equiv 3\pmod{4}\), the slices \(q\) can kill are the
divisors \(a\le A\) of \((q+1)/4\). Slice \(a\) forbids
\(p\equiv -4a^2\pmod{q}\). Write \(m_q\) for the number of such slices
and \(k_q\) for the number of distinct forbidden residues. The
prime-aligned joint/product Euler factor is
\[
C_{\mathrm{euler}}(A)
=\prod_{q}
\frac{1-k_q/(q-1)}{\bigl(1-1/(q-1)\bigr)^{m_q}}.
\]
Union and sum of \(1/q\) agree at exponent level (distinct residues
cost \(m_q/q\) either way); the discrepancy is the quadratic Euler
term \(O(m_q^2/q^2)\).

**Computed** (`c4_euler_factor.py`, primes \(q\le 10^7\), \(A\le 200\)):

| \(A\) | \(C_{\mathrm{euler}}\) (\(1/(q-1)\)) | \(C_{\mathrm{euler}}\) (\(1/q\)) |
|------:|-------------------------------------:|--------------------------------:|
| 40    | 0.8977 | 0.9140 |
| 80    | 0.8950 | 0.9113 |
| 200   | 0.8935 | 0.9097 |

The \(1/q\) column is the comparison value \(\approx 0.91\). The product is
**flat**: from \(A=40\) to \(A=200\) it moves \(0.004\). Almost all of
it sits in \(q<840\) (\(0.899\) of \(0.898\) at \(A=40\)); the tail
\(q\ge 840\) is \(0.9987\to 0.9973\). Truncation past \(10^7\) is
smaller still.

**Residue collisions.** \(k_q<m_q\) requires \(q\mid(a^2-b^2)\) for
some \(1\le a<b\le A\), hence \(q\le A^2\). Exhaustive factorisation of
every \(a^2-b^2\) for \(A=200\) finds **no** prime \(q\equiv 3\pmod{4}\)
that serves two slices with the same residue (`collision_check` in
`c4_euler_factor.py`; empty list). So for \(A\le 200\),
\(k_q=m_q\) identically, and \(C_{\mathrm{euler}}\) is exactly the
quadratic-overlap product with no residue-identification correction.

This factor **cannot** be the source of \(\hat C\sim\exp(0.104\log^2 A)\).
It is a constant \(\approx 0.89\)–\(0.91\) that has finished moving by
\(A=40\). T(A)'s selection constant is whatever remains after this
Euler product is divided out of the prime-aligned joint. The totient
mismatch lives in the ClassRough *marginals* \(\rho_a\), computed next.

Hard-class conditioning modulo \(840\) does not change the picture at
the only ramified primes that can serve a slice: \(q=3\) contributes
ratio \(1\); \(q=7\) has generic ratio \(0.96\) and exact hard-class
ratio \(1\). (\(q=5\equiv 1\pmod{4}\) never serves.)

---

## The 2.7–3.0 totient mismatch is \(\Pi_{\mathrm{gen}}(\sqrt{x})\), not a new Dirichlet density

A composite \(q\equiv -1\pmod{4a}\) is *genuine extra* when none of its
prime factors is itself \(\equiv -1\pmod{4a}\) (otherwise prime-aligned
already forbids it). Example: \(35=5\cdot 7\equiv -1\pmod{12}\); neither
factor is \(\equiv 11\pmod{12}\). For \(a=1\) (\(m=4\)) the genuine-extra
set is empty: every composite \(\equiv 3\pmod{4}\) has a prime factor
\(\equiv 3\pmod{4}\). Write
\[
\Pi_{\mathrm{gen}}(a,Z)
=\prod\bigl(1-1/q\bigr)
\]
over genuine-extra \(q\le Z\) (`c4_composite_layer.py`). Among values
\(N=p+4a^2\) of size \(x\), proper divisors run up to \(\sqrt{x}\).

Measured \(\rho_a^{\mathrm{CR}}/\rho_a^{\mathrm{prime}}\) at \(x=10^9\)
against \(\Pi_{\mathrm{gen}}(a,\sqrt{x})\):

- \(a=1\): both \(1.000\).
- \(a\ge 20\): per-slice match to \(\le 1\%\) (e.g. \(a=30\): \(0.9741\) vs
  \(0.9740\); \(a=80\): \(0.9861\) vs \(0.9876\)).
- Product \(A=40\): emp\(/\Pi = 1.005\), \(1.002\), \(1.033\) at
  \(x=10^6,10^8,10^9\) (cutoff \(\sqrt{x}=10^3,10^4,3\cdot 10^4\)).
- Product \(A=80\): emp\(/\Pi = 0.76\to 0.58\). Independent Euler
  under-kills \(a=40..80\), where \(4a^2\sim\sqrt{x}\); not a reason to
  drop the identification at \(A=40\).

The naive product over *all* aligned composites over-kills \(a=1\)
(\(0.27\) against \(1.00\)) by double-counting aligned primes. Genuine
extra is the correction.

The apparent extra Mertens exponent \(\beta_{\mathrm{CR}}-\beta_{\mathrm{prime}}\)
(\(4.13\) at \(A=40\), \(5.90\) at \(A=80\)) is the OLS slope of
\(\log\Pi_{\mathrm{gen}}(\sqrt{x})\) against \(\ln\ln x\) on a window
where \(\log x\) and \(\ln\ln x\) are collinear (\(R^2=0.997\)). It is
not a new Dirichlet density \(c/\varphi(4a)\). As \(x\to\infty\) at
fixed \(A\), more genuine extras enter and the CR/prime ratio is not a
constant; T(A) already folds that \(x\)-dependence into \(\rho_a(x)\).
The totient mismatch is a fact about the *marginals*, not about
\(\hat C=S/\prod\rho_a\).

---

## What the vector sieve still has to do

The local prime-union calculation predicts
\[
S^{\mathrm{prime}}(A,x)
\sim C_{\mathrm{euler}}(A)\,
\prod_{a\le A}\rho_a^{\mathrm{prime}}(x),
\]
with \(C_{\mathrm{euler}}(A)\to C_{\mathrm{euler}}(\infty)\approx 0.89\),
no exponent haircut. ClassRough marginals are that times
\(\Pi_{\mathrm{gen}}(a,\sqrt{x})\) (matched at \(A=40\)). Transfer to
primes in the hard classes, a joint error term, and the *selection*
constants \(c_\pm(A)\) in a two-sided bound for \(S\) remain the
analysis. \(\hat C(200)=6.92\),
\(\mathrm{cond}(a)\to 1\), and \(\log\hat C\) tracks \(\log^2 A\): that
is still not \(C_{\mathrm{euler}}\) and not \(\Pi_{\mathrm{gen}}\).

A paper that only produces \(C_{\mathrm{euler}}(A)\) has tracked the
wrong constant. The constant that has to be tracked is the ClassRough
selection sequence whose empirical shadow is \(\hat C(A)\) at
\(x=10^9\). A bracket with those constants explicit answers the
exposure; an LSD asymptotic at each fixed \(A\) does not.

**Literature, the shelf for T(3).** T(3)\(^+\) is Selberg of dimension
\(3/2\) (Halberstam–Richert; Friedlander–Iwaniec, *Opera de Cribro*).
T(1) is Iwaniec, Acta Arith. **24** (1973/74), plus Fuchs et al.,
arXiv:2504.20289. The lower-bound plan is Iwaniec, Acta Arith. **29**
(1976), combined by Brüdern–Fouvry (Compositio Math. **102** (1996);
J. Reine Angew. Math. **454** (1994)); Nath–Xie, arXiv:2501.16723, is
the two-component template. Completion of \(q>x^{1/2}\) is the named
risk; the \(r_\chi\)-weighted escape is Linnik, Izv. Akad. Nauk **24**
(1960). Details: `erdos-straus-T-3.md`.

---

## T(A)\(^+\) — uniform Selberg (fixed \(A\) immediate; growing \(A\) needs FL)

The T(3)\(^+\) argument generalizes to any *fixed* covering width \(A\).
This is E_partial's true vehicle (`erdos-straus-E-partial.md`).
Computation: `c4_sieve_constant.py`.

The sieve bounds the **aligned-prime** condition: \(p+4a^2\) has no prime
factor \(q\equiv-1\pmod{4a}\). That is a *necessary* condition for
`ClassRough` (no divisor \(q\ge 3\) with \(q\equiv-1\pmod{4a}\),
composites included). An upper bound on a weaker predicate is a valid
upper bound on ClassRough; the write-up records this explicitly.

**Theorem T(A)\(^+\) (fixed \(A\); claimed).** For each fixed \(A\ge 1\),
write \(S^{\mathrm{align}}(A,x)\) for the probability that a hard prime
\(p\le x\) has no prime \(q\equiv-1\pmod{4a}\) dividing \(p+4a^2\) for
any \(a\le A\). Then \(S(A,x)\le S^{\mathrm{align}}(A,x)\) (ClassRough
is the stronger predicate), and
\[
S^{\mathrm{align}}(A,x)
\;\ll\;
C_{\mathrm{sieve}}(A)\,(\log x)^{-\beta(A)}\qquad(x\to\infty),
\]
hence the same bound for \(S(A,x)\). Here
\(\beta(A)=\sum_{a\le A}1/\varphi(4a)\) is the joint Mertens
dimension of the aligned-prime sieve (\(k_q=\) number of distinct
residues \(-4a^2\bmod q\) over \(a\le A\) with \(q\equiv-1\pmod{4a}\);
residue collisions only decrease \(k_q\), and there are none for
\(A\le 200\)), and
\[
C_{\mathrm{sieve}}(A)
\;=\;
\Gamma\bigl(\beta(A)+1\bigr)\,
\exp\bigl(\gamma\beta(A)-B(A)\bigr).
\]
Here \(B(A)=\lim_{Q\to\infty}\bigl(\sum_{q<Q}k_q/q-\beta(A)\log\log Q\bigr)\)
is the Mertens-constant sum of the sifting set, defined via late-start
Mertens (each slice \(a\) sees primes \(\gtrsim 4a\)). This is the
textbook dimension-\(\beta\) Selberg constant. Proof of the shape:
Selberg at \(z=x^{1/4}(\log x)^{-B}\) with Bombieri–Vinogradov
remainders at level \(z^2=x^{1/2-}\) (Halberstam–Richert, Thm. 5.1;
the \(A=3\) case is T(3)\(^+\)). On the exactness locus
\(\{1,2,3,6\}\) a certificate kernel may replace the aligned-prime
condition and can only improve the exponent.

Fixed \(A\) is immediate from T(3)\(^+\)'s argument and is claimed.
Using T(A)\(^+\) at *growing* \(A=A(x)\) requires a uniformity-in-\(A\)
lemma: the dimension-uniform fundamental lemma (Halberstam–Richert,
*Sieve Methods*, Ch. 2; Friedlander–Iwaniec, *Opera de Cribro*, the
fundamental lemma in the dimension-uniform form). That citation does
the real work in E_lane, below. “Claimed in shape” is the working
language until that lemma is written out; the paper writes it before
the bound is used at growing \(A\).

**Dimension.** \(\beta(A)\sim c_\varphi\log A\) with
\(c_\varphi=\lim\beta(A)/\log A\). Computed: \(c_\varphi\) decreases
\(0.686\) at \(A=40\) to \(0.659\) at \(A=10^5\). Unconditionally
\(\varphi(n)\gg n/\log\log n\), so \(\beta(A)\ll\log A\cdot\log\log A\).

**The \(\Gamma\)-inflation is \(o(\log^2 A)\), as a theorem.** Stirling:
\(\log\Gamma(\beta+1)=\beta\log\beta-\beta+O(\log\beta)\). With
\(\beta=O(\log A\log\log A)\) this is \(O(\log A\,(\log\log A)^2)
=o(\log^2 A)\). The factor \(e^{\gamma\beta}\) is \(O(\log A)\), also
\(o(\log^2 A)\). A naive stack of \(A\) independent \(\kappa=1/2\)
certificates would have given \(\beta\sim A/2\) and
\(\exp(\Theta(A\log A))\), a worthless bound; the aligned-prime
structure — the certificate architecture and the divisor structure of
the witness moduli — keeps the dimension logarithmic in \(A\). That is
the section's structural payoff in a provable constant.

**Selberg does not re-create the covering law.** The schedule's
upper-bound half survives unconditionally at the combinatorial
constant. If \(c'(\infty)\to\kappa\), the saturation cannot come from
the joint sieve constant; it would have to live in the marginals' own
structure. Dummy covering (\(\mathrm{cond}\equiv 1\)) remains the live
kill of a retuned QED schedule.

**\(B(A)\), with a citation.** Late-start Mertens
(each slice \(a\) sees primes \(\gtrsim 4a\)) at \(Q=10^6\) and
\(Q=10^7\) agree to three decimals:

| \(A\) | \(\beta\) | \(B(A)\) | \(\log C_{\mathrm{sieve}}\) | \(\log C/\log^2 A\) | \(\log\Gamma/\log^2 A\) |
|------:|----------:|---------:|----------------------------:|---------------------:|------------------------:|
| 3 | 1.000 | 0.322 | 0.255 | 0.212 | 0 |
| 40 | 2.531 | 0.425 | 2.271 | 0.167 | 0.091 |
| 80 | 2.974 | 0.443 | 3.033 | 0.158 | 0.092 |
| 200 | 3.564 | 0.465 | 4.135 | 0.147 | 0.091 |
| \(10^5\) | 7.588 | — | — | — | 0.073 |

OLS on \(A\ge 40\) against \(\log^2 A\): \(B(A)\) has slope \(0.0026\)
(\(R^2=0.95\)); \(\log\Gamma\) has slope \(0.090\) (\(R^2=0.9998\)),
and that ratio is already falling at \(A=10^5\). A raw OLS of
\(\log C_{\mathrm{sieve}}\) on the same window has slope \(0.128\),
next to \(\kappa=0.139\): that is the finite-\(Q\) artefact — the
late-start deficit \(\sum_a\log\log(4a)/\varphi(4a)\sim\log A\log\log A\)
masquerading as cap-scale growth — not cap-scale growth.

\(B(A)=\sum_{a\le A}M(4a,-1)\) with \(M(q,a)\) the Mertens constant in
the progression \(p\equiv a\pmod{q}\). Norton, Illinois J. Math.
**20** (1976), Lemma 6.3 (cf. Languasco–Zaccagnini, J. Number Theory
**127** (2007)) gives \(M(q,a)=\delta_a/a+O((\log q)/\varphi(q))\).
Summing the error term in the worst case is \(O(\log^2 A)\); that is
not the expected size. The typical size of \(L(1,\chi)\) in the
Granville–Soundararajan circle (Geom. Funct. Anal. **13** (2003))
makes \(M(q,a)\ll 1/\varphi(q)\) in the mean, hence
\(B(A)=O(\log A)\). Nothing at \(A\le 200\) supports cap-scale growth
of \(B\), and the expected size is \(O(\log A)\).

The k-budget question of plan §4l is this ratio, as a provable object:
\[
\hat C(A,x)
\;=\;
\frac{S(A,x)}{\prod\rho_a}
\;\ll\;
\frac{C_{\mathrm{sieve}}(A)}{c_{\mathrm{marg}}(A)}.
\]
Measured \(c'=0.104\) at \(x=10^9\), \(A\le 200\), is an upper shadow
at finite \(x\); T(A)\(^+\) says the \(x\to\infty\) implied constant
cannot grow as \(\exp(\Theta(\log^2 A))\) from Selberg weights alone.

**Not claimed here:** a two-sided T(A) bracket, occupancy of \(C_+\),
or Erdős–Straus. Fixed-\(A\) T(A)\(^+\) is claimed; E_lane below uses
the uniformity lemma. Neither is Lean; neither discharges
`AnalyticSurvivorBound`.

---

## E_lane — the \(d=1\) floor (claimed)

T(A)\(^+\) is one uniformity lemma from a standalone exceptional-set
theorem. The main term is \(C_{\mathrm{sieve}}(A)\,(\log x)^{-\beta(A)}\);
Stirling converts this to net exponent
\[
\beta(A)\bigl(\log\log x-\log\beta(A)+O(1)\bigr).
\]
The \(\Gamma\)-term eats exactly \(\log\beta\) of the Mertens saving.
The dimension-uniform fundamental lemma at distribution level
\(x^{1/2}\) constrains \(\beta\log z\lesssim\log x\). Maximizing under
that constraint, with every slice visible (\(z\gtrsim 4A\)), puts the
optimum at
\[
A=\exp\bigl(c\sqrt{\log x}\bigr),\qquad \beta\asymp\sqrt{\log x},
\]
for a sufficiently small effective \(c>0\).

**Lemma (uniformity in \(A\); written as FL).**
Halberstam–Richert, *Sieve Methods*; Friedlander–Iwaniec, *Opera de
Cribro*, the fundamental lemma in the dimension-uniform form: the
Selberg main term and Bombieri–Vinogradov remainders of T(A)\(^+\)
remain valid uniformly for \(A\le\exp(c\sqrt{\log x})\), with
effective implied constants. Fixed \(A\) does not need this; growing
\(A\) does. This is the one written lemma between T(A)\(^+\) and
E_lane.

**Theorem E_lane (claimed).** There exist effective constants
\(c,c'>0\) such that the number of hard primes \(p\le x\) with no
aligned prime factor of \(p+4a^2\) for any \(a\le A(x):=\exp(c\sqrt{\log x})\)
satisfies
\[
E_{\mathrm{lane}}(x)
\;\ll\;
x\exp\bigl(-c'\sqrt{\log x}\,\log\log x\bigr).
\]
The implied constant is effective. Because aligned primes are necessary
for ClassRough, this upper-bounds the number of hard primes that escape
the \(d=1\) covering lane at that width.

Proof sketch. Uniform T(A)\(^+\) at this \(A(x)\) gives
\(S\ll\exp\bigl(-\beta(\log\log x-\log\beta+O(1))\bigr)\). Then
\(E_{\mathrm{lane}}\ll\pi_{\mathrm{hard}}(x)\,S\) with
\(\pi_{\mathrm{hard}}(x)\sim x/(32\log x)\) and
\(\beta\sim c_\varphi c\sqrt{\log x}\), so
\(\log\beta=\tfrac12\log\log x+O(1)\) and the net saving is
\(\tfrac12 c_\varphi c\,\sqrt{\log x}\,\log\log x+O(\sqrt{\log x})\).
Choose \(c\) small enough for the uniformity lemma; \(c'\) follows.

**Honest comparison.** Vaughan, Mathematika **17** (1970), 193–198:
the number of \(n\le x\) for which \(4/n\) is not a sum of three unit
fractions is \(\ll x\exp\bigl(-c(\log x)^{2/3}\bigr)\). That counts
*all* \(n\le x\) failing Erdős–Straus. E_lane counts *hard primes*
escaping the \(d=1\) *aligned-prime* condition at width \(A(x)\). The
objects differ; the comparison is of exponents. E_lane sits *below*
Vaughan (a weaker exceptional-set estimate), because the \(d=1\) lane
carries only \(\log A\) mass where the full covering box carries
\(\log^2 A\). E_lane is the provable floor, with effective constants,
and is publishable as such. The full-box record is E_power
(`erdos-straus-E-power.md`), claimed there: covering-congruence
survivors among all integers, \(S_A\ll x^{1-\delta}\). Not this
theorem.

---

## Dummy slices

If \(\mathrm{cond}(a)\equiv 1\) persists to QED-scale \(A\), extra
factors in \(\prod\rho_a\) are fictitious covering mass: the joint no
longer pays them. Further multiplicative statistics are then those of a
**conditioned** subset (a selected pretentious tail), not of
\(\sim\log^2 A\) weakly dependent free characters. The G–S dictionary
(`erdos-straus-gs-reformulation.md`) attaches to that conditioned
object, not to the covering product.

---

## What this note does not do

- It does not prove T(A) as a two-sided bracket, H_ES, or occupancy of \(C_+\).
- It does not claim Vaughan's bound, nor E_power. E_lane is the \(d=1\)
  floor, below Vaughan. The covering-box \(x^{1-\delta}\) is
  `erdos-straus-E-power.md`.
- It does not prove a limit theorem for \(B(A)\) as \(A\to\infty\).
  The expected size is \(O(\log A)\) (Norton; Granville–Soundararajan
  typical \(L(1,\chi)\)).
- It does not retune \(\kappa\) as if the prime-aligned Euler product
  were the theorem.
- It does not revive the pair asymptotic as the first theorem.
- It does not densify covering, assault the full level statement, or
  run \(x=10^{10}\).

**Dies if** \(c'\ge\kappa\) uniformly in \(A\), or if
\(\mathrm{cond}\equiv 1\) makes extra covering fictitious at
QED-scale \(A\). Growing \(A\) to \(200\) gave \(c'=0.104<\kappa\) and
\(\mathrm{cond}\approx 1\). Not a completed kill; the margin is thin.

**Measurement has saturated.** \(c'(x)\) is still climbing at \(10^9\);
a linear hit of \(\kappa\) extrapolates to \(\sim 10^{24}\) and is
correctly out of reach. Further scans refine constants inside the same
window without touching \(c'(\infty)\). The remaining access to
\(c'(\infty)\) is theory-side: Euler products of the certificate
expansion, compared to \(\hat C(A,x)\) at \(A\le 10\)–\(20\).

**Next, in order.**

1. **E_power repaired** (`erdos-straus-E-power.md`). One-stage
   \(S_A\ll x^{1-\delta}\) withdrawn. Live target: two-stage finite
   density plus transfer (`EPower.lean`). Lemma SM is a surrogate,
   checked through \(A=2000\). Gate A still forbids compiling a
   power-saving count as QED. E_lane remains the \(d=1\) floor.
2. **T(3) lower bound**, three-step plan with named risk
   (`erdos-straus-T-3.md`): (a) Iwaniec per slice; (b) Brüdern–Fouvry;
   (c) completion of \(q>x^{1/2}\). Sharp frontier question (plan §4w,
   with roadmap §9): does a joint well-factorable weight exist for the
   moving CRT residue of the triple? The \(r_\chi\to\) Kloosterman look
   is a range no-go at the stall. Per-slice BFI still feeds escape 1.
   Two escapes for the paper's outlook: weaker \(c_-\), or that joint
   weight if it can be built. Not an LSD asymptotic. Do not cite
   Nath–Xie as three semi-linear components.
3. **Derive the defect exponent for \(a\notin\{1,2,3,6\}\).** Structure
   is done (`c4_defect_layer.py`): Rough = certificate-union + defect,
   defect = \(-1\) in \(\langle S\rangle\) but not a subset product.
   Correction machinery for general \(A\), not an error in T(3).
4. The analytic worklist (`erdos-straus-sieve-desk.md`) records the
   T(3) completion step. T(A)\(^+\) is written. It is still a question
   list, not a request to densify covering.

Do not densify covering. Do not run \(x=10^{10}\). Do not assault H_ES.
Do not upgrade T(3) to an LSD asymptotic. Do not claim the matching
lower bound by citing Nath–Xie.
