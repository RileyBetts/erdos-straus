<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Well-factorability of real kernel characters (Zheng Def. 1.1)

**Riley Betts Erdős–Straus programme, 21 August 2026.**
Companion to `erdos-straus-T-2.md`. Primary reference: Zongkun Zheng,
*Primes in Simultaneous Arithmetic Progressions*, arXiv:2512.22798,
Definition 1.1. Not Lean. Not a T(3) claim. Do not densify covering.

Zheng’s Definition 1.1: a sequence \((\lambda_d)\) is well-factorable of
level \(D\) if, for every factorization \(D=D_1 D_2\), there exist
sequences \(\lambda',\lambda''\) bounded by \(1\), supported on
\(d_1\le D_1\) and \(d_2\le D_2\) respectively, such that
\(\lambda_d=\sum_{d_1 d_2=d}\lambda'(d_1)\lambda''(d_2)\) for all
\(d\le D\).

---

## Lemma 0.1 (complete multiplicativity, and what it does not buy)

Let \(\chi\) be a real character modulo \(k\) (completely multiplicative,
\(|\chi|\le 1\)). The sequence \(\gamma_q:=\chi(q)\) is divisor-bounded,
so it may occupy Zheng’s \(\gamma\)-slot in Theorem 1.1 with no extra
level hypothesis. Complete multiplicativity also *transfers*
well-factorability: if \((\rho_d)\) is well-factorable of level \(D\),
then \(\lambda_d:=\chi(d)\rho_d\) is well-factorable of the same level,
by taking \(\lambda'(d_1)=\chi(d_1)\rho'(d_1)\) and
\(\lambda''(d_2)=\chi(d_2)\rho''(d_2)\). That is the correct input to
Zheng’s \(\lambda\)-slot.

The sequence \(\lambda_d=\chi(d)\,1_{d\le D}\) itself is **not**
well-factorable of every level \(D\) merely by writing
\(\chi(d)=\chi(d_1)\chi(d_2)\) along a single splitting. Zheng’s identity
is a Dirichlet convolution (a *sum* over factorizations). That sum
equals \(\chi(d)\) times a restricted divisor function, not \(\chi(d)\).
The proposed construction with \(\lambda'=\chi\cdot 1_{\le D_1}\) and
\(\lambda''=\chi\cdot 1_{\le D_2}\) therefore does not meet Definition
1.1. Characters of fixed conductor may still be absorbed into a residue
class modulo \(k=O(1)\), or multiplied onto an Iwaniec well-factorable
sieve weight (Zheng Corollary 11.2). Neither move is free if the object
is exactly \(r_\chi\).

Specialise to the T(2) kernels. Lean `OddRealChar` is completely
multiplicative (`map_mul`). At \(a=1\), \(\chi_1=\chi_4\) modulo \(4\)
(`oddRealChar_four`); at \(a=2\), \(\chi_2\) is one of
`oddRealChar_eight_chi4` or `oddRealChar_eight_chi4chi8`, modulo \(8\).
Zheng’s \(|a_1|\le\log^B x\) holds with \(a_1=-4\), \(|a_1|=4\). The
coprimality \((d,a_1)=(q,a_2)=1\) is the same coprimality already in
`classRough_of_certifies`: aligned divisors are coprime to \(4a\)
(`OddRealChar.gcd_eq_one_of_aligned`), and \(\chi_4,\chi_8\) vanish on
evens, so the support of \(\chi_1(d_1)\) (resp. \(\chi_2(d_2)\)) is
already coprime to \(4\) (resp. \(16\)).

---

## Task 0.2 — squarefree support

Zheng Theorem 1.1 requires \(\mu^2(d)=\mu^2(q)=1\). Lean does **not**
reduce the divisor sum to squarefree \(d\).

`classRough_of_certifies` quantifies over *primes* \(q\mid p+4a^2\).
`chi_eq_one_of_dvd` then extends the prime certificate to every coprime
divisor of \(N\), including powerful ones, by complete multiplicativity.
The kernel statement is therefore about prime factors. The detector
\(r_\chi(n)=\sum_{d\mid n}\chi(d)\) is not: it sums over all divisors.

Isolate the powerful part before quoting Zheng. Write
\(r_\chi(n)=\sum_{d\mid n,\,\mu^2(d)=1}\chi(d)+R_{\mathrm{pow}}(n)\).
If a square \(k^2\ge\log^{C}x\) divides \(p+4\) or \(p+16\), the count of
such primes is \(\ll x^{1/2}(\log x)^{-C}\) after a trivial estimate, which
is \(o(x/\log^A x)\) and does not affect the Zheng remainder. Apply
Theorem 1.1 only to the squarefree sum. This split is not in Lean and
is not absorbed into `classRough_123_iff_certificates`.
