<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# The varying-modulus correlation gap

**Riley Betts Erdős–Straus programme, 21 August 2026.**
Companion to `erdos-straus-T-3.md` (Phase 4), `erdos-straus-T-2.md`
(A2.2/A2.3), `erdos-straus-T-3-delta.md`, `erdos-straus-T-3-monodromy.md`.
This memo does not propose a construction. It names an absence: after
four independent routes hit the same wall, the remaining T(3) object is
a correlation in which the **modulus itself** is the jointly growing
variable. Not a theorem, not T(3) progress, not Lean. Do not densify
covering. Do not discharge `AnalyticSurvivorBound`.

---

## Four routes, one object

| Route | Write-up | Mechanism of failure |
|---|---|---|
| Maynard I–III, uniform residue class | chat record, not a filed look | Reach \(x^{1/2+\delta}\) for small \(\delta\) is a thin near-BV slab; a window inside it forces sacrificing a leg, which reduces to the closed two-modulus cell |
| Zheng, asymmetric reroute | `erdos-straus-T-2.md` §A2.3 | Leg-sacrifice converts T(3) into T(2) on the remaining pair, which dies on the A2.2 ceiling |
| Joint Heath-Brown \(\delta\)-symbol at \(D\) | `erdos-straus-T-3-delta.md` | Farey–\(k\) incompatibility; where that identity is vacuous (\((0,1/2,1/2)\)), what survives is the object below |
| Joint monodromy independence (FKMS) | `erdos-straus-T-3-monodromy.md` | Wrong category: FKMS sheaves live over a *fixed* \(\mathbf{F}_q\); the correlation has the modulus itself varying |

After Phase 1 of `erdos-straus-T-3.md`, what remains is square-root
cancellation, uniform in \(d_2,d_3\), of
\[
\sum_{d_2,d_3}\chi_2(d_2)\chi_3(d_3)\,K(\,\cdot\,;D),
\qquad D=\mathrm{lcm}(d_2,d_3)\asymp d_2 d_3,
\]
where \(\chi_2,\chi_3\) are the odd real characters mod \(8\) and \(12\)
and \(K\) is the Kloosterman-type kernel produced once Type II is
opened. Both \(d_2\) and \(d_3\) run up to (and, before switching, past)
\(\sqrt{x}\), so \(D\) is jointly growing — not a fixed number relative
to which something else varies.

That four unrelated technologies fail by four different proofs is why
this is a gap, not four disconnected no-gos.

---

## The common failure mode

Every method surveyed falls into one of two shapes:

1. **Fixed residue, growing modulus.** Bombieri–Vinogradov, BFI
   well-factorable estimates, Maynard I–III. These want a residue
   \(a\) independent of \(q\) as \(q\) grows. The T(3) residue
   \(\alpha(d_2,d_3)\) moves with the modulus by construction.
2. **Fixed modulus (field), growing or varying argument.** The
   \(\delta\)-symbol’s Farey dissection past the BV wall, and the whole
   \(\ell\)-adic trace-function line: Katz; Fouvry–Kowalski–Michel on
   trace functions over the primes and sums of products; Kowalski–
   Michel–Sawin; Fouvry–Kowalski–Michel–Sawin arXiv:2511.09459. Each
   fixes a base field \(\mathbf{F}_q\) (or a prime modulus \(q\)) and
   lets an argument, an auxiliary tuple, or a family index vary.

No route surveyed supplies cancellation when the **modulus itself** is
the multi-factor, jointly growing object. That is already the FKMS
failure in `erdos-straus-T-3-monodromy.md`. The same cut holds for the
family tree behind it:

- Fouvry–Kowalski–Michel, *A study in sums of products*, Philos. Trans.
  Roy. Soc. A **373** (2015): fixes a prime \(p\), varies auxiliary
  linear / Möbius arguments against it.
- Kowalski–Michel CLT for divisor sums: fixed \(p\), varying
  \(\kappa\)-tuples of Kloosterman *arguments*.
- Ricotta–Royer, arXiv:1609.03694: Kloosterman paths for prime-power
  moduli \(p^n\) with \(n\ge 2\) **fixed**, only \(p\to\infty\).

One adjacent question, Kowalski arXiv:math/0608718 (big symplectic or
orthogonal monodromy modulo \(\ell\)), asks for uniform monodromy as
*both* the field and a conductor grow, for elliptic-curve twists. Flagged
there as a harder regime with only partial results. Structurally closer
to what T(3) would need, but not the same object (twists of a curve, not
a correlation over \(d_2,d_3\)).

This is a literature check, not a completeness proof. Evidence the
absence is real, not evidence it is permanent.

---

## The question

Does there exist — or can one construct — a Goursat–Kolchin–Ribet-type
independence statement for a family of Kloosterman-type (or gallant)
sheaves in which the **modulus is the outer, growing, multi-factor
summation variable**, rather than the fixed base field over which a
single sheaf’s argument ranges? Concretely: is there a framework in
which
\[
\sum_{d_2,d_3\le X}\chi_2(d_2)\chi_3(d_3)\,K(\,\cdot\,;d_2 d_3)
\]
gets a saving from independence of the \(d_2\)-part and the \(d_3\)-part
of the kernel, analogous to GKR over one fixed field, with the roles of
“fixed field” and “growing modulus” reversed?

A citation would close the gap. “Open, and here is why it is hard” is
the same status as `erdos-straus-T-3-delta.md` and
`erdos-straus-T-3-monodromy.md`.

---

## Function-field companion (not an in-house step)

The \(\mathbb{F}_q[t]\) analogue replaces a large modulus by a
high-degree polynomial. Weil-quality bounds are unconditional there, so
independence across several *jointly growing* polynomial moduli might be
stateable and testable before any attempt over \(\mathbf{Z}\). Not
claimed to resolve the number-field question; a testbed for whether the
needed independence statement is plausible.

---

## What this memo does not do

- It does not prove the gap is permanent, only that the search across
  the family tree already engaged by this programme did not find a
  varying-modulus GKR.
- It does not propose a construction.
- It does not reopen `erdos-straus-T-2.md` §A2.3,
  `erdos-straus-T-3-delta.md`, or `erdos-straus-T-3-monodromy.md`.
- It does not claim T(3) progress. The joint well-factorable CRT residue
  (Phase 4; plan §4w) remains the object, now with four documented
  reasons the tools surveyed do not reach it.

**Next.** Not an in-house step. Do not densify covering.
