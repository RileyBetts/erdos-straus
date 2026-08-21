<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Bradford 2026, and Bello–Hernández Lemma 3 / Theorem 8

**Library documentation, 21 August 2026.** Brought from the prior
`erdosstrauss` archive as notes, not as a Track-1 merge.
Companion: `erdos-straus-prior-archive.md`. Not Lean. Not QED.
Do not densify covering.

Sources: Bello–Hernández–Benito–Fernández arXiv:[2606.10922](https://arxiv.org/abs/2606.10922)
Theorem 8 (statement; proof deferred to arXiv:[1010.2035](https://arxiv.org/abs/1010.2035)
Lemma 3); K. Bradford, arXiv:[2602.11774](https://arxiv.org/abs/2602.11774).

---

## Lemma 3 / Theorem 8

One cannot generate a finite number of congruence classes containing all
primes \(p\equiv 1\pmod{4}\) by fixing, in the Type I / Type II equations,
three of the four parameters in a finite subset of \(\mathbb{Z}_{>0}\) and
leaving the remaining parameter free.

Proof idea (1010.2035, Lemma 3): each frozen triple produces \(n\) in an
arithmetic progression (or a finite set). Let \(T\) be the lcm of the
finitely many moduli attached to a finite set \(S\) of triples. There is
an infinite progression \(\{4Tt+1:t>0\}\) that cannot arise from any
triple in \(S\): matching the parametric formula would force \(1\) itself
to be an Erdős–Straus number. Intersecting the four choices of which
parameter is free yields one progression missed by the whole
finite-parameter package. The argument is elementary LCM arithmetic, not
density and not Brauer–Manin.

**Rules out.** Finitely many fixed FCT pairs \((i,d)\), finitely many
fixed tame APs, finitely many CRT classes with fixed \((i,d)\). Growing a
finite catalogue cannot cover all primes \(p\equiv 1\pmod{4}\). That is
the same freeze as “do not densify covering” in this archive.

**Does not rule out.** Constructions whose free parameters grow with \(n\)
(or with \(q\)), so there is no finite \(S\) and no single LCM modulus
\(T\). Scaled Type I/II lifts with unbounded \((i,d)\) are outside the
hypothesis, not a confirmed full-density escape. They only discharge thin
subclasses.

Lemma 3 alone is not a rigidity theorem against every countable family of
gated identities. This programme’s k-budget / dummy-covering record is
the separate reason a growing covering schedule still fails as QED.

---

## Bradford 2026 (arXiv:2602.11774)

The preprint claims an elementary proof for every prime. After \(p=2\)
and \(p\equiv 3\pmod{4}\) it treats \(p\equiv 1\pmod{4}\) via Type I /
Type II identities (Lemmas 1–2) and says combining them will yield a
covering system. The only written check is a \(k=0\) list (moduli 44, 20,
8, 140) and the sentence that 5, 13, 17, 29 are the first four primes
that are \(1\bmod 4\). There is no verification that every
\(p\equiv 1\pmod{4}\) lies in one of the listed APs, no \(k\ge 1\) table,
and no engagement with Mordell’s quadratic-residue obstruction.

Why the covering claim fails:

1. **Mordell.** A polynomial identity valid for all \(p\equiv r\pmod{q}\)
   can exist only if \(r\) is a nonsquare mod \(q\). Since \(1\) is always
   a square, no finite family of such identities covers
   \(p\equiv 1\pmod{840}\). Bradford’s Lemmas 1–2 are such identities.
2. **Lemma 3.** The *written* proof only exhibits \(k=0\) and a handful
   of moduli, so it is a finite-parameter cover. An infinite template
   over all \(k\) would sit outside Lemma 3’s hypothesis; that template
   is not supplied.
3. Listing four small primes is not a covering argument.
4. Several listed APs (\(13\bmod 20\), \(29\bmod 44\)) are identities
   already in the Mordell / covering-landing layer here.

Formalizing Bradford as a proof is not worthwhile. Formalizing Lemmas 1–2
as identity schemas would be covering densification; this archive does
not do that.

Bradford 2021 (*Integers* A24), Bradford–Ionascu 2015, and
arXiv:2403.16047 are different papers. None of them remove Mordell.
