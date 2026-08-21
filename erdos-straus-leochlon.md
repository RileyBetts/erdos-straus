<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Leochlon Type-II dictionary

**Library documentation, 21 August 2026.** Companion Lean: `Leochlon.lean`.
Not a Track-1 merge, not Bounded-A, not FCT/gateway encodings.
See `erdos-straus-prior-archive.md`.

The construction reported for `leochlon/erdstrau` (survey of a sorry-free
Lean 4 identity programme; the GitHub URL was not reachable when first
recorded) is
\[
(4b-1)(4c-1)=4p\delta+1,\qquad \delta\mid bc.
\]
That identity always produces an explicit Type-II triple
\((pb,\;pc,\;bc/\delta)\). Lean: `ES.LeochlonWitness`,
`ES.isES_of_leochlon`.

It is the same *shape* of Egyptian-fraction integrality as this archive’s
`Witness` ( \(n\) divides two coordinates ). It is **not** automatically a
covering-landing witness at a given \((a,c,d,m)\), and it is **not** a
gateway \(A\le C\) hit. Importing leftover residue-class certificates
from that programme, if they reappear, would be a literature check — not
a reason to densify covering or to reopen Bounded-A.

The small-\(q\) special case \(b=(q+1)/4\) when \(q\equiv 3\pmod{4}\) is
`ES.leochlon_of_q_succ_div_four`. That is a dictionary lemma, not a
coverage theorem for hard classes.
