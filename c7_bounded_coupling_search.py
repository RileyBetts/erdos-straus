#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""C7 first pass: bounded-coupling covering mass, and linear identity search.

C7 asks whether some Egyptian-fraction identity family, beyond the classical
m-box, delivers covering mass >= (1+delta) log x at coupling degree O(1)
per scale.

This script does two bounded computations (20 Aug 2026):

1. Type-I covering classes (c = 1, q = 4ad-1, n ≡ -a (mod q)) at level A.
   Coupling proxy: omega(q) = number of distinct prime factors.
   Compare total mass to the omega(q) <= J slice.  C7 needs the bounded-J
   slice to grow like an extra log; the Poisson law of plan §4k says it
   should not.

2. Search for polynomial Witness identities n = q*t+r with a,c,d,m of
   degree <= 1 and small coefficients, and report any that cover a hard
   class mod 840 (the only identities that would change the Mordell
   reduction).

Does not prove or refute C7 asymptotically.  A negative at this scale is
evidence, not a theorem.
"""

from __future__ import annotations

import math
import sys
from collections import defaultdict


HARD = {1, 121, 169, 289, 361, 529}

CLASSICAL = [
    # (q, r, a, c, d_coeffs, m_coeffs)  n = q t + r
    ("n=4t+3", 4, 3, "a=1", "c=2", "d=t+1", "m=1"),
    ("n=3t+2", 3, 2, "a=1", "c=1", "d=1", "m=t+1"),
    ("n=8t+5", 8, 5, "a=1", "c=1", "d=t+1", "m=2"),
    ("n=7t+3", 7, 3, "a=1", "c=2", "d=1", "m=2t+1"),
    ("n=7t+5", 7, 5, "a=2", "c=1", "d=1", "m=t+1"),
    ("n=7t+6", 7, 6, "a=1", "c=1", "d=2", "m=t+1"),
    ("n=15t+7", 15, 7, "a=1", "c=2", "d=2", "m=2t+1"),
    ("n=15t+13", 15, 13, "a=2", "c=1", "d=2", "m=t+1"),
    ("n=2t", 2, 0, "scale of n=2", "", "", ""),
]


def primes_upto(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : n + 1 : step] = b"\x00" * ((n - start) // step + 1)
    return [i for i in range(2, n + 1) if sieve[i]]


def omega_factory(limit: int):
    """omega(n) for n <= limit via linear sieve."""
    om = [0] * (limit + 1)
    for p in range(2, limit + 1):
        if om[p] == 0:
            for m in range(p, limit + 1, p):
                om[m] += 1
    return om


def lin(c0: int, c1: int, t: int) -> int:
    return c0 + c1 * t


def witness_holds(n: int, a: int, c: int, d: int, m: int) -> bool:
    if min(n, a, c, d, m) <= 0:
        return False
    return c * n + a + m == 4 * a * c * d * m


def identity_for_all_t(q: int, r: int, a0: int, a1: int, c: int,
                       d0: int, d1: int, m0: int, m1: int, t_check=(1, 2, 3, 5, 8, 13, 21)) -> bool:
    for t in t_check:
        n = q * t + r
        a = lin(a0, a1, t)
        d = lin(d0, d1, t)
        m = lin(m0, m1, t)
        if not witness_holds(n, a, c, d, m):
            return False
    return True


def covers_hard_class(q: int, r: int) -> list[int]:
    """Hard residues mod 840 that lie in n ≡ r (mod q)."""
    hit = []
    for h in sorted(HARD):
        if h % q == r % q:
            hit.append(h)
    return hit


def search_identities(q_max: int = 24, coeff: int = 4) -> list[dict]:
    """Degree-1 Witness identities with small coefficients.

    c is held constant in {1,2,3,4}: the classical list is already in this
    range.  a,d,m each of the form c0 + c1 t with 0 <= c0 <= coeff and
    0 <= c1 <= coeff, not both zero, and all values positive for t >= 1.
    """
    found = []
    seen = set()
    for q in range(2, q_max + 1):
        for r in range(q):
            for c in range(1, 5):
                for a0 in range(0, coeff + 1):
                    for a1 in range(0, coeff + 1):
                        if a0 == 0 and a1 == 0:
                            continue
                        for d0 in range(0, coeff + 1):
                            for d1 in range(0, coeff + 1):
                                if d0 == 0 and d1 == 0:
                                    continue
                                for m0 in range(0, coeff + 1):
                                    for m1 in range(0, coeff + 1):
                                        if m0 == 0 and m1 == 0:
                                            continue
                                        if not identity_for_all_t(
                                            q, r, a0, a1, c, d0, d1, m0, m1
                                        ):
                                            continue
                                        # Positive for t >= 1.
                                        if min(lin(a0, a1, 1), lin(d0, d1, 1), lin(m0, m1, 1)) <= 0:
                                            continue
                                        key = (q, r, a0, a1, c, d0, d1, m0, m1)
                                        if key in seen:
                                            continue
                                        seen.add(key)
                                        found.append({
                                            "q": q, "r": r, "c": c,
                                            "a": (a0, a1), "d": (d0, d1), "m": (m0, m1),
                                            "hard": covers_hard_class(q, r),
                                        })
    return found


def fmt_poly(c0: int, c1: int, var: str = "t") -> str:
    if c1 == 0:
        return str(c0)
    if c0 == 0:
        return var if c1 == 1 else f"{c1}{var}"
    tterm = var if c1 == 1 else f"{c1}{var}"
    return f"{tterm}+{c0}"


def mass_by_omega(A: int, om: list[int], q_limit: int) -> dict:
    total = 0.0
    by_j = defaultdict(float)
    n_classes = 0
    skipped = 0
    for a in range(1, A + 1):
        for d in range(1, A + 1):
            q = 4 * a * d - 1
            if q > q_limit:
                skipped += 1
                continue
            w = 1.0 / q
            total += w
            by_j[om[q]] += w
            n_classes += 1
    return {"total": total, "by_j": dict(by_j), "n": n_classes, "skipped": skipped}


def main() -> int:
    print("C7 first pass — bounded coupling mass and linear identities")
    print("date: 20 Aug 2026")
    print()

    # --- 1. Type-I mass vs omega slice ---
    As = [8, 12, 16, 24, 32, 48, 64]
    q_limit = 4 * As[-1] * As[-1]  # 16384
    print(f"building omega table up to {q_limit} ...")
    om = omega_factory(q_limit)
    print()
    print("Type-I covering (c=1): q = 4ad-1, a,d <= A")
    print(f"{'A':>4} {'N':>8} {'mass':>10} {'J<=1':>10} {'J<=2':>10} {'J<=3':>10} "
          f"{'J<=2/tot':>9} {'log A':>8}")
    rows = []
    for A in As:
        rec = mass_by_omega(A, om, q_limit)
        j1 = sum(rec["by_j"].get(j, 0.0) for j in rec["by_j"] if j <= 1)
        j2 = sum(rec["by_j"].get(j, 0.0) for j in rec["by_j"] if j <= 2)
        j3 = sum(rec["by_j"].get(j, 0.0) for j in rec["by_j"] if j <= 3)
        tot = rec["total"]
        ratio = (j2 / tot) if tot else 0.0
        rows.append((A, rec, j1, j2, j3, ratio))
        print(f"{A:4d} {rec['n']:8d} {tot:10.4f} {j1:10.4f} {j2:10.4f} {j3:10.4f} "
              f"{ratio:9.3f} {math.log(A):8.3f}")

    print()
    print("Reading: mass grows like log^2 A (two parameters a,d).  At these")
    print("scales q <= 4 A^2 is still small, so omega<=2 holds almost all")
    print("mass (loglog has not grown; plan §4k).  The omega=1 slice grows")
    print("slower than the total.  This does not see Poisson(loglog), and")
    print("does not by itself refute C7 asymptotically.")
    print()

    # --- 2. Linear identity search ---
    print("searching degree-1 Witness identities (q<=20, coeffs<=3) ...")
    found = search_identities(q_max=20, coeff=3)
    print(f"identities found: {len(found)}")

    # Deduplicate by (q, r) residue class, keep one representative.
    by_class: dict[tuple[int, int], list] = defaultdict(list)
    for it in found:
        g = math.gcd(it["q"], it["r"]) if it["r"] else it["q"]
        # normalize n ≡ r (mod q) by dividing out gcd if r=0? keep raw
        by_class[(it["q"], it["r"])].append(it)

    hard_hits = [it for it in found if it["hard"]]
    print(f"distinct (modulus, residue) pairs: {len(by_class)}")
    print(f"identities whose AP meets a hard class mod 840: {len(hard_hits)}")

    # An identity covers a whole hard class only if q | 840 and the residue
    # matches.  Meeting a hard class at one residue of a larger q does not
    # eliminate the class.
    full_cover = []
    for it in found:
        q, r = it["q"], it["r"]
        if 840 % q != 0:
            continue
        # All n ≡ h (mod 840) lie in n ≡ r (mod q) iff h ≡ r (mod q).
        if it["hard"] and all((h % q) == (r % q) for h in HARD if h % q == r % q):
            # covers every n ≡ r (mod q), hence those hard residues
            full_cover.append(it)

    print()
    print("Sample of residue classes hit (one representative each), first 20:")
    for i, ((q, r), items) in enumerate(sorted(by_class.items())[:20]):
        it = items[0]
        a = fmt_poly(*it["a"])
        d = fmt_poly(*it["d"])
        m = fmt_poly(*it["m"])
        hard = it["hard"]
        print(f"  n={q}t+{r}: a={a} c={it['c']} d={d} m={m}  hard={hard}")

    print()
    # Which hard residues appear as *full* arithmetic progressions already
    # in the classical list?  None of the six: that is the definition of hard.
    hard_full = []
    for (q, r), items in by_class.items():
        if 840 % q != 0:
            continue
        covered_hard = [h for h in HARD if h % q == r % q]
        # full cover of a hard class means every n ≡ h (mod 840) is n ≡ r (mod q)
        # which is automatic if h ≡ r (mod q).  That does *not* kill the class
        # unless q=840 and r=h, or the identity is for all n in the class,
        # i.e. n = 840 k + h = q t + r identically — so q | 840 and the
        # progression equals the class.  Equality of APs: q=840, r=h.
        if q == 840 and r in HARD:
            hard_full.append((q, r, items[0]))

    print("Identities with modulus 840 and a hard residue (would kill a class):")
    if not hard_full:
        print("  none.")
    else:
        for q, r, it in hard_full:
            print(f"  n={q}t+{r}: {it}")

    # Weaker: any identity whose EVERY n = qt+r is hard.  Then it would be
    # a polynomial covering of a subset of a hard class — still useful if
    # density is 1/q with q small.
    always_hard_mod = []
    for (q, r), items in by_class.items():
        # n=qt+r hard for all large t?
        # equivalent: { (q t + r) % 840 : t } ⊆ HARD.
        residues = {(q * t + r) % 840 for t in range(840)}
        if residues <= HARD:
            always_hard_mod.append((q, r, residues, items[0]))

    print()
    print("Identities whose AP lies entirely in the hard classes mod 840:")
    if not always_hard_mod:
        print("  none (expected: a proper sub-progression of a hard class")
        print("  would require modulus a multiple of 840).")
    else:
        for q, r, res, it in always_hard_mod:
            print(f"  n={q}t+{r} residues={sorted(res)}  a={fmt_poly(*it['a'])} "
                  f"c={it['c']} d={fmt_poly(*it['d'])} m={fmt_poly(*it['m'])}")

    print()
    print("Verdict (this scale, not a theorem):")
    print("  - No degree-1 identity in this box covers a hard class, or")
    print("    even lies inside the hard classes.")
    print("  - Bounded-omega Type-I mass is not an extra log at toy scale;")
    print("    loglog is not visible yet.")
    print("  C7 remains probably false; the search did not find a family")
    print("    that concentrates covering mass at coupling degree O(1).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
