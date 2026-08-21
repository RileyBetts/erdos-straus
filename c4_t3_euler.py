#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Certificate-expansion Euler products for T(3).

S(3) is the union of 4 assignments (1 × 2 × 2 kernels), each the condition
that every coprime prime factor of p+4a² lies in a prescribed index-2
subgroup of (Z/4aZ)* for a=1,2,3. Kernel: classRough_123_iff_certificates.

This file evaluates the local selection constant of each assignment
(joint vs product of three certificate-marginals), the same quantity
C_euler computed for prime-aligned ClassRough in c4_euler_factor.py, and
empirical assignment occupancy among hard primes at X=10^6.

Do not run 10^10. Default Qmax=10^6 (assignment products); empirical X=10^6.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

from c4_S_xscan import factor_spf, sieve_hard_primes, spf_numpy
from c4_euler_factor import hard_avoid_density

HERE = os.path.dirname(os.path.abspath(__file__))
GROW_JSON = os.path.join(HERE, "c4_growing_A_X1000000000_A200.json")

# (a, shift, modulus, kernel predicate on q)
def ker_chi4(q: int) -> bool:
    return q % 2 == 1 and q % 4 == 1


def ker_chi4chi8(q: int) -> bool:
    return q % 2 == 1 and q % 8 in (1, 3)


def ker_chi4chi3(q: int) -> bool:
    return math.gcd(q, 12) == 1 and q % 12 in (1, 7)


SLICES = [
    # a, shift, m=4a, name -> pred
    (1, 4, 4),
    (2, 16, 8),
    (3, 36, 12),
]

ASSIGNMENTS = {
    "444": (ker_chi4, ker_chi4, ker_chi4),
    "44c": (ker_chi4, ker_chi4, ker_chi4chi3),
    "4c4": (ker_chi4, ker_chi4chi8, ker_chi4),
    "4cc": (ker_chi4, ker_chi4chi8, ker_chi4chi3),
}

# Intersections needed for inclusion-exclusion of the union of four.
# At a=2, χ4 ∩ χ4χ8 is q ≡ 1 (mod 8); at a=3, χ4 ∩ χ4χ3 is q ≡ 1 (mod 12).
def ker_a2_both(q: int) -> bool:
    return q % 2 == 1 and q % 8 == 1


def ker_a3_both(q: int) -> bool:
    return math.gcd(q, 12) == 1 and q % 12 == 1


IE_EVENTS = {
    **ASSIGNMENTS,
    "a2both_a3chi4": (ker_chi4, ker_a2_both, ker_chi4),
    "a2both_a3chi3": (ker_chi4, ker_a2_both, ker_chi4chi3),
    "a2chi4_a3both": (ker_chi4, ker_chi4, ker_a3_both),
    "a2chi8_a3both": (ker_chi4, ker_chi4chi8, ker_a3_both),
    "both_both": (ker_chi4, ker_a2_both, ker_a3_both),
}


def in_ker(pred, q: int, m: int) -> bool:
    """Coprime-to-m factors only; q sharing a factor with m is unconstrained."""
    if math.gcd(q, m) != 1:
        return True
    return pred(q)


def local_of(preds, q: int) -> dict:
    den = q - 1
    forb = []
    marg = []
    for pred, (a, shift, m) in zip(preds, SLICES):
        if math.gcd(q, m) != 1:
            continue
        if not pred(q):
            forb.append((-shift) % q)
            marg.append(1)
        else:
            marg.append(0)
    k = len(set(forb))
    mcount = len(forb)
    if k >= den or den <= 0:
        joint = 0.0
        prod = 0.0
        ratio = float("nan")
    else:
        joint = 1.0 - k / den
        prod = 1.0
        for bit in marg:
            if bit:
                prod *= 1.0 - 1.0 / den
        ratio = joint / prod if prod else float("nan")
    rec = {
        "k": k,
        "m": mcount,
        "joint": joint,
        "prod": prod,
        "ratio": ratio,
        "forb": sorted(set(forb)),
    }
    if q in (3, 5, 7):
        rec["hard_joint"] = hard_avoid_density(q, rec["forb"]) if rec["forb"] else 1.0
        rec["hard_prod"] = 1.0
        for bit, (_, shift, m) in zip(
            [math.gcd(q, sl[2]) == 1 and not pr(q) for pr, sl in zip(preds, SLICES)],
            SLICES,
        ):
            if bit:
                rec["hard_prod"] *= hard_avoid_density(q, [(-shift) % q])
        rec["hard_ratio"] = (
            rec["hard_joint"] / rec["hard_prod"] if rec["hard_prod"] else float("nan")
        )
    return rec


def euler_product(preds, primes: list[int], qmax: int) -> dict:
    logC = 0.0
    logC_q = 0.0
    log_small = 0.0
    n_terms = 0
    n_coll = 0
    small = []
    for q in primes:
        if q == 2:
            continue
        loc = local_of(preds, q)
        if loc["m"] == 0:
            continue
        n_terms += 1
        if loc["k"] < loc["m"]:
            n_coll += 1
        if loc["joint"] <= 0:
            logC = float("-inf")
            break
        term = math.log(loc["joint"]) - math.log(loc["prod"]) if loc["prod"] else float("-inf")
        term_q = math.log1p(-loc["k"] / q) - loc["m"] * math.log1p(-1 / q)
        logC += term
        logC_q += term_q
        if q < 840:
            log_small += term
        if q < 50 or q in (3, 5, 7):
            small.append({"q": q, **{k: loc[k] for k in ("k", "m", "ratio") if k in loc},
                          **{k: loc[k] for k in loc if k.startswith("hard")}})
    return {
        "C": math.exp(logC) if logC != float("-inf") else 0.0,
        "C_1q": math.exp(logC_q) if logC_q != float("-inf") else 0.0,
        "C_small": math.exp(log_small),
        "n_terms": n_terms,
        "n_coll": n_coll,
        "small_q": small,
        "Qmax": qmax,
    }


def odd_primes_upto(n: int) -> list[int]:
    sv = bytearray(b"\x01") * (n + 1)
    sv[0:2] = b"\x00\x00"
    r = int(n ** 0.5)
    for p in range(2, r + 1):
        if sv[p]:
            sv[p * p : n + 1 : p] = b"\x00" * ((n - p * p) // p + 1)
    return [i for i in range(3, n + 1) if sv[i]]


def chi4(n: int) -> int:
    if n % 2 == 0:
        return 0
    return 1 if n % 4 == 1 else -1


def chi8(n: int) -> int:
    if n % 2 == 0:
        return 0
    return 1 if (n * n - 1) // 8 % 2 == 0 else -1


def chi3mod12(n: int) -> int:
    if n % 2 == 0 or n % 3 == 0:
        return 0
    return 1 if n % 12 in (1, 11) else -1


def certifies(qs: list[int], pred) -> bool:
    return all(pred(q) for q in qs)


def empirical(Xmax: int = 1_000_000) -> dict:
    hard = sieve_hard_primes(Xmax)
    spf = spf_numpy(Xmax + 36)
    n = len(hard)
    counts = {name: 0 for name in ASSIGNMENTS}
    n_union = 0
    n_cr = 0

    def coprime_primes(fac, m):
        return [q for q, _e in fac if math.gcd(q, m) == 1]

    def class_rough(fac, m):
        # no divisor ≡ −1 (mod m): check all divisors via prime factors
        # aligned iff product of a subset of residues ≡ −1, for squarefree;
        # use the full divisor list from factorization.
        N = 1
        for q, e in fac:
            N *= q ** e
        # walk divisors
        divs = [1]
        for q, e in fac:
            more = []
            pe = 1
            for _ in range(e):
                pe *= q
                for d in divs:
                    more.append(d * pe)
            divs.extend(more)
        for d in divs:
            if d >= 3 and (d + 1) % m == 0:
                return False
        return True

    for p in hard:
        facs = []
        crs = []
        qss = []
        for a, shift, m in SLICES:
            fac = factor_spf(p + shift, spf)
            facs.append(fac)
            crs.append(class_rough(fac, m))
            qss.append(coprime_primes(fac, m))
        if all(crs):
            n_cr += 1
        fired = []
        for name, preds in ASSIGNMENTS.items():
            ok = all(certifies(qs, pred) for qs, pred in zip(qss, preds))
            if ok:
                counts[name] += 1
                fired.append(name)
        if fired:
            n_union += 1
    return {
        "Xmax": Xmax,
        "n_hard": n,
        "n_CR123": n_cr,
        "n_union": n_union,
        "match": n_cr == n_union,
        "S": n_cr / n,
        "assignments": {k: {"n": v, "rate": v / n} for k, v in counts.items()},
    }


def measured_C3() -> dict | None:
    if not os.path.exists(GROW_JSON):
        return None
    row = json.load(open(GROW_JSON))["enrich"][2]
    return {
        "C_hat": row["C_hat"],
        "S": row["S"],
        "n_alive": row["n_alive"],
        "rho": row["rho"],
        "x": 1_000_000_000,
    }


def main(Qmax: int = 1_000_000, Xemp: int = 1_000_000) -> dict:
    t0 = time.time()
    print(f"T(3) Euler  Qmax={Qmax}  Xemp={Xemp}", flush=True)
    primes = odd_primes_upto(Qmax)
    products = {}
    print("\n  assignment     C      C_1/q   small    coll  terms")
    for name, preds in IE_EVENTS.items():
        rec = euler_product(preds, primes, Qmax)
        products[name] = rec
        mark = "*" if name in ASSIGNMENTS else " "
        print(
            f"  {mark}{name:16s}  {rec['C']:.5f}  {rec['C_1q']:.5f}  "
            f"{rec['C_small']:.5f}  {rec['n_coll']:4d}  {rec['n_terms']}",
            flush=True,
        )

    print("\n  empirical occupancy...", flush=True)
    emp = empirical(Xemp)
    print(
        f"  X={Xemp}  hard={emp['n_hard']}  CR123={emp['n_CR123']}  "
        f"union={emp['n_union']}  match={emp['match']}  S={emp['S']:.4f}",
        flush=True,
    )
    for name, rec in emp["assignments"].items():
        print(f"    {name}  {rec['n']:5d}  {rec['rate']:.4f}", flush=True)

    chat = measured_C3()
    if chat:
        print(
            f"\n  measured Ĉ(3) at x=10^9: {chat['C_hat']:.4f}  "
            f"S={chat['S']:.4f}  n_alive={chat['n_alive']}",
            flush=True,
        )

    out = {
        "Qmax": Qmax,
        "elapsed_s": time.time() - t0,
        "products": products,
        "empirical": emp,
        "measured_C3": chat,
        "note": (
            "C is the local selection constant of one certificate assignment "
            "(joint / product of three ker-marginals), analogue of C_euler. "
            "It is not Ĉ(3): the four events overlap, Wirsing log-powers differ, "
            "and Ĉ divides by ClassRough (union) marginals. Empirical union = "
            "CR123 is the kernel theorem at this X."
        ),
    }
    print(f"\n  elapsed {out['elapsed_s']:.1f}s", flush=True)
    return out


if __name__ == "__main__":
    Qmax = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    Xemp = int(sys.argv[2]) if len(sys.argv) > 2 else 1_000_000
    result = main(Qmax, Xemp)
    path = os.path.join(HERE, f"c4_t3_euler_Q{Qmax}.json")
    with open(path, "w") as f:
        json.dump(result, f)
    print(f"  wrote {path}")
