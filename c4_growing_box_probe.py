#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Growing-box probe of the level-schedule independence assumption.

Pair ratios at fixed A=30 were ~1.  The schedule's actual hypothesis is
quasi-independence of *all* slice-failure events in a growing (a,d)-box.
This script measures the full-box joint against the product of one-slot
densities, in two directions:

  (i)  d = 1, A growing: P(∩_{a≤A} ClassRough(p,a)) / ∏_{a≤A} ρ_a
  (ii) a,d ≤ D growing: the same for slots (a,d) with N = p+4a²d,
       aligned modulus 4ad  (Lean ClassRough, any divisor q ≥ 3)

Default X = 10^6 (hard primes), plus an optional second X.  The QED box
A = exp(c√ln x) with κc² > 1 is ~ 2·10^4 at x = 10^6 and is not brute-forced.

Does not prove or refute H_ES.  A ratio that grows with the box is the
high-order accumulation the pair test cannot see.
"""

from __future__ import annotations

import json
import math
import sys


HARD = {1, 121, 169, 289, 361, 529}


def primes_upto(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    r = int(n**0.5)
    for p in range(2, r + 1):
        if sieve[p]:
            start = p * p
            sieve[start : n + 1 : p] = b"\x00" * ((n - start) // p + 1)
    return [i for i in range(2, n + 1) if sieve[i]]


def spf_upto(n: int) -> list[int]:
    spf = list(range(n + 1))
    r = int(n**0.5)
    for p in range(2, r + 1):
        if spf[p] == p:
            for m in range(p * p, n + 1, p):
                if spf[m] == m:
                    spf[m] = p
    return spf


def factor_with_spf(n: int, spf: list[int]) -> dict[int, int]:
    fac: dict[int, int] = {}
    while n > 1:
        p = spf[n]
        fac[p] = fac.get(p, 0) + 1
        n //= p
    return fac


def divisors(fac: dict[int, int]) -> list[int]:
    divs = [1]
    for p, e in fac.items():
        divs = [d * p**k for d in divs for k in range(e + 1)]
    return divs


def is_class_rough(divs: list[int], modulus: int) -> bool:
    for q in divs:
        if q >= 3 and (q + 1) % modulus == 0:
            return False
    return True


def qed_A(x: int, kappa: float = 0.139) -> float:
    """A = exp(c √ln x) at the κc² = 1 threshold."""
    c = 1.0 / math.sqrt(kappa)
    return math.exp(c * math.sqrt(math.log(x)))


def run_d1_growing(hard: list[int], spf: list[int], Amax: int) -> dict:
    n = len(hard)
    # rough[i][a] for a=1..Amax
    rough = [[False] * (Amax + 1) for _ in range(n)]
    for i, p in enumerate(hard):
        for a in range(1, Amax + 1):
            N = p + 4 * a * a
            divs = divisors(factor_with_spf(N, spf))
            rough[i][a] = is_class_rough(divs, 4 * a)

    count_a = [0] * (Amax + 1)
    for i in range(n):
        for a in range(1, Amax + 1):
            if rough[i][a]:
                count_a[a] += 1
    rho = [count_a[a] / n for a in range(Amax + 1)]

    # still_all[i] = still class-rough on 1..A as A grows
    still = [True] * n
    log_prod = 0.0
    rows = []
    for A in range(1, Amax + 1):
        for i in range(n):
            if still[i] and not rough[i][A]:
                still[i] = False
        n_esc = sum(still)
        obs = n_esc / n
        if rho[A] > 0:
            log_prod += math.log(rho[A])
        prod = math.exp(log_prod)
        ratio = obs / prod if prod > 0 else float("nan")
        rows.append({
            "A": A,
            "n_esc": n_esc,
            "obs": obs,
            "prod": prod,
            "ratio": ratio,
            "rho_A": rho[A],
            "log_obs": math.log(obs) if obs > 0 else None,
            "log_prod": log_prod,
        })

    # pair-ratio mean at selected A (subsample pairs to keep it cheap)
    pair_at = []
    for A in (10, 20, 30, 40, 50, 80, 100, 120):
        if A > Amax:
            continue
        ratios = []
        step = 1 if A <= 40 else 2
        for a in range(1, A + 1, step):
            for b in range(a + 1, A + 1, step):
                both = sum(1 for i in range(n) if rough[i][a] and rough[i][b])
                indep = rho[a] * rho[b]
                if indep > 0:
                    ratios.append((both / n) / indep)
        pair_at.append({
            "A": A,
            "n_pairs": len(ratios),
            "mean": sum(ratios) / len(ratios),
            "min": min(ratios),
            "max": max(ratios),
        })

    return {"rho": rho[1:], "rows": rows, "pair_at": pair_at}


def run_ad_box(hard: list[int], spf: list[int], Dmax: int) -> dict:
    """Slots (a,d) with 1 ≤ a,d ≤ D. Prefix boxes D = 1..Dmax."""
    n = len(hard)
    slots = [(a, d) for a in range(1, Dmax + 1) for d in range(1, Dmax + 1)]
    # rough_slot[i][idx]
    nslots = len(slots)
    rough = [[False] * nslots for _ in range(n)]
    idx_of = {(a, d): k for k, (a, d) in enumerate(slots)}
    for i, p in enumerate(hard):
        for k, (a, d) in enumerate(slots):
            N = p + 4 * a * a * d
            divs = divisors(factor_with_spf(N, spf))
            rough[i][k] = is_class_rough(divs, 4 * a * d)

    count = [0] * nslots
    for i in range(n):
        for k in range(nslots):
            if rough[i][k]:
                count[k] += 1
    rho = [c / n for c in count]

    rows = []
    for D in range(1, Dmax + 1):
        active = [idx_of[(a, d)] for a in range(1, D + 1) for d in range(1, D + 1)]
        n_esc = 0
        for i in range(n):
            if all(rough[i][k] for k in active):
                n_esc += 1
        obs = n_esc / n
        log_prod = 0.0
        for k in active:
            if rho[k] > 0:
                log_prod += math.log(rho[k])
        prod = math.exp(log_prod)
        ratio = obs / prod if prod > 0 else float("nan")
        rows.append({
            "D": D,
            "n_slots": len(active),
            "n_esc": n_esc,
            "obs": obs,
            "prod": prod,
            "ratio": ratio,
        })
    return {"rows": rows}


def main(X: int = 1_000_000, Amax: int = 120, Dmax: int = 20) -> dict:
    maxN = max(X + 4 * Amax * Amax, X + 4 * Dmax * Dmax * Dmax)
    primes = primes_upto(X)
    hard = [p for p in primes if p % 840 in HARD]
    spf = spf_upto(maxN)
    d1 = run_d1_growing(hard, spf, Amax)
    ad = run_ad_box(hard, spf, Dmax)
    return {
        "X": X,
        "n_hard": len(hard),
        "Amax": Amax,
        "Dmax": Dmax,
        "qed_A": qed_A(X),
        "d1": d1,
        "ad": ad,
    }


def show(out: dict) -> None:
    print(f"hard primes p ≤ {out['X']}: {out['n_hard']}")
    print(f"QED-threshold A at this x (κc²=1, κ=0.139): {out['qed_A']:.0f}")
    print()
    print("d=1 growing A:  n_esc  obs     prod      ratio=obs/prod")
    want = {1, 2, 3, 5, 10, 15, 20, 30, 40, 50, 60, 80, 100, 120}
    for r in out["d1"]["rows"]:
        if r["A"] in want or r["A"] == out["Amax"]:
            print(f"  A={r['A']:3d}  {r['n_esc']:4d}  {r['obs']:.4e}  "
                  f"{r['prod']:.4e}  {r['ratio']:.3f}  ρ_A={r['rho_A']:.4f}")
    print()
    print("pair-ratio mean inside a≤A (still ~1 if only pairs are independent):")
    for p in out["d1"]["pair_at"]:
        print(f"  A≤{p['A']:3d}  n_pairs={p['n_pairs']:4d}  mean={p['mean']:.4f}  "
              f"min={p['min']:.4f}  max={p['max']:.4f}")
    print()
    print(" (a,d)≤D growing box:  slots  n_esc  obs      prod      ratio")
    for r in out["ad"]["rows"]:
        print(f"  D={r['D']:2d}  {r['n_slots']:3d}  {r['n_esc']:4d}  "
              f"{r['obs']:.4e}  {r['prod']:.4e}  {r['ratio']:.3f}")


if __name__ == "__main__":
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    Amax = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    Dmax = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    out = main(X, Amax, Dmax)
    show(out)
    path = f"c4_growing_box_X{X}.json"
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"\nwrote {path}")
