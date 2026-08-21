#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""C4_1 / C2 numerical probe of the level-schedule independence assumption.

Population: hard-class primes p ≤ X (six QR classes mod 840).
Slot a (d = 1): ClassRough(p, a) iff p + 4a² has no divisor q ≥ 3 with
q ≡ −1 (mod 4a) — the Lean predicate `ClassRough`.

Measurements
  (i)  two-shift: ρ_{a,b} / (ρ_a ρ_b) for 1 ≤ a < b ≤ A
  (ii) shared-prime fraction on the both-fail and both-rough sets
  (iii) C2: Jacobi (p/11)×(p/19) on all hard primes vs d=1 escapees

Default X = 10^6, A = 30 matches plan §4r (sanity: 2370 hard primes).
§4r's 161 d=1 escapees is the *prime-aligned* convention (a prime q ≡ −1
(mod 4a) divides p+4a²). Lean `ClassRough` forbids any divisor q ≥ 3 with
that congruence, so this script reports 48 escapees; both conventions are
printed.  Pair ratios are ~1 under either convention.
"""

from __future__ import annotations

import json
import math
import sys
from collections import defaultdict

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


def jacobi(a: int, n: int) -> int:
    """Jacobi symbol (a/n), n odd positive."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be odd and positive")
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            n8 = n % 8
            if n8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def class_rough_from_divisors(divs: list[int], a: int) -> bool:
    mod = 4 * a
    for q in divs:
        if q >= 3 and (q + 1) % mod == 0:
            return False
    return True


def main(X: int = 1_000_000, A: int = 30) -> dict:
    maxN = X + 4 * A * A
    primes = primes_upto(X)
    hard = [p for p in primes if p % 840 in HARD]
    spf = spf_upto(maxN)

    # per-prime, per-a: rough? and the integer N = p+4a² (for gcd)
    rough = [[False] * (A + 1) for _ in range(len(hard))]
    Nslot = [[0] * (A + 1) for _ in range(len(hard))]
    for i, p in enumerate(hard):
        for a in range(1, A + 1):
            N = p + 4 * a * a
            Nslot[i][a] = N
            fac = factor_with_spf(N, spf)
            divs = divisors(fac)
            rough[i][a] = class_rough_from_divisors(divs, a)

    n = len(hard)
    count_a = [0] * (A + 1)
    for i in range(n):
        for a in range(1, A + 1):
            if rough[i][a]:
                count_a[a] += 1
    rho = [0.0] * (A + 1)
    for a in range(1, A + 1):
        rho[a] = count_a[a] / n

    escapee = []
    for i, p in enumerate(hard):
        if all(rough[i][a] for a in range(1, A + 1)):
            escapee.append(p)

    pairs = []
    ratios = []
    for a in range(1, A + 1):
        for b in range(a + 1, A + 1):
            both_r = both_f = share_r = share_f = 0
            for i in range(n):
                ra, rb = rough[i][a], rough[i][b]
                g = math.gcd(Nslot[i][a], Nslot[i][b])
                if ra and rb:
                    both_r += 1
                    if g > 1:
                        share_r += 1
                if (not ra) and (not rb):
                    both_f += 1
                    if g > 1:
                        share_f += 1
            indep = rho[a] * rho[b]
            obs = both_r / n
            ratio = obs / indep if indep > 0 else float("nan")
            ratios.append(ratio)
            pairs.append({
                "a": a, "b": b, "gcd_ab": math.gcd(a, b),
                "n_a": count_a[a], "n_b": count_a[b], "n_both": both_r,
                "rho_a": rho[a], "rho_b": rho[b], "rho_both": obs,
                "indep": indep, "ratio": ratio,
                "both_fail": both_f,
                "share_rough": share_r / both_r if both_r else None,
                "share_fail": share_f / both_f if both_f else None,
            })

    ratios_sorted = sorted(ratios)
    def pct(xs, q):
        if not xs:
            return None
        k = min(len(xs) - 1, max(0, int(round(q * (len(xs) - 1)))))
        return xs[k]

    coprime = [p for p in pairs if p["gcd_ab"] == 1]
    not_cop = [p for p in pairs if p["gcd_ab"] > 1]

    def mean(ps):
        return sum(p["ratio"] for p in ps) / len(ps) if ps else None

    flagship_keys = [(1, 2), (1, 3), (1, 5), (1, 30), (2, 3), (3, 5),
                     (3, 11), (5, 7), (15, 30), (2, 4), (6, 8), (10, 20)]
    flag_map = {(p["a"], p["b"]): p for p in pairs}
    flagship = [flag_map[k] for k in flagship_keys if k in flag_map]

    # ratio histogram
    buckets = [0.70, 0.85, 0.95, 1.05, 1.15, 1.30, 1.50, 2.00]
    hist = []
    prev = 0.0
    for hi in buckets:
        hist.append({
            "lo": prev, "hi": hi,
            "n": sum(1 for r in ratios if prev <= r < hi),
        })
        prev = hi
    hist.append({"lo": buckets[-1], "hi": None,
                 "n": sum(1 for r in ratios if r >= buckets[-1])})

    def jac_table(primes_list, q1=11, q2=19):
        tab = defaultdict(int)
        skipped = 0
        for p in primes_list:
            if p in (q1, q2):
                skipped += 1
                continue
            s1 = jacobi(p, q1)
            s2 = jacobi(p, q2)
            tab[(s1, s2)] += 1
        m = len(primes_list) - skipped
        cells = {f"{s1},{s2}": tab[(s1, s2)] for s1 in (-1, 1) for s2 in (-1, 1)}
        # also zeros if any
        for s1 in (-1, 0, 1):
            for s2 in (-1, 0, 1):
                if tab[(s1, s2)] and (s1, s2) not in ((-1, -1), (-1, 1), (1, -1), (1, 1)):
                    cells[f"{s1},{s2}"] = tab[(s1, s2)]
        marg1 = {1: 0, -1: 0, 0: 0}
        marg2 = {1: 0, -1: 0, 0: 0}
        for (s1, s2), c in tab.items():
            marg1[s1] += c
            marg2[s2] += c
        return {
            "n": m, "skipped": skipped, "cells": cells,
            "marg11": marg1, "marg19": marg2,
            "bias11": (marg1[1] - marg1[-1]) / m if m else None,
            "bias19": (marg2[1] - marg2[-1]) / m if m else None,
        }

    covered = [p for p in hard if p not in set(escapee)]
    c2_all = jac_table(hard)
    c2_esc = jac_table(escapee)
    c2_cov = jac_table(covered)

    # a=1 3-mod-4-free among escapees (should be 100% per §4r)
    a1_esc = sum(1 for i, p in enumerate(hard)
                 if p in set(escapee) and rough[i][1])

    out = {
        "X": X, "A": A, "n_hard": n, "n_escapee": len(escapee),
        "escapees_head": escapee[:12],
        "a1_rough_among_escapees": a1_esc,
        "rho_by_a": {str(a): {"n": count_a[a], "rho": rho[a]} for a in range(1, A + 1)},
        "ratio_summary": {
            "n_pairs": len(pairs),
            "mean": mean(pairs),
            "median": pct(ratios_sorted, 0.5),
            "p10": pct(ratios_sorted, 0.1),
            "p90": pct(ratios_sorted, 0.9),
            "min": min(ratios),
            "max": max(ratios),
            "mean_coprime": mean(coprime),
            "mean_not_coprime": mean(not_cop),
            "n_coprime": len(coprime),
            "n_not_coprime": len(not_cop),
            "frac_ratio_gt_1_15": sum(1 for r in ratios if r > 1.15) / len(ratios),
            "frac_ratio_gt_1_05": sum(1 for r in ratios if r > 1.05) / len(ratios),
            "frac_ratio_lt_0_95": sum(1 for r in ratios if r < 0.95) / len(ratios),
        },
        "hist": hist,
        "flagship": flagship,
        "share_fail_mean": sum(p["share_fail"] or 0 for p in pairs) / len(pairs),
        "share_rough_mean": sum((p["share_rough"] or 0) for p in pairs) / len(pairs),
        "c2_all": c2_all, "c2_escapee": c2_esc, "c2_covered": c2_cov,
    }
    return out


def fmt_pair(p: dict) -> str:
    sf = p["share_fail"]
    sr = p["share_rough"]
    return (
        f"  ({p['a']:2d},{p['b']:2d}) gcd={p['gcd_ab']:2d}  "
        f"ρa={p['rho_a']:.4f} ρb={p['rho_b']:.4f} ρab={p['rho_both']:.4f}  "
        f"indep={p['indep']:.4f}  ratio={p['ratio']:.3f}  "
        f"share_fail={sf:.3f} share_rough={sr:.3f}"
        if sf is not None and sr is not None else
        f"  ({p['a']:2d},{p['b']:2d}) ratio={p['ratio']:.3f}"
    )


if __name__ == "__main__":
    X = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    A = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    out = main(X, A)
    s = out["ratio_summary"]
    print(f"hard primes p ≤ {out['X']}: {out['n_hard']}")
    print(f"d=1 escapees a ≤ {out['A']}: {out['n_escapee']}  "
          f"(§4r expected 2370 / 161)")
    print(f"a=1 class-rough among escapees: {out['a1_rough_among_escapees']}"
          f"/{out['n_escapee']}")
    print()
    print("Two-shift ratio ρ_ab/(ρ_a ρ_b) over all 1≤a<b≤A:")
    print(f"  n_pairs={s['n_pairs']}  mean={s['mean']:.4f}  median={s['median']:.4f}"
          f"  p10={s['p10']:.4f}  p90={s['p90']:.4f}  min={s['min']:.4f}  max={s['max']:.4f}")
    print(f"  mean coprime (n={s['n_coprime']}): {s['mean_coprime']:.4f}")
    print(f"  mean gcd>1   (n={s['n_not_coprime']}): {s['mean_not_coprime']:.4f}")
    print(f"  fraction ratio>1.05: {s['frac_ratio_gt_1_05']:.3f}"
          f"  >1.15: {s['frac_ratio_gt_1_15']:.3f}"
          f"  <0.95: {s['frac_ratio_lt_0_95']:.3f}")
    print(f"  mean shared-prime fraction on both-fail:  {out['share_fail_mean']:.4f}")
    print(f"  mean shared-prime fraction on both-rough: {out['share_rough_mean']:.4f}")
    print()
    print("Flagship pairs:")
    for p in out["flagship"]:
        print(fmt_pair(p))
    print()
    print("Histogram of ratios:")
    for h in out["hist"]:
        hi = f"{h['hi']:.2f}" if h["hi"] is not None else "∞"
        print(f"  [{h['lo']:.2f}, {hi:>4s}): {h['n']}")
    print()
    print("ρ_a (class-rough density) for a=1..10:")
    for a in range(1, 11):
        r = out["rho_by_a"][str(a)]
        print(f"  a={a:2d}  n={r['n']:4d}  ρ={r['rho']:.4f}")
    print()

    def dump_c2(name, t):
        print(f"C2 Jacobi (p/11)×(p/19) on {name} (n={t['n']}):")
        print(f"  bias (p/11)={t['bias11']:+.3f}  (p/19)={t['bias19']:+.3f}")
        for key in ("-1,-1", "-1,1", "1,-1", "1,1"):
            c = t["cells"].get(key, 0)
            print(f"  ({key}): {c:4d}  ({c / t['n']:.3f})" if t["n"] else f"  ({key}): {c}")

    dump_c2("all hard primes", out["c2_all"])
    dump_c2("d=1 escapees", out["c2_escapee"])
    dump_c2("covered (some a≤A lands)", out["c2_covered"])

    path = "c4_two_shift_probe.json"
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\nwrote {path}")
