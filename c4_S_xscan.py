#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""x-scan of S(A, x) at fixed A, plus the conditional enrichment profile.

ClassRough: p+4a² has no divisor q≥3 with q ≡ −1 (mod 4a).
e(a) = P(R_a | R_1,…,R_{a−1}) / ρ_a.

Default Xmax = 10^8.  Xmax = 10^9 is the extra-decade discriminator
(lever arm lnln x from 2.63 to 3.04 on x≥10^6).
"""

from __future__ import annotations

import json
import math
import sys
import time
from array import array

import numpy as np

HARD = {1, 121, 169, 289, 361, 529}


def sieve_primes(n: int) -> list[int]:
    sv = bytearray(b"\x01") * (n + 1)
    sv[0:2] = b"\x00\x00"
    r = int(n**0.5)
    for p in range(2, r + 1):
        if sv[p]:
            start = p * p
            sv[start : n + 1 : p] = b"\x00" * ((n - start) // p + 1)
    return [i for i in range(2, n + 1) if sv[i]]


def sieve_hard_primes(n: int) -> list[int]:
    """Primes p≤n in the six hard classes mod 840. Segmented; O(√n) memory."""
    r = int(n**0.5)
    base = sieve_primes(r)
    hard = [p for p in base if p % 840 in HARD]
    SEG = 2_000_000
    for start in range(r + 1, n + 1, SEG):
        end = min(start + SEG - 1, n)
        length = end - start + 1
        seg = np.ones(length, dtype=np.uint8)
        for p in base:
            first = ((start + p - 1) // p) * p
            pp = p * p
            if first < pp:
                first = pp
            if first > end:
                continue
            seg[first - start : length : p] = 0
        idx = np.nonzero(seg)[0]
        for i in idx:
            p = start + int(i)
            if p % 840 in HARD:
                hard.append(p)
    return hard


def spf_numpy(n: int) -> np.ndarray:
    """Smallest-prime-factor table as uint32. ~4n bytes."""
    spf = np.arange(n + 1, dtype=np.uint32)
    r = int(n**0.5)
    for p in range(2, r + 1):
        if spf[p] == p:
            spf[p * p :: p] = np.minimum(spf[p * p :: p], np.uint32(p))
    return spf


def factor_spf(n: int, spf) -> list[tuple[int, int]]:
    fac: list[tuple[int, int]] = []
    while n > 1:
        p = int(spf[n])
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        fac.append((p, e))
    return fac


def has_aligned_divisor(fac: list[tuple[int, int]], modulus: int) -> bool:
    """True iff some divisor q ≥ 3 of N is ≡ −1 (mod modulus).

    This is Lean `ClassRough`: no aligned divisor, composite or prime.
    Strictly stronger than 'no aligned prime factor'.
    """
    divs = [1]
    for p, e in fac:
        more = []
        pe = 1
        for _ in range(e):
            pe *= p
            for d in divs:
                q = d * pe
                if q >= 3 and (q + 1) % modulus == 0:
                    return True
                more.append(q)
        divs.extend(more)
    return False


def has_aligned_prime(fac: list[tuple[int, int]], modulus: int) -> bool:
    """True iff some prime factor q ≥ 3 of N is ≡ −1 (mod modulus)."""
    for q, _e in fac:
        if q >= 3 and (q + 1) % modulus == 0:
            return True
    return False


def euler_phi(n: int) -> int:
    r, x, i = n, n, 2
    while i * i <= x:
        if x % i == 0:
            while x % i == 0:
                x //= i
            r = r // i * (i - 1)
        i += 1
    if x > 1:
        r = r // x * (x - 1)
    return r


def main(Xmax: int = 100_000_000, Amax: int = 80) -> dict:
    t0 = time.time()
    maxN = Xmax + 4 * Amax * Amax
    print(f"sieving hard primes ≤ {Xmax} and SPF ≤ {maxN} …", flush=True)
    hard = sieve_hard_primes(Xmax)
    print(f"  {len(hard)} hard  ({time.time()-t0:.1f}s)", flush=True)
    spf = spf_numpy(maxN)
    print(f"  SPF done  ({time.time()-t0:.1f}s)", flush=True)

    n = len(hard)
    nbytes = (n * Amax + 7) // 8
    bits = bytearray(nbytes)
    pbits = bytearray(nbytes)

    def _set(buf: bytearray, i: int, a: int) -> None:
        k = i * Amax + (a - 1)
        buf[k >> 3] |= 1 << (k & 7)

    def _get(buf: bytearray, i: int, a: int) -> bool:
        k = i * Amax + (a - 1)
        return bool(buf[k >> 3] & (1 << (k & 7)))

    mods = [4 * a for a in range(Amax + 1)]
    step = 50_000 if n > 400_000 else 20_000
    for i, p in enumerate(hard):
        if i % step == 0 and i:
            print(f"  factored {i}/{n}  ({time.time()-t0:.1f}s)", flush=True)
        for a in range(1, Amax + 1):
            N = p + 4 * a * a
            fac = factor_spf(N, spf)
            if not has_aligned_divisor(fac, mods[a]):
                _set(bits, i, a)
            if not has_aligned_prime(fac, mods[a]):
                _set(pbits, i, a)
    print(f"  all slots  ({time.time()-t0:.1f}s)", flush=True)
    del spf

    # prefix: still_A[i] = largest A such that all a≤A are rough (0 if a=1 fails)
    still = [0] * n
    for i in range(n):
        A = 0
        for a in range(1, Amax + 1):
            if not _get(bits, i, a):
                break
            A = a
        still[i] = A

    xs = [100_000, 200_000, 500_000, 1_000_000, 2_000_000, 5_000_000,
          10_000_000, 20_000_000, 50_000_000, 100_000_000,
          200_000_000, 500_000_000, 1_000_000_000]
    xs = [x for x in xs if x <= Xmax]

    phi = [0.0] + [1.0 / euler_phi(4 * a) for a in range(1, Amax + 1)]
    beta_th = {A: sum(phi[1 : A + 1]) for A in (40, 80, Amax)}

    As = [40, 80]
    scan = {A: [] for A in As}
    by_x: list[dict] = []

    j = 0
    for x in xs:
        while j < n and hard[j] <= x:
            j += 1
        nh = j
        if nh == 0:
            continue
        rho = [0.0] * (Amax + 1)
        rho_p = [0.0] * (Amax + 1)
        for a in range(1, Amax + 1):
            c = p = 0
            for i in range(nh):
                if _get(bits, i, a):
                    c += 1
                if _get(pbits, i, a):
                    p += 1
            rho[a] = c / nh
            rho_p[a] = p / nh

        n_alive = nh
        alive = [True] * nh
        enrich_row = []
        S_prev = 1.0
        for a in range(1, Amax + 1):
            for i in range(nh):
                if alive[i] and not _get(bits, i, a):
                    alive[i] = False
                    n_alive -= 1
            Sa = n_alive / nh
            cond = Sa / S_prev if S_prev > 0 else float("nan")
            e = cond / rho[a] if rho[a] > 0 else float("nan")
            enrich_row.append({
                "a": a,
                "S": Sa,
                "n_alive": n_alive,
                "rho": rho[a],
                "rho_prime": rho_p[a],
                "cond": cond,
                "e": e,
            })
            S_prev = Sa

        def log_prod(vals: list[float], A: int) -> float:
            s = 0.0
            for a in range(1, A + 1):
                if vals[a] > 0:
                    s += math.log(vals[a])
            return s

        L = math.log(math.log(x))
        row_scan = {
            "x": x,
            "n_hard": nh,
            "loglog_x": L,
        }
        for A in As:
            n_esc = sum(1 for i in range(nh) if still[i] >= A)
            s = n_esc / nh
            lp = log_prod(rho, A)
            lp_p = log_prod(rho_p, A)
            prod = math.exp(lp)
            chat = s / prod if prod > 0 else float("nan")
            rec = {
                **row_scan,
                "n_esc": n_esc,
                "S": s,
                "prod": prod,
                "prod_prime": math.exp(lp_p),
                "C_hat": chat,
                "log_S": math.log(s) if s > 0 else None,
                "log_prod": lp,
                "log_prod_prime": lp_p,
                "log_n_esc": math.log(n_esc) if n_esc > 0 else None,
                "log10_x": math.log10(x),
            }
            scan[A].append(rec)

        def mean_em1(lo: int, hi: int) -> float:
            xs_ = [enrich_row[a - 1]["e"] - 1.0 for a in range(lo, hi + 1)
                   if math.isfinite(enrich_row[a - 1]["e"])]
            return sum(xs_) / len(xs_) if xs_ else float("nan")

        by_x.append({
            "x": x,
            "n_hard": nh,
            "loglog_x": L,
            "rho": rho[1:],
            "rho_prime": rho_p[1:],
            "e": [r["e"] for r in enrich_row],
            "n_alive": [r["n_alive"] for r in enrich_row],
            "mean_e_m1": {
                "a1_80": mean_em1(1, 80),
                "a10_80": mean_em1(10, 80),
                "a1_20": mean_em1(1, 20),
                "a1_40": mean_em1(1, 40),
            },
        })

    enrich = [
        {
            "a": a,
            "S": by_x[-1]["n_alive"][a - 1] / n if n else 0.0,
            "n_alive": by_x[-1]["n_alive"][a - 1],
            "rho": by_x[-1]["rho"][a - 1],
            "cond": None,
            "e": by_x[-1]["e"][a - 1],
        }
        for a in range(1, Amax + 1)
    ]
    # restore cond at Xmax from e * rho
    for rec in enrich:
        rec["cond"] = rec["e"] * rec["rho"] if rec["rho"] else float("nan")

    return {
        "Xmax": Xmax,
        "Amax": Amax,
        "n_hard_max": n,
        "elapsed_s": time.time() - t0,
        "convention": {
            "ClassRough": (
                "no divisor q≥3 of p+4a² with q ≡ −1 (mod 4a); "
                "Lean ClassRough, composites included"
            ),
            "rho_a": "P(ClassRough(p,a) | p≤x hard)",
            "e_a": "P(R_a | R_1,…,R_{a-1}) / ρ_a = [S(a)/S(a-1)] / ρ_a, S(0)=1",
            "beta_th_phi": {str(A): beta_th[A] for A in (40, 80)},
            "note": (
                "Mertens/LSD prime-aligned exponent per slice is 1/φ(4a). "
                "Composite aligned divisors are extra; they may affect the "
                "constant or, if unbounded, the exponent."
            ),
        },
        "scan": {str(A): scan[A] for A in As},
        "by_x": by_x,
        "enrich": enrich,
    }


def show(out: dict) -> None:
    print(f"\nXmax={out['Xmax']}  hard={out['n_hard_max']}  {out['elapsed_s']:.1f}s")
    print("convention:", out.get("convention", {}).get("ClassRough", ""))
    print("e_a:", out.get("convention", {}).get("e_a", ""))
    print("β_th = Σ 1/φ(4a):", out.get("convention", {}).get("beta_th_phi"))
    for A, rows in out["scan"].items():
        print(f"\nA={A}   x          n_hard  n_esc     S         ∏ρ        Ĉ      log S   ln ln x")
        for r in rows:
            ls = f"{r['log_S']:7.3f}" if r["log_S"] is not None else "   -inf"
            print(f"  {r['x']:11d}  {r['n_hard']:6d}  {r['n_esc']:5d}  "
                  f"{r['S']:.4e}  {r['prod']:.4e}  {r['C_hat']:6.3f}  {ls}  {r['loglog_x']:.4f}")
    if "by_x" in out:
        print("\nmean(e(a)−1) by x:")
        print(f"  {'x':>11}  {'L':>6}  {'a=1..20':>8}  {'a=1..40':>8}  {'a=10..80':>8}  {'a=1..80':>8}")
        for r in out["by_x"]:
            m = r["mean_e_m1"]
            print(f"  {r['x']:11d}  {r['loglog_x']:6.3f}  {m['a1_20']:8.4f}  "
                  f"{m['a1_40']:8.4f}  {m['a10_80']:8.4f}  {m['a1_80']:8.4f}")
    print("\nenrichment e(a) at Xmax (selected a):")
    for e in out["enrich"]:
        if e["a"] in {1, 2, 3, 5, 10, 15, 20, 30, 40, 50, 60, 80} or e["a"] % 10 == 0:
            print(f"  a={e['a']:3d}  S={e['S']:.4e}  ρ={e['rho']:.4f}  "
                  f"cond={e['cond']:.4f}  e={e['e']:.3f}")


if __name__ == "__main__":
    Xmax = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000_000
    Amax = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    out = main(Xmax, Amax)
    show(out)
    path = f"c4_S_xscan_X{Xmax}.json"
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"\nwrote {path}")
