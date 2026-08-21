#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Prime-aligned local Euler factor of T(A).

For each prime q ≡ 3 (mod 4), the slices a ≤ A that q can kill are the
divisors a of (q+1)/4.  Each such slice forbids p ≡ −4a² (mod q).  The
joint local density is 1 − k/(q−1) with k = # distinct forbidden
residues; the product of marginals is (1 − 1/(q−1))^m with m = # slices.
The Euler factor is

    C_euler(A) = ∏_q  (1 − k_q/(q−1)) / (1 − 1/(q−1))^{m_q}.

This is the referee's constant-level overlap (~0.91, predicted flat in A).
It is the shared-prime main-term correction to ∏ ρ_a^{prime}, not the
selection constant Ĉ = S / ∏ ρ_a^{ClassRough}.
"""

from __future__ import annotations

import json
import math
import sys
import time

import numpy as np

HARD = (1, 121, 169, 289, 361, 529)


def spf_numpy(n: int) -> np.ndarray:
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


def divisors_of(fac: list[tuple[int, int]]) -> list[int]:
    divs = [1]
    for p, e in fac:
        more = []
        pe = 1
        for _ in range(e):
            pe *= p
            for d in divs:
                more.append(d * pe)
        divs.extend(more)
    return divs


def hard_avoid_density(q: int, residues: list[int]) -> float:
    """Density among the six hard classes mod 840 of avoiding `residues` mod q.

    Used only for q | 840 (q = 3, 5, 7).  For q coprime to 840 the CRT
    density is exactly 1 − k/(q−1) among units, matching the generic term.
    """
    uniq = sorted(set(residues))
    n_hard = 0
    n_ok = 0
    mod = 840 * q // math.gcd(840, q)
    for r in range(mod):
        if r % 840 not in HARD:
            continue
        if math.gcd(r, mod) != 1:
            continue
        n_hard += 1
        if all(r % q != res for res in uniq):
            n_ok += 1
    return n_ok / n_hard if n_hard else float("nan")


def main(Qmax: int = 10_000_000, Amax: int = 200) -> dict:
    t0 = time.time()
    print(f"euler factor  Qmax={Qmax} Amax={Amax}", flush=True)
    spf = spf_numpy(Qmax + 1)
    primes = [int(p) for p in range(3, Qmax + 1) if spf[p] == p]
    print(f"  {len(primes)} odd primes  ({time.time() - t0:.1f}s)", flush=True)

    As = list(range(5, Amax + 1, 5))
    logC = {A: 0.0 for A in As}
    logC_q = {A: 0.0 for A in As}  # 1/q version
    n_terms = {A: 0 for A in As}
    n_coll = {A: 0 for A in As}
    n_mge2 = {A: 0 for A in As}
    coll_mass = {A: 0 for A in As}  # sum (m − k)
    logC_small = {A: 0.0 for A in As}  # q < 840
    logC_large = {A: 0.0 for A in As}
    zero_hits = {A: [] for A in As}

    # q | 840 specials, recorded separately
    small_q_records: list[dict] = []

    for q in primes:
        if (q + 1) % 4 != 0:
            continue
        M = (q + 1) // 4
        fac = factor_spf(M, spf)
        served = []
        for a in divisors_of(fac):
            if 1 <= a <= Amax:
                served.append((a, (-4 * a * a) % q))
        if not served:
            continue
        served.sort()

        # prefix by A
        by_A: dict[int, list[int]] = {}
        acc_res: list[int] = []
        acc_a: list[int] = []
        si = 0
        for A in As:
            while si < len(served) and served[si][0] <= A:
                acc_a.append(served[si][0])
                acc_res.append(served[si][1])
                si += 1
            by_A[A] = list(acc_res)

        den = q - 1
        for A in As:
            ress = by_A[A]
            m = len(ress)
            if m == 0:
                continue
            k = len(set(ress))
            n_terms[A] += 1
            if m >= 2:
                n_mge2[A] += 1
            if k < m:
                n_coll[A] += 1
                coll_mass[A] += m - k
            if k >= den:
                zero_hits[A].append(q)
                continue
            term = math.log1p(-k / den) - m * math.log1p(-1 / den)
            term_q = math.log1p(-k / q) - m * math.log1p(-1 / q)
            logC[A] += term
            logC_q[A] += term_q
            if q < 840:
                logC_small[A] += term
            else:
                logC_large[A] += term

        if q in (3, 5, 7) or q < 50:
            rec = {
                "q": q,
                "served": [{"a": a, "res": r} for a, r in served if a <= Amax],
            }
            # exact hard-class densities at Amax
            ress_full = [r for a, r in served]
            rec["m"] = len(ress_full)
            rec["k"] = len(set(ress_full))
            rec["generic"] = math.exp(
                math.log1p(-rec["k"] / den) - rec["m"] * math.log1p(-1 / den)
            )
            if q in (3, 5, 7):
                rec["hard_joint"] = hard_avoid_density(q, ress_full)
                margs = [
                    hard_avoid_density(q, [r]) for r in ress_full
                ]
                rec["hard_prod_marg"] = math.prod(margs) if margs else 1.0
                rec["hard_ratio"] = (
                    rec["hard_joint"] / rec["hard_prod_marg"]
                    if rec["hard_prod_marg"]
                    else float("nan")
                )
            small_q_records.append(rec)

    rows = []
    for A in As:
        rows.append({
            "A": A,
            "C_euler": math.exp(logC[A]),
            "C_euler_1q": math.exp(logC_q[A]),
            "C_small": math.exp(logC_small[A]),
            "C_large": math.exp(logC_large[A]),
            "n_terms": n_terms[A],
            "n_mge2": n_mge2[A],
            "n_coll": n_coll[A],
            "coll_mass": coll_mass[A],
            "n_zero": len(zero_hits[A]),
        })

    out = {
        "Qmax": Qmax,
        "Amax": Amax,
        "elapsed_s": time.time() - t0,
        "rows": rows,
        "small_q": small_q_records,
        "zero_hits": {str(A): v[:20] for A, v in zero_hits.items() if v},
    }
    print("\n  A    C_euler   C_1/q    small     large    coll  m≥2")
    for r in rows:
        if r["A"] % 20 == 0 or r["A"] in (5, 40, 80, 200):
            print(
                f"  {r['A']:3d}  {r['C_euler']:.5f}  {r['C_euler_1q']:.5f}  "
                f"{r['C_small']:.5f}  {r['C_large']:.5f}  "
                f"{r['n_coll']:4d}  {r['n_mge2']:5d}",
                flush=True,
            )
    out["collisions"] = collision_check(Amax)
    print(
        f"  residue collisions a<b≤{Amax}: {len(out['collisions'])}",
        flush=True,
    )
    print(f"\n  elapsed {out['elapsed_s']:.1f}s", flush=True)
    return out


def collision_check(Amax: int) -> list[dict]:
    """Any colliding q must divide a²−b² ≤ Amax². Exhaustive for fixed Amax."""
    Nmax = Amax * Amax
    sv = bytearray(b"\x01") * (Nmax + 1)
    sv[0:2] = b"\x00\x00"
    r = int(Nmax**0.5)
    for p in range(2, r + 1):
        if sv[p]:
            sv[p * p : Nmax + 1 : p] = b"\x00" * ((Nmax - p * p) // p + 1)
    primes = [i for i in range(2, Nmax + 1) if sv[i]]

    def factor(n: int) -> list[int]:
        fac = []
        x = n
        for p in primes:
            if p * p > x:
                break
            if x % p == 0:
                fac.append(p)
                while x % p == 0:
                    x //= p
        if x > 1:
            fac.append(x)
        return fac

    hits = []
    for a in range(1, Amax + 1):
        for b in range(a + 1, Amax + 1):
            for q in factor(abs(a * a - b * b)):
                if q == 2 or (q + 1) % 4:
                    continue
                if (q + 1) % (4 * a) == 0 and (q + 1) % (4 * b) == 0:
                    hits.append({"a": a, "b": b, "q": q})
    return hits


if __name__ == "__main__":
    Qmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
    Amax = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    out = main(Qmax, Amax)
    path = f"c4_euler_factor_Q{Qmax}_A{Amax}.json"
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"wrote {path}")
