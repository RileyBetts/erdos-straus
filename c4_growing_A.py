#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Growing-A scan at x = 10^9.

Question: does cond(a) = P(R_a | prefix) stay at 1 past a = 80, or does
mean(e(a)−1) finally fall?  That is the remaining empirical kill fork.

Reuses ClassRough (any aligned divisor) from c4_S_xscan.py.
Amax = 200, Xmax = 10^9, multiprocessing over hard primes.
"""

from __future__ import annotations

import json
import math
import multiprocessing as mp
import sys
import time

from c4_S_xscan import (
    factor_spf,
    has_aligned_divisor,
    sieve_hard_primes,
    spf_numpy,
)

# filled after SPF; workers inherit via fork
_G: dict = {}


def _factor_range(span: tuple[int, int]) -> tuple[int, bytes]:
    i0, i1 = span
    hard = _G["hard"]
    spf = _G["spf"]
    Amax = _G["Amax"]
    mods = _G["mods"]
    nloc = i1 - i0
    bits = bytearray((nloc * Amax + 7) // 8)
    for i in range(i0, i1):
        p = int(hard[i])
        li = i - i0
        for a in range(1, Amax + 1):
            fac = factor_spf(p + 4 * a * a, spf)
            if not has_aligned_divisor(fac, mods[a]):
                k = li * Amax + (a - 1)
                bits[k >> 3] |= 1 << (k & 7)
    return i0, bytes(bits)


def main(Xmax: int = 1_000_000_000, Amax: int = 200) -> dict:
    t0 = time.time()
    maxN = Xmax + 4 * Amax * Amax
    nworkers = min(4, mp.cpu_count() or 1)
    print(f"growing-A  Xmax={Xmax} Amax={Amax}  workers={nworkers}", flush=True)
    hard = sieve_hard_primes(Xmax)
    print(f"  {len(hard)} hard  ({time.time()-t0:.1f}s)", flush=True)
    spf = spf_numpy(maxN)
    print(f"  SPF done  ({time.time()-t0:.1f}s)", flush=True)

    n = len(hard)
    row_bytes = Amax // 8
    if Amax % 8 != 0:
        raise ValueError("Amax must be a multiple of 8 for packed rows")
    _G["hard"] = hard
    _G["spf"] = spf
    _G["Amax"] = Amax
    _G["mods"] = [4 * a for a in range(Amax + 1)]

    packed = bytearray(n * row_bytes)
    chunk = max(20_000, n // (nworkers * 8))
    spans = [(i, min(i + chunk, n)) for i in range(0, n, chunk)]
    done = 0
    with mp.Pool(nworkers) as pool:
        for i0, blob in pool.imap_unordered(_factor_range, spans):
            nloc = len(blob) * 8 // Amax
            packed[i0 * row_bytes : (i0 + nloc) * row_bytes] = blob
            done += nloc
            print(f"  factored {done}/{n}  ({time.time()-t0:.1f}s)", flush=True)
    print(f"  all slots  ({time.time()-t0:.1f}s)", flush=True)
    del spf
    _G.clear()

    def get(i: int, a: int) -> bool:
        k = i * Amax + (a - 1)
        return bool(packed[k >> 3] & (1 << (k & 7)))

    rho = [0.0] * (Amax + 1)
    for a in range(1, Amax + 1):
        c = 0
        for i in range(n):
            if get(i, a):
                c += 1
        rho[a] = c / n

    n_alive = n
    alive = [True] * n
    enrich = []
    S_prev = 1.0
    C = 1.0
    survivors_at = {}
    for a in range(1, Amax + 1):
        for i in range(n):
            if alive[i] and not get(i, a):
                alive[i] = False
                n_alive -= 1
        Sa = n_alive / n
        cond = Sa / S_prev if S_prev > 0 else float("nan")
        e = cond / rho[a] if rho[a] > 0 else float("nan")
        C *= e if e == e else 1.0
        rec = {
            "a": a,
            "S": Sa,
            "n_alive": n_alive,
            "rho": rho[a],
            "cond": cond,
            "e": e,
            "C_hat": C,
            "logC_over_A": (math.log(C) / a) if C > 0 else None,
        }
        enrich.append(rec)
        if a in {80, 100, 120, 140, 160, 180, 200} or n_alive <= 20:
            survivors_at[str(a)] = [int(hard[i]) for i in range(n) if alive[i]]
        S_prev = Sa
        if a % 10 == 0 or a in {1, 2, 5, 80, 81}:
            print(
                f"  a={a:3d}  n={n_alive:6d}  S={Sa:.4e}  ρ={rho[a]:.4f}  "
                f"cond={cond:.4f}  e={e:.4f}  Ĉ={C:.3f}  logĈ/A={rec['logC_over_A']:.4f}",
                flush=True,
            )
        if n_alive == 0:
            print(f"  box empty at a={a}", flush=True)
            break

    bands = []
    for lo, hi in [(1, 10), (11, 20), (21, 40), (41, 80), (81, 120), (121, 160), (161, 200)]:
        sl = [r for r in enrich if lo <= r["a"] <= hi]
        if not sl:
            continue
        bands.append({
            "lo": lo,
            "hi": hi,
            "mean_e_m1": sum(r["e"] - 1 for r in sl) / len(sl),
            "mean_cond": sum(r["cond"] for r in sl) / len(sl),
            "n_end": sl[-1]["n_alive"],
        })

    out = {
        "Xmax": Xmax,
        "Amax": Amax,
        "n_hard": n,
        "elapsed_s": time.time() - t0,
        "enrich": enrich,
        "bands": bands,
        "n_survivors": {r["a"]: r["n_alive"] for r in enrich},
        "survivors_at": {k: v for k, v in survivors_at.items() if len(v) <= 50},
        "survivor_counts": {k: len(v) for k, v in survivors_at.items()},
    }
    print("\nbands:")
    for b in bands:
        print(
            f"  a={b['lo']:3d}-{b['hi']:3d}  mean(e-1)={b['mean_e_m1']:+.4f}  "
            f"mean cond={b['mean_cond']:.4f}  n_end={b['n_end']}"
        )
    return out


if __name__ == "__main__":
    Xmax = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000_000
    Amax = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    out = main(Xmax, Amax)
    path = f"c4_growing_A_X{Xmax}_A{Amax}.json"
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"\nwrote {path}  ({out['elapsed_s']:.1f}s)")
