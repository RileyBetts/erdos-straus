#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Revival attempt: largest-prime residual, cofactor hub.

T-smooth q is hub-forced (ell = 1), as before. Otherwise ell = P(q)^v
and s = q/ell goes into the hub. Residual events are prime powers, so
Δ is only inside the same largest prime.

Not a proof. Do not inhabit H1/H2.
"""

from __future__ import annotations

import json
import math
import os
import random
import time
from collections import defaultdict

from e_power_fibre_moments import all_rho, build_events, factor, sample_rho
from e_power_residual_primes import smallest_prime

HERE = os.path.dirname(os.path.abspath(__file__))


def split_lp(q: int, T: int) -> tuple[int, int]:
    fac = factor(q)
    if not fac:
        return q, 1
    if all(p <= T for p in fac):
        return q, 1
    p = max(fac)
    ell = p ** fac[p]
    return q // ell, ell


def hub_val_lp(events: list[tuple[int, int]], T: int) -> dict[int, int]:
    val: dict[int, int] = {}
    for q, _r in events:
        s, _ell = split_lp(q, T)
        for p, k in factor(s).items():
            val[p] = max(val.get(p, 0), k)
    return val


def hub_mod(val: dict[int, int]) -> int:
    H = 1
    for p, k in val.items():
        H *= p**k
    return H


def compatible(s: int, r: int, rho: dict[int, int]) -> bool:
    if s == 0:
        return False
    if s == 1:
        return True
    for p, k in factor(s).items():
        pk = p**k
        if rho.get(p, 0) % pk != r % pk:
            return False
    return True


def residual_lp(
    events: list[tuple[int, int]], T: int, rho: dict[int, int]
) -> list[tuple[int, int]] | None:
    residual: list[tuple[int, int]] = []
    for q, r in events:
        s, ell = split_lp(q, T)
        if not compatible(s, r, rho):
            continue
        if ell <= 1:
            return None
        residual.append((ell, r % ell))
    return residual


def titu_of(residual: list[tuple[int, int]]) -> dict:
    mu = sum(1.0 / ell for ell, _r in residual)
    buckets: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for ell, r in residual:
        buckets[smallest_prime(ell)].append((ell, r))
    delta = 0.0
    n_dep = 0
    n_compat = 0
    by_p: dict[int, float] = defaultdict(float)
    for p, items in buckets.items():
        m = len(items)
        n_dep += m * (m - 1) // 2
        for i in range(m):
            ei, ri = items[i]
            for j in range(i + 1, m):
                ej, rj = items[j]
                g = math.gcd(ei, ej)
                if ri % g != rj % g:
                    continue
                n_compat += 1
                pij = 1.0 / math.lcm(ei, ej)
                delta += pij
                by_p[p] += pij
    den = mu + 2.0 * delta
    titu = (mu * mu / den) if den > 0 else 0.0
    top = sorted(by_p.items(), key=lambda kv: -kv[1])[:5]
    return {
        "n_residual": len(residual),
        "mu": mu,
        "Delta": delta,
        "delta_over_mu": (delta / mu) if mu else 0.0,
        "janson_titu": titu,
        "n_dep_pairs": n_dep,
        "n_compat_pairs": n_compat,
        "n_primes": len(buckets),
        "largest_bucket": max((len(v) for v in buckets.values()), default=0),
        "delta_by_p": {str(p): v for p, v in top},
    }


def scan(A: int, T: int, samples: int, seed: int) -> dict:
    t0 = time.time()
    evs = build_events(A)
    val = hub_val_lp(evs, T)
    H = hub_mod(val)
    rng = random.Random(seed)
    exhaustive = 0 < H <= 120
    rhos = all_rho(val) if exhaustive else [sample_rho(val, rng) for _ in range(samples)]
    titus: list[float] = []
    worst: dict | None = None
    n_kill = 0
    for rho in rhos:
        res = residual_lp(evs, T, rho)
        if res is None:
            n_kill += 1
            continue
        d = titu_of(res)
        titus.append(d["janson_titu"])
        if worst is None or d["janson_titu"] < worst["janson_titu"]:
            worst = d
    n_try = len(rhos)
    n_surv = n_try - n_kill
    p_hub = n_surv / n_try if n_try else 0.0
    k = math.log2(A)
    k2 = k * k
    titu_min = min(titus) if titus else 0.0
    h1 = -math.log(p_hub) if 0 < p_hub < 1 else (float("inf") if p_hub == 0 else 0.0)
    return {
        "split": "largest-prime residual, cofactor hub",
        "A": A,
        "T": T,
        "k2": k2,
        "H": H,
        "hub_omega": len(val),
        "exhaustive": exhaustive,
        "tried": n_try,
        "P_hub": p_hub,
        "h1_over_k2": (h1 / k2) if math.isfinite(h1) and k2 else None,
        "titu_min": titu_min,
        "titu_mean": (sum(titus) / len(titus)) if titus else 0.0,
        "titu_min_over_k2": titu_min / k2 if k2 else None,
        "pass_h1": bool(isinstance(h1, float) and math.isfinite(h1) and h1 / k2 >= 0.3),
        "pass_h2": bool(titu_min / k2 >= 0.3) if k2 else False,
        "worst": worst,
        "seconds": time.time() - t0,
    }


def main() -> None:
    As = [int(x) for x in os.environ.get("LP_AS", "8,16,32").split(",")]
    Ts = [int(x) for x in os.environ.get("LP_TS", "3,5,7").split(",")]
    samples = int(os.environ.get("LP_SAMPLES", "40"))
    seed = int(os.environ.get("LP_SEED", "1"))
    rows: list[dict] = []
    print("largest-prime residual revival table", flush=True)
    for A in As:
        for T in Ts:
            print(f"A={A} T={T}...", flush=True)
            row = scan(A, T, samples, seed)
            rows.append(row)
            h1 = row["h1_over_k2"]
            h1s = f"{h1:.4f}" if isinstance(h1, float) else str(h1)
            print(
                f"  P={row['P_hub']:.4f}  −logP/k²={h1s}  "
                f"titu_min={row['titu_min']:.3f}  titu/k²={row['titu_min_over_k2']}  "
                f"H1={row['pass_h1']} H2={row['pass_h2']}  "
                f"H={row['H']} ω={row['hub_omega']}  {row['seconds']:.1f}s",
                flush=True,
            )
    out = os.path.join(HERE, "e_power_lp_split.json")
    with open(out, "w") as f:
        json.dump({"rows": rows}, f, indent=2)
    print(f"wrote {out}", flush=True)


if __name__ == "__main__":
    main()
