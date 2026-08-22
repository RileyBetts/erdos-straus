#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Why residual Δ/μ rises, and whether any T(A) is two-log on both sides.

Reuses the covering construction in e_power_fibre_moments.py.
Not a proof of H1 or H2. Do not inhabit the Lean hypotheses from this.
"""

from __future__ import annotations

import json
import math
import os
import random
import time
from collections import defaultdict

from e_power_fibre_moments import (
    all_rho,
    build_events,
    classify,
    factor,
    hub_modulus,
    hub_valuation,
    sample_rho,
    split_q,
)

HERE = os.path.dirname(os.path.abspath(__file__))


def smallest_prime(n: int) -> int:
    if n <= 1:
        return 0
    if n % 2 == 0:
        return 2
    p = 3
    while p * p <= n:
        if n % p == 0:
            return p
        p += 2
    return n


def residual_of(
    events: list[tuple[int, int]], T: int, rho: dict[int, int]
) -> list[tuple[int, int]] | None:
    residual: list[tuple[int, int]] = []
    for q, r in events:
        cls = classify(q, r, T, rho)
        if cls == "hub_forced":
            return None
        if isinstance(cls, int):
            residual.append((cls, r % cls))
    return residual


def fibre_diag(residual: list[tuple[int, int]]) -> dict:
    n = len(residual)
    mu = sum(1.0 / ell for ell, _r in residual)
    delta = 0.0
    n_dep = 0
    n_compat = 0
    by_p: dict[int, float] = defaultdict(float)
    hits: dict[int, int] = defaultdict(int)
    mass: dict[int, float] = defaultdict(float)
    for ell, _r in residual:
        for p in factor(ell):
            hits[p] += 1
            mass[p] += 1.0 / ell
    for i in range(n):
        ei, ri = residual[i]
        for j in range(i + 1, n):
            ej, rj = residual[j]
            g = math.gcd(ei, ej)
            if g <= 1:
                continue
            n_dep += 1
            if ri % g != rj % g:
                continue
            n_compat += 1
            pij = 1.0 / math.lcm(ei, ej)
            delta += pij
            by_p[smallest_prime(g)] += pij
    den = mu + 2.0 * delta
    titu = (mu * mu / den) if den > 0 else 0.0
    top = sorted(by_p.items(), key=lambda kv: -kv[1])[:6]
    cover = sorted(hits.items(), key=lambda kv: -kv[1])[:6]
    return {
        "n_residual": n,
        "mu": mu,
        "Delta": delta,
        "delta_over_mu": (delta / mu) if mu else 0.0,
        "janson_titu": titu,
        "n_dep_pairs": n_dep,
        "n_compat_pairs": n_compat,
        "delta_by_minprime": {str(p): v for p, v in top},
        "residual_prime_hits": {str(p): c for p, c in cover},
        "residual_prime_mass": {
            str(p): mass[p] for p, _c in cover
        },
    }


def census(A: int, T: int) -> dict:
    """Unconditional T-rough parts: no hub residue."""
    evs = build_events(A)
    n_forced = 0
    n_res = 0
    mu_res = 0.0
    hits: dict[int, int] = defaultdict(int)
    mass: dict[int, float] = defaultdict(float)
    for q, _r in evs:
        _s, ell = split_q(q, T)
        if ell <= 1:
            n_forced += 1
            continue
        n_res += 1
        mu_res += 1.0 / ell
        for p in factor(ell):
            hits[p] += 1
            mass[p] += 1.0 / ell
    top = sorted(hits.items(), key=lambda kv: -kv[1])[:8]
    return {
        "A": A,
        "T": T,
        "n_events": len(evs),
        "n_hub_forced": n_forced,
        "n_residual_type": n_res,
        "mu_rough": mu_res,
        "mu_rough_over_logA2": mu_res / (math.log(A) ** 2) if A > 1 else None,
        "top_residual_primes": [
            {
                "p": p,
                "hits": c,
                "hit_frac": c / n_res if n_res else 0.0,
                "mass": mass[p],
                "mass_frac": mass[p] / mu_res if mu_res else 0.0,
            }
            for p, c in top
        ],
    }


def schedule_row(A: int, T: int, samples: int, seed: int) -> dict:
    t0 = time.time()
    evs = build_events(A)
    val = hub_valuation(evs, T)
    H = hub_modulus(val)
    rng = random.Random(seed)
    exhaustive = 0 < H <= 120
    rhos = all_rho(val) if exhaustive else [sample_rho(val, rng) for _ in range(samples)]
    titus: list[float] = []
    mus: list[float] = []
    deltas: list[float] = []
    worst: dict | None = None
    n_kill = 0
    for rho in rhos:
        res = residual_of(evs, T, rho)
        if res is None:
            n_kill += 1
            continue
        d = fibre_diag(res)
        titus.append(d["janson_titu"])
        mus.append(d["mu"])
        deltas.append(d["Delta"])
        if worst is None or d["janson_titu"] < worst["janson_titu"]:
            worst = d
    n_try = len(rhos)
    n_surv = n_try - n_kill
    p_hub = n_surv / n_try if n_try else 0.0
    k = math.log2(A)
    k2 = k * k
    logA2 = math.log(A) ** 2
    titu_min = min(titus) if titus else 0.0
    h1 = -math.log(p_hub) if 0 < p_hub < 1 else (float("inf") if p_hub == 0 else 0.0)
    return {
        "A": A,
        "T": T,
        "k": k,
        "k2": k2,
        "H": H,
        "exhaustive": exhaustive,
        "tried": n_try,
        "P_hub": p_hub,
        "h1_neglog": h1 if math.isfinite(h1) else None,
        "h1_over_k2": (h1 / k2) if math.isfinite(h1) and k2 else None,
        "titu_min": titu_min,
        "titu_mean": (sum(titus) / len(titus)) if titus else 0.0,
        "titu_min_over_k2": titu_min / k2 if k2 else None,
        "titu_min_over_logA2": titu_min / logA2 if logA2 else None,
        "mu_min": min(mus) if mus else 0.0,
        "Delta_at_worst": None if worst is None else worst["Delta"],
        "delta_over_mu_worst": None if worst is None else worst["delta_over_mu"],
        "worst": worst,
        "seconds": time.time() - t0,
    }


def main() -> None:
    As = [int(x) for x in os.environ.get("DIAG_AS", "8,16,32").split(",")]
    Ts = [int(x) for x in os.environ.get("DIAG_TS", "3,5,7,11").split(",")]
    samples = int(os.environ.get("DIAG_SAMPLES", "30"))
    seed = int(os.environ.get("DIAG_SEED", "1"))

    print("unconditional residual-prime census", flush=True)
    cens: list[dict] = []
    for A in As:
        for T in Ts:
            row = census(A, T)
            cens.append(row)
            tops = ", ".join(
                f"p={t['p']}({t['hit_frac']:.2f})"
                for t in row["top_residual_primes"][:4]
            )
            print(
                f"  A={A} T={T} forced={row['n_hub_forced']} "
                f"rough={row['n_residual_type']} μ_rough={row['mu_rough']:.3f} "
                f"{tops}",
                flush=True,
            )

    print("T(A) fibre grid (Titu min vs k², −log P vs k²)", flush=True)
    grid: list[dict] = []
    for A in As:
        for T in Ts:
            print(f"A={A} T={T}...", flush=True)
            row = schedule_row(A, T, samples, seed)
            grid.append(row)
            h1 = row["h1_over_k2"]
            h1s = f"{h1:.4f}" if isinstance(h1, float) else str(h1)
            print(
                f"  P={row['P_hub']:.4f}  −logP/k²={h1s}  "
                f"titu_min={row['titu_min']:.3f}  "
                f"titu/k²={row['titu_min_over_k2']}  "
                f"Δ/μ={row['delta_over_mu_worst']}  "
                f"{'exact' if row['exhaustive'] else 'mc'} H={row['H']}  "
                f"{row['seconds']:.1f}s",
                flush=True,
            )

    out = os.path.join(HERE, "e_power_residual_primes.json")
    with open(out, "w") as f:
        json.dump({"census": cens, "grid": grid}, f, indent=2)
    print(f"wrote {out}", flush=True)


if __name__ == "__main__":
    main()
