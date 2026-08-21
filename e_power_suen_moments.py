#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Suen second-moment gates for E_power, as A grows.

Plan §4e cited Δ ≪ μ²/T, δ ≪ μ/T at A = 24–48. E_power uses that bound at
A = exp(c √log x). This script checks whether

    R_Δ = T · Σ_{ℓ>T} μ_ℓ² / μ²
    R_δ = T · δ_ub / μ

stay O(1) as A grows on the Lean covering cells (q = 4acd − 1, d ≤ 5),
and records the same ratios on the plan-(a,d,m) family for comparison
with the cited T-scaling at A = 48.

μ_ℓ = total cell mass whose tracked integer is divisible by the prime ℓ.
δ_ub(cell) = Σ_{ℓ|n, ℓ>T} μ_ℓ  (union bound on neighbour mass; valid
upper bound for Suen δ). Do not densify covering. Do not run x = 10^10.

For A up to a few thousand, use e_power_suen_moments_large.py (Lean
family only, two-pass, no cell storage).
"""

from __future__ import annotations

import json
import math
import os
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def spf_numpy(n: int) -> np.ndarray:
    spf = np.arange(n + 1, dtype=np.uint32)
    r = int(n**0.5)
    for p in range(2, r + 1):
        if spf[p] == p:
            spf[p * p :: p] = np.minimum(spf[p * p :: p], np.uint32(p))
    return spf


def all_primes_of(n: int, spf: np.ndarray) -> list[int]:
    out: list[int] = []
    while n > 1:
        p = int(spf[n])
        out.append(p)
        while n % p == 0:
            n //= p
    return out


def harmonic(n: int) -> float:
    return sum(1.0 / k for k in range(1, n + 1))


def run_family(name: str, cells: list[tuple[float, list[int]]], T: int) -> dict:
    """cells: (mass, all prime factors of the tracked integer)."""
    mu = 0.0
    mu_rem = 0.0
    mu_ell: dict[int, float] = {}
    large: list[tuple[float, list[int]]] = []
    for mass, ps in cells:
        mu += mass
        lps = [p for p in dict.fromkeys(ps) if p > T]
        large.append((mass, lps))
        if lps:
            mu_rem += mass
            for p in lps:
                mu_ell[p] = mu_ell.get(p, 0.0) + mass

    delta_bound = sum(v * v for v in mu_ell.values())
    delta_ub = 0.0
    worst_omega = 0
    for mass, lps in large:
        if not lps:
            continue
        worst_omega = max(worst_omega, len(lps))
        s = sum(mu_ell[p] for p in lps)
        if s > delta_ub:
            delta_ub = s

    if mu <= 0:
        return {"family": name, "T": T, "mu": 0.0}
    r_delta = T * delta_bound / (mu * mu)
    r_delta_rem = T * delta_bound / (mu_rem * mu_rem) if mu_rem > 0 else None
    suen_loss = None
    if delta_ub > 0:
        suen_loss = delta_bound * math.exp(2.0 * min(delta_ub, 20.0)) / mu
    return {
        "family": name,
        "T": T,
        "n_cells": len(cells),
        "n_active_primes": len(mu_ell),
        "mu": mu,
        "mu_remaining": mu_rem,
        "Delta_bound": delta_bound,
        "delta_ub": delta_ub,
        "max_omega_large": worst_omega,
        "R_Delta": r_delta,
        "R_Delta_remaining": r_delta_rem,
        "Delta_over_mu": delta_bound / mu,
        "R_delta": T * delta_ub / mu,
        "suen_loss_over_mu": suen_loss,
        "frac_remaining": mu_rem / mu,
    }


def build_lean(A: int, spf: np.ndarray) -> list[tuple[float, list[int]]]:
    out: list[tuple[float, list[int]]] = []
    for a in range(1, A + 1):
        for c in range(1, A + 1):
            for d in range(1, 6):
                q = 4 * a * c * d - 1
                out.append((1.0 / q, all_primes_of(q, spf)))
    return out


def build_plan_m(A: int, spf: np.ndarray) -> list[tuple[float, list[int]]]:
    out: list[tuple[float, list[int]]] = []
    for a in range(1, A + 1):
        for m in range(1, A + 1):
            for d in range(1, 6):
                Q = 4 * a * d * m
                out.append((1.0 / Q, all_primes_of(m, spf)))
    return out


def build_plan_Q(A: int, spf: np.ndarray) -> list[tuple[float, list[int]]]:
    out: list[tuple[float, list[int]]] = []
    for a in range(1, A + 1):
        for m in range(1, A + 1):
            for d in range(1, 6):
                Q = 4 * a * d * m
                out.append((1.0 / Q, all_primes_of(Q, spf)))
    return out


def fmt(r: dict) -> str:
    rr = r.get("R_Delta_remaining")
    rr_s = f"{rr:.4f}" if rr is not None else "  nan"
    sl = r.get("suen_loss_over_mu")
    sl_s = f"{sl:.3f}" if sl is not None else " nan"
    return (
        f"    {r['family']:16s}  T={r['T']:3d}  μ={r['mu']:.3f}  "
        f"μ_rem={r['mu_remaining']:.3f}  R_Δ={r['R_Delta']:.4f}  "
        f"R_Δ,rem={rr_s}  R_δ={r['R_delta']:.3f}  "
        f"Δ/μ={r['Delta_over_mu']:.3f}  loss/μ={sl_s}"
    )


def scan(Amax: int, As: list[int], Ts: list[int]) -> dict:
    qmax = 4 * Amax * Amax * 5
    print(f"SPF up to {qmax} for Amax={Amax}...", flush=True)
    t0 = time.time()
    spf = spf_numpy(qmax + 1)
    print(f"  SPF {time.time() - t0:.1f}s", flush=True)

    rows: list[dict] = []
    for A in As:
        print(f"\nA={A}  cells={5 * A * A}  H_A={harmonic(A):.4f}", flush=True)
        t1 = time.time()
        lean = build_lean(A, spf)
        adm_m = build_plan_m(A, spf)
        adm_Q = build_plan_Q(A, spf)
        print(f"  built three families {time.time() - t1:.1f}s", flush=True)
        for T in Ts:
            for fam, cells in (
                ("lean_q=4acd-1", lean),
                ("plan_m_large", adm_m),
                ("plan_Q_large", adm_Q),
            ):
                r = run_family(fam, cells, T)
                r["A"] = A
                rows.append(r)
                print(fmt(r), flush=True)

    return {
        "Amax": Amax,
        "As": As,
        "Ts": Ts,
        "note": (
            "R_Δ = T Σ_ℓ μ_ℓ² / μ²; R_δ = T δ_ub / μ; "
            "δ_ub = max_cell Σ_{ℓ|n, ℓ>T} μ_ℓ. "
            "lean = E_power covering cells; plan_m = §4e (large primes of m); "
            "plan_Q = large primes of 4adm."
        ),
        "rows": rows,
    }


def main() -> None:
    Amax = int(os.environ.get("SUEN_AMAX", "240"))
    As = [24, 48, 80, 120, 160, 200, 240]
    As = [A for A in As if A <= Amax]
    Ts = [13, 23, 37, 53]
    extra = os.environ.get("SUEN_TS")
    if extra:
        Ts = [int(x) for x in extra.split(",")]
    data = scan(Amax, As, Ts)
    out = os.path.join(HERE, f"e_power_suen_moments_A{Amax}.json")
    with open(out, "w") as f:
        json.dump(data, f, indent=2)
    print(f"\nwrote {out}", flush=True)

    print("\n=== Lean family, R_Δ vs A at each T (the E_power gate) ===")
    print("  A     T    μ      R_Δ    R_Δ,rem   R_δ    Δ/μ   frac_rem")
    for r in data["rows"]:
        if r["family"] != "lean_q=4acd-1":
            continue
        rr = r["R_Delta_remaining"]
        rr_s = f"{rr:7.4f}" if rr is not None else "    nan"
        print(
            f"  {r['A']:3d}  {r['T']:3d}  {r['mu']:6.3f}  {r['R_Delta']:6.4f}  "
            f"{rr_s}  {r['R_delta']:6.3f}  {r['Delta_over_mu']:5.3f}  "
            f"{r['frac_remaining']:6.3f}"
        )

    print("\n=== plan_m family at A=48 (compare §4e T-scaling) ===")
    for r in data["rows"]:
        if r["family"] == "plan_m_large" and r["A"] == 48:
            print(fmt(r))


if __name__ == "__main__":
    main()
