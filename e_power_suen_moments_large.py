#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Lean-only Suen second moments at A up to a few thousand.

Two-pass, no cell storage. First pass accumulates μ_ℓ; second pass
computes δ_ub. Do not densify covering. Do not run x = 10^10.
"""

from __future__ import annotations

import json
import math
import os
import time
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def spf_numpy(n: int) -> np.ndarray:
    spf = np.arange(n + 1, dtype=np.uint32)
    r = int(n**0.5)
    for p in range(2, r + 1):
        if spf[p] == p:
            spf[p * p :: p] = np.minimum(spf[p * p :: p], np.uint32(p))
    return spf


def primes_of(n: int, spf: np.ndarray) -> list[int]:
    out: list[int] = []
    while n > 1:
        p = int(spf[n])
        if not out or out[-1] != p:
            out.append(p)
        n //= p
    return out


def scan_A(A: int, Ts: list[int], spf: np.ndarray) -> list[dict]:
    t0 = time.time()
    mu = 0.0
    mu_ell: dict[int, float] = defaultdict(float)
    n_cells = 5 * A * A
    for d in range(1, 6):
        for c in range(1, A + 1):
            four_cd = 4 * c * d
            for a in range(1, A + 1):
                q = four_cd * a - 1
                mass = 1.0 / q
                mu += mass
                for p in primes_of(q, spf):
                    mu_ell[p] += mass
    print(f"  A={A} pass1 {time.time() - t0:.1f}s  μ={mu:.3f}  primes={len(mu_ell)}", flush=True)

    t1 = time.time()
    delta_ub = {T: 0.0 for T in Ts}
    worst_om = {T: 0 for T in Ts}
    mu_rem = {T: 0.0 for T in Ts}
    for d in range(1, 6):
        for c in range(1, A + 1):
            four_cd = 4 * c * d
            for a in range(1, A + 1):
                q = four_cd * a - 1
                ps = primes_of(q, spf)
                mass = 1.0 / q
                for T in Ts:
                    s = 0.0
                    om = 0
                    for p in ps:
                        if p > T:
                            s += mu_ell[p]
                            om += 1
                    if om:
                        mu_rem[T] += mass
                    if om > worst_om[T]:
                        worst_om[T] = om
                    if s > delta_ub[T]:
                        delta_ub[T] = s
    print(f"  A={A} pass2 {time.time() - t1:.1f}s", flush=True)

    rows = []
    for T in Ts:
        dlt = 0.0
        n_act = 0
        for p, v in mu_ell.items():
            if p > T:
                dlt += v * v
                n_act += 1
        r_delta = T * dlt / (mu * mu) if mu else 0.0
        r_delta_rem = T * dlt / (mu_rem[T] ** 2) if mu_rem[T] > 0 else None
        suen_loss = None
        if delta_ub[T] > 0:
            suen_loss = dlt * math.exp(2.0 * min(delta_ub[T], 20.0)) / mu
        rows.append({
            "family": "lean_q=4acd-1",
            "A": A,
            "T": T,
            "n_cells": n_cells,
            "n_active_primes": n_act,
            "mu": mu,
            "mu_remaining": mu_rem[T],
            "Delta_bound": dlt,
            "delta_ub": delta_ub[T],
            "max_omega_large": worst_om[T],
            "R_Delta": r_delta,
            "R_Delta_remaining": r_delta_rem,
            "Delta_over_mu": dlt / mu if mu else 0.0,
            "R_delta": T * delta_ub[T] / mu if mu else 0.0,
            "suen_loss_over_mu": suen_loss,
            "frac_remaining": mu_rem[T] / mu if mu else 0.0,
        })
    return rows


def main() -> None:
    As = [int(x) for x in os.environ.get("SUEN_AS", "400,800,1200,1600,2000").split(",")]
    Ts = [int(x) for x in os.environ.get("SUEN_TS", "13,37,97,199,409").split(",")]
    Amax = max(As)
    qmax = 4 * Amax * Amax * 5
    print(f"SPF up to {qmax} (Amax={Amax})...", flush=True)
    t0 = time.time()
    spf = spf_numpy(qmax + 1)
    print(f"  SPF {time.time() - t0:.1f}s", flush=True)

    rows: list[dict] = []
    for A in As:
        rows.extend(scan_A(A, Ts, spf))
        for r in rows[-len(Ts):]:
            rr = r["R_Delta_remaining"]
            rr_s = f"{rr:.4f}" if rr is not None else "nan"
            sl = r["suen_loss_over_mu"]
            sl_s = f"{sl:.3f}" if sl is not None else "nan"
            print(
                f"    T={r['T']:3d}  μ={r['mu']:.3f}  R_Δ={r['R_Delta']:.4f}  "
                f"R_Δ,rem={rr_s}  R_δ={r['R_delta']:.3f}  Δ/μ={r['Delta_over_mu']:.3f}  "
                f"loss/μ={sl_s}  T/μ={r['T']/r['mu']:.2f}",
                flush=True,
            )

    out = os.path.join(HERE, f"e_power_suen_moments_A{Amax}.json")
    with open(out, "w") as f:
        json.dump({"Amax": Amax, "As": As, "Ts": Ts, "rows": rows}, f, indent=2)
    print(f"wrote {out}", flush=True)

    print("\n=== Lean R_Δ vs A ===")
    print("  A      T     μ     R_Δ    R_δ    Δ/μ   T/μ   loss/μ")
    for r in rows:
        sl = r["suen_loss_over_mu"]
        sl_s = f"{sl:7.3f}" if sl is not None else "    nan"
        print(
            f"  {r['A']:4d}  {r['T']:3d}  {r['mu']:6.2f}  {r['R_Delta']:6.4f}  "
            f"{r['R_delta']:5.3f}  {r['Delta_over_mu']:5.3f}  {r['T']/r['mu']:5.2f}  {sl_s}"
        )


if __name__ == "__main__":
    main()
