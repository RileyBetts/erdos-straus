#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Fibre-level Suen quantities for the two-stage E_power repair.

Computes, after deduplicating (q, r) events and splitting each modulus
into a T-smooth prime-power part s and a T-rough part ℓ:

    P(hub survives),
    distributions of μ_ρ, Δ_ρ, δ_ρ, and −μ_ρ + Δ_ρ exp(2δ_ρ),

on the finite product space of coordinates modulo the prime-power hub
H = lcm_i(s_i). This is not a proof. Do not treat the output as H1 or H2.

The older scripts e_power_suen_moments.py / e_power_suen_moments_large.py
measure the surrogate Σ_{ℓ>T} μ_ℓ². They are not this check.

Hub H is usually too large to enumerate. Residues are sampled in the
product space (independent uniform coordinates n mod p^k for p^k || H).
"""

from __future__ import annotations

import json
import math
import os
import random
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))


def factor(n: int) -> dict[int, int]:
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def split_q(q: int, T: int) -> tuple[int, int]:
    """Return (s, ℓ) with q = s·ℓ, s T-smooth prime-power, ℓ T-rough."""
    s = 1
    ell = 1
    for p, k in factor(q).items():
        pk = p**k
        if p <= T:
            s *= pk
        else:
            ell *= pk
    return s, ell


def residue(a: int, c: int, q: int) -> int:
    """r with c·r + a ≡ 0 (mod q). gcd(c, q) = 1 always for Lean cells."""
    return (-a * pow(c, -1, q)) % q


def build_events(A: int) -> list[tuple[int, int]]:
    seen: set[tuple[int, int]] = set()
    for a in range(1, A + 1):
        for c in range(1, A + 1):
            for d in range(1, 6):
                q = 4 * a * c * d - 1
                seen.add((q, residue(a, c, q)))
    return sorted(seen)


def hub_valuation(events: list[tuple[int, int]], T: int) -> dict[int, int]:
    """p ↦ max v_p(s_i). H = ∏ p^{k_p}."""
    val: dict[int, int] = {}
    for q, _r in events:
        s, _ell = split_q(q, T)
        for p, k in factor(s).items():
            val[p] = max(val.get(p, 0), k)
    return val


def compatible(s: int, r: int, rho: dict[int, int]) -> bool:
    if s == 0:
        return False
    for p, k in factor(s).items():
        pk = p**k
        if rho.get(p, 0) % pk != r % pk:
            return False
    return True


def classify(q: int, r: int, T: int, rho: dict[int, int]) -> str | int:
    s, ell = split_q(q, T)
    if not compatible(s, r, rho):
        return "incompatible"
    if ell <= 1:
        return "hub_forced"
    return ell


def sample_rho(val: dict[int, int], rng: random.Random) -> dict[int, int]:
    return {p: rng.randrange(p**k) for p, k in val.items()}


def hub_modulus(val: dict[int, int]) -> int:
    H = 1
    for p, k in val.items():
        H *= p**k
    return H


def all_rho(val: dict[int, int]) -> list[dict[int, int]]:
    """Every hub residue as a p ↦ coordinate map."""
    primes = list(val.keys())
    if not primes:
        return [{}]
    coords = [[(p, r) for r in range(p ** val[p])] for p in primes]
    out: list[dict[int, int]] = [{}]
    for choices in coords:
        out = [{**rho, p: r} for rho in out for p, r in choices]
    return out


def fibre_quantities(
    events: list[tuple[int, int]],
    T: int,
    rho: dict[int, int],
    need_star: bool = False,
) -> dict | None:
    residual: list[tuple[int, int]] = []  # (ell, r) but r is original; remaining is r mod ell
    for q, r in events:
        cls = classify(q, r, T, rho)
        if cls == "hub_forced":
            return None
        if isinstance(cls, int):
            residual.append((cls, r % cls))

    if not residual:
        return {
            "mu": 0.0,
            "Delta": 0.0,
            "delta": 0.0,
            "janson_titu": 0.0,
            "suen_exp": 0.0,
            "n_residual": 0,
        }

    ells = [ell for ell, _r in residual]
    mu = sum(1.0 / ell for ell in ells)

    def joint(i: int, j: int) -> float:
        ei, ri = residual[i]
        ej, rj = residual[j]
        g = math.gcd(ei, ej)
        if g <= 1:
            return 0.0  # independent: not a Δ summand
        if ri % g != rj % g:
            return 0.0
        return 1.0 / math.lcm(ei, ej)

    n = len(residual)
    delta_pair = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            pij = joint(i, j)
            if pij != 0.0:
                delta_pair += pij

    delta = 0.0
    suen_exp = 0.0
    if need_star:
        neigh = [0.0] * n
        for i in range(n):
            ei = residual[i][0]
            s = 0.0
            for j in range(n):
                if i == j:
                    continue
                if math.gcd(ei, residual[j][0]) > 1:
                    s += 1.0 / residual[j][0]
            neigh[i] = s
        delta = max(neigh) if neigh else 0.0
        suen_exp = -mu + delta_pair * math.exp(2.0 * min(delta, 20.0))
    den = mu + 2.0 * delta_pair
    janson_titu = (mu * mu / den) if den > 0 else 0.0
    return {
        "mu": mu,
        "Delta": delta_pair,
        "delta": delta,
        "janson_titu": janson_titu,
        "suen_exp": suen_exp,
        "n_residual": n,
    }


def summarize(xs: list[float]) -> dict:
    if not xs:
        return {"n": 0}
    ys = sorted(xs)
    n = len(ys)

    def pct(p: float) -> float:
        return ys[min(n - 1, max(0, int(p * (n - 1))))]

    return {
        "n": n,
        "mean": sum(ys) / n,
        "min": ys[0],
        "p50": pct(0.50),
        "p90": pct(0.90),
        "p99": pct(0.99),
        "max": ys[-1],
    }


def scan(A: int, T: int, samples: int, seed: int) -> dict:
    t0 = time.time()
    raw_n = 5 * A * A
    evs = build_events(A)
    mu_dedup = sum(1.0 / q for q, _r in evs)
    mu_raw = 0.0
    for a in range(1, A + 1):
        for c in range(1, A + 1):
            for d in range(1, 6):
                mu_raw += 1.0 / (4 * a * c * d - 1)

    val = hub_valuation(evs, T)
    logH = sum(k * math.log(p) for p, k in val.items())
    H = hub_modulus(val)
    rng = random.Random(seed)

    n_hub_kill = 0
    mus: list[float] = []
    Deltas: list[float] = []
    deltas: list[float] = []
    titus: list[float] = []
    suens: list[float] = []
    worst: dict | None = None
    worst_titu: dict | None = None
    exhaustive = H > 0 and H <= 120
    rhos = all_rho(val) if exhaustive else [sample_rho(val, rng) for _ in range(samples)]
    n_tried = len(rhos)
    for rho in rhos:
        qnt = fibre_quantities(evs, T, rho)
        if qnt is None:
            n_hub_kill += 1
            continue
        mus.append(qnt["mu"])
        Deltas.append(qnt["Delta"])
        deltas.append(qnt["delta"])
        titus.append(qnt["janson_titu"])
        suens.append(qnt["suen_exp"])
        if worst is None or qnt["suen_exp"] > worst["suen_exp"]:
            worst = dict(qnt)
        if worst_titu is None or qnt["janson_titu"] < worst_titu["janson_titu"]:
            worst_titu = dict(qnt)

    n_surv = n_tried - n_hub_kill
    p_hub = n_surv / n_tried if n_tried else 0.0
    gamma_H_hat = None
    if p_hub > 0 and mu_dedup > 0 and p_hub < 1:
        gamma_H_hat = -math.log(p_hub) / mu_dedup
    elif p_hub == 0 and mu_dedup > 0:
        gamma_H_hat = float("inf")

    logA2 = math.log(A) ** 2
    titu = summarize(titus)
    titu_over = None
    titu_min_over = None
    if titu.get("n", 0) and logA2 > 0:
        titu_over = titu["mean"] / logA2
        titu_min_over = titu["min"] / logA2
    return {
        "A": A,
        "T": T,
        "samples": n_tried,
        "seed": seed,
        "exhaustive": exhaustive,
        "H": H,
        "n_cells_raw": raw_n,
        "n_events": len(evs),
        "mu_raw": mu_raw,
        "mu_dedup": mu_dedup,
        "mu_dedup_over_logA2": mu_dedup / logA2 if logA2 else None,
        "logA2": logA2,
        "hub_omega": len(val),
        "logH": logH,
        "P_hub_survives": p_hub,
        "gamma_H_hat": gamma_H_hat,
        "mu_rho": summarize(mus),
        "Delta_rho": summarize(Deltas),
        "delta_rho": summarize(deltas),
        "janson_titu": titu,
        "janson_titu_over_logA2": titu_over,
        "janson_titu_min_over_logA2": titu_min_over,
        "suen_exp": summarize(suens),
        "worst_surviving_fibre": worst,
        "worst_titu_fibre": worst_titu,
        "seconds": time.time() - t0,
        "note": (
            "Δ_ρ sums only dependent pairs (gcd(ℓ_i,ℓ_j)>1). "
            "janson_titu is μ²/(μ+2Δ) on surviving fibres. "
            "Not a proof of H1 or H2."
        ),
    }


def mass_growth_row(A: int) -> dict:
    """Exact dedup event count and harmonic mass. No sampling."""
    raw_n = 5 * A * A
    evs = build_events(A)
    mu_dedup = sum(1.0 / q for q, _r in evs)
    mu_raw = 0.0
    for a in range(1, A + 1):
        for c in range(1, A + 1):
            for d in range(1, 6):
                mu_raw += 1.0 / (4 * a * c * d - 1)
    logA2 = math.log(A) ** 2 if A > 1 else 0.0
    k = int(round(math.log2(A))) if A > 0 and (A & (A - 1)) == 0 else None
    return {
        "A": A,
        "k": k,
        "n_cells_raw": raw_n,
        "n_events": len(evs),
        "k2": None if k is None else k * k,
        "events_over_k2": None if k is None or k == 0 else len(evs) / (k * k),
        "mu_raw": mu_raw,
        "mu_dedup": mu_dedup,
        "mu_raw_over_logA2": mu_raw / logA2 if logA2 else None,
        "mu_dedup_over_logA2": mu_dedup / logA2 if logA2 else None,
        "dedup_keep": len(evs) / raw_n if raw_n else None,
    }


def main() -> None:
    As = [int(x) for x in os.environ.get("FIBRE_AS", "6,8,12").split(",")]
    Ts = [int(x) for x in os.environ.get("FIBRE_TS", "3,5,7").split(",")]
    samples = int(os.environ.get("FIBRE_SAMPLES", "400"))
    seed = int(os.environ.get("FIBRE_SEED", "1"))
    mass_As = [int(x) for x in os.environ.get("MASS_AS", "").split(",") if x]
    if not mass_As:
        mass_As = [2**k for k in range(1, 9)]
    mass_rows = [mass_growth_row(A) for A in mass_As]
    print("mass growth (exact):", flush=True)
    for m in mass_rows:
        print(
            f"  A={m['A']:<4} events={m['n_events']:<6} "
            f"μ_dedup={m['mu_dedup']:.3f}  "
            f"μ/(log A)²={m['mu_dedup_over_logA2']}  "
            f"events/k²={m['events_over_k2']}",
            flush=True,
        )
    rows: list[dict] = []
    for A in As:
        for T in Ts:
            print(f"A={A} T={T} samples={samples}...", flush=True)
            row = scan(A, T, samples, seed)
            rows.append(row)
            gh = row["gamma_H_hat"]
            gh_s = f"{gh:.3f}" if isinstance(gh, float) and math.isfinite(gh) else str(gh)
            jt = row["janson_titu"]
            print(
                f"  events={row['n_events']}/{row['n_cells_raw']}  "
                f"μ_dedup={row['mu_dedup']:.3f}  "
                f"P(hub)={row['P_hub_survives']:.4f}  "
                f"γ_H~{gh_s}  "
                f"titu mean={jt.get('mean', float('nan'))}  "
                f"titu min={jt.get('min', float('nan'))}  "
                f"min/(log A)²={row['janson_titu_min_over_logA2']}  "
                f"{'exact H=' + str(row['H']) if row['exhaustive'] else 'mc'}  "
                f"{row['seconds']:.1f}s",
                flush=True,
            )

    out = os.path.join(HERE, f"e_power_fibre_moments_A{max(As)}.json")
    with open(out, "w") as f:
        json.dump(
            {
                "As": As,
                "Ts": Ts,
                "samples": samples,
                "mass": mass_rows,
                "rows": rows,
            },
            f,
            indent=2,
        )
    print(f"wrote {out}", flush=True)


if __name__ == "__main__":
    main()
