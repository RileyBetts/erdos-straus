#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Fit the 2D surface of Ĉ(A,x) from zip JSONs, and test certificate counts.

Urgent question (v0.10 referee): the x-slope deficit (~14% of β) and the
A-curvature (c′≈0.104≈75% of κ) are different partials of log S. The
schedule's fate is κ_eff = κ − c′. Test whether c′(x) is still growing
toward κ.

Also: nχ(a) = # real odd Dirichlet characters mod 4a (2-rank of units,
odd half). Compare log Ĉ against log² A vs the certificate-count
predictors Σ log nχ and Σ ω.

Does not prove T(A). Does not densify covering. Does not run new primes.
"""

from __future__ import annotations

import json
import math
import os
import sys


KAPPA = 0.139
HERE = os.path.dirname(os.path.abspath(__file__))


def ols(xs: list[float], ys: list[float]) -> dict:
    n = len(xs)
    mx = sum(xs) / n
    my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    syy = sum((y - my) ** 2 for y in ys)
    slope = sxy / sxx if sxx else float("nan")
    intercept = my - slope * mx
    pred = [intercept + slope * x for x in xs]
    sse = sum((y - p) ** 2 for y, p in zip(ys, pred))
    r2 = 1.0 - sse / syy if syy else float("nan")
    return {"slope": slope, "intercept": intercept, "r2": r2, "n": n}


def omega_odd(n: int) -> int:
    n = abs(n)
    w = 0
    p = 3
    while p * p <= n:
        if n % p == 0:
            w += 1
            while n % p == 0:
                n //= p
        p += 2
    if n > 1:
        w += 1
    return w


def two_val(n: int) -> int:
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def two_rank_units(m: int) -> int:
    """2-rank of (Z/mZ)*. Number of real Dirichlet characters is 2^this."""
    k = two_val(m)
    odd = m >> k
    r = omega_odd(odd)
    if k == 2:
        r += 1
    elif k >= 3:
        r += 2
    return r


def nchi_odd(a: int) -> int:
    """Number of real odd characters mod 4a.

    (Z/4aZ)* always has 2-power at least 4. The functional χ ↦ χ(−1)
    is surjective on Hom to {±1} (χ₄ is odd), so exactly half of the
    real characters are odd.
    """
    r = two_rank_units(4 * a)
    return 1 if r == 0 else 2 ** (r - 1)


def chat_from_alive_rho(n_alive: list[int], rho: list[float], nh: int) -> list[float]:
    """Ĉ(A) for A=1..len, from prefix-alive counts and one-slice ρ."""
    out = []
    log_prod = 0.0
    for a in range(1, len(n_alive) + 1):
        S = n_alive[a - 1] / nh if nh else 0.0
        r = rho[a - 1]
        if r > 0:
            log_prod += math.log(r)
        prod = math.exp(log_prod)
        out.append(S / prod if prod > 0 and S > 0 else float("nan"))
    return out


def load() -> dict:
    xscan_path = os.path.join(HERE, "c4_S_xscan_X1000000000.json")
    grow_path = os.path.join(HERE, "c4_growing_A_X1000000000_A200.json")
    with open(xscan_path) as f:
        xscan = json.load(f)
    with open(grow_path) as f:
        grow = json.load(f)
    return {"xscan": xscan, "grow": grow}


def surface(xscan: dict, grow: dict) -> dict:
    """Ĉ(A,x) grid from by_x (A≤80, many x) plus growing-A at x=10^9 (A≤200)."""
    grid = []  # {x, A, C_hat, S, n_alive, n_hard, loglog_x}
    cprime_at_x = []

    for row in xscan["by_x"]:
        x = row["x"]
        nh = row["n_hard"]
        L = row["loglog_x"]
        rho = row["rho"]
        n_alive = row["n_alive"]
        chats = chat_from_alive_rho(n_alive, rho, nh)
        Amax = len(chats)
        for A, C in enumerate(chats, 1):
            S = n_alive[A - 1] / nh if nh else 0.0
            grid.append({
                "x": x, "A": A, "C_hat": C, "S": S,
                "n_alive": n_alive[A - 1], "n_hard": nh, "loglog_x": L,
            })
        # c′(x): OLS log Ĉ ~ c′ log² A on A≥40 with Ĉ>0
        xs, ys = [], []
        for A, C in enumerate(chats, 1):
            if A >= 40 and C == C and C > 0:
                xs.append(math.log(A) ** 2)
                ys.append(math.log(C))
        fit = ols(xs, ys) if len(xs) >= 8 else None
        cprime_at_x.append({
            "x": x,
            "n_hard": nh,
            "loglog_x": L,
            "Amax": Amax,
            "C80": chats[79] if Amax >= 80 else None,
            "C40": chats[39] if Amax >= 40 else None,
            "c_prime": None if fit is None else fit["slope"],
            "r2": None if fit is None else fit["r2"],
            "n_pts": 0 if fit is None else fit["n"],
            "mean_e_m1_10_80": row["mean_e_m1"]["a10_80"],
        })

    # growing-A at x=1e9 goes to A=200; replace/extend that x's A>80
    gC = [r["C_hat"] for r in grow["enrich"]]
    xs, ys = [], []
    for r in grow["enrich"]:
        if r["a"] >= 40 and r["C_hat"] > 0:
            xs.append(math.log(r["a"]) ** 2)
            ys.append(math.log(r["C_hat"]))
    fit200 = ols(xs, ys)
    xs80, ys80 = [], []
    for r in grow["enrich"]:
        if 40 <= r["a"] <= 80 and r["C_hat"] > 0:
            xs80.append(math.log(r["a"]) ** 2)
            ys80.append(math.log(r["C_hat"]))
    fit80 = ols(xs80, ys80)

    return {
        "grid": grid,
        "cprime_at_x": cprime_at_x,
        "grow_cprime_A40_200": fit200,
        "grow_cprime_A40_80": fit80,
        "grow_C80": grow["enrich"][79]["C_hat"],
        "grow_C200": grow["enrich"][199]["C_hat"],
    }


def partition_predictors(grow: dict) -> dict:
    nchi = [nchi_odd(a) for a in range(1, 201)]
    om = [omega_odd(4 * a) for a in range(1, 201)]  # odd primes in 4a = primes in a
    om_a = [omega_odd(a) if a % 2 else omega_odd(a) for a in range(1, 201)]

    sum_log_nchi = []
    s = 0.0
    for n in nchi:
        s += math.log(n)
        sum_log_nchi.append(s)
    sum_om = []
    s = 0.0
    for w in om_a:
        s += w
        sum_om.append(s)

    As, y, x_log2, x_nchi, x_om = [], [], [], [], []
    for r in grow["enrich"]:
        a = r["a"]
        if a < 40 or r["C_hat"] <= 0:
            continue
        As.append(a)
        y.append(math.log(r["C_hat"]))
        x_log2.append(math.log(a) ** 2)
        x_nchi.append(sum_log_nchi[a - 1])
        x_om.append(sum_om[a - 1])

    return {
        "nchi_sample": {str(a): nchi[a - 1] for a in (1, 2, 3, 4, 5, 6, 12, 15, 30, 60, 80, 120, 200)},
        "fit_log2A": ols(x_log2, y),
        "fit_sum_log_nchi": ols(x_nchi, y),
        "fit_sum_omega": ols(x_om, y),
        "corr_note": (
            "Naive Π nχ grows like exp(c A): Σ_{a≤A} log nχ ~ A, not log² A. "
            "If that OLS R² beats log² A, the partition function is not "
            "the 0.104 curve. If log² A wins, inflation is not raw character count."
        ),
        "sum_log_nchi_200": sum_log_nchi[199],
        "sum_omega_200": sum_om[199],
        "logC_200": math.log(grow["enrich"][199]["C_hat"]),
        "points": [
            {
                "A": a,
                "logC": math.log(grow["enrich"][a - 1]["C_hat"]),
                "log2A": math.log(a) ** 2,
                "sum_log_nchi": sum_log_nchi[a - 1],
                "sum_omega": sum_om[a - 1],
            }
            for a in range(40, 201, 20)
        ],
    }


def x_slope_deficit(xscan: dict) -> dict:
    """Reproduce β_S / β_∏ρ at A=40,80 on x≥10^6."""
    out = {}
    for A, rows in xscan["scan"].items():
        xs, yS, yP = [], [], []
        for r in rows:
            if r["x"] < 1_000_000:
                continue
            if r["log_S"] is None:
                continue
            xs.append(r["loglog_x"])
            yS.append(r["log_S"])
            yP.append(r["log_prod"])
        fS = ols(xs, yS)
        fP = ols(xs, yP)
        out[str(A)] = {
            "beta_S": fS["slope"],
            "beta_prod": fP["slope"],
            "ratio": fS["slope"] / fP["slope"] if fP["slope"] else None,
            "deficit": 1.0 - fS["slope"] / fP["slope"] if fP["slope"] else None,
            "r2_S": fS["r2"],
            "r2_prod": fP["r2"],
        }
    return out


def main() -> dict:
    data = load()
    surf = surface(data["xscan"], data["grow"])
    part = partition_predictors(data["grow"])
    slope = x_slope_deficit(data["xscan"])

    # is c′(x) growing? OLS c′ vs ln ln x on x≥1e6
    xs, ys = [], []
    for r in surf["cprime_at_x"]:
        if r["x"] >= 1_000_000 and r["c_prime"] is not None:
            xs.append(r["loglog_x"])
            ys.append(r["c_prime"])
    cprime_vs_L = ols(xs, ys) if len(xs) >= 4 else None
    c_last = surf["cprime_at_x"][-1]["c_prime"]
    c_1e6 = next(r["c_prime"] for r in surf["cprime_at_x"] if r["x"] == 1_000_000)
    c_1e8 = next(r["c_prime"] for r in surf["cprime_at_x"] if r["x"] == 100_000_000)

    kill = {
        "kappa": KAPPA,
        "c_prime_A40_80_at_1e9": surf["grow_cprime_A40_80"]["slope"],
        "c_prime_A40_200_at_1e9": surf["grow_cprime_A40_200"]["slope"],
        "c_prime_from_xscan_grid_at_1e9": c_last,
        "kappa_eff_A_reading": KAPPA - surf["grow_cprime_A40_200"]["slope"],
        "x_deficit_A80": slope["80"]["deficit"],
        "kappa_eff_x_reading": KAPPA * (1.0 - slope["80"]["deficit"]),
        "c_prime_vs_loglog_x": cprime_vs_L,
        "c_prime_1e6": c_1e6,
        "c_prime_1e8": c_1e8,
        "c_prime_1e9": c_last,
        "growing_toward_kappa": bool(
            cprime_vs_L and cprime_vs_L["slope"] > 0 and c_last < KAPPA
        ),
        "would_hit_kappa": None,
    }
    if cprime_vs_L and cprime_vs_L["slope"] > 0:
        # linear in ln ln x: c′ = b0 + b1 L, hit κ at L = (κ-b0)/b1
        b0, b1 = cprime_vs_L["intercept"], cprime_vs_L["slope"]
        Lhit = (KAPPA - b0) / b1
        kill["would_hit_kappa"] = {
            "loglog_x": Lhit,
            "x_exp_exp": math.exp(math.exp(Lhit)) if Lhit < 20 else None,
            "note": "linear extrapolation in ln ln x; not a theorem",
        }

    return {
        "cprime_at_x": surf["cprime_at_x"],
        "grow_fits": {
            "A40_80": surf["grow_cprime_A40_80"],
            "A40_200": surf["grow_cprime_A40_200"],
            "C80": surf["grow_C80"],
            "C200": surf["grow_C200"],
        },
        "x_slope": slope,
        "kill": kill,
        "partition": part,
    }


def show(out: dict) -> None:
    print("c′(x) from x-scan grid, OLS log Ĉ ~ c′ log² A on A=40..80")
    print(f"  {'x':>12}  {'L':>6}  {'c′':>8}  {'R²':>6}  Ĉ(80)  mean(e−1)10..80")
    for r in out["cprime_at_x"]:
        if r["c_prime"] is None:
            continue
        print(
            f"  {r['x']:12d}  {r['loglog_x']:6.3f}  {r['c_prime']:8.4f}  "
            f"{r['r2']:6.3f}  {r['C80']:6.3f}  {r['mean_e_m1_10_80']:+.4f}"
        )
    k = out["kill"]
    print()
    print(f"κ = {k['kappa']}")
    print(f"c′ A-reading (A=40..200, x=1e9): {k['c_prime_A40_200_at_1e9']:.4f}  "
          f"κ_eff={k['kappa_eff_A_reading']:.4f}")
    print(f"c′ A-reading (A=40..80,  x=1e9): {k['c_prime_A40_80_at_1e9']:.4f}")
    print(f"x-deficit at A=80: {k['x_deficit_A80']:.4f}  "
          f"κ_eff x-reading={k['kappa_eff_x_reading']:.4f}")
    print(f"c′(1e6)={k['c_prime_1e6']:.4f}  c′(1e8)={k['c_prime_1e8']:.4f}  "
          f"c′(1e9)={k['c_prime_1e9']:.4f}")
    cv = k["c_prime_vs_loglog_x"]
    print(f"c′ vs ln ln x (x≥1e6): slope={cv['slope']:.4f}  R²={cv['r2']:.3f}  "
          f"growing_toward_κ={k['growing_toward_kappa']}")
    if k["would_hit_kappa"]:
        w = k["would_hit_kappa"]
        print(f"  linear hit κ at ln ln x={w['loglog_x']:.3f}  "
              f"x~{w['x_exp_exp']:.3g}" if w["x_exp_exp"] else
              f"  linear hit κ at ln ln x={w['loglog_x']:.3f} (x overflow)")
    print()
    p = out["partition"]
    print("partition-function predictors vs log Ĉ on A≥40 at x=1e9")
    print(f"  log² A:          slope={p['fit_log2A']['slope']:.4f}  R²={p['fit_log2A']['r2']:.4f}")
    print(f"  Σ log nχ:        slope={p['fit_sum_log_nchi']['slope']:.4f}  "
          f"R²={p['fit_sum_log_nchi']['r2']:.4f}")
    print(f"  Σ ω(a):          slope={p['fit_sum_omega']['slope']:.4f}  "
          f"R²={p['fit_sum_omega']['r2']:.4f}")
    print(f"  nχ samples: {p['nchi_sample']}")
    print(f"  {p['corr_note']}")


if __name__ == "__main__":
    out = main()
    show(out)
    path = os.path.join(HERE, "c4_surface_fit.json")
    # drop the huge grid from disk? we didn't put grid in out. Good.
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\nwrote {path}")
    if len(sys.argv) > 1:
        pass
