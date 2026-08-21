#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""ClassRough composite layer: Euler product over aligned composite moduli.

Prime-aligned forbids q prime, q ≡ −1 (mod 4a). ClassRough also forbids
composite q in that AP.  Among polynomial values N = p+4a² of size ~x,
the extra is the product over those composites up to ~√x (proper divisors).

This script computes, for each a ≤ Amax,

    Π_comp(a, Z) = ∏ (1 − 1/q)   over composite q ≤ Z, q ≡ −1 (mod 4a),

and compares it to the measured ρ_CR / ρ_prime at x = 10^9
(from c4_S_xscan_X1000000000.json).
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np


def spf_numpy(n: int) -> np.ndarray:
    spf = np.arange(n + 1, dtype=np.uint32)
    r = int(n**0.5)
    for p in range(2, r + 1):
        if spf[p] == p:
            spf[p * p :: p] = np.minimum(spf[p * p :: p], np.uint32(p))
    return spf


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


def main(Zmax: int = 50_000, Amax: int = 80, scan_path: str | None = None) -> dict:
    scan_path = scan_path or "c4_S_xscan_X1000000000.json"
    scan = json.loads(Path(scan_path).read_text())
    byx = {r["x"]: r for r in scan["by_x"]}
    x_emp = 1_000_000_000
    emp = byx[x_emp]
    sqrtx = int(x_emp**0.5)

    print(f"composite Euler  Zmax={Zmax} Amax={Amax}  sqrt(x)={sqrtx}", flush=True)
    spf = spf_numpy(Zmax)
    is_prime = (spf == np.arange(Zmax + 1))
    is_prime[0:2] = False

    Zs = [100, 300, 1000, 3000, 10_000, 30_000, min(Zmax, sqrtx), Zmax]
    Zs = sorted(set(z for z in Zs if z <= Zmax))

    rows = []
    for a in range(1, Amax + 1):
        m = 4 * a
        logp = {Z: 0.0 for Z in Zs}
        logg = {Z: 0.0 for Z in Zs}  # genuine extra: no aligned prime factor
        ncomp = {Z: 0 for Z in Zs}
        ngen = {Z: 0 for Z in Zs}
        npr = {Z: 0 for Z in Zs}
        # q = k*m - 1 ≥ 3
        q = m - 1
        if q < 3:
            q += m
        while q <= Zmax:
            composite = q >= 4 and not bool(is_prime[q])
            prime = bool(is_prime[q])
            genuine = False
            if composite:
                t = q
                genuine = True
                while t > 1:
                    p = int(spf[t])
                    if (p + 1) % m == 0:
                        genuine = False
                        break
                    while t % p == 0:
                        t //= p
            for Z in Zs:
                if q <= Z:
                    if composite:
                        logp[Z] += math.log1p(-1.0 / q)
                        ncomp[Z] += 1
                        if genuine:
                            logg[Z] += math.log1p(-1.0 / q)
                            ngen[Z] += 1
                    elif prime:
                        npr[Z] += 1
            q += m
        rho_cr = emp["rho"][a - 1]
        rho_pr = emp["rho_prime"][a - 1]
        ratio = rho_cr / rho_pr if rho_pr else float("nan")
        rec = {
            "a": a,
            "m": m,
            "inv_phi": 1.0 / euler_phi(m),
            "rho_cr": rho_cr,
            "rho_prime": rho_pr,
            "ratio_emp": ratio,
            "Pi": {str(Z): math.exp(logp[Z]) for Z in Zs},
            "Pi_gen": {str(Z): math.exp(logg[Z]) for Z in Zs},
            "n_comp": {str(Z): ncomp[Z] for Z in Zs},
            "n_gen": {str(Z): ngen[Z] for Z in Zs},
            "n_prime": {str(Z): npr[Z] for Z in Zs},
        }
        rows.append(rec)

    print(f"\n{'a':>4} {'1/φ':>7} {'emp':>7} {'Πnaive':>7} {'Πgen√x':>7} {'ΠgenZ':>7}  ngen√x")
    zsqrt = str(min(Zmax, sqrtx))
    for rec in rows:
        if rec["a"] in {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 24, 30, 40, 48, 60, 80}:
            print(
                f"{rec['a']:4d} {rec['inv_phi']:7.4f} {rec['ratio_emp']:7.4f} "
                f"{rec['Pi'][zsqrt]:7.4f} {rec['Pi_gen'][zsqrt]:7.4f} "
                f"{rec['Pi_gen'][str(Zmax)]:7.4f}  {rec['n_gen'][zsqrt]:5d}"
            )

    for A in (40, 80):
        empP = math.prod(rows[a - 1]["ratio_emp"] for a in range(1, A + 1))
        piP = math.prod(rows[a - 1]["Pi_gen"][zsqrt] for a in range(1, A + 1))
        print(
            f"\nA={A}  ∏ emp(ρCR/ρpr)={empP:.4e}  "
            f"∏ Π_gen(√x)={piP:.4e}  emp/Π={empP/piP:.3f}"
        )

    xs = [math.log(rec["Pi_gen"][zsqrt]) for rec in rows]
    ys = [math.log(rec["ratio_emp"]) for rec in rows]
    X = np.vstack([xs, np.ones(len(xs))]).T
    sl, ic = np.linalg.lstsq(X, ys, rcond=None)[0]
    pred = sl * np.array(xs) + ic
    r2 = 1 - ((np.array(ys) - pred) ** 2).sum() / ((np.array(ys) - np.mean(ys)) ** 2).sum()
    print(f"\nlog emp ~ {sl:.3f} log Π_gen(√x) + {ic:.3f}   R²={r2:.3f}  (a=1..{Amax})")
    # a≥10, where the AP is sparse
    idx = [i for i, rec in enumerate(rows) if rec["a"] >= 10]
    xs2 = [xs[i] for i in idx]
    ys2 = [ys[i] for i in idx]
    X2 = np.vstack([xs2, np.ones(len(xs2))]).T
    sl2, ic2 = np.linalg.lstsq(X2, ys2, rcond=None)[0]
    pred2 = sl2 * np.array(xs2) + ic2
    r22 = 1 - ((np.array(ys2) - pred2) ** 2).sum() / ((np.array(ys2) - np.mean(ys2)) ** 2).sum()
    print(f"a≥10:     ~ {sl2:.3f} log Π_gen(√x) + {ic2:.3f}   R²={r22:.3f}")

    out = {
        "Zmax": Zmax,
        "Amax": Amax,
        "x_emp": x_emp,
        "sqrtx": sqrtx,
        "scan": scan_path,
        "Zs": Zs,
        "fit_sqrt": {"slope": float(sl), "intercept": float(ic), "r2": float(r2)},
        "fit_sqrt_a10": {"slope": float(sl2), "intercept": float(ic2), "r2": float(r22)},
        "rows": rows,
    }
    return out


if __name__ == "__main__":
    Zmax = int(sys.argv[1]) if len(sys.argv) > 1 else 50_000
    Amax = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    out = main(Zmax, Amax)
    path = f"c4_composite_layer_Z{Zmax}_A{Amax}.json"
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"\nwrote {path}")
