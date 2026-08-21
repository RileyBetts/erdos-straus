#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Selberg constant C_sieve(A) of T(A)+.

Aligned-prime joint sieve: for each q ≡ −1 (mod 4a) some a≤A, forbid
p ≡ −4a² (mod q). Dimension

    β(A) = Σ_{a≤A} 1/φ(4a)

(residue collisions only decrease k_q, hence β). Selberg main-term
inflation against (log z)^{-β} is Γ(β+1) E_landau(A), where

    E_landau(A) = ∏_q (1 − k_q/q) (1 − 1/q)^{-β(A)}

(the e^{γβ} in 1/G cancels the Mertens factor in V(z)). Track
log C_sieve against log² A. Do not run x=10^10.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def totient_sieve(n: int) -> np.ndarray:
    phi = np.arange(n + 1, dtype=np.int64)
    for p in range(2, n + 1):
        if phi[p] == p:
            phi[p::p] = phi[p::p] // p * (p - 1)
    return phi


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


def beta_table(Amax: int) -> tuple[list[float], list[int]]:
    phi = totient_sieve(4 * Amax)
    beta = [0.0] * (Amax + 1)
    phi4 = [0] * (Amax + 1)
    s = 0.0
    for a in range(1, Amax + 1):
        phi4[a] = int(phi[4 * a])
        s += 1.0 / phi4[a]
        beta[a] = s
    return beta, phi4


def gamma_inflation(beta: float) -> float:
    """log Γ(β+1).  C_sieve ~ Γ(β+1) E_landau; Stirling is β log β − β."""
    if beta <= 0:
        return 0.0
    return math.lgamma(beta + 1.0)


def landau_and_mertens(Amax: int, Qmax: int, As: list[int], beta: list[float], phi4: list[int]) -> dict:
    """Truncate E_landau and the Mertens sum Σ k_q/q at primes q < Qmax."""
    t0 = time.time()
    spf = spf_numpy(Qmax + 1)
    primes = [int(p) for p in range(3, Qmax + 1) if spf[p] == p]
    print(f"  {len(primes)} odd primes Qmax={Qmax} ({time.time() - t0:.1f}s)", flush=True)

    logE = {A: 0.0 for A in As}
    logE_qm1 = {A: 0.0 for A in As}
    Sk = {A: 0.0 for A in As}
    Sm = {A: 0.0 for A in As}
    n_coll = {A: 0 for A in As}
    n_terms = {A: 0 for A in As}
    kmax = {A: 0 for A in As}
    slice_s = [0.0] * (Amax + 1)

    for q in primes:
        if (q + 1) % 4 != 0:
            continue
        M = (q + 1) // 4
        if M >= len(spf):
            continue
        fac = factor_spf(M, spf)
        served = [a for a in divisors_of(fac) if 1 <= a <= Amax]
        if not served:
            continue
        served.sort()
        ress_by_a = [(a, (-4 * a * a) % q) for a in served]
        invq = 1.0 / q
        for a, _r in ress_by_a:
            slice_s[a] += invq

        si = 0
        acc_res: list[int] = []
        for A in As:
            while si < len(ress_by_a) and ress_by_a[si][0] <= A:
                acc_res.append(ress_by_a[si][1])
                si += 1
            m = len(acc_res)
            if m == 0:
                continue
            k = len(set(acc_res))
            n_terms[A] += 1
            if k < m:
                n_coll[A] += 1
            if k > kmax[A]:
                kmax[A] = k
            if k >= q:
                continue
            b = beta[A]
            logE[A] += math.log1p(-k / q) - b * math.log1p(-1 / q)
            den = q - 1
            if k < den:
                logE_qm1[A] += math.log1p(-k / den) - b * math.log1p(-1 / den)
            Sk[A] += k * invq
            Sm[A] += m * invq

    L = math.log(math.log(Qmax))
    # Late-start Mertens: each slice a only sees primes ≳ 4a.
    def Lcut(a: int) -> float:
        z = max(4 * a, 3)
        if Qmax <= z:
            return 0.0
        return max(0.0, L - math.log(math.log(z)))

    late = [0.0] * (Amax + 1)
    s_late = 0.0
    Msum = [0.0] * (Amax + 1)
    sM = 0.0
    for a in range(1, Amax + 1):
        s_late += Lcut(a) / phi4[a]
        late[a] = s_late
        sM += slice_s[a] - L / phi4[a]
        Msum[a] = sM

    rows = []
    for A in As:
        b = beta[A]
        log_gamma = gamma_inflation(b)
        log2A = math.log(A) ** 2 if A > 1 else float("nan")
        B_est = Sk[A] - late[A]
        # Halberstam–Richert: 1/G ∼ Γ(β+1) e^{γβ} V, V ∼ e^{-γβ}(log z)^{-β} e^{-B}
        # so C_sieve = Γ(β+1) exp(γβ − B(A)), B(A) = lim (Σ k/q − β log log Q).
        log_C_inf = log_gamma + 0.5772156649 * b - B_est
        logE_raw = logE[A]
        log_C_raw = log_gamma + logE_raw
        rows.append({
            "A": A,
            "beta": b,
            "beta_over_logA": b / math.log(A) if A > 1 else float("nan"),
            "log_Gamma": log_gamma,
            "log_E_raw": logE_raw,
            "log_E_qm1": logE_qm1[A],
            "log_C_raw": log_C_raw,
            "log_C_inf": log_C_inf,
            "B_est": B_est,
            "B_trunc_naive": Msum[A],
            "gamma_beta": 0.5772156649 * b,
            "C_sieve_inf": math.exp(log_C_inf) if log_C_inf < 700 else float("inf"),
            "log_C_inf_over_log2A": log_C_inf / log2A if log2A else float("nan"),
            "log_Gamma_over_log2A": log_gamma / log2A if log2A else float("nan"),
            "Sk": Sk[A],
            "Sm": Sm[A],
            "late_pred": late[A],
            "beta_loglogQ": b * L,
            "Sk_minus_betaL": Sk[A] - b * L,
            "n_terms": n_terms[A],
            "n_coll": n_coll[A],
            "kmax": kmax[A],
        })
    print(f"  landau {time.time() - t0:.1f}s", flush=True)
    return {"Qmax": Qmax, "rows": rows}


def ols_vs_log2A(rows: list[dict], key: str, Amin: int = 40) -> dict:
    xs, ys = [], []
    for r in rows:
        if r["A"] < Amin:
            continue
        xs.append(math.log(r["A"]) ** 2)
        ys.append(r[key])
    n = len(xs)
    if n < 3:
        return {"n": n}
    mx = sum(xs) / n
    my = sum(ys) / n
    varx = sum((x - mx) ** 2 for x in xs)
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    slope = cov / varx if varx else float("nan")
    intercept = my - slope * mx
    ss_res = sum((y - (intercept + slope * x)) ** 2 for x, y in zip(xs, ys))
    ss_tot = sum((y - my) ** 2 for y in ys)
    r2 = 1 - ss_res / ss_tot if ss_tot else float("nan")
    return {
        "n": n,
        "Amin": Amin,
        "slope": slope,
        "intercept": intercept,
        "R2": r2,
        "key": key,
        "note": f"OLS of {key} vs log² A; measured c'=0.104, covering κ=0.139",
    }


def main(Amax: int = 200, Qmax: int = 1_000_000, Abig: int = 100_000) -> dict:
    t0 = time.time()
    print(f"C_sieve  Amax={Amax} Qmax={Qmax} Abig={Abig}", flush=True)
    Aphi = max(Amax, Abig)
    print("  totient sieve...", flush=True)
    beta, phi4_big = beta_table(Aphi)
    phi4 = phi4_big[: Amax + 1]

    # high-A beta only (cheap)
    checkpoints = [10, 20, 40, 80, 200, 400, 1000, 2000, 5000, 10000, 20000, 50000, 100000]
    checkpoints = [A for A in checkpoints if A <= Aphi]
    beta_rows = []
    for A in checkpoints:
        b = beta[A]
        logA = math.log(A)
        log_gamma = gamma_inflation(b)
        beta_rows.append({
            "A": A,
            "beta": b,
            "beta_over_logA": b / logA,
            "log_Gamma": log_gamma,
            "log_Gamma_over_log2A": log_gamma / (logA ** 2),
            "stirling_beta_log_beta": b * math.log(b) - b if b > 1 else 0.0,
        })

    As = list(range(5, Amax + 1, 5))
    if 3 not in As:
        As = [3] + As
    print("  Landau / Mertens...", flush=True)
    landau = landau_and_mertens(Amax, Qmax, As, beta, phi4)
    fit_inf = ols_vs_log2A(landau["rows"], "log_C_inf", Amin=40)
    fit_B = ols_vs_log2A(landau["rows"], "B_est", Amin=40)
    fit_G = ols_vs_log2A(landau["rows"], "log_Gamma", Amin=40)

    print("\n  A     β     β/logA  logΓ   B_est  log C_∞  log C_∞/log²A  Sk-late")
    for r in landau["rows"]:
        if r["A"] in (3, 5, 10, 20, 40, 80, 120, 160, 200) or r["A"] % 40 == 0:
            print(
                f"  {r['A']:3d}  {r['beta']:6.3f}  {r['beta_over_logA']:6.3f}  "
                f"{r['log_Gamma']:6.3f}  {r['B_est']:6.3f}  {r['log_C_inf']:7.3f}  "
                f"{r['log_C_inf_over_log2A']:8.4f}  {r['B_est']:6.3f}  "
                f"coll={r['n_coll']} kmax={r['kmax']}",
                flush=True,
            )

    print("\n  large-A β (no Euler product):")
    print("  A         β      β/log A   log Γ / log²A")
    for r in beta_rows:
        print(
            f"  {r['A']:7d}  {r['beta']:8.3f}  {r['beta_over_logA']:7.4f}  "
            f"{r['log_Gamma_over_log2A']:8.5f}",
            flush=True,
        )

    print(
        f"\n  OLS A≥40 vs log² A:  log C_∞ slope={fit_inf.get('slope')} R²={fit_inf.get('R2')}"
        f"\n                       B_est   slope={fit_B.get('slope')} R²={fit_B.get('R2')}"
        f"\n                       log Γ   slope={fit_G.get('slope')} R²={fit_G.get('R2')}",
        flush=True,
    )
    print(f"  elapsed {time.time() - t0:.1f}s", flush=True)

    return {
        "Amax": Amax,
        "Qmax": Qmax,
        "Abig": Abig,
        "elapsed_s": time.time() - t0,
        "formula": (
            "C_sieve(A) = Γ(β(A)+1) exp(γ β(A) − B(A)), "
            "β(A)=Σ_{a≤A} 1/φ(4a), "
            "B(A)=lim (Σ k_q/q − β log log Q) estimated via late-start Mertens"
        ),
        "beta_large": beta_rows,
        "landau": landau,
        "ols_C_inf": fit_inf,
        "ols_B": fit_B,
        "ols_Gamma": fit_G,
        "measured_c_prime": 0.104,
        "covering_kappa": 0.139,
    }


if __name__ == "__main__":
    Amax = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    Qmax = int(sys.argv[2]) if len(sys.argv) > 2 else 1_000_000
    Abig = int(sys.argv[3]) if len(sys.argv) > 3 else 100_000
    out = main(Amax, Qmax, Abig)
    path = os.path.join(HERE, f"c4_sieve_constant_Q{Qmax}_A{Amax}.json")
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"  wrote {path}")
