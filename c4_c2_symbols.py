#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""C2: cross-moduli Jacobi symbols on ClassRough survivors vs all hard primes.

§4r: bias at q | 4a is the shadow of deterministic square-coset exclusions,
decaying to nothing by q = 43 at A = 30.  C2 asks whether, as A grows, the
accumulated conditions interact through quadratic reciprocity:

  (i)  extra cross-correlation E[χ_q1 χ_q2] − E[χ_q1]E[χ_q2] on survivors,
       beyond the product of marginal biases;
  (ii) bias leaking to untouched q (q > A, so q divides no 4a in the box).

If survivors look like random hard primes on Jacobi symbols, leftover Ĉ is
not reciprocity entanglement.  If correlations grow with A, that is C(A).

Reuses ClassRough from c4_S_xscan.py.  Abort-on-fail (stop at first failed
slice).  Default X = 10^8, Amax = 80.
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
    has_aligned_prime,
    sieve_hard_primes,
    sieve_primes,
    spf_numpy,
)

_G: dict = {}


def jacobi(a: int, n: int) -> int:
    """Jacobi (a/n), n odd positive."""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be odd and positive")
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            n8 = n % 8
            if n8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def _still_range(span: tuple[int, int]) -> tuple[int, bytes, bytes]:
    i0, i1 = span
    hard = _G["hard"]
    spf = _G["spf"]
    Amax = _G["Amax"]
    mods = _G["mods"]
    nloc = i1 - i0
    cr = bytearray(nloc)  # still_A as uint8, Amax ≤ 255
    pr = bytearray(nloc)
    for i in range(i0, i1):
        p = int(hard[i])
        li = i - i0
        cr_alive = pr_alive = True
        still_cr = still_pr = 0
        for a in range(1, Amax + 1):
            if not cr_alive and not pr_alive:
                break
            fac = factor_spf(p + 4 * a * a, spf)
            if cr_alive:
                if not has_aligned_divisor(fac, mods[a]):
                    still_cr = a
                else:
                    cr_alive = False
            if pr_alive:
                if not has_aligned_prime(fac, mods[a]):
                    still_pr = a
                else:
                    pr_alive = False
        cr[li] = still_cr
        pr[li] = still_pr
    return i0, bytes(cr), bytes(pr)


def _mean_chi(vals: list[int]) -> tuple[float, int]:
    xs = [v for v in vals if v != 0]
    n = len(xs)
    if n == 0:
        return float("nan"), 0
    return sum(xs) / n, n


def _cov(a: list[int], b: list[int]) -> tuple[float, float, float, int]:
    xs, ys = [], []
    for u, v in zip(a, b):
        if u == 0 or v == 0:
            continue
        xs.append(u)
        ys.append(v)
    n = len(xs)
    if n == 0:
        return float("nan"), float("nan"), float("nan"), 0
    mx = sum(xs) / n
    my = sum(ys) / n
    mxy = sum(x * y for x, y in zip(xs, ys)) / n
    return mxy - mx * my, mx, my, n


def main(Xmax: int = 100_000_000, Amax: int = 80) -> dict:
    t0 = time.time()
    if Amax > 255:
        raise ValueError("Amax must fit in uint8")
    nworkers = min(4, mp.cpu_count() or 1)
    print(f"C2 symbols  Xmax={Xmax} Amax={Amax}  workers={nworkers}", flush=True)
    hard = sieve_hard_primes(Xmax)
    print(f"  {len(hard)} hard  ({time.time() - t0:.1f}s)", flush=True)
    maxN = Xmax + 4 * Amax * Amax
    spf = spf_numpy(maxN)
    print(f"  SPF done  ({time.time() - t0:.1f}s)", flush=True)

    n = len(hard)
    _G["hard"] = hard
    _G["spf"] = spf
    _G["Amax"] = Amax
    _G["mods"] = [4 * a for a in range(Amax + 1)]

    still_cr = bytearray(n)
    still_pr = bytearray(n)
    chunk = max(5_000, n // (nworkers * 8))
    spans = [(i, min(i + chunk, n)) for i in range(0, n, chunk)]
    done = 0
    with mp.Pool(nworkers) as pool:
        for i0, cr, pr in pool.imap_unordered(_still_range, spans):
            still_cr[i0 : i0 + len(cr)] = cr
            still_pr[i0 : i0 + len(pr)] = pr
            done += len(cr)
            print(f"  still {done}/{n}  ({time.time() - t0:.1f}s)", flush=True)
    del spf
    _G.clear()

    qs = [q for q in sieve_primes(103) if q >= 11]
    print(f"  Jacobi q={qs[0]}..{qs[-1]}  ({len(qs)} primes)", flush=True)
    chi = [[0] * len(qs) for _ in range(n)]
    for i, p in enumerate(hard):
        for j, q in enumerate(qs):
            chi[i][j] = 0 if p == q else jacobi(int(p), q)

    def q_kind(q: int, A: int) -> str:
        """a=1 covering (q≡3 mod 4); extra box slice; or inert (q≡1 mod 4)."""
        if q % 4 == 1:
            return "inert"
        M = (q + 1) // 4
        extra = any(a > 1 and A >= a and M % a == 0 for a in range(2, A + 1))
        return "box" if extra else "s2"

    As = [A for A in (1, 5, 10, 11, 15, 20, 30, 40, 60, 80) if A <= Amax]
    if Amax not in As:
        As.append(Amax)

    def pop_stats(mask: list[bool], label: str, A_box: int | None) -> dict:
        idx = [i for i, m in enumerate(mask) if m]
        n_pop = len(idx)
        biases = []
        for j, q in enumerate(qs):
            mu, nchi = _mean_chi([chi[i][j] for i in idx])
            z = mu * math.sqrt(nchi) if nchi else float("nan")
            biases.append({
                "q": q, "mean": mu, "n": nchi, "z": z,
                "kind": "inert" if q % 4 == 1 else (
                    q_kind(q, A_box) if A_box is not None else "s2"
                ),
            })
        pairs = []
        for ja in range(len(qs)):
            for jb in range(ja + 1, len(qs)):
                cov, mx, my, npair = _cov(
                    [chi[i][ja] for i in idx],
                    [chi[i][jb] for i in idx],
                )
                se = 1.0 / math.sqrt(npair) if npair else float("nan")
                k1 = biases[ja]["kind"]
                k2 = biases[jb]["kind"]
                pairs.append({
                    "q1": qs[ja], "q2": qs[jb],
                    "kind1": k1, "kind2": k2,
                    "cov": cov, "mean1": mx, "mean2": my,
                    "n": npair, "z": cov / se if npair else float("nan"),
                })
        return {"label": label, "n": n_pop, "biases": biases, "pairs": pairs}

    all_mask = [True] * n
    base = pop_stats(all_mask, "all_hard", None)

    def rms(xs):
        return math.sqrt(sum(x * x for x in xs) / len(xs)) if xs else float("nan")

    def meanabs(xs):
        return sum(abs(x) for x in xs) / len(xs) if xs else float("nan")

    by_A = []
    for A in As:
        mask = [still_cr[i] >= A for i in range(n)]
        st = pop_stats(mask, f"surv_A{A}", A)
        n_surv = st["n"]
        base_mu = {b["q"]: b["mean"] for b in base["biases"]}
        for b in st["biases"]:
            b["dmean"] = b["mean"] - base_mu[b["q"]]
        base_cov = {(p["q1"], p["q2"]): p["cov"] for p in base["pairs"]}
        for p in st["pairs"]:
            p["dcov"] = p["cov"] - base_cov[(p["q1"], p["q2"])]
        s2 = [b for b in st["biases"] if b["kind"] == "s2"]
        box = [b for b in st["biases"] if b["kind"] == "box"]
        inert = [b for b in st["biases"] if b["kind"] == "inert"]
        cov_33 = [p for p in st["pairs"] if p["kind1"] != "inert" and p["kind2"] != "inert"]
        cov_11 = [p for p in st["pairs"] if p["kind1"] == "inert" and p["kind2"] == "inert"]
        rec = {
            "A": A,
            "n_surv": n_surv,
            "mean_|z|_s2": meanabs([b["z"] for b in s2]),
            "mean_|z|_box": meanabs([b["z"] for b in box]),
            "mean_|z|_inert": meanabs([b["z"] for b in inert]),
            "rms_dmean_s2": rms([b["dmean"] for b in s2]),
            "rms_dmean_inert": rms([b["dmean"] for b in inert]),
            "mean_|z_cov|_3x3": meanabs([p["z"] for p in cov_33]),
            "mean_|z_cov|_1x1": meanabs([p["z"] for p in cov_11]),
            "pop": st,
        }
        by_A.append(rec)
        print(
            f"  A={A:3d}  n={n_surv:6d}  "
            f"|z| s2/box/inert="
            f"{rec['mean_|z|_s2']:.2f}/"
            f"{(rec['mean_|z|_box'] if rec['mean_|z|_box'] == rec['mean_|z|_box'] else 0):.2f}/"
            f"{rec['mean_|z|_inert']:.2f}  "
            f"|z|_cov 3×3/1×1="
            f"{rec['mean_|z_cov|_3x3']:.2f}/{rec['mean_|z_cov|_1x1']:.2f}",
            flush=True,
        )

    out = {
        "Xmax": Xmax,
        "Amax": Amax,
        "n_hard": n,
        "elapsed_s": time.time() - t0,
        "qs": qs,
        "all_hard": base,
        "by_A": by_A,
        "n_surv": {rec["A"]: rec["n_surv"] for rec in by_A},
    }
    print(f"  elapsed {out['elapsed_s']:.1f}s", flush=True)
    return out


if __name__ == "__main__":
    Xmax = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000_000
    Amax = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    out = main(Xmax, Amax)
    path = f"c4_c2_symbols_X{Xmax}_A{Amax}.json"
    # drop bulky per-A pair lists' redundancy? keep them; file is small
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"wrote {path}")
