#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""In-house certificate measurements for T(A).

(1) Converse: ClassRough vs ∃ real odd χ mod 4a certifying the coprime
    prime factors of p+4a². Exact direction is Lean classRough_of_certifies;
    this owns the other direction as a measurement.

(2) Shared certificates as dummy covering: on primes that survive a
    prefix a≤A0, does a character that certified a divisor a'|a also
    certify the later slice? Inheritance ⇒ cond→1 is the same χ, not
    new covering. Does not densify; does not grow d>1.

(3) Assignment partition function: global Z of (χ_a) consistent along
    the divisibility poset, vs Π nχ(a). Compare log Ĉ from the existing
    growing-A JSON. No new primes.

Default Xmax = 10^6, Amax = 40. Do not run 10^10.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

from c4_S_xscan import (
    factor_spf,
    has_aligned_divisor,
    sieve_hard_primes,
    spf_numpy,
)
from c4_c2_symbols import jacobi
from c4_surface_fit import nchi_odd, ols


HERE = os.path.dirname(os.path.abspath(__file__))
GROW_JSON = os.path.join(HERE, "c4_growing_A_X1000000000_A200.json")


def chi4(n: int) -> int:
    if n % 2 == 0:
        return 0
    return 1 if n % 4 == 1 else -1


def chi8(n: int) -> int:
    if n % 2 == 0:
        return 0
    return 1 if (n * n - 1) // 8 % 2 == 0 else -1


def odd_prime_factors(n: int) -> list[int]:
    n = abs(n)
    out: list[int] = []
    p = 3
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 2
    if n > 1:
        if n % 2 == 0:
            while n % 2 == 0:
                n //= 2
            if n > 1:
                out.append(n)
        else:
            out.append(n)
    return out


def gens_of(a: int) -> list:
    """Named generators of real characters of (Z/4aZ)*."""
    g: list = ["chi4"]
    if a % 2 == 0:
        g.append("chi8")
    g.extend(odd_prime_factors(a))
    return g


def eval_named(gens: list, mask: int, n: int) -> int:
    r = 1
    for i, g in enumerate(gens):
        if not (mask >> i) & 1:
            continue
        if g == "chi4":
            r *= chi4(n)
        elif g == "chi8":
            r *= chi8(n)
        else:
            if n % 2 == 0:
                return 0
            r *= jacobi(int(g), n)
        if r == 0:
            return 0
    return r


def odd_masks(a: int) -> list[int]:
    gens = gens_of(a)
    m = 4 * a
    out = []
    for mask in range(1 << len(gens)):
        if eval_named(gens, mask, m - 1) == -1:
            out.append(mask)
    return out


def phi(n: int) -> int:
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


def odd_primes_upto(n: int) -> list[int]:
    if n < 3:
        return []
    sv = bytearray(b"\x01") * (n + 1)
    sv[0:2] = b"\x00\x00"
    r = int(n**0.5)
    for p in range(2, r + 1):
        if sv[p]:
            start = p * p
            sv[start : n + 1 : p] = b"\x00" * ((n - start) // p + 1)
    return [i for i in range(3, n + 1) if sv[i]]


def gf2_rank(rows: list[int], nvars: int) -> int:
    """Rank of a 0-1 matrix given as bitmasks, over GF(2)."""
    mat = list(rows)
    rank = 0
    for col in range(nvars):
        piv = None
        for i in range(rank, len(mat)):
            if (mat[i] >> col) & 1:
                piv = i
                break
        if piv is None:
            continue
        mat[rank], mat[piv] = mat[piv], mat[rank]
        bit = 1 << col
        for i in range(len(mat)):
            if i != rank and mat[i] & bit:
                mat[i] ^= mat[rank]
        rank += 1
    return rank


def partition_function(Amax: int) -> dict:
    """Z_global: # global Kronecker assignments with every restriction odd.

    Generators: χ₄ (forced on by a=1), χ₈ (free for A≥2), and (p/·) for
    each odd prime p≤A. Consistent (χ_a) along a|b are exactly these
    global characters, reduced.

    Oddness is vacuous: if p|a then (p/(4a−1))=+1 by quadratic
    reciprocity (4a−1 ≡ −1 (mod p) and 4a−1 ≡ 3 (mod 4)), and χ₈(4a−1)=+1
    when a is even. Rank of the GF(2) system is identically 0, so
    Z_global(A) = 2^{1+π_odd(A)} for A≥2.
    """
    primes = odd_primes_upto(Amax)
    pidx = {p: i for i, p in enumerate(primes)}
    nvars = len(primes)
    rows: list[int] = []
    for a in range(1, Amax + 1):
        row = 0
        m1 = 4 * a - 1
        x = a
        p = 3
        while p * p <= x:
            if x % p == 0:
                while x % p == 0:
                    x //= p
                if pidx.get(p) is not None and jacobi(p, m1) == -1:
                    row |= 1 << pidx[p]
            p += 2
        if x > 1:
            px = x
            if px % 2 == 0:
                while px % 2 == 0:
                    px //= 2
            if px > 1 and pidx.get(px) is not None and jacobi(px, m1) == -1:
                row |= 1 << pidx[px]
        rows.append(row)
    rank = gf2_rank(rows, nvars)
    chi8_free = 2 if Amax >= 2 else 1
    z_global = chi8_free * (1 << (nvars - rank)) if nvars >= rank else 0
    z_local = 1
    nchi = []
    log_nchi = 0.0
    log_nchi_over_a = 0.0
    log_nchi_over_phi = 0.0
    curve = []
    for a in range(1, Amax + 1):
        na = nchi_odd(a)
        nchi.append(na)
        z_local *= na
        log_nchi += math.log(na)
        log_nchi_over_a += math.log(na) / a
        log_nchi_over_phi += math.log(na) / phi(4 * a)
        # running global Z at this A (recompute rank prefix)
        # cheaper: record at each a by filtering rows[:a]
        curve.append({"a": a, "nchi": na})

    # running Z_global(A) for A=1..Amax
    running = []
    for A in range(1, Amax + 1):
        primes_A = [p for p in primes if p <= A]
        pidx_A = {p: i for i, p in enumerate(primes_A)}
        nv = len(primes_A)
        rs = []
        for a in range(1, A + 1):
            row = 0
            m1 = 4 * a - 1
            for p in odd_prime_factors(a):
                j = pidx_A.get(p)
                if j is not None and jacobi(p, m1) == -1:
                    row |= 1 << j
            rs.append(row)
        rk = gf2_rank(rs, nv)
        z = (2 if A >= 2 else 1) * (1 << (nv - rk))
        running.append({
            "a": A,
            "nvars": nv,
            "rank": rk,
            "dim": nv - rk,
            "Z_global": z,
            "nchi": nchi[A - 1],
            "log_nchi_cum": sum(math.log(nchi[i]) for i in range(A)),
        })

    return {
        "Amax": Amax,
        "nvars": nvars,
        "rank": rank,
        "dim": nvars - rank,
        "Z_global": z_global,
        "Z_local": z_local,
        "log_Z_global": math.log(z_global) if z_global else float("-inf"),
        "log_Z_local": log_nchi,
        "log_nchi_over_a": log_nchi_over_a,
        "log_nchi_over_phi": log_nchi_over_phi,
        "chi8_free": chi8_free,
        "running": running,
        "nchi_vs_enum": None,
    }


def nchi_enum_check(Amax: int) -> list[dict]:
    mismatches = []
    for a in range(1, Amax + 1):
        got = len(odd_masks(a))
        want = nchi_odd(a)
        if got != want:
            mismatches.append({"a": a, "enum": got, "formula": want})
    return mismatches


def partition_vs_chat(Amax: int = 200) -> dict:
    part = partition_function(Amax)
    with open(GROW_JSON) as f:
        grow = json.load(f)
    chats = [r["C_hat"] for r in grow["enrich"]]
    xs_log2, ys = [], []
    pred = {
        "log2A": [],
        "log_Zg": [],
        "log_Zl": [],
        "log_Zl_over_Zg": [],
        "log_nchi_over_a": [],
        "log_nchi_over_phi": [],
        "dim": [],
        "rank": [],
    }
    log_nchi_a = 0.0
    log_nchi_phi = 0.0
    for r in part["running"]:
        A = r["a"]
        C = chats[A - 1]
        if A < 40 or C <= 0:
            log_nchi_a += math.log(r["nchi"]) / A
            log_nchi_phi += math.log(r["nchi"]) / phi(4 * A)
            continue
        ys.append(math.log(C))
        xs_log2.append(math.log(A) ** 2)
        pred["log2A"].append(math.log(A) ** 2)
        pred["log_Zg"].append(math.log(r["Z_global"]) if r["Z_global"] else 0.0)
        pred["log_Zl"].append(r["log_nchi_cum"])
        zg = r["Z_global"]
        pred["log_Zl_over_Zg"].append(
            r["log_nchi_cum"] - (math.log(zg) if zg else 0.0)
        )
        log_nchi_a += math.log(r["nchi"]) / A
        log_nchi_phi += math.log(r["nchi"]) / phi(4 * A)
        pred["log_nchi_over_a"].append(log_nchi_a)
        pred["log_nchi_over_phi"].append(log_nchi_phi)
        pred["dim"].append(r["dim"])
        pred["rank"].append(r["rank"])

    fits = {}
    for name, xs in pred.items():
        fits[name] = ols(xs, ys) if len(xs) == len(ys) and len(xs) >= 8 else None

    snap = []
    for A in (40, 80, 120, 160, 200):
        if A > Amax:
            continue
        r = part["running"][A - 1]
        snap.append({
            "A": A,
            "C_hat": chats[A - 1],
            "log_C_hat": math.log(chats[A - 1]),
            "Z_global": r["Z_global"],
            "log_Z_global": math.log(r["Z_global"]) if r["Z_global"] else None,
            "log_nchi_cum": r["log_nchi_cum"],
            "rank": r["rank"],
            "dim": r["dim"],
            "nvars": r["nvars"],
        })

    part["fits_vs_logC"] = {
        k: ({"slope": v["slope"], "intercept": v["intercept"], "r2": v["r2"]}
            if v else None)
        for k, v in fits.items()
    }
    part["snapshot"] = snap
    part["n_pts"] = len(ys)
    # drop bulky running from the printed summary later; keep in JSON
    return part


def coprime_primes(fac: list[tuple[int, int]], m: int) -> list[int]:
    out = []
    for q, _e in fac:
        if math.gcd(q, m) == 1:
            out.append(q)
    return out


def certifying_masks(a: int, gens: list, masks: list[int], qs: list[int]) -> list[int]:
    hit = []
    for mask in masks:
        ok = True
        for q in qs:
            if eval_named(gens, mask, q) != 1:
                ok = False
                break
        if ok:
            hit.append(mask)
    return hit


def measure(Xmax: int = 1_000_000, Amax: int = 40, A0s: tuple[int, ...] = (5, 10, 20)) -> dict:
    t0 = time.time()
    print(f"certificates  Xmax={Xmax} Amax={Amax}", flush=True)
    mismatch_nchi = nchi_enum_check(Amax)
    print(f"  nχ enum vs formula mismatches: {len(mismatch_nchi)}", flush=True)

    hard = sieve_hard_primes(Xmax)
    print(f"  {len(hard)} hard  ({time.time()-t0:.1f}s)", flush=True)
    spf = spf_numpy(Xmax + 4 * Amax * Amax)
    print(f"  SPF done  ({time.time()-t0:.1f}s)", flush=True)

    gens = [None] + [gens_of(a) for a in range(1, Amax + 1)]
    masks = [None] + [odd_masks(a) for a in range(1, Amax + 1)]
    mods = [0] + [4 * a for a in range(1, Amax + 1)]
    divisors = [None]
    for a in range(1, Amax + 1):
        divisors.append([d for d in range(1, a + 1) if a % d == 0])

    # converse accumulators
    # four cells: CR×cert
    n_cr = n_cert = n_both = n_neither = n_cr_not = n_cert_not = 0
    by_omega: dict[int, dict[str, int]] = {}
    by_a = [{"a": a, "n": 0, "cr": 0, "cert": 0, "both": 0,
             "cr_not_cert": 0, "cert_not_cr": 0} for a in range(Amax + 1)]
    omega_of = lambda k: k if k <= 6 else 7  # 7 = 7+

    n = len(hard)
    # still prefix; cert masks per (i,a) as list of lists
    still = [0] * n
    cert_at: list[list[list[int]]] = [[[] for _ in range(Amax)] for _ in range(n)]
    cr_at = [bytearray(Amax) for _ in range(n)]
    chi4_at = [bytearray(Amax) for _ in range(n)]

    step = 500 if n > 2000 else 200
    for i, p in enumerate(hard):
        if i % step == 0 and i:
            print(f"  factored {i}/{n}  ({time.time()-t0:.1f}s)", flush=True)
        prefix_ok = True
        for a in range(1, Amax + 1):
            N = p + 4 * a * a
            fac = factor_spf(N, spf)
            cr = not has_aligned_divisor(fac, mods[a])
            qs = coprime_primes(fac, mods[a])
            w = omega_of(len(qs))
            hit = certifying_masks(a, gens[a], masks[a], qs)
            cert = len(hit) > 0
            chi4_cert = all(chi4(q) == 1 for q in qs)

            cell = by_omega.setdefault(w, {
                "n": 0, "cr": 0, "cert": 0, "both": 0,
                "cr_not_cert": 0, "cert_not_cr": 0,
            })
            cell["n"] += 1
            by_a[a]["n"] += 1
            if cr:
                n_cr += 1
                cell["cr"] += 1
                by_a[a]["cr"] += 1
            if cert:
                n_cert += 1
                cell["cert"] += 1
                by_a[a]["cert"] += 1
            if cr and cert:
                n_both += 1
                cell["both"] += 1
                by_a[a]["both"] += 1
            elif cr and not cert:
                n_cr_not += 1
                cell["cr_not_cert"] += 1
                by_a[a]["cr_not_cert"] += 1
            elif cert and not cr:
                n_cert_not += 1
                cell["cert_not_cr"] += 1
                by_a[a]["cert_not_cr"] += 1
            else:
                n_neither += 1

            if cr:
                cr_at[i][a - 1] = 1
                if prefix_ok:
                    still[i] = a
            else:
                prefix_ok = False
            if cert:
                cert_at[i][a - 1] = hit
            if chi4_cert:
                chi4_at[i][a - 1] = 1

    del spf
    n_slots = n * Amax
    converse = {
        "n_hard": n,
        "n_slots": n_slots,
        "cr": n_cr,
        "cert": n_cert,
        "both": n_both,
        "cr_not_cert": n_cr_not,
        "cert_not_cr": n_cert_not,
        "neither": n_neither,
        "P_cert_given_cr": n_both / n_cr if n_cr else None,
        "P_cr_given_cert": n_both / n_cert if n_cert else None,
        "by_omega": {str(k): v for k, v in sorted(by_omega.items())},
        "by_a": by_a[1:],
        "nchi_enum_mismatches": mismatch_nchi,
    }

    # dummy covering / inheritance
    inherit_rows = []
    for A0 in A0s:
        if A0 >= Amax:
            continue
        idx = [i for i in range(n) if still[i] >= A0]
        n0 = len(idx)
        later = []
        for a in range(A0 + 1, Amax + 1):
            n_cr_l = n_cert_l = n_chi4 = n_inh = n_inh_odd = 0
            divs_small = [d for d in divisors[a] if d <= A0]
            for i in idx:
                if cr_at[i][a - 1]:
                    n_cr_l += 1
                if cert_at[i][a - 1]:
                    n_cert_l += 1
                if chi4_at[i][a - 1]:
                    n_chi4 += 1
                inherited = False
                inherited_odd = False
                # rebuild qs? expensive. Use stored cert masks from a'|a
                # Evaluate inherited χ on later N by re-reading factors...
                # We stored only masks at each a, not the primes of N_a.
                # Inheritance test: some certifying mask at a'|a, a'≤A0,
                # as a named character, is among certifying masks at a
                # after translating bits by generator names.
                for a1 in divs_small:
                    for mask1 in cert_at[i][a1 - 1]:
                        # translate mask1 (gens a1) to a function; check
                        # it equals some certifying mask at a with matching
                        # named gens, and is odd at 4a.
                        g1 = gens[a1]
                        ga = gens[a]
                        # build mask on gens[a] that turns on the same named gens
                        mask_a = 0
                        ok_trans = True
                        for j, g in enumerate(g1):
                            if not (mask1 >> j) & 1:
                                continue
                            if g not in ga:
                                ok_trans = False
                                break
                            mask_a |= 1 << ga.index(g)
                        if not ok_trans:
                            continue
                        if eval_named(g1, mask1, mods[a] - 1) == -1:
                            inherited_odd = True
                            if mask_a in cert_at[i][a - 1]:
                                inherited = True
                                break
                    if inherited:
                        break
                if inherited:
                    n_inh += 1
                if inherited_odd:
                    n_inh_odd += 1
            later.append({
                "a": a,
                "n_prefix": n0,
                "P_cr": n_cr_l / n0 if n0 else None,
                "P_cert": n_cert_l / n0 if n0 else None,
                "P_chi4": n_chi4 / n0 if n0 else None,
                "P_inherited": n_inh / n0 if n0 else None,
                "P_inherited_odd_at_a": n_inh_odd / n0 if n0 else None,
                "n_cr": n_cr_l,
                "n_cert": n_cert_l,
                "n_chi4": n_chi4,
                "n_inherited": n_inh,
            })
        inherit_rows.append({
            "A0": A0,
            "n_prefix": n0,
            "later": later,
            "mean_P_cr": (
                sum(r["P_cr"] for r in later) / len(later) if later else None
            ),
            "mean_P_inherited": (
                sum(r["P_inherited"] for r in later) / len(later) if later else None
            ),
            "mean_P_chi4": (
                sum(r["P_chi4"] for r in later) / len(later) if later else None
            ),
            "end_P_cr": later[-1]["P_cr"] if later else None,
            "end_P_inherited": later[-1]["P_inherited"] if later else None,
            "end_P_chi4": later[-1]["P_chi4"] if later else None,
        })

    out = {
        "Xmax": Xmax,
        "Amax": Amax,
        "n_hard": n,
        "elapsed_s": time.time() - t0,
        "converse": converse,
        "inherit": inherit_rows,
        "still_hist": {str(k): still.count(k) for k in range(Amax + 1)},
        "n_still_Amax": sum(1 for s in still if s >= Amax),
    }
    print(f"  elapsed {out['elapsed_s']:.1f}s", flush=True)
    return out


def main(Xmax: int = 1_000_000, Amax: int = 40) -> dict:
    part = partition_vs_chat(200)
    print("partition vs log Ĉ (A≥40, x=1e9 growing-A):", flush=True)
    for k, v in part["fits_vs_logC"].items():
        if v:
            print(f"  {k:20s}  slope={v['slope']:.5f}  R²={v['r2']:.4f}",
                  flush=True)
    for s in part["snapshot"]:
        print(
            f"  A={s['A']:3d}  Ĉ={s['C_hat']:.3f}  "
            f"log Ĉ={s['log_C_hat']:.3f}  "
            f"log Zg={s['log_Z_global']:.3f}  "
            f"rank={s['rank']} dim={s['dim']}",
            flush=True,
        )
    emp = measure(Xmax, Amax)
    c = emp["converse"]
    print(
        f"converse  slots={c['n_slots']}  "
        f"P(cert|CR)={c['P_cert_given_cr']:.4f}  "
        f"cert_not_CR={c['cert_not_cr']}  "
        f"CR_not_cert={c['cr_not_cert']}",
        flush=True,
    )
    for w, cell in sorted(c["by_omega"].items(), key=lambda kv: int(kv[0])):
        label = w if w != "7" else "7+"
        pcc = cell["both"] / cell["cr"] if cell["cr"] else None
        print(
            f"  ω={label}  n={cell['n']}  CR={cell['cr']}  "
            f"CR\\cert={cell['cr_not_cert']}  "
            f"P(cert|CR)={pcc}",
            flush=True,
        )
    for rec in emp["inherit"]:
        print(
            f"inherit A0={rec['A0']}  n0={rec['n_prefix']}  "
            f"end P(CR)={rec['end_P_cr']}  "
            f"end P(inh)={rec['end_P_inherited']}  "
            f"end P(χ₄)={rec['end_P_chi4']}",
            flush=True,
        )
    # drop running curve from JSON? keep it; useful. It's ~200 rows.
    running = part.pop("running")
    out = {
        "empirical": emp,
        "partition": {
            **{k: v for k, v in part.items() if k != "running"},
            "running_tail": running[39::20],  # A=40,60,... snapshots extra
        },
    }
    # put running back into a compact form
    out["partition"]["running"] = [
        {k: r[k] for k in ("a", "Z_global", "rank", "dim", "nvars", "log_nchi_cum")}
        for r in running
        if r["a"] in {40, 80, 120, 160, 200} or r["a"] % 10 == 0
    ]
    return out


if __name__ == "__main__":
    Xmax = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    Amax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    out = main(Xmax, Amax)
    path = f"c4_certificates_X{Xmax}_A{Amax}.json"
    with open(path, "w") as f:
        json.dump(out, f)
    print(f"wrote {path}")
