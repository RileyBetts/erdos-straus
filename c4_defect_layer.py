#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Defect layer of ClassRough vs certificate-union.

Squarefree model: ω residues in G = (Z/4aZ)*. ClassRough = no nonempty
subset product ≡ −1 (mod 4a). Certificate = −1 ∉ ⟨residues⟩.

These coincide iff G is an elementary 2-group (λ(4a) | 2), which holds
exactly for a ∈ {1, 2, 3, 6}. Measured converse (c4_certificates.py) is
exact on those four slices and opens at a = 4.

Default: exact enumeration for φ(4a)^ω ≤ ENUM_MAX, else Monte Carlo.
No new prime scan. Do not run 10^10.
"""

from __future__ import annotations

import itertools
import json
import math
import os
import random
import sys
import time


HERE = os.path.dirname(os.path.abspath(__file__))
CERT_JSON = os.path.join(HERE, "c4_certificates_X1000000_A40.json")
ENUM_MAX = 2_000_000


def units(m: int) -> list[int]:
    return [k for k in range(1, m) if math.gcd(k, m) == 1]


def carmichael_lambda(n: int) -> int:
    """λ(n), Carmichael function."""
    if n <= 0:
        raise ValueError(n)
    x, n0, lam = n, n, 1

    def lcm(a: int, b: int) -> int:
        return a // math.gcd(a, b) * b

    v2 = 0
    while x % 2 == 0:
        x //= 2
        v2 += 1
    if v2 == 1:
        lam = lcm(lam, 1)
    elif v2 == 2:
        lam = lcm(lam, 2)
    elif v2 >= 3:
        lam = lcm(lam, 1 << (v2 - 2))
    p = 3
    while p * p <= x:
        if x % p == 0:
            pk, phi = p, p - 1
            x //= p
            while x % p == 0:
                x //= p
                pk *= p
                phi *= p
            lam = lcm(lam, phi)
        p += 2
    if x > 1:
        lam = lcm(lam, x - 1)
    return lam if n0 > 1 else 1


def elem2_as() -> list[int]:
    """a ≥ 1 with λ(4a) | 2: v2(a) ≤ 1 and odd part of a is 1 or 3."""
    out = []
    for a in range(1, 200):
        if carmichael_lambda(4 * a) <= 2:
            out.append(a)
    return out


def subgroup(gens: tuple[int, ...], m: int) -> set[int]:
    s = {1 % m}
    changed = True
    while changed:
        changed = False
        extra = []
        for g in gens:
            for x in s:
                y = (x * g) % m
                if y not in s:
                    extra.append(y)
        if extra:
            s.update(extra)
            changed = True
    return s


def subset_products(gs: tuple[int, ...], m: int) -> set[int]:
    out = {1 % m}
    for g in gs:
        out |= {(x * g) % m for x in out}
    return out


def stats_of_tuple(gs: tuple[int, ...], m: int) -> tuple[bool, bool]:
    minus = (m - 1) % m
    cr = minus not in subset_products(gs, m)
    cert = minus not in subgroup(gs, m)
    return cr, cert


def enumerate_omega(a: int, omega: int, rng: random.Random, n_mc: int = 80_000) -> dict:
    m = 4 * a
    G = units(m)
    nG = len(G)
    n_space = nG ** omega if omega else 1
    exact = n_space <= ENUM_MAX
    n_cr = n_cert = n_cr_not = 0
    n = 0
    if omega == 0:
        cr, cert = stats_of_tuple((), m)
        return {
            "a": a, "omega": 0, "phi": nG, "n": 1, "exact": True,
            "P_cr": float(cr), "P_cert": float(cert),
            "P_cr_not_cert": float(cr and not cert),
        }
    if exact:
        for gs in itertools.product(G, repeat=omega):
            cr, cert = stats_of_tuple(gs, m)
            n += 1
            n_cr += int(cr)
            n_cert += int(cert)
            n_cr_not += int(cr and not cert)
    else:
        for _ in range(n_mc):
            gs = tuple(rng.choice(G) for _ in range(omega))
            cr, cert = stats_of_tuple(gs, m)
            n += 1
            n_cr += int(cr)
            n_cert += int(cert)
            n_cr_not += int(cr and not cert)
    return {
        "a": a,
        "omega": omega,
        "phi": nG,
        "lambda": carmichael_lambda(m),
        "elem2": carmichael_lambda(m) <= 2,
        "n": n,
        "exact": exact,
        "P_cr": n_cr / n,
        "P_cert": n_cert / n,
        "P_cr_not_cert": n_cr_not / n,
        "P_cert_given_cr": (n_cert / n_cr) if n_cr else float("nan"),
    }


def main(Amax: int = 12, Wmax: int = 5) -> dict:
    t0 = time.time()
    rng = random.Random(4)
    exact_as = elem2_as()
    print(f"defect layer  λ(4a)|2 ⇒ a in {exact_as}", flush=True)

    rows = []
    for a in range(1, Amax + 1):
        for w in range(1, Wmax + 1):
            rec = enumerate_omega(a, w, rng)
            rows.append(rec)
            if w == 1 or a <= 6:
                print(
                    f"  a={a:2d} ω={w}  φ={rec['phi']:3d}  "
                    f"P(CR)={rec['P_cr']:.3f}  P(χ)={rec['P_cert']:.3f}  "
                    f"defect={rec['P_cr_not_cert']:.3f}  "
                    f"{'exact' if rec['exact'] else 'MC'}",
                    flush=True,
                )

    pooled = {w: {"n": 0.0, "cr": 0.0, "cert": 0.0, "cr_not": 0.0} for w in range(1, Wmax + 1)}
    for rec in rows:
        w = rec["omega"]
        pooled[w]["n"] += 1
        pooled[w]["cr"] += rec["P_cr"]
        pooled[w]["cert"] += rec["P_cert"]
        pooled[w]["cr_not"] += rec["P_cr_not_cert"]
    pooled_out = {}
    print("\n  uniform-a model, P(χ|CR) vs ω:")
    for w, s in pooled.items():
        pcr = s["cr"] / s["n"]
        px = s["cert"] / s["n"]
        pgiven = px / pcr if pcr else float("nan")
        pooled_out[str(w)] = {
            "P_cr": pcr, "P_cert": px, "P_cert_given_cr": pgiven,
            "P_cr_not_cert": s["cr_not"] / s["n"],
        }
        print(f"    ω={w}  P(χ|CR)={pgiven:.3f}  (uniform a≤{Amax})", flush=True)

    measured = None
    if os.path.exists(CERT_JSON):
        emp = json.load(open(CERT_JSON))["empirical"]["converse"]
        measured = {
            "P_cert_given_cr": emp["P_cert_given_cr"],
            "by_omega": emp["by_omega"],
            "by_a_gap": [
                {
                    "a": r["a"],
                    "P_cert_given_cr": (r["cert"] / r["cr"]) if r["cr"] else None,
                    "cr_not_cert": r["cr_not_cert"],
                }
                for r in emp["by_a"] if 1 <= r["a"] <= max(Amax, 12)
            ],
        }
        print("\n  measured P(χ|CR) at x=10^6:")
        for w, cell in emp["by_omega"].items():
            rate = cell["cert"] / cell["cr"] if cell["cr"] else float("nan")
            print(f"    ω={w}  {rate:.3f}  (n_CR={cell['cr']})", flush=True)

    out = {
        "elapsed_s": time.time() - t0,
        "elem2_a": exact_as,
        "note": (
            "Squarefree independent-uniform residues in (Z/4aZ)*. "
            "CR = cert identically on elementary 2-groups, a in {1,2,3,6}. "
            "Defect is −1 in ⟨S⟩ but not a subset product. "
            "Pooled 100/90/66/35 is a mixture over a, not a single G."
        ),
        "rows": rows,
        "pooled_uniform_a": pooled_out,
        "measured": measured,
    }
    print(f"\n  elapsed {out['elapsed_s']:.1f}s", flush=True)
    return out


if __name__ == "__main__":
    Amax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    Wmax = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    result = main(Amax, Wmax)
    path = os.path.join(HERE, f"c4_defect_layer_A{Amax}_W{Wmax}.json")
    with open(path, "w") as f:
        json.dump(result, f)
    print(f"  wrote {path}")
