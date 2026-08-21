#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""T(2) range check: Zheng arXiv:2512.22798 Theorems 1.1 and 1.2.

Exponents in units of log x. After switching, d1, d2 ≤ √x, so the plane
is (α, β) ∈ [0, 1/2]² with d1 ~ x^α, d2 ~ x^β. Zheng's q is the shorter
leg (asymmetric): θ = min(α, β), σ = max(α, β).

This is a range check, not a covering run. Do not densify covering.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def L11(theta: Fraction) -> Fraction | None:
    """Zheng Theorem 1.1, piecewise L(θ), for 0 ≤ θ ≤ 7/36."""
    if theta < 0 or theta > Fraction(7, 36):
        return None
    if theta <= Fraction(1, 78):
        return Fraction(7, 13) - 3 * theta
    if theta <= Fraction(1, 40):
        return Fraction(1, 2)
    if theta <= Fraction(1, 35):
        return Fraction(7, 13) - Fraction(20, 13) * theta
    if theta <= Fraction(17, 192):
        return Fraction(19, 36) - Fraction(20, 17) * theta
    if theta <= Fraction(7, 72):
        return Fraction(295, 576) - theta
    return Fraction(151, 288) - Fraction(9, 8) * theta


def in_th11(alpha: Fraction, beta: Fraction) -> bool:
    theta = min(alpha, beta)
    sigma = max(alpha, beta)
    L = L11(theta)
    if L is None:
        return False
    return sigma <= L


def in_bv(alpha: Fraction, beta: Fraction) -> bool:
    """Ordinary Bombieri–Vinogradov: lcm(d1,d2) ≪ d1 d2 ≤ x^{1/2}."""
    return alpha + beta <= Fraction(1, 2)


def L12(theta: Fraction, nu: Fraction) -> Fraction | None:
    """Zheng Theorem 1.2, L(θ, ν), or None if (θ, ν) is outside all cases."""
    if theta < 0:
        return None
    # Case (1): θ ≤ 1/60, 1/10 ≤ ν ≤ 4/15, three ν-subranges.
    if theta <= Fraction(1, 60) and Fraction(1, 10) <= nu <= Fraction(4, 15):
        cut1 = (1 + theta) / 5
        cut2 = (2 - 13 * theta) / 7
        if nu <= cut1:
            return (1 + nu) / 2 - 3 * theta
        upper = min(cut2, Fraction(4, 15))
        if nu <= upper:
            return (2 - nu) / 3 - Fraction(17, 6) * theta
        if cut2 < Fraction(4, 15) and nu >= cut2:
            return 1 - Fraction(3, 2) * nu - 5 * theta
        return None
    # Case (2): θ ≤ 1/30, 31/90 ≤ ν ≤ 83/220.
    if theta <= Fraction(1, 30) and Fraction(31, 90) <= nu <= Fraction(83, 220):
        return (3 + 6 * nu - 12 * theta) / 10
    # Case (3): 1/60 ≤ θ ≤ 2/23, 8/23 ≤ ν ≤ 56/117.
    if Fraction(1, 60) <= theta <= Fraction(2, 23) and Fraction(8, 23) <= nu <= Fraction(
        56, 117
    ):
        return (16 + 5 * nu - 40 * theta) / 34
    return None


def lemma_L_exceeds_theta_at_endpoint() -> None:
    """At θ = 7/36, L(θ) = 11/36 > 7/36. Never θ = L(θ) on the interval."""
    theta = Fraction(7, 36)
    L = L11(theta)
    assert L == Fraction(11, 36), L
    assert L > theta
    # L decreases from 7/13 to 11/36, both > 7/36 ≥ θ.
    assert L11(Fraction(0)) == Fraction(7, 13)
    assert L11(Fraction(1, 78)) == Fraction(1, 2)
    assert Fraction(7, 13) > Fraction(7, 36)
    assert Fraction(11, 36) > Fraction(7, 36)


def grid(n: int = 180) -> list[tuple[Fraction, Fraction]]:
    """Inclusive grid of the switched plane [0, 1/2]², step 1/(2n)."""
    step = Fraction(1, 2 * n)
    vals = [step * i for i in range(n + 1)]
    return [(a, b) for a in vals for b in vals]


def native_zheng_unswitched(theta: Fraction, sigma: Fraction) -> bool:
    """No √x switch: q ~ x^θ, d ≤ x^{L(θ)}; the long leg may exceed 1/2."""
    if theta > sigma:
        theta, sigma = sigma, theta
    L = L11(theta)
    return L is not None and sigma <= L


def cube_covered(a: Fraction, b: Fraction, c: Fraction, eps: Fraction) -> dict[str, bool]:
    """Leftover Type I on one kernel, Zheng or pair-BV on a complementary pair."""
    three_bv = a + b + c <= Fraction(1, 2)
    zheng_slab = (
        (a <= eps and in_th11(b, c))
        or (b <= eps and in_th11(a, c))
        or (c <= eps and in_th11(a, b))
    )
    pair_bv_slab = (
        (a <= eps and b + c <= Fraction(1, 2))
        or (b <= eps and a + c <= Fraction(1, 2))
        or (c <= eps and a + b <= Fraction(1, 2))
    )
    return {
        "three_bv": three_bv,
        "zheng_slab": zheng_slab,
        "pair_bv_slab": pair_bv_slab,
        "any": three_bv or zheng_slab or pair_bv_slab,
    }


def reroute_tables() -> dict:
    """Coverage shift from uneven Type I leftover + Zheng on a sub-pair."""
    epsilons = {
        "polylog_face": Fraction(0),
        "theta_1_78": Fraction(1, 78),
        "theta_1_40": Fraction(1, 40),
        "theta_7_36": Fraction(7, 36),
    }
    plane = grid(180)
    plane_n = len(plane)
    plane_rows = {}
    for name, eps in epsilons.items():
        n_ti_zheng = n_union = n_ti_bv = 0
        for a, b in plane:
            ti_z = (a <= eps and in_th11(a, b)) or (b <= eps and in_th11(a, b))
            # Assign Type I leg as q (θ=eps-scale) and the other as d ≤ L(θ).
            if a <= eps:
                L = L11(a)
                if L is not None and b <= L:
                    ti_z = True
            if b <= eps:
                L = L11(b)
                if L is not None and a <= L:
                    ti_z = True
            ti_bv = (a <= eps or b <= eps) and in_bv(a, b)
            if ti_z:
                n_ti_zheng += 1
            if ti_bv:
                n_ti_bv += 1
            if in_bv(a, b) or in_th11(a, b) or ti_z:
                n_union += 1
        plane_rows[name] = {
            "eps": str(eps),
            "type_i_times_zheng": round(n_ti_zheng / plane_n, 6),
            "type_i_times_pair_bv": round(n_ti_bv / plane_n, 6),
            "union_bv_zheng_typei": round(n_union / plane_n, 6),
            "cell_sqrt_covered": bool(
                in_bv(Fraction(1, 2), Fraction(1, 2))
                or in_th11(Fraction(1, 2), Fraction(1, 2))
                or (eps >= Fraction(1, 2) and in_th11(Fraction(1, 2), Fraction(1, 2)))
            ),
        }

    n_unsw = 90
    step = Fraction(1, n_unsw)
    vals = [step * i for i in range(n_unsw + 1)]
    n_native = n_native_past_half = n_full = 0
    for a in vals:
        for b in vals:
            n_full += 1
            if native_zheng_unswitched(a, b):
                n_native += 1
                if max(a, b) > Fraction(1, 2):
                    n_native_past_half += 1

    n_cube = 36
    step_c = Fraction(1, 2 * n_cube)
    cvals = [step_c * i for i in range(n_cube + 1)]
    cube = [(a, b, c) for a in cvals for b in cvals for c in cvals]
    cube_n = len(cube)
    cube_rows = {}
    stall_cells = {}
    half = Fraction(1, 2)
    zero = Fraction(0)
    for name, eps in epsilons.items():
        counts = {"three_bv": 0, "zheng_slab": 0, "pair_bv_slab": 0, "any": 0}
        for a, b, c in cube:
            flags = cube_covered(a, b, c, eps)
            for k in counts:
                if flags[k]:
                    counts[k] += 1
        cube_rows[name] = {k: round(v / cube_n, 6) for k, v in counts.items()}
        stall_cells[name] = {
            "sym_half_half_half": cube_covered(half, half, half, eps)["any"],
            "type_i_two_sqrt": cube_covered(zero, half, half, eps)["any"],
            "type_i_two_sqrt_flags": {
                k: v for k, v in cube_covered(zero, half, half, eps).items()
            },
        }

    return {
        "note": (
            "Plan '91% of witnesses at a,m ≤ log² p' is covering-cell mass, "
            "not r_χ divisor mass. Polylog Type I is the α=0 face. "
            "The cell (0, 1/2, 1/2) is the uneven T(3) stall."
        ),
        "plane_type_i_slabs": plane_rows,
        "native_unswitched": {
            "grid": n_full,
            "zheng_box_frac_of_unit_square": round(n_native / n_full, 6),
            "of_which_long_leg_past_sqrt": round(n_native_past_half / n_full, 6),
            "long_leg_max": "7/13",
            "pairing_remark": (
                "A long leg in (1/2, 7/13] pairs to a switched divisor in "
                "[6/13, 1/2]; with a polylog short leg that cell is BV after pairing."
            ),
        },
        "cube_t3_uneven": cube_rows,
        "stall_cells": stall_cells,
        "cube_points": cube_n,
    }


def main() -> None:
    lemma_L_exceeds_theta_at_endpoint()
    print("Lemma: at θ=7/36, L(θ)=11/36 > θ. θ = L(θ) never occurs in range.")
    print()

    cells = grid(180)
    n = len(cells)
    n_bv = n_11 = n_11_only = n_uncovered = 0
    n_sym_half = n_sym_quarter = 0
    flags = {
        "cell_sqrt": None,
        "cell_quarter": None,
    }
    for a, b in cells:
        bv = in_bv(a, b)
        z11 = in_th11(a, b)
        if bv:
            n_bv += 1
        if z11:
            n_11 += 1
        if z11 and not bv:
            n_11_only += 1
        if not bv and not z11:
            n_uncovered += 1
        if a == Fraction(1, 2) and b == Fraction(1, 2):
            flags["cell_sqrt"] = {
                "alpha": "1/2",
                "beta": "1/2",
                "bv": bv,
                "th11": z11,
                "th12_note": "q-support ≤ x^{2/23}; does not reach √x",
            }
        if a == Fraction(1, 4) and b == Fraction(1, 4):
            flags["cell_quarter"] = {
                "alpha": "1/4",
                "beta": "1/4",
                "bv": bv,
                "th11": z11,
            }

    # Theorem 1.2: max L(θ,ν) and max θ; not a (d1,d2) window.
    max_L12 = None
    max_theta12 = Fraction(2, 23)
    nu_samples = [Fraction(i, 400) for i in range(40, 201)]
    theta_samples = [Fraction(i, 400) for i in range(0, 36)]
    for th in theta_samples:
        for nu in nu_samples:
            L = L12(th, nu)
            if L is None:
                continue
            if max_L12 is None or L > max_L12[0]:
                max_L12 = (L, th, nu)

    # Harmonic measure = Lebesgue on the exponent square (dα dβ).
    area = Fraction(1, 4)
    out = {
        "grid_points": n,
        "fractions": {
            "bv": n_bv / n,
            "th11": n_11 / n,
            "th11_past_bv": n_11_only / n,
            "uncovered": n_uncovered / n,
        },
        "switched_plane_area": "1/4",
        "endpoint_L": {
            "theta": "7/36",
            "L": "11/36",
            "L_minus_theta": "4/36=1/9",
        },
        "cell_sqrt_x": flags["cell_sqrt"],
        "cell_x_quarter": flags["cell_quarter"],
        "th12": {
            "theta_max": "2/23",
            "theta_max_float": float(max_theta12),
            "max_L": None if max_L12 is None else str(max_L12[0]),
            "max_L_float": None if max_L12 is None else float(max_L12[0]),
            "at_theta": None if max_L12 is None else str(max_L12[1]),
            "at_nu": None if max_L12 is None else str(max_L12[2]),
            "covers_sqrt_cell": False,
        },
        "dies_if": (
            "symmetric cell d1 ≈ d2 ≈ √x is in neither Theorem 1.1 nor 1.2; "
            "d1 ≈ d2 ≈ x^{1/4} is ordinary BV (product x^{1/2}). "
            "Zheng does not cover the two-modulus switching ceiling."
        ),
        "trivial_uncovered": (
            "Uncovered harmonic mass is a positive fraction of "
            "∫_{ [0,1/2]^2 } dα dβ. Pointwise trivial bound "
            "≪ x^{α+β} + x^{1-α-β} per dyadic cell; at α=β=1/2 this is ≪ x, "
            "which swamps S(2,x) ≍ (log x)^{-1}."
        ),
    }
    out["fractions"] = {k: round(v, 6) for k, v in out["fractions"].items()}

    reroute = reroute_tables()
    out["reroute"] = reroute
    out["dies_if_uneven"] = (
        "Leaving one kernel Type I / polylog converts T(3) to T(2) on the "
        "remaining pair. The cell (0, 1/2, 1/2) is still uncovered: the pair "
        "is the T(2) switching ceiling. Symmetric (1/2,1/2,1/2) remains uncovered. "
        "Not T(3) progress."
    )

    print("Switched plane [0, 1/2]², grid", n, "points.")
    print("  BV (α+β ≤ 1/2):          ", out["fractions"]["bv"])
    print("  Zheng 1.1:               ", out["fractions"]["th11"])
    print("  Zheng 1.1 past BV:       ", out["fractions"]["th11_past_bv"])
    print("  Uncovered:               ", out["fractions"]["uncovered"])
    print()
    print("Symmetric cell d1 ≈ d2 ≈ √x  (α=β=1/2):", flags["cell_sqrt"])
    print("Symmetric cell d1 ≈ d2 ≈ x^{1/4} (α=β=1/4):", flags["cell_quarter"])
    print()
    print("Theorem 1.2: θ ≤ 2/23;", "max L(θ,ν) =", out["th12"]["max_L"],
          "at θ =", out["th12"]["at_theta"], "ν =", out["th12"]["at_nu"])
    print()
    print("DIES IF:", out["dies_if"])
    print()
    print("Reroute (Type I leftover + Zheng on a sub-pair):")
    print("  native unswitched Zheng box / [0,1]²:",
          reroute["native_unswitched"]["zheng_box_frac_of_unit_square"],
          " (long leg past √x:",
          reroute["native_unswitched"]["of_which_long_leg_past_sqrt"], ")")
    print("  plane Type I slabs:")
    for name, row in reroute["plane_type_i_slabs"].items():
        print(f"    {name:16s} union={row['union_bv_zheng_typei']}  "
              f"√x-cell={row['cell_sqrt_covered']}")
    print("  T(3) cube, leftover ≤ ε:")
    for name, row in reroute["cube_t3_uneven"].items():
        stall = reroute["stall_cells"][name]
        print(f"    {name:16s} any={row['any']}  "
              f"(1/2)^3={stall['sym_half_half_half']}  "
              f"(0,1/2,1/2)={stall['type_i_two_sqrt']}")
    print()
    print("DIES IF (uneven):", out["dies_if_uneven"])

    path = Path("t2_zheng_ranges.json")
    path.write_text(json.dumps(out, indent=2) + "\n")
    print()
    print(f"Wrote {path}")


if __name__ == "__main__":
    main()
