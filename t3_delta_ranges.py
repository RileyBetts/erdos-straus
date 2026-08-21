#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""T(3) δ-method range check at the joint modulus.

Heath-Brown, J. Reine Angew. Math. 481 (1996):
  δ(n) = c_Q Q^{-2} Σ_q Σ_{a mod q}^* e_q(a n) h(q/Q, n/Q^2),
  with h negligible unless q ≲ Q and |n| ≲ Q^2.

Detect p ≡ α(d1,d2,d3) (mod D) jointly by Σ_k δ(n − α − D k), then
Vaughan/Heath-Brown Type II n = m ν with M+N = 1 (log-exponents).

Notation (exponents in units of log x):
  Q_D   = α1+α2+α3     arithmetic CRT modulus D ≍ d1 d2 d3
  Q_δ   = Farey/δ order (dissection parameter, not D)
  M, N  = Type II lengths, M+N = 1, 0 < N ≤ 1/2 ≤ M < 1
  K     = max(1 − Q_D, 0)   length of the AP index k ~ x/D
  bilinear (m,ν) vs Farey iff M < Q_δ and N < Q_δ
  k-complete iff K ≥ Q_δ > 0
  k-absent iff Q_D ≥ 1

This is a range check, not a covering run. Do not densify covering.
Do not re-run Zheng / A2.3.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def K_of(Q_D: Fraction) -> Fraction:
    return max(1 - Q_D, Fraction(0))


def bilinear(M: Fraction, N: Fraction, Q_d: Fraction) -> bool:
    return M < Q_d and N < Q_d


def k_complete(K: Fraction, Q_d: Fraction) -> bool:
    return K > 0 and K >= Q_d


def k_absent(Q_D: Fraction) -> bool:
    return Q_D >= 1


def lemma_no_complete_k_bilinear_at_wall() -> None:
    """Farey–k incompatibility.

    If M+N=1 and Q_D ≥ 1/2, one cannot have both
      (i)  (m,ν)-bilinear vs Farey: Q_δ > max(M,N) ≥ 1/2
      (ii) k-complete: Q_δ ≤ K = 1−Q_D ≤ 1/2.
    """
    Q_D_min = Fraction(1, 2)
    for i in range(0, 51):
        N = Fraction(i, 100)
        if N == 0 or N > Fraction(1, 2):
            continue
        M = 1 - N
        # Any Q_δ that is bilinear forces Q_δ > 1/2 ≥ K at the wall.
        K = K_of(Q_D_min)
        assert K == Fraction(1, 2)
        for j in range(1, 61):
            Q_d = Fraction(j, 40)  # up to 1.5
            both = bilinear(M, N, Q_d) and k_complete(K, Q_d)
            assert not both, (M, N, Q_d, K)
    # The obstruction is the cut 1/2, independent of the Type II split:
    assert Fraction(1, 2) == K_of(Fraction(1, 2))


def lemma_symmetric_k_absent() -> None:
    """At (1/2)^3, Q_D = 3/2 > 1 so k is absent. Same at (0,1/2,1/2)."""
    assert k_absent(Fraction(3, 2))
    assert k_absent(Fraction(1))
    assert K_of(Fraction(3, 2)) == 0
    assert K_of(Fraction(1)) == 0
    assert not k_absent(Fraction(1, 2))


def duals(M: Fraction, N: Fraction, Q_d: Fraction) -> tuple[Fraction, Fraction] | None:
    if not bilinear(M, N, Q_d):
        return None
    return Q_d - M, Q_d - N


def weil_balanced(I: Fraction, J: Fraction, Q_d: Fraction) -> bool:
    """Duals at Weil's |I| ~ √q ⇔ I = Q_δ/2 (log-exponents)."""
    return abs(float(I - Q_d / 2)) < 0.02 and abs(float(J - Q_d / 2)) < 0.02


def main() -> None:
    lemma_no_complete_k_bilinear_at_wall()
    lemma_symmetric_k_absent()
    print("Lemma (Farey–k incompatibility at Q_D ≥ 1/2): proved.")
    print("Lemma (k absent at Q_D ≥ 1): proved.")
    print()

    cells = {
        "bv_wall": {
            "name": "BV wall δ→0+",
            "alpha": (Fraction(1, 6), Fraction(1, 6), Fraction(1, 6)),
            "note": "product just past x^{1/2}; named T(3) stall of Phase 1",
        },
        "uneven_two_sqrt": {
            "name": "(0, 1/2, 1/2)",
            "alpha": (Fraction(0), Fraction(1, 2), Fraction(1, 2)),
            "note": "A2.3 leftover Type I, remaining pair at √x",
        },
        "symmetric": {
            "name": "(1/2)^3",
            "alpha": (Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)),
            "note": "three-way balanced switch, D ~ x^{3/2}",
        },
    }

    # Balanced Type II throughout.
    M = N = Fraction(1, 2)
    # Farey orders: wall, just past, 2/3, Weil-spot (=1), past x.
    farey = [
        Fraction(1, 2),
        Fraction(1, 2) + Fraction(1, 20),
        Fraction(2, 3),
        Fraction(1),
        Fraction(5, 6),
        Fraction(3, 2),
    ]

    out_cells = {}
    for key, spec in cells.items():
        a1, a2, a3 = spec["alpha"]
        Q_D = a1 + a2 + a3
        K = K_of(Q_D)
        additive_bil = bilinear(M, N, Q_D)
        rows = []
        for Q_d in farey:
            d = duals(M, N, Q_d)
            row = {
                "Q_delta": str(Q_d),
                "Q_delta_float": float(Q_d),
                "bilinear_mn": bilinear(M, N, Q_d),
                "k_complete": k_complete(K, Q_d),
                "k_absent": k_absent(Q_D),
                "both_bilinear_and_k_complete": bilinear(M, N, Q_d)
                and k_complete(K, Q_d),
                "I": None if d is None else str(d[0]),
                "J": None if d is None else str(d[1]),
                "I_float": None if d is None else float(d[0]),
                "weil_spot": False if d is None else weil_balanced(*d, Q_d),
            }
            rows.append(row)
        out_cells[key] = {
            "name": spec["name"],
            "alpha": [str(a) for a in spec["alpha"]],
            "Q_D": str(Q_D),
            "Q_D_float": float(Q_D),
            "K": str(K),
            "K_float": float(K),
            "additive_characters_bilinear": additive_bil,
            "note": spec["note"],
            "farey_scan": rows,
        }

    # 2D Farey (Heath-Brown–Pierce analogue): two dissection orders Q1, Q2
    # for the two linear relations after eliminating p. Combined modulus
    # for the (d1,n1) phase is Q1+Q2 (log). Incomplete in n1 ~ 1/2 iff
    # Q1+Q2 > 1/2. Type II bilinear still lives on a *third* δ for
    # d1 n1 − mν = 4, whose order Q3 is independent of (Q1,Q2).
    q1q2 = []
    for i in range(0, 7):
        Q1 = Fraction(i, 12)
        for j in range(0, 7):
            Q2 = Fraction(j, 12)
            q1q2.append(
                {
                    "Q1": str(Q1),
                    "Q2": str(Q2),
                    "combined_for_n1": str(Q1 + Q2),
                    "n1_incomplete": (Q1 + Q2) > Fraction(1, 2),
                    "opens_mn_bilinear": False,  # Q1,Q2 do not open Type II
                }
            )

    out = {
        "lemmas": {
            "farey_k_incompatibility": (
                "If M+N=1 and Q_D ≥ 1/2, (m,ν)-bilinear vs Farey and "
                "k-complete cannot both hold."
            ),
            "k_absent_past_x": "If Q_D ≥ 1 then K=0; there is no AP index to complete.",
            "stall_lemma_is_bv_wall": (
                "M+N=1, Q=1/2 forbids bilinear for additive characters "
                "(Phase 1). That is Q_D=1/2, not (0,1/2,1/2) and not (1/2)^3."
            ),
        },
        "cells": out_cells,
        "two_d_farey_note": (
            "Heath-Brown–Pierce 2D Kloosterman is a minor-arc L^2 bound "
            "for two quadratic forms in k≥5 variables. The T(3) pair of "
            "linear relations is 2-dimensional, but Type II bilinear for "
            "the prime lives on a third δ (Q3). Q1,Q2 do not replace Q3."
        ),
        "two_d_farey_sample": q1q2[:8],
        "bettin_chandee": (
            "Trilinear Kloosterman fractions B(M,N,A) add an averaging "
            "variable a∈A to DFI, not three independent residue moduli."
        ),
        "verdict": {
            "avoids_uneven_cell_identity": True,
            "avoids_bv_wall_identity": False,
            "reaches_D_up_to_x": False,
            "reaches_D_up_to_x_3_2": False,
            "t3_progress": False,
            "note": (
                "At (0,1/2,1/2) and (1/2)^3 the k-sum is absent, so the "
                "stall identity M+N=1, Q=1/2 does not apply to the Farey "
                "modulus. Additive characters already give Q_D ≥ 1 > 1/2, "
                "so bilinear exists. Opening Farey Q_δ > 1/2 still has "
                "short duals until Q_δ ~ 1 (Weil). No bound is claimed "
                "for D up to x or x^{3/2}. At the BV wall the extra Q_δ "
                "cannot both open bilinear and complete k; the degeneracy "
                "reappears as that incompatibility."
            ),
        },
    }

    print("Balanced Type II M=N=1/2.")
    print()
    for key, cell in out_cells.items():
        print(f"{cell['name']}: Q_D={cell['Q_D']}, K={cell['K']}, "
              f"additive bilinear={cell['additive_characters_bilinear']}")
        for row in cell["farey_scan"]:
            flag = ""
            if row["both_bilinear_and_k_complete"]:
                flag = "  BOTH (forbidden)"
            elif row["bilinear_mn"] and cell["K_float"] == 0:
                flag = "  bilinear, k-absent"
            elif row["bilinear_mn"] and not row["k_complete"]:
                flag = "  bilinear, k incomplete"
            elif row["k_complete"] and not row["bilinear_mn"]:
                flag = "  k-complete, (m,ν) folded"
            print(f"  Q_δ={row['Q_delta']:8s}  bil={row['bilinear_mn']}  "
                  f"k-comp={row['k_complete']}  I={row['I']}{flag}")
        print()

    print("VERDICT:", out["verdict"]["note"])

    path = Path("t3_delta_ranges.json")
    path.write_text(json.dumps(out, indent=2) + "\n")
    print()
    print(f"Wrote {path}")


if __name__ == "__main__":
    main()
