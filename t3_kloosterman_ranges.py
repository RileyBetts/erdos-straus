#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""Phase 2 range check: T(3) r_χ Type II remainder vs Pascadi / Blomer–Pascadi / MQW.

Notation (exponents in units of log x):
  Q = 1/2 + δ     modulus D = lcm(d1,d2,d3)  (the named stall is δ → 0+)
  N = θ, M = 1-θ  Type II split of p-sum, MN = x, θ ≤ 1/2
  bilinear iff M < Q and N < Q (both factors shorter than the modulus,
    so Poisson produces two incomplete intervals, not a complete residue system)
  I = Q - M, J = Q - N   dual interval lengths in the Kloosterman arguments

Pascadi Cor 1.4: |I|, |J| ≪ Q^{1/2}.  Thm 7.1 beats Weil if (best factorisation)
  min(I,J) > Q^{2/5} with both ≤ Q.
Blomer–Pascadi Thm 1.1: max(I,J) ∈ (Q^{13/28}, Q^{7/12}).
MQW Thm 1.1: product-argument Kl_2(mn; Q) with Type II lengths (M,N), conditions
  (1.2) plus the balanced nontrivial threshold M ≳ Q^{10/21}.

This is a range check, not a covering run. Do not densify covering.
"""

from __future__ import annotations

import json
from pathlib import Path


def lemma_no_bilinear_cell_at_wall() -> None:
    """Lemma (no bilinear cell at δ=0).

    If M+N=1 and Q=1/2 (log-exponents), then M<Q and N<Q cannot both
    hold: otherwise M+N<2Q=1. This is an identity, not a grid artefact.
    """
    Q = 0.5
    for i in range(0, 101):
        N = i / 100
        M = 1 - N
        assert not bilinear(M, N, Q), (M, N, Q)
    # The obstruction is the sum, independent of the split:
    assert 1 == 2 * Q


def bilinear(M: float, N: float, Q: float) -> bool:
    return M < Q - 1e-15 and N < Q - 1e-15


def duals(M: float, N: float, Q: float) -> tuple[float, float] | None:
    if not bilinear(M, N, Q):
        return None
    return Q - M, Q - N


def pascadi_length_ok(I: float, J: float, Q: float) -> bool:
    cap = 0.5 * Q
    return I <= cap + 1e-12 and J <= cap + 1e-12


def pascadi_71_beats_weil(I: float, J: float, Q: float) -> bool:
    short = min(I, J)
    long = max(I, J)
    if long > Q + 1e-12:
        return False
    return short > (2 / 5) * Q + 1e-12


def bp_window(I: float, J: float, Q: float) -> bool:
    Nmax = max(I, J)
    if Nmax > Q + 1e-12:
        return False
    return (13 / 28) * Q < Nmax + 1e-12 and Nmax < (7 / 12) * Q + 1e-12


def balanced_duals(I: float, J: float, ratio: float = 0.5) -> bool:
    """Papers' saving is stated for |I| ~ |J| ~ N. Tiny × long is Weil's regime."""
    return min(I, J) >= ratio * max(I, J) - 1e-15


def bp_beats_weil(I: float, J: float, Q: float) -> bool:
    """Compare Thm 1.1's three-term bound to Weil √(|I||J|Q), in log-exponents.

    BP factor ~ max(I^{1/8} Q^{29/32}, J^{5/16} Q^{13/16}, N^{2/3} Q^{11/18})
    with N = max(I,J). Save iff this is strictly smaller than 0.5*(I+J+Q).
    """
    N = max(I, J)
    terms = [
        (1 / 8) * N + (29 / 32) * Q,
        (5 / 16) * N + (13 / 16) * Q,
        (2 / 3) * N + (11 / 18) * Q,
    ]
    weil = 0.5 * (I + J + Q)
    return min(terms) < weil - 1e-9


def mqw_ok(M: float, N: float, Q: float) -> bool:
    if M > N:
        M, N = N, M
    cond1 = M <= N + 0.25 * Q + 1e-12
    cond2 = (7 / 5) * M + N < 1.5 * Q - 1e-12
    cond3 = M + N <= 1.25 * Q + 1e-12
    nontrivial = M >= (10 / 21) * Q - 1e-9
    return cond1 and cond2 and cond3 and nontrivial


def main() -> None:
    lemma_no_bilinear_cell_at_wall()
    print("Lemma (no bilinear cell at δ=0): proved (M+N=1, Q=1/2 ⇒ not both < Q).")
    print()
    deltas = [i / 60 for i in range(0, 31)]  # 0 .. 0.5
    thetas = [i / 30 for i in range(2, 15)]  # 0.067 .. 0.467

    counts = {
        "bilinear_cells": 0,
        "balanced_duals": 0,
        "pascadi_length": 0,
        "pascadi_71_save": 0,
        "bp_window": 0,
        "bp_beats_weil": 0,
        "bp_balanced_save": 0,
        "mqw": 0,
    }
    first_bp_window = None
    first_bp_save = None
    first_bp_balanced = None
    first_p71 = None
    first_mqw = None
    stall_bilinear = []
    bilinear_hits = []

    for delta in deltas:
        Q = 0.5 + delta
        for theta in thetas:
            M, N = 1 - theta, theta
            mqw = mqw_ok(M, N, Q)
            if mqw and first_mqw is None:
                first_mqw = (delta, theta, Q)
            if mqw:
                counts["mqw"] += 1

            d = duals(M, N, Q)
            if d is None:
                continue
            I, J = d
            counts["bilinear_cells"] += 1
            p_len = pascadi_length_ok(I, J, Q)
            p71 = pascadi_71_beats_weil(I, J, Q)
            bp = bp_window(I, J, Q)
            bp_save = bp_beats_weil(I, J, Q)
            bal = balanced_duals(I, J)
            if bal:
                counts["balanced_duals"] += 1
            if p_len:
                counts["pascadi_length"] += 1
            if p71:
                counts["pascadi_71_save"] += 1
                if first_p71 is None:
                    first_p71 = (delta, theta, Q, I, J)
            if bp:
                counts["bp_window"] += 1
                if first_bp_window is None:
                    first_bp_window = (delta, theta, Q, I, J)
            if bp_save:
                counts["bp_beats_weil"] += 1
                if first_bp_save is None:
                    first_bp_save = (delta, theta, Q, I, J)
            if bp_save and bal:
                counts["bp_balanced_save"] += 1
                if first_bp_balanced is None:
                    first_bp_balanced = (delta, theta, Q, I, J)
            if abs(delta) < 1e-15:
                stall_bilinear.append((theta, I, J, p_len, p71, bp, bp_save, mqw))
            if p71 or (bp_save and bal) or mqw:
                bilinear_hits.append(
                    {
                        "delta": round(delta, 4),
                        "theta": round(theta, 4),
                        "Q": round(Q, 4),
                        "I": round(I, 4),
                        "J": round(J, 4),
                        "pascadi_length": p_len,
                        "pascadi_71": p71,
                        "bp_window": bp,
                        "bp_beats_weil": bp_save,
                        "balanced": bal,
                        "mqw": mqw,
                    }
                )

    print("Bilinear cells: both Type II factors strictly shorter than Q.")
    print("Folded (Type I) cells are excluded from Pascadi/BP checks.")
    print("A window hit with |I| ≪ |J| is not a saving: Weil already wins there.")
    print()
    print("Counts:")
    for k, v in counts.items():
        print(f"  {k:20s} {v}")
    print()
    print("First BP interval-window hit (may be unbalanced, not a saving):")
    print(" ", first_bp_window)
    print("First BP bound actually beating Weil:")
    print(" ", first_bp_save)
    print("First BP saving with balanced duals (|I| ≳ |J|/2):")
    print(" ", first_bp_balanced)
    print("First Pascadi Thm 7.1 Weil-beating bilinear hit:")
    print(" ", first_p71)
    print("First MQW (1.2) hit (product-argument shape, Type II lengths):")
    print(" ", first_mqw)
    print()
    print("Stall slice δ=0, bilinear cells:")
    if not stall_bilinear:
        print("  none (at Q = x^{1/2} one Type II factor is always ≥ Q)")
    else:
        for row in stall_bilinear:
            print(" ", row)

    print()
    print("Balanced Type II (θ = 1/2, I = J = δ), closed-form thresholds:")
    print("  Pascadi Cor 1.4 length |I| ≪ √Q:  always for δ ≤ 1/2")
    print("  Pascadi 7.1 beats Weil:           δ > 1/3     (Q > x^{5/6})")
    print("  Blomer–Pascadi window:            δ > 13/30 ≈ 0.4333  (Q > x^{14/15})")
    print("  MQW MN ≤ Q^{5/4}:                 δ ≥ 0.3     (Q ≥ x^{4/5})")

    out = {
        "counts": counts,
        "first_bp_window": first_bp_window,
        "first_bp_save": first_bp_save,
        "first_bp_balanced": first_bp_balanced,
        "first_p71": first_p71,
        "first_mqw": first_mqw,
        "stall_bilinear": stall_bilinear,
        "bilinear_hits": bilinear_hits,
        "verdict": {
            "stall_delta_0": "lemma: M+N=1 and Q=1/2 ⇒ not both M<Q and N<Q",
            "first_bp_balanced_delta": None if first_bp_balanced is None else first_bp_balanced[0],
            "first_p71_delta": None if first_p71 is None else first_p71[0],
            "first_mqw_delta": None if first_mqw is None else first_mqw[0],
            "reaches_past_sqrt_x": False,
            "note": (
                "The named stall is the first increment δ → 0+. "
                "Balanced duals enter a genuine BP/Pascadi saving only at "
                "Q ≳ x^{5/6} (Pascadi 7.1) or Q ≳ x^{14/15} (BP). "
                "MQW needs Q ≥ x^{4/5} and a product-argument kernel."
            ),
        },
    }
    path = Path("t3_kloosterman_ranges.json")
    path.write_text(json.dumps(out, indent=2) + "\n")
    print()
    print(f"Wrote {path}")


if __name__ == "__main__":
    main()
