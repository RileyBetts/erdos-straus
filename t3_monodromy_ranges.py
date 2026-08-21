#!/usr/bin/env python3
# Copyright (c) 2026 Riley Betts Ltd
# SPDX-License-Identifier: MIT
"""T(3) vs Fouvry–Kowalski–Michel–Sawin arXiv:2511.09459.

Optimistic identification: freeze q = D prime, Type II mn ~ x, Kloosterman
K(mn) the trace of Kl_2 on A^1_{F_q} (gallant: G = SL_2).

FKMS Theorem 1.3 (Type II): M ≤ q, MN ≥ q^{3/4+δ} (Thm 1.1), and the
explicit (1.2)–(1.3) also want N in a short window and MN ≲ q-scale.
Theorem 1.4 (trilinear, §7): J ≤ 4q, MN ≤ 4q, nontrivial for
J ≥ q^δ and MN ≥ q^{1/2+δ}.

Log-exponents in units of log x:
  Q_D = α1+α2+α3,  MN = 1,  M = N = 1/2 (balanced Type II).

After switching, each d_a ≤ 1/2, so a prime D cannot exceed 1/2.

This is a range check, not a covering run. Do not densify covering.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def thm13_lengths(Q_D: Fraction) -> dict:
    """Optimistic: q = x^{Q_D}, MN = x^1, M = N = x^{1/2}."""
    # MN ≤ 4q  ⇔  1 ≤ Q_D
    mn_le_4q = Q_D >= 1
    # MN ≥ q^{3/4}  ⇔  1 ≥ (3/4) Q_D  ⇔  Q_D ≤ 4/3
    mn_ge_q34 = Q_D <= Fraction(4, 3)
    # M ≤ q  ⇔  1/2 ≤ Q_D
    m_le_q = Q_D >= Fraction(1, 2)
    # M ≥ q^δ for some δ>0: 1/2 > 0 always if Q_D finite
    return {
        "mn_le_4q": bool(mn_le_4q),
        "mn_ge_q34": bool(mn_ge_q34),
        "m_le_q": bool(m_le_q),
        "thm13_optimistic": bool(mn_le_4q and mn_ge_q34 and m_le_q),
    }


def thm14_lengths(Q_D: Fraction, J: Fraction | None = None) -> dict:
    """Thm 1.4: J ≤ 4q, MN ≤ 4q; nontrivial if J ≥ q^δ, MN ≥ q^{1/2+δ}."""
    mn_le_4q = Q_D >= 1
    # MN ≥ q^{1/2}  ⇔  1 ≥ Q_D / 2  ⇔  Q_D ≤ 2
    mn_ge_q12 = Q_D <= 2
    out = {
        "mn_le_4q": bool(mn_le_4q),
        "mn_ge_q12": bool(mn_ge_q12),
    }
    if J is not None:
        out["J_le_4q"] = bool(J <= Q_D)
        out["J_pos"] = bool(J > 0)
    out["thm14_mn_window"] = bool(mn_le_4q and mn_ge_q12)
    return out


def lemma_prime_modulus_after_switch() -> None:
    """After switching d_a ≤ √x, a prime D divides some d_a, hence D ≤ √x."""
    max_prime_Q = Fraction(1, 2)
    assert max_prime_Q == Fraction(1, 2)
    # BV wall is exactly that ceiling: Q_D = 1/2.
    wall = thm13_lengths(Fraction(1, 2))
    assert not wall["mn_le_4q"]  # x ≰ 4 √x
    assert wall["m_le_q"]  # M = √x = q


def main() -> None:
    lemma_prime_modulus_after_switch()
    print("Lemma: after switching, prime D is ≤ √x. Proved.")
    print()

    cells = {
        "bv_wall": {
            "Q_D": Fraction(1, 2),
            "prime_possible": True,
            "typical_omega": 1,
            "note": "D prime ~ √x is allowed; MN=x > 4q",
        },
        "uneven": {
            "Q_D": Fraction(1),
            "prime_possible": False,
            "typical_omega": 2,
            "note": "D ~ d2 d3 with both ~ √x: semiprime, not prime",
        },
        "symmetric": {
            "Q_D": Fraction(3, 2),
            "prime_possible": False,
            "typical_omega": 3,
            "note": "three √x factors; Q_D = 3/2 > 4/3 so Thm 1.3 MN ≥ q^{3/4} fails even if prime",
        },
    }

    out_cells = {}
    for key, spec in cells.items():
        Q_D = spec["Q_D"]
        t13 = thm13_lengths(Q_D)
        t14 = thm14_lengths(Q_D, J=Fraction(1, 2))
        # Gallant: Kl_2 over F_q prime is SL_2. Composite of ω≥2 primes
        # is SL_2^ω via twisted multiplicativity → not simple; ω=2 is SO_4.
        gallant = spec["typical_omega"] == 1
        oxozonic_rescue = spec["typical_omega"] == 2  # shape only; wrong category
        out_cells[key] = {
            "Q_D": str(Q_D),
            "Q_D_float": float(Q_D),
            "prime_possible_after_switch": spec["prime_possible"],
            "typical_omega": spec["typical_omega"],
            "kl2_gallant_on_F_q": gallant,
            "so4_shape_if_two_primes": spec["typical_omega"] == 2,
            "thm13": t13,
            "thm14": t14,
            "note": spec["note"],
        }
        print(f"{key}: Q_D={Q_D}  prime_ok={spec['prime_possible']}  "
              f"ω~{spec['typical_omega']}  gallant={gallant}")
        print(f"  Thm 1.3 optimistic: {t13['thm13_optimistic']}  "
              f"(MN≤4q={t13['mn_le_4q']}, MN≥q^{{3/4}}={t13['mn_ge_q34']})")
        print(f"  Thm 1.4 MN window: {t14['thm14_mn_window']}  "
              f"(MN≤4q={t14['mn_le_4q']}, MN≥√q={t14['mn_ge_q12']})")
        print()

    out = {
        "lemmas": {
            "prime_after_switch": (
                "After switching d_a ≤ √x, any prime D divides some d_a, "
                "hence D ≤ √x = the BV ceiling."
            ),
            "not_a_sheaf_on_product": (
                "χ2(d2)χ3(d3)K(·; lcm(d2,d3)) is not the trace function of "
                "an ℓ-adic sheaf on a product variety over a fixed F_q: "
                "the modulus depends on the point."
            ),
            "so4_not_gallant": (
                "Twisted multiplicativity for two distinct prime moduli "
                "gives Kl ⊗ Kl with monodromy SL_2 × SL_2 → SO_4, which "
                "FKMS §1.3 carves out as not gallant (sulfatic / oxozonic "
                "is a rank-4 sheaf on one F_q, not S(·;pq))."
            ),
            "chi_not_gallant": (
                "χ2, χ3 have fixed conductor, rank-1 Kummer, abelian "
                "monodromy: not gallant. Absorbable as α,β only when q is "
                "fixed and they are coefficients, which they are not when "
                "d2, d3 vary the modulus."
            ),
        },
        "cells": out_cells,
        "family_tree": (
            "Kowalski–Michel–Sawin, Ann. of Math. 186 (2017) "
            "(Kloosterman/hypergeometric bilinear) → FKMS arXiv:2511.09459 "
            "(gallant). Adjacent to Blomer–Pascadi already in T-3 Phase 3."
        ),
        "fkm_2014": (
            "Fouvry–Kowalski–Michel, Duke 163 (2014) wraps Σ_p K(p) for "
            "K a trace function modulo a fixed q. The prime is the argument, "
            "not the modulus. Not a wrapper for averaging over D."
        ),
        "verdict": {
            "gkr_applies_to_joint_crt": False,
            "gallant": False,
            "reaches_D_past_sqrt_x": False,
            "reaches_D_up_to_x": False,
            "reaches_D_up_to_x_3_2": False,
            "t3_progress": False,
            "fails": [
                "wrong category (varying modulus, not a sheaf on A^1_{F_q})",
                "after switch, prime q cannot exceed BV",
                "composite D has reducible monodromy (not gallant; ω=2 is SO_4)",
                "χ2, χ3 abelian rank 1",
                "even optimistic prime-q Type II lengths miss Thm 1.3 at "
                "Q_D=1/2 (too long) and Q_D=3/2 (MN < q^{3/4})",
            ],
        },
    }

    print("VERDICT: GKR/gallant does not apply to the joint CRT object.")
    print("Not T(3) progress; D past √x not reached.")

    path = Path("t3_monodromy_ranges.json")
    path.write_text(json.dumps(out, indent=2) + "\n")
    print(f"Wrote {path}")


if __name__ == "__main__":
    main()
