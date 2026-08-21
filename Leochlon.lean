/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  Library dictionary: leochlon `(δ,b,c)` → `ES.IsES`.

  The open construction reported for `leochlon/erdstrau` is
  `(4b−1)(4c−1) = 4pδ+1` with `δ ∣ bc`. That identity always produces an
  explicit Type-II triple. It is **not** a gateway / Bounded-A / FCT
  encoding and is **not** imported as a Track-1 merge.

  See `erdos-straus-leochlon.md`, `erdos-straus-prior-archive.md`.
-/

import ErdosStraus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ES

/-- Leochlon open construction on a positive integer `p`. -/
def LeochlonWitness (p δ b c : Nat) : Prop :=
  0 < p ∧ 0 < δ ∧ 0 < b ∧ 0 < c ∧
    δ ∣ b * c ∧ (4 * b - 1) * (4 * c - 1) = 4 * p * δ + 1

/-- The governing cancellation: `(4b−1)(4c−1)=4pδ+1` iff `4bc = b+c+pδ`. -/
theorem leochlon_key_identity {p δ b c : Nat}
    (hb : 0 < b) (hc : 0 < c)
    (h : (4 * b - 1) * (4 * c - 1) = 4 * p * δ + 1) :
    4 * b * c = b + c + p * δ := by
  have hb1 : 1 ≤ 4 * b := by omega
  have hc1 : 1 ≤ 4 * c := by omega
  have hZ : ((4 * b : Int) - 1) * ((4 * c : Int) - 1) = (4 : Int) * p * δ + 1 := by
    have h' : ((4 * b - 1 : Nat) : Int) * ((4 * c - 1 : Nat) : Int) =
        ((4 * p * δ + 1 : Nat) : Int) := congrArg Nat.cast h
    rw [Nat.cast_sub hb1, Nat.cast_sub hc1, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_mul, Nat.cast_mul] at h'
    exact h'
  have hkey : (4 * b * c : Int) = (b + c + p * δ : Int) := by
    ring_nf at hZ
    linarith
  exact_mod_cast hkey

/-- Always: leochlon data gives the Type-II triple `(p b, p c, bc/δ)`. -/
theorem isES_of_leochlon {p δ b c : Nat} (h : LeochlonWitness p δ b c) :
    IsES p (p * b) (p * c) (b * c / δ) := by
  obtain ⟨hp, hδ, hb, hc, hdiv, hid⟩ := h
  set t := b * c / δ
  have ht : δ * t = b * c := Nat.mul_div_cancel' hdiv
  have htpos : 0 < t :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hb hc) hdiv) hδ
  have hkey := leochlon_key_identity hb hc hid
  refine ⟨Nat.mul_pos hp hb, Nat.mul_pos hp hc, htpos, ?_⟩
  have hclear : 4 * (p * b) * (p * c) * t * δ =
      p * ((p * c) * t + (p * b) * t + (p * b) * (p * c)) * δ := by
    calc
      4 * (p * b) * (p * c) * t * δ
          = 4 * p * p * (δ * t) * b * c := by ring
        _ = 4 * p * p * (b * c) * b * c := by rw [ht]
        _ = p * p * (4 * b * c) * b * c := by ring
        _ = p * p * (b + c + p * δ) * b * c := by rw [hkey]
        _ = p * ((p * c) * (b * c) + (p * b) * (b * c) +
              (p * b) * (p * c) * δ) := by ring
        _ = p * ((p * c) * (δ * t) + (p * b) * (δ * t) +
              (p * b) * (p * c) * δ) := by rw [ht]
        _ = p * ((p * c) * t + (p * b) * t + (p * b) * (p * c)) * δ := by ring
  have hδ0 : δ ≠ 0 := Nat.pos_iff_ne_zero.mp hδ
  have hmul : 4 * (p * b) * (p * c) * t =
      p * ((p * c) * t + (p * b) * t + (p * b) * (p * c)) :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hδ0) hclear
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_comm, Nat.add_left_comm] at hmul ⊢
  exact hmul

/-- Small-`q` construction: `b = (q+1)/4` when `q ≡ 3 (mod 4)`. -/
theorem leochlon_of_q_succ_div_four {p q c δ : Nat}
    (hp : 0 < p) (hq3 : q % 4 = 3) (hc : 0 < c) (hδ : 0 < δ)
    (hid : q * (4 * c - 1) = 4 * p * δ + 1)
    (hdiv : δ ∣ (q + 1) / 4 * c) :
    LeochlonWitness p δ ((q + 1) / 4) c := by
  have hb : 0 < (q + 1) / 4 := by
    have : 4 ≤ q + 1 := by omega
    exact Nat.div_pos this (by decide)
  have h4b1 : 4 * ((q + 1) / 4) - 1 = q := by
    have : (q + 1) % 4 = 0 := by omega
    have hdiv4 : 4 ∣ q + 1 := Nat.dvd_of_mod_eq_zero this
    have : 4 * ((q + 1) / 4) = q + 1 := Nat.mul_div_cancel' hdiv4
    omega
  refine ⟨hp, hδ, hb, hc, hdiv, ?_⟩
  simpa [h4b1] using hid

end ES
