/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  SchinzelSep.lean — Layer A (core).  See README.md.
  Bare Lean, no imports.

  S1 flagship (erdos-straus-candidate-conjectures.md): the Schinzel surface
  for 9/5 = 1/x + 1/y + 1/z has a mixed-sign integer point.  The unordered
  no-positive statement, and a verified decision procedure for general
  (m, n), live in `SchinzelDecide.lean`.  The ordered `no_pos_9_5` below
  is kept as an analytic (non-search) proof for x ≤ y ≤ z.

  This file does not claim a Brauer–Manin obstruction (or the absence of
  one) on these models.  It does not claim ErdosStraus.
-/

namespace ES.SchinzelSep

/-- Integer points on the Schinzel affine model, nonzero coordinates.
    Cleared form of `m/n = 1/x + 1/y + 1/z`. -/
def OnSchinzel (m n : Nat) (x y z : Int) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
    (m : Int) * (x * y * z) = (n : Int) * (x * y + y * z + z * x)

/-- Mixed-sign point of the 9/5 surface: `1 + 1 − 1/5 = 9/5`. -/
theorem signed_9_5 : OnSchinzel 9 5 (-5) 1 1 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

/-- Positive solutions of `9/5 = 1/x+1/y+1/z` do not exist.
    Ordering `x ≤ y ≤ z` forces `x = 1` and `y ≤ 2`; both residues fail. -/
theorem no_pos_9_5 {x y z : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ y) (hyz : y ≤ z)
    (heq : 9 * (x * y * z) = 5 * (x * y + y * z + z * x)) :
    False := by
  have hyz0 : 0 < y * z := Nat.mul_pos hy hz
  have hxz : x ≤ z := Nat.le_trans hxy hyz
  have hxy_le : x * y ≤ y * z := by
    have : x * y ≤ z * y := Nat.mul_le_mul_right y hxz
    rwa [Nat.mul_comm z y] at this
  have hzx_le : z * x ≤ y * z := by
    have : z * x ≤ z * y := Nat.mul_le_mul_left z hxy
    rwa [Nat.mul_comm z y] at this
  have hsum : x * y + y * z + z * x ≤ 3 * (y * z) := by
    have : x * y + z * x ≤ y * z + y * z := Nat.add_le_add hxy_le hzx_le
    omega
  have hL : 9 * (x * y * z) = (9 * x) * (y * z) := by
    simp [Nat.mul_assoc]
  have hbound : (9 * x) * (y * z) ≤ 15 * (y * z) := by
    have : 5 * (x * y + y * z + z * x) ≤ 5 * (3 * (y * z)) :=
      Nat.mul_le_mul_left 5 hsum
    have h15 : 5 * (3 * (y * z)) = 15 * (y * z) := by omega
    calc (9 * x) * (y * z)
        = 9 * (x * y * z) := hL.symm
      _ = 5 * (x * y + y * z + z * x) := heq
      _ ≤ 5 * (3 * (y * z)) := this
      _ = 15 * (y * z) := h15
  have hxle : 9 * x ≤ 15 := Nat.le_of_mul_le_mul_right hbound hyz0
  have hx1 : x = 1 := by omega
  subst hx1
  have heq' : 9 * (y * z) = 5 * (y + y * z + z) := by
    simpa [Nat.one_mul, Nat.mul_one] using heq
  have h4 : 4 * (y * z) = 5 * (y + z) := by omega
  have hy2 : y ≤ 2 := by
    have hyz' : y + z ≤ z + z := Nat.add_le_add hyz (Nat.le_refl z)
    have h10 : 5 * (z + z) = 10 * z := by omega
    have : 4 * (y * z) ≤ 10 * z := by
      calc 4 * (y * z)
          = 5 * (y + z) := h4
        _ ≤ 5 * (z + z) := Nat.mul_le_mul_left 5 hyz'
        _ = 10 * z := h10
    have : (4 * y) * z ≤ 10 * z := by
      simpa [Nat.mul_assoc] using this
    have : 4 * y ≤ 10 := Nat.le_of_mul_le_mul_right this hz
    omega
  have hy12 : y = 1 ∨ y = 2 := by omega
  rcases hy12 with hy1 | hy2'
  · subst hy1
    have : 4 * z = 5 * (1 + z) := by simpa using h4
    omega
  · subst hy2'
    have : 4 * (2 * z) = 5 * (2 + z) := by simpa using h4
    omega

end ES.SchinzelSep
