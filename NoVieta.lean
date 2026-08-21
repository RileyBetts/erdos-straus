/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  NoVieta.lean — Layer A (core).  See README.md.
  Bare Lean, no imports.

  The Schinzel/ES affine equation m·xyz = n(xy+yz+zx) is linear in each
  coordinate separately.  Given (y,z) with the fibre denominator nonzero,
  there is at most one x.  There is no second root and therefore no Vieta
  involution of Markoff type (x ↦ 3yz−x).  That is the structural reason
  the Bourgain–Gamburd–Sarnak / Markoff playbook does not apply to these
  surfaces: the correspondence orbit does not exist.

  This file does not claim ErdosStraus.  It does not claim that the
  automorphism group of the projective model is finite — only that the
  affine equation admits no Vieta-style second-root involution in a
  coordinate.
-/

namespace ES.NoVieta

/-- Cleared form of `m/n = 1/x + 1/y + 1/z`. -/
def Cleared (m n x y z : Int) : Prop :=
  m * (x * y * z) = n * (x * y + y * z + z * x)

/-- Fibre denominator for the x-coordinate: `x = nyz / D_x` when D_x ≠ 0. -/
def denomX (m n y z : Int) : Int :=
  m * y * z - n * y - n * z

def denomY (m n x z : Int) : Int := denomX m n x z

def denomZ (m n x y : Int) : Int := denomX m n x y

theorem denomX_swap {m n y z : Int} : denomX m n y z = denomX m n z y := by
  unfold denomX
  have e1 : m * y * z = m * z * y := by
    simp [Int.mul_comm, Int.mul_left_comm]
  have e2 : n * y + n * z = n * z + n * y := by omega
  omega

theorem cleared_swap_xy {m n x y z : Int} (h : Cleared m n x y z) :
    Cleared m n y x z := by
  unfold Cleared at *
  have e1 : y * x * z = x * y * z := by
    simp [Int.mul_comm, Int.mul_left_comm]
  have c1 : y * x = x * y := Int.mul_comm y x
  have c2 : x * z = z * x := Int.mul_comm x z
  have c3 : z * y = y * z := Int.mul_comm z y
  have e2 : y * x + x * z + z * y = x * y + y * z + z * x := by omega
  rw [e1, e2]
  exact h

theorem cleared_swap_xz {m n x y z : Int} (h : Cleared m n x y z) :
    Cleared m n z y x := by
  unfold Cleared at *
  have e1 : z * y * x = x * y * z := by
    simp [Int.mul_comm, Int.mul_left_comm]
  have c1 : z * y = y * z := Int.mul_comm z y
  have c2 : y * x = x * y := Int.mul_comm y x
  have c3 : x * z = z * x := Int.mul_comm x z
  have e2 : z * y + y * x + x * z = x * y + y * z + z * x := by omega
  rw [e1, e2]
  exact h

/-- The equation is the linear relation `x · D_x = nyz`. -/
theorem linear_in_x {m n x y z : Int} (h : Cleared m n x y z) :
    x * denomX m n y z = n * (y * z) := by
  unfold Cleared denomX at *
  have hd : x * (m * y * z - n * y - n * z)
      = x * (m * y * z) - x * (n * y) - x * (n * z) := by
    simp [Int.mul_sub]
  have hxmyz : x * (m * y * z) = m * (x * y * z) := by
    simp [Int.mul_comm, Int.mul_left_comm]
  have hxny : x * (n * y) = n * (x * y) := by
    simp [Int.mul_left_comm]
  have hxnz : x * (n * z) = n * (z * x) := by
    simp [Int.mul_comm, Int.mul_left_comm]
  have hsum : n * (x * y + y * z + z * x)
      = n * (x * y) + n * (y * z) + n * (z * x) := by
    simp [Int.mul_add]
  omega

theorem linear_in_y {m n x y z : Int} (h : Cleared m n x y z) :
    y * denomY m n x z = n * (x * z) :=
  linear_in_x (cleared_swap_xy h)

theorem linear_in_z {m n x y z : Int} (h : Cleared m n x y z) :
    z * denomZ m n x y = n * (x * y) := by
  have hlin := linear_in_x (cleared_swap_xz h)
  -- z * denomX m n y x = n * (y * x)
  rw [denomX_swap] at hlin
  have hR : n * (y * x) = n * (x * y) := by simp [Int.mul_comm]
  rw [hR] at hlin
  exact hlin

/-- A nonzero solution forces the fibre denominator to be nonzero
    (otherwise `nyz = 0`). -/
theorem denomX_ne_zero {m n x y z : Int}
    (hy : y ≠ 0) (hz : z ≠ 0) (hn : n ≠ 0)
    (h : Cleared m n x y z) : denomX m n y z ≠ 0 := by
  intro hD
  have hlin := linear_in_x h
  rw [hD, Int.mul_zero] at hlin
  have hne : n * (y * z) ≠ 0 := Int.mul_ne_zero hn (Int.mul_ne_zero hy hz)
  exact hne hlin.symm

/-- Unique x on a fibre with D_x ≠ 0.  The Markoff second root does not exist. -/
theorem unique_x {m n x x' y z : Int}
    (h : Cleared m n x y z) (h' : Cleared m n x' y z)
    (hD : denomX m n y z ≠ 0) : x = x' := by
  have hx := linear_in_x h
  have hx' := linear_in_x h'
  have : x * denomX m n y z = x' * denomX m n y z := by
    rw [hx, hx']
  exact Int.eq_of_mul_eq_mul_right hD this

theorem unique_y {m n x y y' z : Int}
    (h : Cleared m n x y z) (h' : Cleared m n x y' z)
    (hD : denomY m n x z ≠ 0) : y = y' :=
  unique_x (cleared_swap_xy h) (cleared_swap_xy h') hD

theorem unique_z {m n x y z z' : Int}
    (h : Cleared m n x y z) (h' : Cleared m n x y z')
    (hD : denomZ m n x y ≠ 0) : z = z' := by
  have hD' : denomX m n y x ≠ 0 := by
    rw [denomX_swap]
    exact hD
  exact unique_x (cleared_swap_xz h) (cleared_swap_xz h') hD'

/-- Positive-octant uniqueness: two positive solutions with the same
    trailing pair are equal.  Specializes to ES at `m = 4`. -/
theorem unique_x_nat {m n x x' y z : Nat}
    (hy : 0 < y) (hz : 0 < z) (hn : 0 < n)
    (h : m * (x * y * z) = n * (x * y + y * z + z * x))
    (h' : m * (x' * y * z) = n * (x' * y + y * z + z * x')) :
    x = x' := by
  have hI : Cleared (m : Int) (n : Int) (x : Int) (y : Int) (z : Int) := by
    unfold Cleared
    exact_mod_cast h
  have hI' : Cleared (m : Int) (n : Int) (x' : Int) (y : Int) (z : Int) := by
    unfold Cleared
    exact_mod_cast h'
  have hyI : (y : Int) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr hy
  have hzI : (z : Int) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr hz
  have hnI : (n : Int) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr hn
  have hD := denomX_ne_zero hyI hzI hnI hI
  have hxeq := unique_x hI hI' hD
  exact Int.natCast_inj.mp hxeq

/-- ES instance: unique leading denominator given the other two. -/
theorem es_unique_x {n x x' y z : Nat}
    (hy : 0 < y) (hz : 0 < z) (hn : 0 < n)
    (h : 4 * (x * y * z) = n * (x * y + y * z + z * x))
    (h' : 4 * (x' * y * z) = n * (x' * y + y * z + z * x')) :
    x = x' :=
  unique_x_nat hy hz hn h h'

end ES.NoVieta
