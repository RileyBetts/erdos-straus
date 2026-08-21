/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  TwistDescent.lean — Layer A (core).  See README.md.
  Bare Lean, no imports.  Axioms: propext, Quot.sound only (intended audit).

  Gate 2 of C5_1 (erdos-straus-candidate-conjectures.md): the cheap half of
  R1.  The real-compatible twist V_{n,d} is the affine cubic U_n together
  with w² = d·u₁·u₃, d > 0.  An integral point of V_{n,d} in the positive
  real locus (u₁,u₂,u₃ > 0) projects to a positive-octant point of U_n.
  Conversely every positive-octant point lifts to some twist (not claimed
  squarefree-unique here).

  This file does not produce a point of V_{n,d}.  It does not apply Harpaz.
  It does not prove ErdosStraus.

  Gate 3: the t-fibration π(x,y,z,w) = y on V_{n,d} (the fibration C5_1
  Step 3 named) has an explicit rational section over Q(y), recorded as
  `t_fiber_section_cleared`.  The generic fiber is therefore split, so
  Harpaz Theorem 1.0.1 (JEMS 2019 / arXiv:1511.04876; special case of
  3.1.16) does not apply to this fibration — same obstruction as §4t.

  Autopsy (20 Aug 2026): the same rational curve, reparametrized, is a
  section of π = u₁ and of π = w (`u1_fiber_section_cleared`).  Changing
  the linear projection does not produce a non-split conic fibration.

  Equation convention: 4·u₁u₂u₃ = n·(u₁u₂+u₂u₃+u₃u₁), matching IsES /
  Layer-B IsESZ.  Coordinates (u₁,u₂,u₃) = (x,y,z).
-/

namespace ES.TwistDescent

/-- Integer points on the affine model `U_n`, nonzero coordinates. -/
def OnUn (n : Nat) (x y z : Int) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
    (4 : Int) * (x * y * z) = (n : Int) * (x * y + y * z + z * x)

/-- Real-compatible twist `V_{n,d}`: the cubic plus `w² = d·u₁·u₃`. -/
def IsTwist (n d : Nat) (x y z w : Int) : Prop :=
  0 < d ∧ OnUn n x y z ∧ w * w = (d : Int) * x * z

/-- Positive real locus of `A³` — the octant C₊, not merely "the cover is real". -/
def PosRealLocus (x y z : Int) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z

/-- The naive α-trivializing cover `w² = −u₁u₃` has no integral (hence no
    real) points over C₊.  This is the kernel form of C5's refutation. -/
theorem naive_cover_empty {x z w : Int} (hx : 0 < x) (hz : 0 < z) :
    ¬ w * w = -(x * z) := by
  intro h
  have hpos : 0 < x * z := Int.mul_pos hx hz
  have hsq : 0 ≤ w * w :=
    match Int.le_total 0 w with
    | .inl hw => Int.mul_nonneg hw hw
    | .inr hw => Int.mul_nonneg_of_nonpos_of_nonpos hw hw
  omega

/-- For d > 0 the product d·u₁·u₃ is positive iff u₁,u₃ have the same
    (nonzero) sign.  So "the twist is real" includes the all-negative
    (u₁,u₃) quadrant; C₊ is a stricter condition. -/
theorem twist_real_iff {d : Nat} {x z : Int} (hd : 0 < d) :
    0 < (d : Int) * x * z ↔
      (0 < x ∧ 0 < z) ∨ (x < 0 ∧ z < 0) := by
  have hdI : (0 : Int) < d := Int.natCast_pos.mpr hd
  have hmul : 0 < (d : Int) * x * z ↔ 0 < x * z := by
    constructor
    · intro h
      have : 0 < (d : Int) * (x * z) := by
        simpa [Int.mul_assoc] using h
      exact Int.pos_of_mul_pos_right this hdI
    · intro h
      have : 0 < (d : Int) * (x * z) := Int.mul_pos hdI h
      simpa [Int.mul_assoc] using this
  constructor
  · intro h
    have hxz : 0 < x * z := hmul.mp h
    rcases Int.lt_trichotomy x 0 with hx | hx | hx
    · rcases Int.lt_trichotomy z 0 with hz | hz | hz
      · exact Or.inr ⟨hx, hz⟩
      · subst hz; simp at hxz
      · have : x * z < 0 := Int.mul_neg_of_neg_of_pos hx hz
        exact (Int.lt_asymm hxz this).elim
    · subst hx; simp at hxz
    · rcases Int.lt_trichotomy z 0 with hz | hz | hz
      · have : x * z < 0 := Int.mul_neg_of_pos_of_neg hx hz
        exact (Int.lt_asymm hxz this).elim
      · subst hz; simp at hxz
      · exact Or.inl ⟨hx, hz⟩
  · intro h
    apply hmul.mpr
    rcases h with ⟨hx, hz⟩ | ⟨hx, hz⟩
    · exact Int.mul_pos hx hz
    · exact Int.mul_pos_of_neg_of_neg hx hz

/-- Projection: a twist point is a point of `U_n`. -/
theorem twist_on_Un {n d : Nat} {x y z w : Int}
    (h : IsTwist n d x y z w) : OnUn n x y z :=
  h.2.1

/-- **Gate 2, descent.**  An integral point of `V_{n,d}` in the positive
    real locus is a positive-octant point of `U_n`. -/
theorem descent {n d : Nat} {x y z w : Int}
    (h : IsTwist n d x y z w) (hpos : PosRealLocus x y z) :
    OnUn n x y z ∧ 0 < x ∧ 0 < y ∧ 0 < z :=
  ⟨twist_on_Un h, hpos⟩

/-- Every positive-octant point of `U_n` lifts to some twist
    (`d = u₁u₃`, `w = u₁u₃`).  Squarefree uniqueness is not claimed. -/
theorem lift {n : Nat} {x y z : Int}
    (h : OnUn n x y z) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ∃ d w, IsTwist n d x y z w ∧ PosRealLocus x y z := by
  have hxz : 0 < x * z := Int.mul_pos hx hz
  have hxz0 : 0 ≤ x * z := Int.le_of_lt hxz
  refine ⟨(x * z).toNat, x * z, ?_, ⟨hx, hy, hz⟩⟩
  have hdI : ((x * z).toNat : Int) = x * z := Int.toNat_of_nonneg hxz0
  have hdpos : 0 < (x * z).toNat := by
    have : ¬ (x * z).toNat = 0 := by
      intro h0
      have : x * z ≤ 0 := Int.toNat_eq_zero.mp h0
      exact Int.not_le_of_gt hxz this
    omega
  refine ⟨hdpos, h, ?_⟩
  calc (x * z) * (x * z)
      = (x * z) * x * z := by simp [Int.mul_assoc]
    _ = ((x * z).toNat : Int) * x * z := by rw [hdI]

/-! ## Gate 3 — the t-fibration of `V_{n,d}` is split

C5_1 fibers the twist by `u₂ = t`.  Over `ℚ(t)`, with `A = 4t − n`,
the point
  `x = nt(d+1)/A`, `z = nt(d+1)/(A d)`, `w = nt(d+1)/A`, `y = t`
lies on `V_{n,d}`.  Clearing denominators gives the Nat identity below.
A rational section means the generic fiber is split, so it is not a
non-split conic `a X² + b Y² = 1` over a quadratic field: Harpaz
Theorem 1.0.1's engine does not run on this fibration. -/

/-- After cancelling the common factor `nt(d+1)`, the cubic on the
    rational section is this identity (`A + n = 4t`). -/
theorem t_fiber_section_reduced {n d t : Nat} (hA : n < 4 * t) :
    4 * t * (n * t * (d + 1))
      = n * (t * (4 * t - n) * (d + 1) + n * t * (d + 1)) := by
  have hAn : (4 * t - n) + n = 4 * t := Nat.sub_add_cancel (Nat.le_of_lt hA)
  have h1 : t * (4 * t - n) * (d + 1) + n * t * (d + 1)
      = t * (d + 1) * ((4 * t - n) + n) := by
    have hL : t * (4 * t - n) * (d + 1) = t * (d + 1) * (4 * t - n) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hR : n * t * (d + 1) = t * (d + 1) * n := by
      simp [Nat.mul_assoc, Nat.mul_comm]
    rw [hL, hR, ← Nat.mul_add]
  have h2 : n * (t * (d + 1) * ((4 * t - n) + n))
      = n * t * (d + 1) * (4 * t) := by
    rw [hAn]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h3 : 4 * t * (n * t * (d + 1)) = n * t * (d + 1) * (4 * t) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [h1, h2, h3]

/-- Cleared cubic: `4 x y z = n(xy+yz+zx)` at
    `x = num/A`, `z = num/(A d)`, `y = t`, `num = nt(d+1)`, `A = 4t−n`.
    The twist equation `w² = d x z` on the same section is `num²/A² =
    d·(num/A)·(num/(A d))`, i.e. holds identically. -/
theorem t_fiber_section_cleared {n d t : Nat} (hA : n < 4 * t) :
    4 * (n * t * (d + 1)) * t * (n * t * (d + 1))
      = n * ((n * t * (d + 1)) * t * (4 * t - n) * d
          + t * (n * t * (d + 1)) * (4 * t - n)
          + (n * t * (d + 1)) * (n * t * (d + 1))) := by
  let A := 4 * t - n
  let num := n * t * (d + 1)
  have hred : 4 * t * num = n * (t * A * (d + 1) + n * t * (d + 1)) :=
    t_fiber_section_reduced hA
  have hfactor : t * A * (d + 1) = t * A * d + t * A := by
    calc t * A * (d + 1)
        = t * A * d + t * A * 1 := by rw [Nat.mul_add]
      _ = t * A * d + t * A := by rw [Nat.mul_one]
  have hsum : t * A * (d + 1) + n * t * (d + 1) = t * A * d + t * A + num := by
    rw [hfactor]
  have hl : 4 * num * t * num = num * (4 * t * num) := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  change 4 * num * t * num
      = n * (num * t * A * d + t * num * A + num * num)
  rw [hl, hred, hsum]
  simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-! ## Autopsy — π = u₁ and π = w are split by the same curve

The t-section sets w = x and z = x/d.  Solving for the remaining
coordinate as a function of x = s gives a rational section of
π(x,y,z,w) = x:
  y = n s / B,  z = s/d,  w = s,  B = 4s − n(d+1).
Because w = x on this curve, the same formulae are a section of
π = w.  The twist equation holds identically (w² = s² = d·s·(s/d)). -/

/-- Cleared cubic on the u₁-section: `x = s`, `y = ns/B`, `z = s/d`,
    `B = 4s − n(d+1)`.  Multiply `4xyz = n(xy+yz+zx)` through by `B d`. -/
theorem u1_fiber_section_cleared {n d s : Nat}
    (hB : n * (d + 1) < 4 * s) :
    4 * s * (n * s) * s
      = n * (s * (n * s) * d
          + (n * s) * s
          + s * s * (4 * s - n * (d + 1))) := by
  let B := 4 * s - n * (d + 1)
  have hBadd : B + n * (d + 1) = 4 * s :=
    Nat.sub_add_cancel (Nat.le_of_lt hB)
  have hl : 4 * s * (n * s) * s = n * s * s * (4 * s) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hr : n * (s * (n * s) * d + (n * s) * s + s * s * B)
      = n * s * s * (n * d + n + B) := by
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hn : n * d + n = n * (d + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hsum : n * d + n + B = 4 * s := by
    rw [hn, Nat.add_comm (n * (d + 1)), hBadd]
  rw [hl, hr, hsum]

/-- On the same curve, `w = x = s` and `d·x·z = d·s·(s/d) = s²`, so
    the twist equation is this tautology after clearing `d`. -/
theorem u1_fiber_twist (d s : Nat) :
    s * s * d = d * s * s := by
  simp [Nat.mul_comm, Nat.mul_left_comm]

end ES.TwistDescent
