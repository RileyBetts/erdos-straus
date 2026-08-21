/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  SchinzelDecide.lean — Layer A (core). Bare Lean, no imports.

  Positive-octant solvability of m/n = 1/x + 1/y + 1/z (cleared form
  m·xyz = n(xy+yz+zx)) is decided by `decideCplus`, with soundness and
  completeness proved.  Flagship evaluations: 9/5 and 13/7 have no
  positive solution; 4/5 does.  This file does not treat Brauer–Manin,
  integral models, or Hilbert symbols.  Signed witnesses live in
  `SchinzelSep.lean`.  See `erdos-straus-candidate-conjectures.md` S1 / S1_1.
-/

namespace ES.SchinzelDecide
set_option maxRecDepth 4096

def SolEq (m n x y z : Nat) : Prop :=
  m*(x*y*z) = n*(x*y + y*z + z*x)

/-- inner check at (x, y): D = (mx−n)y − nx must be positive, divide nxy,
and the resulting z must satisfy the equation. -/
def checkXY (m n x y : Nat) : Bool :=
  decide (n < m*x) && decide (n*x < (m*x - n)*y) &&
  ((n*(x*y)) % ((m*x - n)*y - n*x) == 0) &&
  (m*(x*y*((n*(x*y)) / ((m*x - n)*y - n*x))) ==
    n*(x*y + y*((n*(x*y)) / ((m*x - n)*y - n*x))
        + ((n*(x*y)) / ((m*x - n)*y - n*x))*x))

/-- the decision procedure: x ≤ 3n, y ≤ 2nx suffice (proved below). -/
def decideCplus (m n : Nat) : Bool :=
  (List.range (3*n)).any fun x' =>
    (List.range (2*n*(x'+1))).any fun y' =>
      checkXY m n (x'+1) (y'+1)

/-- SOUNDNESS: a positive verdict yields a positive solution. -/
theorem decideCplus_sound {m n : Nat} (hn : 0 < n)
    (h : decideCplus m n = true) :
    ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ SolEq m n x y z := by
  unfold decideCplus at h
  rw [List.any_eq_true] at h
  obtain ⟨x', _, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨y', _, h⟩ := h
  unfold checkXY at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨x'+1, y'+1, (n*((x'+1)*(y'+1))) / ((m*(x'+1) - n)*(y'+1) - n*(x'+1)),
    Nat.succ_pos x', Nat.succ_pos y', ?_, h4⟩
  -- z > 0: z*D = nxy > 0 forces z ≠ 0
  have hD : 0 < (m*(x'+1) - n)*(y'+1) - n*(x'+1) := by omega
  have hprod : 0 < n*((x'+1)*(y'+1)) :=
    Nat.mul_pos hn (Nat.mul_pos (Nat.succ_pos x') (Nat.succ_pos y'))
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h3
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hc; omega
    · exact h0
  rw [hc, Nat.mul_div_cancel_left c hD]
  exact hcpos

/-- equation symmetry under the transposition (y z). -/
theorem solEq_swap_yz {m n x y z : Nat} (h : SolEq m n x y z) :
    SolEq m n x z y := by
  unfold SolEq at *
  have e1 : x*z*y = x*y*z := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have c1 : x*z = z*x := Nat.mul_comm x z
  have c2 : z*y = y*z := Nat.mul_comm z y
  have c3 : y*x = x*y := Nat.mul_comm y x
  have e2 : x*z + z*y + y*x = x*y + y*z + z*x := by omega
  rw [e1, e2]
  exact h

/-- equation symmetry under the transposition (x y). -/
theorem solEq_swap_xy {m n x y z : Nat} (h : SolEq m n x y z) :
    SolEq m n y x z := by
  unfold SolEq at *
  have e1 : y*x*z = x*y*z := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have c1 : y*x = x*y := Nat.mul_comm y x
  have c2 : x*z = z*x := Nat.mul_comm x z
  have c3 : z*y = y*z := Nat.mul_comm z y
  have e2 : y*x + x*z + z*y = x*y + y*z + z*x := by omega
  rw [e1, e2]
  exact h

/-- any positive solution has a sorted positive solution. -/
theorem exists_sorted {m n x y z : Nat}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : SolEq m n x y z) :
    ∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≤ b ∧ b ≤ c ∧ SolEq m n a b c := by
  rcases Nat.le_total x y with hxy | hxy
  · rcases Nat.le_total y z with hyz | hyz
    · exact ⟨x, y, z, hx, hy, hz, hxy, hyz, h⟩
    · rcases Nat.le_total x z with hxz | hxz
      · exact ⟨x, z, y, hx, hz, hy, hxz, hyz, solEq_swap_yz h⟩
      · exact ⟨z, x, y, hz, hx, hy, hxz, hxy,
          solEq_swap_xy (solEq_swap_yz h)⟩
  · rcases Nat.le_total x z with hxz | hxz
    · exact ⟨y, x, z, hy, hx, hz, hxy, hxz, solEq_swap_xy h⟩
    · rcases Nat.le_total y z with hyz | hyz
      · exact ⟨y, z, x, hy, hz, hx, hyz, hxz,
          solEq_swap_yz (solEq_swap_xy h)⟩
      · exact ⟨z, y, x, hz, hy, hx, hyz, hxy,
          solEq_swap_xy (solEq_swap_yz (solEq_swap_xy h))⟩

/-- COMPLETENESS: a positive solution forces a positive verdict. -/
theorem decideCplus_complete {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (hex : ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ SolEq m n x y z) :
    decideCplus m n = true := by
  obtain ⟨x0, y0, z0, hx0, hy0, hz0, h0⟩ := hex
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, h⟩ := exists_sorted hx0 hy0 hz0 h0
  unfold SolEq at h
  have h0' := h                       -- original association, for the final goal
  rw [Nat.mul_assoc x y z] at h       -- h : m*(x*(y*z)) = n*(x*y + y*z + z*x)
  -- bound 1: m*x ≤ 3*n  (from xy+yz+zx ≤ 3yz and cancellation)
  have hsum : x*y + y*z + z*x ≤ 3*(y*z) := by
    have e1 : x*y ≤ y*z := by
      have : x ≤ z := Nat.le_trans hxy hyz
      calc x*y ≤ z*y := Nat.mul_le_mul_right y this
        _ = y*z := Nat.mul_comm z y
    have e2 : z*x ≤ z*y := Nat.mul_le_mul_left z hxy
    have e3 : z*y = y*z := Nat.mul_comm z y
    omega
  have hb1 : m*x ≤ 3*n := by
    have step : (m*x)*(y*z) ≤ (3*n)*(y*z) := by
      have l : m*(x*(y*z)) = (m*x)*(y*z) := by rw [← Nat.mul_assoc]
      have r : n*(x*y + y*z + z*x) ≤ n*(3*(y*z)) := Nat.mul_le_mul_left n hsum
      have r2 : n*(3*(y*z)) = (3*n)*(y*z) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      omega
    have hyz0 : 0 < y*z := Nat.mul_pos hy hz
    by_cases hle : m*x ≤ 3*n
    · exact hle
    · exfalso
      have hlt : 3*n < m*x := Nat.lt_of_not_le hle
      have h2 : (3*n+1)*(y*z) ≤ (m*x)*(y*z) :=
        Nat.mul_le_mul_right (y*z) (by omega : 3*n+1 ≤ m*x)
      have hs : (3*n+1)*(y*z) = (3*n)*(y*z) + y*z := by rw [Nat.add_mul, Nat.one_mul]
      omega
  -- bound 2: n < m*x  (strict)
  have hb2 : n < m*x := by
    have low : n*(y*z) < n*(x*y + y*z + z*x) := by
      have h1 : 0 < x*y := Nat.mul_pos hx hy
      have h2 : 0 < z*x := Nat.mul_pos hz hx
      have hlt : y*z + 1 ≤ x*y + y*z + z*x := by omega
      have := Nat.mul_le_mul_left n hlt
      have e : n*(y*z + 1) = n*(y*z) + n := by rw [Nat.mul_add, Nat.mul_one]
      omega
    have l : m*(x*(y*z)) = (m*x)*(y*z) := by rw [← Nat.mul_assoc]
    have r : n*(y*z) < (m*x)*(y*z) := by omega
    have hyz0 : 0 < y*z := Nat.mul_pos hy hz
    by_cases hle : n < m*x
    · exact hle
    · exfalso
      have : m*x ≤ n := Nat.le_of_not_lt hle
      have := Nat.mul_le_mul_right (y*z) this
      omega
  -- the fiber relation: (m*x − n)*(y*z) = n*x*(y+z)  in additive form
  have hfib : (m*x - n)*(y*z) + n*(y*z) = m*x*(y*z) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hb2)]
  have hexp : m*x*(y*z) = m*(x*(y*z)) := by rw [Nat.mul_assoc]
  have hdist : n*(x*y + y*z + z*x) = n*(x*y) + n*(y*z) + n*(z*x) := by
    rw [Nat.mul_add, Nat.mul_add]
  -- bound 3: (m*x−n)*y ≤ 2*n*x  (from y+z ≤ 2z, cancel z)
  have hb3 : (m*x - n)*y ≤ 2*(n*x) := by
    have key : ((m*x - n)*y)*z ≤ (2*(n*x))*z := by
      have e1 : ((m*x - n)*y)*z = (m*x - n)*(y*z) := by rw [Nat.mul_assoc]
      have e2 : n*(x*y) = (n*x)*y := by rw [← Nat.mul_assoc]
      have e3 : n*(z*x) = (n*x)*z := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have e4 : (n*x)*y ≤ (n*x)*z := Nat.mul_le_mul_left (n*x) hyz
      have e5 : (2*(n*x))*z = (n*x)*z + (n*x)*z := by
        have e : 2*(n*x) = n*x + n*x := by omega
        rw [e, Nat.add_mul]
      omega
    by_cases hle : (m*x - n)*y ≤ 2*(n*x)
    · exact hle
    · exfalso
      have hlt := Nat.lt_of_not_le hle
      have h2 : (2*(n*x)+1)*z ≤ ((m*x - n)*y)*z :=
        Nat.mul_le_mul_right z (by omega : 2*(n*x)+1 ≤ (m*x - n)*y)
      have hs : (2*(n*x)+1)*z = (2*(n*x))*z + z := by rw [Nat.add_mul, Nat.one_mul]
      omega
  -- z-recovery: z*D = n*x*y with D = (m*x−n)*y − n*x  > 0
  have hDrel : ((m*x - n)*y)*z = n*(x*y) + n*(x*z) := by
    have e1 : ((m*x - n)*y)*z = (m*x - n)*(y*z) := by rw [Nat.mul_assoc]
    have e2 : n*(z*x) = n*(x*z) := by rw [Nat.mul_comm z x]
    omega
  have hb4 : n*x < (m*x - n)*y := by
    have hpos : 0 < n*(x*y) := Nat.mul_pos hn (Nat.mul_pos hx hy)
    have e1 : (n*x)*z = n*(x*z) := by rw [Nat.mul_assoc]
    by_cases hle : n*x < (m*x - n)*y
    · exact hle
    · exfalso
      have hge : (m*x - n)*y ≤ n*x := Nat.le_of_not_lt hle
      have := Nat.mul_le_mul_right z hge
      omega
  have hzD : z*((m*x - n)*y - n*x) = n*(x*y) := by
    have hsplit : z*((m*x - n)*y - n*x) + z*(n*x) = z*((m*x - n)*y) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hb4)]
    have e1 : z*((m*x - n)*y) = ((m*x - n)*y)*z := Nat.mul_comm _ _
    have e2 : z*(n*x) = n*(x*z) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    omega
  -- assemble membership + the inner check
  unfold decideCplus
  rw [List.any_eq_true]
  have hx3n : x - 1 ∈ List.range (3*n) := by
    rw [List.mem_range]
    have : x ≤ 3*n := by
      have : 1*x ≤ m*x := Nat.mul_le_mul_right x hm
      omega
    omega
  refine ⟨x - 1, hx3n, ?_⟩
  rw [List.any_eq_true]
  have hxeq : x - 1 + 1 = x := by omega
  have hy2nx : y - 1 ∈ List.range (2*n*(x - 1 + 1)) := by
    rw [List.mem_range, hxeq]
    have h1 : 1*y ≤ (m*x - n)*y := Nat.mul_le_mul_right y (by omega)
    have h2 : 2*n*x = 2*(n*x) := by rw [Nat.mul_assoc]
    omega
  refine ⟨y - 1, hy2nx, ?_⟩
  unfold checkXY
  have hyeq : y - 1 + 1 = y := by omega
  simp only [hxeq, hyeq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hdvd : ((m*x - n)*y - n*x) ∣ n*(x*y) := by
    refine ⟨z, ?_⟩
    rw [← hzD, Nat.mul_comm]
  have hDpos : 0 < (m*x - n)*y - n*x := by omega
  have hz' : (n*(x*y)) / ((m*x - n)*y - n*x) = z := by
    obtain ⟨c, hc⟩ := hdvd
    have hcz : c = z := by
      have h1 : ((m*x - n)*y - n*x)*c = ((m*x - n)*y - n*x)*z := by
        rw [← hc, ← hzD, Nat.mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hDpos h1
    rw [hc, hcz, Nat.mul_div_cancel_left z hDpos]
  refine ⟨⟨⟨hb2, hb4⟩, ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_mod_right]
  · rw [hz']
    exact h0'

/-! ## Flagship instances -/

/-- positive control: 4/5 = 1/2 + 1/4 + 1/20. -/
theorem pos_4_5 : decideCplus 4 5 = true := by decide

/-- **The 9/5 separator, kernel-decided**: the checker returns false. -/
theorem sep_9_5 : decideCplus 9 5 = false := by decide

/-- The 9/5 surface has no positive-octant solution. Signed occupancy
is `SchinzelSep.signed_9_5`. This does not claim a Brauer–Manin fact. -/
theorem no_pos_9_5 :
    ¬ ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ SolEq 9 5 x y z := by
  intro hex
  have := decideCplus_complete (by omega) (by omega) hex
  rw [sep_9_5] at this
  exact Bool.false_ne_true this

/-- a second separator from the (2z−1)/z family: 13/7. -/
theorem sep_13_7 : decideCplus 13 7 = false := by decide

theorem no_pos_13_7 :
    ¬ ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ SolEq 13 7 x y z := by
  intro hex
  have := decideCplus_complete (by omega) (by omega) hex
  rw [sep_13_7] at this
  exact Bool.false_ne_true this

end ES.SchinzelDecide
