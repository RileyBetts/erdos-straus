/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  ConicFiber.lean — Layer A (core).  See README.md.
  Bare Lean, no imports.  Axioms: propext, Quot.sound only (audited).

  VERDICT (Harpaz mapping, 19 Aug 2026): Harpaz's descent-fibration theorem
  for conic log K3 surfaces (JEMS 21 (2019) 627–664, arXiv:1511.04876) does
  NOT apply to the ES surfaces: fixing the third coordinate t in
  4txy = n(xy+tx+ty) and setting A = 4t−n gives the exact identity
      (Ax − nt)(Ay − nt) = (nt)²,
  so every conic fiber is SPLIT (uv = c).  Harpaz's hypotheses (independence
  of the classes {−1,a,b} ∪ {Δij} in ℚ*/ℚ*²; norm-1 tori of a quadratic
  FIELD) fail degenerately, and the Selmer-comparison engine is vacuous on
  split fibers.  BL's Ũn ⊃ split 𝔾m² shows no fibration of this surface
  escapes splitness.  The constructive content of the reading is the exact
  reduction proved below: positive points on the fiber t correspond exactly
  to divisor pairs of (nt)² in the residue class −nt (mod 4t−n) — for ALL
  n ≥ 2.  Geometrically this wires TubEpHypothesis's fibers to the divisor
  problem: the two wings are one object, kernel-certified.

  Equation convention: 4*t*x*y = n*(x*y + t*x + t*y) is the ES equation
  4/n = 1/x + 1/y + 1/t with denominators cleared (matches IsES n x y t).
-/

namespace ES.ConicFiber

/-- The surface equation forces n < 4t on positive fibers. -/
theorem four_t_gt {n t x y : Nat}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 < t)
    (heq : 4*t*(x*y) = n*(x*y) + n*t*x + n*t*y) : n < 4*t := by
  by_cases h : n < 4*t
  · exact h
  · exfalso
    have h1 : 4*t*(x*y) ≤ n*(x*y) := by
      have := Nat.mul_le_mul_right (x*y) (Nat.le_of_not_lt h)
      exact this
    have h2 : 0 < n*t*x := by
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; simp at heq
          have : 0 < 4*t*(x*y) :=
            Nat.mul_pos (Nat.mul_pos (by omega) ht) (Nat.mul_pos hx hy)
          omega
        · exact h0
      exact Nat.mul_pos (Nat.mul_pos hn ht) hx
    omega

/-- Subtraction-free fiber relation: (4t−n)·x·y = nt·x + nt·y, stated as
`(4t−n)*x*y + n*(x*y) = 4t*x*y` avoided — we keep the additive form. -/
theorem fiber_relation {n t x y : Nat} (h4 : n < 4*t)
    (heq : 4*t*(x*y) = n*(x*y) + n*t*x + n*t*y) :
    (4*t - n)*(x*y) = n*t*x + n*t*y := by
  have hsplit : (4*t - n)*(x*y) + n*(x*y) = 4*t*(x*y) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt h4)]
  omega

/-- The coordinate exceeds the threshold: (4t−n)·x > n·t. -/
theorem coord_exceeds {n t x y : Nat}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) (hn : 0 < n) (h4 : n < 4*t)
    (heq : 4*t*(x*y) = n*(x*y) + n*t*x + n*t*y) :
    n*t < (4*t - n)*x := by
  have hrel := fiber_relation h4 heq
  -- (4t−n)*x*y = ntx + nty > nty  ⟹  ((4t−n)*x)*y > (nt)*y  ⟹  cancel y
  have hgt : n*t*y < ((4*t - n)*x)*y := by
    have hpos : 0 < n*t*x := Nat.mul_pos (Nat.mul_pos hn ht) hx
    have : ((4*t - n)*x)*y = (4*t - n)*(x*y) := by
      rw [Nat.mul_assoc]
    omega
  by_cases hle : n*t < (4*t - n)*x
  · exact hle
  · exfalso
    have := Nat.mul_le_mul_right y (Nat.le_of_not_lt hle)
    omega

/-- **The fiber identity**: on the surface, with u = (4t−n)x − nt and
v = (4t−n)y − nt, one has u·v = (nt)². -/
theorem fiber_identity {n t x y : Nat}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) (hn : 0 < n) (h4 : n < 4*t)
    (heq : 4*t*(x*y) = n*(x*y) + n*t*x + n*t*y) :
    ((4*t - n)*x - n*t) * ((4*t - n)*y - n*t) = (n*t)*(n*t) := by
  have hux : n*t < (4*t - n)*x := coord_exceeds hx hy ht hn h4 heq
  have huy : n*t < (4*t - n)*y := by
    have heq' : 4*t*(y*x) = n*(y*x) + n*t*y + n*t*x := by
      rw [Nat.mul_comm y x]; omega
    exact coord_exceeds hy hx ht hn h4 heq'
  have hrel := fiber_relation h4 heq
  -- e1 : y * u = n*t*x
  have e1 : y * ((4*t - n)*x - n*t) = n*t*x := by
    have expand : y * ((4*t - n)*x - n*t) + y*(n*t) = y*((4*t - n)*x) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hux)]
    have hyx : y*((4*t - n)*x) = (4*t - n)*(x*y) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hq : y*(n*t) = n*t*y := Nat.mul_comm y (n*t)
    omega
  have e2 : x * ((4*t - n)*y - n*t) = n*t*y := by
    have expand : x * ((4*t - n)*y - n*t) + x*(n*t) = x*((4*t - n)*y) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt huy)]
    have hxy : x*((4*t - n)*y) = (4*t - n)*(x*y) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hq : x*(n*t) = n*t*x := Nat.mul_comm x (n*t)
    omega
  -- multiply e1 by v and use e2, then cancel y
  have key : y * (((4*t - n)*x - n*t) * ((4*t - n)*y - n*t))
           = y * ((n*t)*(n*t)) := by
    calc y * (((4*t - n)*x - n*t) * ((4*t - n)*y - n*t))
        = (y * ((4*t - n)*x - n*t)) * ((4*t - n)*y - n*t) := by
          rw [Nat.mul_assoc]
      _ = (n*t*x) * ((4*t - n)*y - n*t) := by rw [e1]
      _ = (n*t) * (x * ((4*t - n)*y - n*t)) := by
          simp [Nat.mul_assoc]
      _ = (n*t) * (n*t*y) := by rw [e2]
      _ = y * ((n*t)*(n*t)) := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.eq_of_mul_eq_mul_left hy key

/-- **Fiber ⟹ divisor data** (all n ≥ 2): every positive point on fiber t
yields a positive divisor pair (u,v) of (nt)² with u ≡ v ≡ −nt (mod 4t−n),
and the coordinates are recovered linearly:  (4t−n)·x = u + nt. -/
theorem fiber_to_divisor {n t x y : Nat}
    (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) (hn : 0 < n)
    (heq : 4*t*(x*y) = n*(x*y) + n*t*x + n*t*y) :
    ∃ u v, 0 < u ∧ 0 < v ∧ u * v = (n*t)*(n*t) ∧
      (4*t - n) ∣ (u + n*t) ∧ (4*t - n) ∣ (v + n*t) ∧
      (4*t - n)*x = u + n*t ∧ (4*t - n)*y = v + n*t := by
  have h4 := four_t_gt hx hy ht heq
  have hux := coord_exceeds hx hy ht hn h4 heq
  have huy : n*t < (4*t - n)*y := by
    have heq' : 4*t*(y*x) = n*(y*x) + n*t*y + n*t*x := by
      rw [Nat.mul_comm y x]; omega
    exact coord_exceeds hy hx ht hn h4 heq'
  refine ⟨(4*t - n)*x - n*t, (4*t - n)*y - n*t,
    by omega, by omega,
    fiber_identity hx hy ht hn h4 heq, ⟨x, by omega⟩, ⟨y, by omega⟩,
    by omega, by omega⟩

/-- **Divisor data ⟹ fiber point** (the converse): a positive divisor pair
of (nt)² in the class −nt (mod 4t−n) produces a positive point on fiber t.
Together with `fiber_to_divisor` this is the kernel-certified statement that
along every conic fiber, TubEp's existence question IS the divisor problem. -/
theorem divisor_to_fiber {n t u v : Nat}
    (ht : 0 < t) (hn : 0 < n) (h4 : n < 4*t)
    (hu : 0 < u) (hv : 0 < v)
    (huv : u * v = (n*t)*(n*t))
    (hcu : (4*t - n) ∣ (u + n*t)) (hcv : (4*t - n) ∣ (v + n*t)) :
    ∃ x y, 0 < x ∧ 0 < y ∧
      4*t*(x*y) = n*(x*y) + n*t*x + n*t*y ∧
      (4*t - n)*x = u + n*t := by
  obtain ⟨x, hxdef⟩ := hcu
  obtain ⟨y, hydef⟩ := hcv
  have hA : 0 < 4*t - n := by omega
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · subst h0; simp at hxdef; omega
    · exact h0
  have hypos : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0; simp at hydef; omega
    · exact h0
  refine ⟨x, y, hxpos, hypos, ?_, hxdef.symm⟩
  -- A²·xy = (u+nt)(v+nt) = uv + nt(u+v) + (nt)² = 2(nt)² + nt(u+v)
  -- A·nt(x+y) = nt(u+v+2nt) = same;  cancel A.
  have hexp : ((4*t - n)*x) * ((4*t - n)*y) = (u + n*t)*(v + n*t) := by
    rw [hxdef, hydef]
  have hrhs : (u + n*t)*(v + n*t)
            = u*v + (n*t)*u + (n*t)*v + (n*t)*(n*t) := by
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm]
    omega
  have hAA : ((4*t - n)*x) * ((4*t - n)*y)
           = (4*t - n) * ((4*t - n)*(x*y)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have p1 : (4*t - n)*(n*t*x) = (n*t)*((4*t - n)*x) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have p2 : (4*t - n)*(n*t*y) = (n*t)*((4*t - n)*y) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hgoal : (4*t - n) * ((4*t - n)*(x*y))
             = (4*t - n) * (n*t*x + n*t*y) := by
    have s1 : (4*t - n) * ((4*t - n)*(x*y)) = (u + n*t)*(v + n*t) := by
      rw [← hAA, hexp]
    have s2 : (n*t)*(u + n*t) = (n*t)*u + (n*t)*(n*t) := by
      rw [Nat.mul_add]
    have s3 : (n*t)*(v + n*t) = (n*t)*v + (n*t)*(n*t) := by
      rw [Nat.mul_add]
    have s4 : (4*t - n) * (n*t*x + n*t*y)
            = (4*t - n)*(n*t*x) + (4*t - n)*(n*t*y) := by
      rw [Nat.mul_add]
    have s5 : (n*t)*((4*t - n)*x) = (n*t)*(u + n*t) := by rw [← hxdef]
    have s6 : (n*t)*((4*t - n)*y) = (n*t)*(v + n*t) := by rw [← hydef]
    omega
  have hfr : (4*t - n)*(x*y) = n*t*x + n*t*y :=
    Nat.eq_of_mul_eq_mul_left hA hgoal
  have hsplit : (4*t - n)*(x*y) + n*(x*y) = 4*t*(x*y) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt h4)]
  omega

end ES.ConicFiber
