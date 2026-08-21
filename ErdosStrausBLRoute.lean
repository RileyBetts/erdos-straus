/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  Layer B (Mathlib).  See README.md.

  Build via `lake build` against the pinned Mathlib.  Discharges the
  Layer-A reciprocity interface and develops the Bright–Loughran route
  around covering-landing.

  Covering-landing (`LandingHypothesis`) asks every prime for a boxed witness.
  The QED implication `conditional_qed_hard` needs only solutions on hard primes
  (`HardLandingHypothesis`).  Witnesses are solutions, not conversely: geometry
  can occupy that gap without proving the covering system is complete.

  Bright–Loughran Theorem 1.8: there is no Brauer–Manin obstruction to ES.
  The remaining geometric content is an integral Hasse principle in the positive
  octant (open; false for Markoff).  This file does not claim that principle.
  It does prove the Z-model facts the principle consumes: mixed-sign points
  exist for every n ≥ 2, the Jahnel–Schindler box bounds every integer point,
  and the real invariant of α is −1 exactly on the positive octant.
  It packages the bypass, and proves the character algebra the hybrid uses
  (plan §4p): Type-I covering classes are square-cosets, so a Legendre-symbol
  mismatch excludes a whole d-slice.

  Hilbert symbols on `ℚ` remain an interface (`BL.InvariantData.reciprocity`)
  for general rationals.  This file discharges Hilbert reciprocity for odd
  integers (including a shared odd factor after cancelling squares),
  2-powers, mixed signs, and odd-denominator ratios — including the ES 3.8
  shape `(-2^s r₁/r₃, -2^s r₂/r₃)` when the odd parts are pairwise coprime
  — via Jacobi / χ₄ / χ₈, and proves BL Lemmas 3.1 / 3.5 / 3.6 / 3.8.
  No `sorry`. Remaining geometric content: the open integral Hasse
  principle in the positive octant (not claimed).  Occupying that octant
  of the Z-model is exactly `ErdosStraus` (`erdos_straus_iff_pos_octant`).
  That occupancy is the named hypothesis `TubEpHypothesis`; the implication
  `erdos_straus_of_tub_ep` is proved, the hypothesis is not.  The Z-model
  facts the principle may consume are `tub_ep_consumed`.
  Octant repair (`es_of_s2_divisor`) converts a divisor pair of `s²` into
  a natural-number point; it does not produce the pair as `n` varies.
  The `r = 3` slice proves the classical `n ≡ 5 (mod 8)` class geometrically
  and those `n ≡ 1 (mod 4)` whose `s` has a prime factor `≡ 2 (mod 3)`;
  it fails at `n = 73` (`r3_slice_obstructed_at_73`).  Not `ErdosStraus`.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.FieldTheory.Finite.Basic
import ErdosStraus
import ErdosStrausQR
import BrightLoughran

open ZMod ES BL

/-! ## Bypass architecture: solutions, not boxed witnesses -/

/-- Geometric existence on hard fibres — the Bright–Loughran target.
    Identical to `HardLandingHypothesis`: every hard prime has an ES *solution*,
    not necessarily a covering witness. -/
def GeometricExistencePrinciple : Prop := HardLandingHypothesis

/-- **Around covering-landing.**  ES follows from existence on hard primes;
    the covering system need not be complete. -/
theorem erdos_straus_of_geometry (H : GeometricExistencePrinciple) :
    ErdosStraus :=
  conditional_qed_hard H

/-- Covering-landing is a special case of the geometric target. -/
theorem geometry_of_landing (H : LandingHypothesis) :
    GeometricExistencePrinciple :=
  landing_implies_hard_landing H

/-- Algebraic covering (character / QR method) is the same Prop as the analytic
    survivor bound; the two lanes share `erdos_straus_of_interface`. -/
abbrev AlgebraicSurvivorBound := ES.Covering.AnalyticSurvivorBound

theorem erdos_straus_of_character_covering
    (Alevel : Nat → Nat) (X0 : Nat)
    (hbig : AlgebraicSurvivorBound Alevel X0)
    (hsmall : ∀ p : Nat, p < X0 → IsPrime p → HardClass p →
      ∃ x y z, IsES p x y z) :
    ErdosStraus :=
  ES.Covering.erdos_straus_of_interface Alevel X0 hbig hsmall

/-! ## General witness fingerprint -/

theorem witness_c_not_dvd {a c d q : Nat} [Fact q.Prime]
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hq : q = 4 * a * c * d - 1) :
    ¬ q ∣ c := by
  intro h
  have hgcd : Nat.gcd q c = 1 := hq ▸ gcd_witness_c ha hc hd
  have : q ∣ 1 := by
    have := Nat.dvd_gcd (Nat.dvd_refl q) h
    rwa [hgcd] at this
  exact Nat.Prime.ne_one Fact.out (Nat.dvd_one.mp this)

theorem witness_c_ne_zero_mod {a c d q : Nat} [Fact q.Prime]
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hq : q = 4 * a * c * d - 1) :
    ((c : ℤ) : ZMod q) ≠ 0 := by
  intro hz
  have hdvd : q ∣ c := (ZMod.natCast_eq_zero_iff c q).1 (by simpa using hz)
  exact witness_c_not_dvd ha hc hd hq hdvd

lemma sq_legendre_one {q : Nat} [Fact q.Prime] {x : ℤ}
    (h : (x : ZMod q) ≠ 0) :
    legendreSym q x * legendreSym q x = 1 := by
  have hx2 : ((x * x : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_mul]
    exact mul_ne_zero h h
  have hsq : legendreSym q (x * x) = 1 :=
    (legendreSym.eq_one_iff (p := q) hx2).2 ⟨(x : ZMod q), by simp⟩
  rwa [legendreSym.mul] at hsq

/-- General covering fingerprint: `c n ≡ −a (mod q)` implies
    `(n/q) = (−a/q) (c/q)`.  Type I is the case `c = 1`. -/
theorem witness_legendre {n a c d m q : Nat} [Fact q.Prime]
    (hw : Witness n a c d m) (hq : q = 4 * a * c * d - 1)
    (_hnq : ((n : ℤ) : ZMod q) ≠ 0) :
    legendreSym q n = legendreSym q (-(a : ℤ)) * legendreSym q c := by
  have ha : 0 < a := hw.1
  have hc : 0 < c := hw.2.1
  have hd : 0 < d := hw.2.2.1
  have hcq := witness_c_ne_zero_mod ha hc hd hq
  have hEq : (4 * a * c * d - 1) * m = c * n + a := witness_cofactor hw
  have hdvd : q ∣ c * n + a := ⟨m, by rw [hq]; exact hEq.symm⟩
  have hsum : ((c * n + a : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (c * n + a) q).2 hdvd
  have hadd : (c : ZMod q) * (n : ZMod q) + (a : ZMod q) = 0 := by
    simpa [Nat.cast_add, Nat.cast_mul] using hsum
  have hneg : (c : ZMod q) * (n : ZMod q) = -(a : ZMod q) :=
    eq_neg_of_add_eq_zero_left hadd
  have hprod : legendreSym q ((c : ℤ) * n) = legendreSym q (-(a : ℤ)) := by
    apply legendreSym_eq_of_cast
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_neg, Int.cast_natCast]
    simpa using hneg
  rw [legendreSym.mul] at hprod
  have hsq := sq_legendre_one hcq
  calc
    legendreSym q n
        = (legendreSym q c * legendreSym q c) * legendreSym q n := by
          rw [hsq, one_mul]
      _ = legendreSym q c * (legendreSym q c * legendreSym q n) := by ring
      _ = legendreSym q c * legendreSym q (-(a : ℤ)) := by rw [hprod]
      _ = legendreSym q (-(a : ℤ)) * legendreSym q c := by ring

/-! ## Type-I d-slice law (plan §4p) -/

theorem typeI_a_ne_zero_mod {p a d m q : Nat} [Fact q.Prime]
    (hw : Witness p a 1 d m) (hq : q = 4 * a * d - 1) :
    ((a : ℤ) : ZMod q) ≠ 0 := by
  intro hz
  have ha : 0 < a := hw.1
  have hd : 0 < d := hw.2.2.1
  have hdvd : q ∣ a := (ZMod.natCast_eq_zero_iff a q).1 (by simpa using hz)
  have hqa : q ∣ 4 * a * d := dvd_trans hdvd ⟨4 * d, by ring⟩
  have hqid : q ∣ 4 * a * d - 1 := by rw [hq]
  have h1 : q ∣ 1 := by
    have := Nat.dvd_sub hqa hqid
    have hsub : 4 * a * d - (4 * a * d - 1) = 1 := by
      have : 1 ≤ 4 * a * d := by
        have : 0 < 4 * a * d := Nat.mul_pos (Nat.mul_pos (by omega) ha) hd
        omega
      omega
    rwa [hsub] at this
  exact Nat.Prime.ne_one (show Nat.Prime q from Fact.out) (Nat.dvd_one.mp h1)

theorem typeI_d_ne_zero_mod {p a d m q : Nat} [Fact q.Prime]
    (hw : Witness p a 1 d m) (hq : q = 4 * a * d - 1) :
    ((d : ℤ) : ZMod q) ≠ 0 := by
  intro hz
  have ha : 0 < a := hw.1
  have hd : 0 < d := hw.2.2.1
  have hdvd : q ∣ d := (ZMod.natCast_eq_zero_iff d q).1 (by simpa using hz)
  have hqa : q ∣ 4 * a * d := dvd_trans hdvd ⟨4 * a, by ring⟩
  have hqid : q ∣ 4 * a * d - 1 := by rw [hq]
  have h1 : q ∣ 1 := by
    have := Nat.dvd_sub hqa hqid
    have hsub : 4 * a * d - (4 * a * d - 1) = 1 := by
      have : 1 ≤ 4 * a * d := by
        have : 0 < 4 * a * d := Nat.mul_pos (Nat.mul_pos (by omega) ha) hd
        omega
      omega
    rwa [hsub] at this
  exact Nat.Prime.ne_one (show Nat.Prime q from Fact.out) (Nat.dvd_one.mp h1)

theorem typeI_two_ne_zero_mod {q : Nat} [Fact q.Prime] (hq2 : q ≠ 2) :
    ((2 : ℤ) : ZMod q) ≠ 0 := by
  intro hz
  have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).1 (by simpa using hz)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact Nat.Prime.ne_one (show Nat.Prime q from Fact.out) h
  · exact hq2 h

/-- **d-slice law.** Type I with prime `q = 4ad − 1` forces
    `(p/q) = (−d/q)`, independent of `a`.  Each d-slice is one square-coset. -/
theorem typeI_d_slice {p a d m q : Nat} [Fact q.Prime]
    (hw : Witness p a 1 d m) (hq : q = 4 * a * d - 1)
    (hpq : ((p : ℤ) : ZMod q) ≠ 0) (hq2 : q ≠ 2) :
    legendreSym q p = legendreSym q (-(d : ℤ)) := by
  have ha : 0 < a := hw.1
  have hd : 0 < d := hw.2.2.1
  have hmain := typeI_legendre hw hq hpq
  have ha0 := typeI_a_ne_zero_mod hw hq
  have hd0 := typeI_d_ne_zero_mod hw hq
  have h20 := typeI_two_ne_zero_mod hq2
  have h4ad : 4 * a * d = q + 1 := by
    have : 1 ≤ 4 * a * d := by
      have : 0 < 4 * a * d := Nat.mul_pos (Nat.mul_pos (by omega) ha) hd
      omega
    omega
  have h1 : ((4 * a * d : ℕ) : ZMod q) = 1 := by
    rw [h4ad, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  have hleg1 : legendreSym q (4 * a * d : ℤ) = 1 := by
    have hcast : ((4 * a * d : ℤ) : ZMod q) = ((1 : ℤ) : ZMod q) := by
      simpa using h1
    have hone : ((1 : ℤ) : ZMod q) ≠ 0 := by
      intro hz
      have hdvd : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).1 (by simpa using hz)
      exact Nat.Prime.ne_one Fact.out (Nat.dvd_one.mp hdvd)
    have : legendreSym q (1 : ℤ) = 1 :=
      (legendreSym.eq_one_iff (p := q) hone).2 ⟨(1 : ZMod q), by simp⟩
    rwa [legendreSym_eq_of_cast hcast]
  have h40 : ((4 : ℤ) : ZMod q) ≠ 0 := by
    have heq : (4 : ℤ) = (2 : ℤ) * 2 := by decide
    rw [heq, Int.cast_mul]
    exact mul_ne_zero h20 h20
  have h4 : legendreSym q (4 : ℤ) = 1 :=
    (legendreSym.eq_one_iff (p := q) h40).2 ⟨(2 : ZMod q), by
      exact (by norm_num : ((4 : ℤ) : ZMod q) = (2 : ZMod q) * 2)⟩
  have hmul : legendreSym q (4 * a * d : ℤ) =
      legendreSym q (4 : ℤ) * legendreSym q a * legendreSym q d := by
    have : (4 * a * d : ℤ) = (4 : ℤ) * a * d := by simp
    rw [this, legendreSym.mul, legendreSym.mul]
  have hprod : legendreSym q a * legendreSym q d = 1 := by
    have := hleg1
    rw [hmul, h4, one_mul] at this
    exact this
  have hsqd := sq_legendre_one hd0
  have haeq : legendreSym q a = legendreSym q d := by
    calc
      legendreSym q a
          = legendreSym q a * (legendreSym q d * legendreSym q d) := by
            rw [hsqd, mul_one]
        _ = (legendreSym q a * legendreSym q d) * legendreSym q d := by ring
        _ = 1 * legendreSym q d := by rw [hprod]
        _ = legendreSym q d := by ring
  calc
    legendreSym q p = legendreSym q (-(a : ℤ)) := hmain
    _ = legendreSym q (-1) * legendreSym q a := by
      rw [show (-(a : ℤ) = (-1) * a) by ring, legendreSym.mul]
    _ = legendreSym q (-1) * legendreSym q d := by rw [haeq]
    _ = legendreSym q (-(d : ℤ)) := by
      rw [← legendreSym.mul, show ((-1) * (d : ℤ) = -(d : ℤ)) by ring]

/-- Wrong d-slice symbol ⇒ no Type-I witness with that `(q, d)`. -/
theorem not_typeI_of_d_slice {p a d m q : Nat} [Fact q.Prime]
    (hq : q = 4 * a * d - 1)
    (hpq : ((p : ℤ) : ZMod q) ≠ 0) (hq2 : q ≠ 2)
    (hsym : legendreSym q p ≠ legendreSym q (-(d : ℤ))) :
    ¬ Witness p a 1 d m :=
  fun hw => hsym (typeI_d_slice hw hq hpq hq2)

/-! ## Hybrid fuel: q = 11 Type-I family only hits non-residues -/

private theorem fact_prime_eleven : Fact (Nat.Prime 11) := ⟨prime_11⟩
private theorem fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
attribute [local instance] fact_prime_eleven fact_prime_three

/-- The only Type-I pairs with modulus 11 are `(a,d) = (1,3)` and `(3,1)`. -/
theorem typeI_modulus_11_pairs {a d : Nat} (ha : 0 < a) (hd : 0 < d)
    (hq : (11 : Nat) = 4 * a * d - 1) :
    (a = 1 ∧ d = 3) ∨ (a = 3 ∧ d = 1) := by
  have hle : 1 ≤ 4 * a * d := by
    have : 0 < 4 * a * d := Nat.mul_pos (Nat.mul_pos (by omega) ha) hd
    omega
  have h12 : 4 * a * d = 12 := by omega
  have hprod : a * d = 3 := by
    have : a * d * 4 = 12 := by
      calc a * d * 4
          = 4 * a * d := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = 12 := h12
    omega
  have hale : a ≤ 3 :=
    Nat.le_trans (Nat.le_mul_of_pos_right a hd) (by omega)
  have hcases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases hcases with ha1 | ha2 | ha3
  · subst ha1
    exact Or.inl ⟨rfl, by omega⟩
  · subst ha2
    omega
  · subst ha3
    exact Or.inr ⟨rfl, by omega⟩

theorem d_slice_neg_1_mod_11 : legendreSym 11 (-((1 : Nat) : ℤ)) = -1 := by
  native_decide

theorem d_slice_neg_3_mod_11 : legendreSym 11 (-((3 : Nat) : ℤ)) = -1 := by
  native_decide

/-- Plan §4p at q = 11: both Type-I classes with this modulus live in the
    non-residue coset.  A residue `(p/11) = +1` cannot be covered by them. -/
theorem typeI_q11_nonresidue {p a d m : Nat}
    (hw : Witness p a 1 d m)
    (hq : (11 : Nat) = 4 * a * d - 1)
    (hpq : ((p : ℤ) : ZMod 11) ≠ 0) :
    legendreSym 11 p = -1 := by
  have ha : 0 < a := hw.1
  have hd : 0 < d := hw.2.2.1
  have hpairs := typeI_modulus_11_pairs ha hd hq
  have hslice := typeI_d_slice hw hq hpq (by decide)
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [d_slice_neg_3_mod_11] at hslice; exact hslice
  · rw [d_slice_neg_1_mod_11] at hslice; exact hslice

theorem not_typeI_q11_of_residue {p a d m : Nat}
    (hpq : ((p : ℤ) : ZMod 11) ≠ 0)
    (hres : legendreSym 11 p = 1)
    (hq : (11 : Nat) = 4 * a * d - 1) :
    ¬ Witness p a 1 d m :=
  fun hw => by
    have := typeI_q11_nonresidue hw hq hpq
    rw [hres] at this
    exact absurd this (by decide)

/-! ## Hard class excludes the q = 3 Type-I identity (QR method) -/

theorem hard_prime_legendre_three {p : Nat} [Fact p.Prime]
    (hh : HardClass p) (_hp3 : p ≠ 3) :
    legendreSym 3 p = 1 := by
  have hmod : p % 3 = 1 := (hardClass_mod hh).2
  have hone : ((1 : ℤ) : ZMod 3) ≠ 0 := by decide
  have hcast : ((p : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
    have hdiv := Nat.div_add_mod p 3
    have : (p : ZMod 3) = ((3 * (p / 3) + p % 3 : Nat) : ZMod 3) := by
      rw [hdiv]
    rw [hmod, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at this
    have hz : ((3 : Nat) : ZMod 3) = 0 := ZMod.natCast_self 3
    rw [hz, zero_mul, zero_add] at this
    simpa using this
  have : legendreSym 3 (1 : ℤ) = 1 :=
    (legendreSym.eq_one_iff (p := 3) hone).2 ⟨(1 : ZMod 3), by simp⟩
  rwa [legendreSym_eq_of_cast hcast]

theorem d_slice_neg_1_mod_3 : legendreSym 3 (-((1 : Nat) : ℤ)) = -1 := by
  native_decide

/-- Hard primes are `1 (mod 3)`, so they cannot occupy the Type-I class
    `q = 3` (which is the identity `n ≡ 2 (mod 3)`).  Same conclusion as
    `es_prime_not_hard`, reached from the d-slice law rather than ω. -/
theorem hard_not_typeI_q3 {p a d m : Nat} [Fact p.Prime]
    (hh : HardClass p) (hp3 : p ≠ 3)
    (hw : Witness p a 1 d m)
    (hq : (3 : Nat) = 4 * a * d - 1) : False := by
  have hpq : ((p : ℤ) : ZMod 3) ≠ 0 := by
    intro h
    have hdvd : (3 : Nat) ∣ p :=
      (ZMod.natCast_eq_zero_iff p 3).1 (by simpa using h)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp hdvd
    exact hp3 this.symm
  have hslice := typeI_d_slice hw hq hpq (by decide)
  have ha : 0 < a := hw.1
  have hd : 0 < d := hw.2.2.1
  have hle : 1 ≤ 4 * a * d := by
    have : 0 < 4 * a * d := Nat.mul_pos (Nat.mul_pos (by omega) ha) hd
    omega
  have h4 : 4 * a * d = 4 := by omega
  have had : a * d = 1 := by
    have hmul : a * d * 4 = 1 * 4 := by
      calc a * d * 4
          = 4 * a * d := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = 4 := h4
        _ = 1 * 4 := rfl
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < (4 : Nat)) hmul
  have ha1 : a = 1 := by
    have hale : a ≤ 1 := by
      have := Nat.le_mul_of_pos_right a hd
      rwa [had] at this
    omega
  have hd1 : d = 1 := by
    have hdle : d ≤ 1 := by
      have := Nat.le_mul_of_pos_right d ha
      rw [Nat.mul_comm] at this
      rwa [had] at this
    omega
  subst ha1; subst hd1
  have hleft := hard_prime_legendre_three hh hp3
  have hneg1 : legendreSym 3 (-((1 : Nat) : ℤ)) = -1 := d_slice_neg_1_mod_3
  rw [hleft, hneg1] at hslice
  exact absurd hslice (by decide)

/-! ## Type-2 dictionary: witness solutions feed BL Lemma 3.4 -/

/-- A covering witness at a prime `p` is a Type-2 BL point: `p` divides the
    last two coordinates.  BL Theorem 1.2 then constrains that solution
    (Yamamoto); it does not produce one. -/
theorem witness_is_type2_solution {p a c d m : Nat} (hp : 0 < p)
    (hw : Witness p a c d m) :
    IsES p (a * d * m) (p * (a * c * d)) (p * (c * d * m)) :=
  (witness_type2 hp hw).1

/-! ## Survivor ⇒ character bundle (roadmap §9) -/

open ES.Covering

theorem d_slice_neg_2_mod_11 : legendreSym 11 (-((2 : Nat) : ℤ)) = 1 := by
  native_decide

theorem d_slice_neg_4_mod_11 : legendreSym 11 (-((4 : Nat) : ℤ)) = -1 := by
  native_decide

theorem d_slice_neg_5_mod_11 : legendreSym 11 (-((5 : Nat) : ℤ)) = -1 := by
  native_decide

/-- Plan §4p table: d-slice signs at q = 11. -/
theorem d_slice_signs_11 :
    legendreSym 11 (-((1 : Nat) : ℤ)) = -1 ∧
    legendreSym 11 (-((2 : Nat) : ℤ)) = 1 ∧
    legendreSym 11 (-((3 : Nat) : ℤ)) = -1 ∧
    legendreSym 11 (-((4 : Nat) : ℤ)) = -1 ∧
    legendreSym 11 (-((5 : Nat) : ℤ)) = -1 :=
  ⟨d_slice_neg_1_mod_11, d_slice_neg_2_mod_11, d_slice_neg_3_mod_11,
    d_slice_neg_4_mod_11, d_slice_neg_5_mod_11⟩

/-- **Survivor ⇒ character.** Avoiding the q = 3 Type-I cell forces `(p/3) = +1`
    (the complementary coset).  This is the one-modulus case where the covering
    AP is the entire non-residue class. -/
theorem survivor_legendre_three {A p : Nat} [Fact p.Prime]
    (hA : 1 ≤ A) (hs : Survivor A p) (hp3 : p ≠ 3) :
    legendreSym 3 p = 1 := by
  have haps := survivor_typeI_aps (a := 1) (d := 1) hA hs
    ⟨Nat.le_refl 1, hA⟩ ⟨by omega, by omega⟩
  have hne : (p + 1) % 3 ≠ 0 := by
    have : 4 * 1 * 1 - 1 = 3 := by decide
    rw [this] at haps
    exact haps
  have hmod : p % 3 = 1 := by
    have hdiv := Nat.div_add_mod p 3
    have hr : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases hr with h0 | h1 | h2
    · have : (3 : Nat) ∣ p := Nat.dvd_of_mod_eq_zero h0
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp this
      exact absurd this.symm hp3
    · exact h1
    · have : (p + 1) % 3 = 0 := by omega
      exact absurd this hne
  have hone : ((1 : ℤ) : ZMod 3) ≠ 0 := by decide
  have hcast : ((p : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
    have hdiv := Nat.div_add_mod p 3
    have : (p : ZMod 3) = ((3 * (p / 3) + p % 3 : Nat) : ZMod 3) := by
      rw [hdiv]
    rw [hmod, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at this
    have hz : ((3 : Nat) : ZMod 3) = 0 := ZMod.natCast_self 3
    rw [hz, zero_mul, zero_add] at this
    simpa using this
  have : legendreSym 3 (1 : ℤ) = 1 :=
    (legendreSym.eq_one_iff (p := 3) hone).2 ⟨(1 : ZMod 3), by simp⟩
  rwa [legendreSym_eq_of_cast hcast]

/-- **Survivor ⇒ avoided APs at q = 11.** If A ≥ 3, both Type-I cells with
    modulus 11 are in the box; a survivor misses residues 8 and 10 (the two
    non-residue APs the family occupies).  Not a full character: non-residues
    2, 6, 7 remain allowed. -/
theorem survivor_avoids_typeI_q11 {A p : Nat}
    (hA : 3 ≤ A) (hs : Survivor A p) :
    p % 11 ≠ 8 ∧ p % 11 ≠ 10 := by
  have hA1 : 1 ≤ A := by omega
  have h8 := survivor_typeI_aps (a := 3) (d := 1) hA1 hs
    ⟨by omega, hA⟩ ⟨by omega, by omega⟩
  have h10 := survivor_typeI_aps (a := 1) (d := 3) hA1 hs
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  constructor
  · intro h
    have : (p + 3) % 11 = 0 := by omega
    have hmod : (p + 3) % (4 * 3 * 1 - 1) = 0 := by
      simpa using this
    exact h8 hmod
  · intro h
    have : (p + 1) % 11 = 0 := by omega
    have hmod : (p + 1) % (4 * 1 * 3 - 1) = 0 := by
      simpa using this
    exact h10 hmod

/-- One-slot (Elsholtz–Tao Type I) character law: if an odd prime `q` divides
    the modulus `4ad`, then `n ≡ −f (mod q)` forces `(n/q) = (−f/q)`. -/
theorem oneSlot_legendre {n a d f m q : Nat} [Fact q.Prime]
    (h : OneSlot n a d f m)
    (hqdiv : q ∣ 4 * a * d)
    (_hnq : ((n : ℤ) : ZMod q) ≠ 0) :
    legendreSym q n = legendreSym q (-(f : ℤ)) := by
  have hnm : n + f = 4 * a * d * m := h.2.2.2.2.2.2.1
  have hdvd : q ∣ n + f :=
    dvd_trans hqdiv ⟨m, by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnm⟩
  have hsum : ((n + f : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (n + f) q).2 hdvd
  have hadd : (n : ZMod q) + (f : ZMod q) = 0 := by
    simpa [Nat.cast_add] using hsum
  have hneg : (n : ZMod q) = -(f : ZMod q) := eq_neg_of_add_eq_zero_left hadd
  apply legendreSym_eq_of_cast
  rw [Int.cast_neg]
  simpa using hneg

theorem erdos_straus_of_hybrid_covering
    (Alevel : Nat → Nat) (X0 : Nat)
    (hbig : HybridSurvivorBound Alevel X0)
    (hsmall : ∀ p : Nat, p < X0 → IsPrime p → HardClass p →
      ∃ x y z, IsES p x y z) :
    ErdosStraus :=
  erdos_straus_of_hybrid Alevel X0 hbig hsmall

/-! ## BL Lemmas 3.5–3.6, Hilbert reciprocity, norm-form bridge -/

open ES.Covering
open FiniteField

/-- **BL Lemma 3.1** on an ES solution: the real invariant is −1. -/
theorem lemma31_of_isES {n x y z : Nat} (h : IsES n x y z) :
    hilbertInf (-(x : ℤ)) (-(y : ℤ)) = -1 :=
  lemma31 h.1 h.2.1 h.2.2.1

/-- Each coordinate of a positive solution satisfies `n ≤ 4x`, i.e. `1/x ≤ 4/n`. -/
theorem es_pos_coord_lower {n x y z : Nat} (h : IsES n x y z) :
    n ≤ 4 * x ∧ n ≤ 4 * y ∧ n ≤ 4 * z := by
  obtain ⟨hx, hy, hz, heq⟩ := h
  have hyz : 0 < y * z := Nat.mul_pos hy hz
  have hzx : 0 < z * x := Nat.mul_pos hz hx
  have hxy : 0 < x * y := Nat.mul_pos hx hy
  have hx' : n ≤ 4 * x := by
    have hsum : y * z ≤ x * y + y * z + z * x := by omega
    have : n * (y * z) ≤ 4 * x * (y * z) := by
      calc n * (y * z) ≤ n * (x * y + y * z + z * x) := Nat.mul_le_mul_left n hsum
        _ = 4 * (x * y * z) := heq.symm
        _ = 4 * x * (y * z) := by ring
    exact Nat.le_of_mul_le_mul_right this hyz
  have hy' : n ≤ 4 * y := by
    have hsum : z * x ≤ x * y + y * z + z * x := by omega
    have : n * (z * x) ≤ 4 * y * (z * x) := by
      calc n * (z * x) ≤ n * (x * y + y * z + z * x) := Nat.mul_le_mul_left n hsum
        _ = 4 * (x * y * z) := heq.symm
        _ = 4 * y * (z * x) := by ring
    exact Nat.le_of_mul_le_mul_right this hzx
  have hz' : n ≤ 4 * z := by
    have hsum : x * y ≤ x * y + y * z + z * x := by omega
    have : n * (x * y) ≤ 4 * z * (x * y) := by
      calc n * (x * y) ≤ n * (x * y + y * z + z * x) := Nat.mul_le_mul_left n hsum
        _ = 4 * (x * y * z) := heq.symm
        _ = 4 * z * (x * y) := by ring
    exact Nat.le_of_mul_le_mul_right this hxy
  exact ⟨hx', hy', hz'⟩

/-- **BL (3.6) / Lemma 3.10, positive octant.**  Ordering `x ≤ y ≤ z` forces
    `4x ≤ 3n`, so the smallest coordinate of a natural-number solution lies
    in a box of length `O(n)`.  This is Jahnel–Schindler strong obstruction
    at infinity: the real locus is unbounded, but integral points are not
    Zariski dense.  It enumerates solutions for fixed `n`; it does not
    produce one as `n` varies. -/
theorem es_pos_min_le {n x y z : Nat} (h : IsES n x y z)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    4 * x ≤ 3 * n := by
  obtain ⟨hx, hy, hz, heq⟩ := h
  have hyz0 : 0 < y * z := Nat.mul_pos hy hz
  have hxy_le : x * y ≤ y * z := by
    rw [Nat.mul_comm x y]
    exact Nat.mul_le_mul_left y (hxy.trans hyz)
  have hzx_le : z * x ≤ y * z := by
    have : z * x ≤ z * y := Nat.mul_le_mul_left z hxy
    rw [Nat.mul_comm z y] at this
    exact this
  have hsum : x * y + y * z + z * x ≤ 3 * (y * z) := by
    calc x * y + y * z + z * x
        = (x * y + z * x) + y * z := by ring
      _ ≤ (y * z + y * z) + y * z := Nat.add_le_add (Nat.add_le_add hxy_le hzx_le) (le_refl _)
      _ = 3 * (y * z) := by ring
  have : 4 * x * (y * z) ≤ 3 * n * (y * z) := by
    calc 4 * x * (y * z) = 4 * (x * y * z) := by ring
      _ = n * (x * y + y * z + z * x) := heq
      _ ≤ n * (3 * (y * z)) := Nat.mul_le_mul_left n hsum
      _ = 3 * n * (y * z) := by ring
  exact Nat.le_of_mul_le_mul_right this hyz0

/-! ## Affine Z-model of `U_n` (TUB-EP hypotheses 2–3)

Bright–Loughran work with the affine cubic
`U_n : 4 u₁ u₂ u₃ = n (u₁ u₂ + u₁ u₃ + u₂ u₃) ⊂ A³`.
Natural-number solutions are the positive octant of the Z-points.
The integral Hasse principle in that octant is open; the lemmas below
discharge the Z-model facts it would consume, without claiming it.

Schinzel’s family `m/n = 1/u+1/v+1/w` is the same equation with 4 replaced
by `m` (BL Remark 1.10). -/

/-- Integer points on the Schinzel affine model, nonzero coordinates.
    Association matches `IsES`: `m · (xyz) = n · (xy+yz+zx)`. -/
def IsSchinzelZ (m n : Nat) (x y z : Int) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
    (m : Int) * (x * y * z) = (n : Int) * (x * y + y * z + z * x)

/-- Integer points on the Erdős–Straus affine model `U_n`. -/
abbrev IsESZ (n : Nat) (x y z : Int) : Prop := IsSchinzelZ 4 n x y z

theorem isES_to_esZ {n x y z : Nat} (h : IsES n x y z) :
    IsESZ n x y z := by
  obtain ⟨hx, hy, hz, heq⟩ := h
  refine ⟨by exact_mod_cast hx.ne', by exact_mod_cast hy.ne',
    by exact_mod_cast hz.ne', ?_⟩
  exact_mod_cast heq

theorem isES_of_esZ_pos {n : Nat} {x y z : Int}
    (h : IsESZ n x y z) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IsES n x.toNat y.toNat z.toNat := by
  obtain ⟨_, _, _, heq⟩ := h
  have hxN : (x.toNat : Int) = x := Int.toNat_of_nonneg hx.le
  have hyN : (y.toNat : Int) = y := Int.toNat_of_nonneg hy.le
  have hzN : (z.toNat : Int) = z := Int.toNat_of_nonneg hz.le
  have hxP : 0 < x.toNat := by
    have : (0 : Int) < x.toNat := by omega
    exact_mod_cast this
  have hyP : 0 < y.toNat := by
    have : (0 : Int) < y.toNat := by omega
    exact_mod_cast this
  have hzP : 0 < z.toNat := by
    have : (0 : Int) < z.toNat := by omega
    exact_mod_cast this
  refine ⟨hxP, hyP, hzP, ?_⟩
  apply Int.ofNat_inj.mp
  simp only [Nat.cast_mul, Nat.cast_add]
  rw [hxN, hyN, hzN]
  exact heq

/-- Occupying the positive octant of `U_n(Z)` is exactly the conjecture. -/
theorem erdos_straus_iff_pos_octant :
    ErdosStraus ↔ ∀ n : Nat, 2 ≤ n → ∃ x y z : Int,
      IsESZ n x y z ∧ 0 < x ∧ 0 < y ∧ 0 < z := by
  constructor
  · intro H n hn
    obtain ⟨x, y, z, h⟩ := H n hn
    refine ⟨x, y, z, isES_to_esZ h, ?_, ?_, ?_⟩
    · exact_mod_cast h.1
    · exact_mod_cast h.2.1
    · exact_mod_cast h.2.2.1
  · intro H n hn
    obtain ⟨x, y, z, hZ, hx, hy, hz⟩ := H n hn
    exact ⟨_, _, _, isES_of_esZ_pos hZ hx hy hz⟩

/-- **TUB-EP**, as a hypothesis this file does not prove.

    Occupying the positive octant of every `U_n(ℤ)` for `n ≥ 2`.  The
    research content is an integral Hasse principle that would deduce this
    from the Z-model facts in `tub_ep_consumed` together with Bright–Loughran
    Theorem 1.8 (nonempty BM in `C₊`, not formalized).  Finiteness of
    integral points, the octant invariant, and mixed-sign occupancy do not
    by themselves produce a point of `C₊`: Markoff fibres can be empty with
    no BM obstruction when those extra geometric features fail.

    Equivalent to `ErdosStraus` (`tub_ep_iff_erdos_straus`). -/
def TubEpHypothesis : Prop :=
  ∀ n : Nat, 2 ≤ n → ∃ x y z : Int,
    IsESZ n x y z ∧ 0 < x ∧ 0 < y ∧ 0 < z

/-- **Conditional QED, geometric.**  TUB-EP implies Erdős–Straus.
    The hypothesis is not discharged. -/
theorem erdos_straus_of_tub_ep (H : TubEpHypothesis) : ErdosStraus :=
  erdos_straus_iff_pos_octant.mpr H

theorem tub_ep_iff_erdos_straus : TubEpHypothesis ↔ ErdosStraus :=
  erdos_straus_iff_pos_octant.symm

/-- TUB-EP is stronger than existence on hard primes. -/
theorem geometry_of_tub_ep (H : TubEpHypothesis) :
    GeometricExistencePrinciple := by
  intro p hp _hhard
  obtain ⟨x, y, z, hZ, hx, hy, hz⟩ := H p hp.1
  exact ⟨_, _, _, isES_of_esZ_pos hZ hx hy hz⟩

theorem schinzelZ_n_pos {m n : Nat} {x y z : Int}
    (h : IsSchinzelZ m n x y z) (hm : 0 < m) : 0 < n := by
  obtain ⟨hx, hy, hz, heq⟩ := h
  have hL : (m : Int) * (x * y * z) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm.ne') (mul_ne_zero (mul_ne_zero hx hy) hz)
  have hn : n ≠ 0 := by
    intro h0
    subst h0
    rw [Nat.cast_zero, zero_mul] at heq
    exact hL heq
  exact Nat.pos_of_ne_zero hn

/-- All-negative points are impossible: the left side of the equation is
    negative and the right side is positive. -/
theorem schinzelZ_not_all_neg {m n : Nat} {x y z : Int}
    (h : IsSchinzelZ m n x y z) (hm : 0 < m) :
    ¬ (x < 0 ∧ y < 0 ∧ z < 0) := by
  intro hneg
  obtain ⟨hxN, hyN, hzN⟩ := hneg
  have hn : 0 < n := schinzelZ_n_pos h hm
  obtain ⟨hx, hy, hz, heq⟩ := h
  have hmI : (0 : Int) < m := by exact_mod_cast hm
  have hnI : (0 : Int) < n := by exact_mod_cast hn
  have hxyP : 0 < x * y := mul_pos_of_neg_of_neg hxN hyN
  have hyzP : 0 < y * z := mul_pos_of_neg_of_neg hyN hzN
  have hzxP : 0 < z * x := mul_pos_of_neg_of_neg hzN hxN
  have hxyzN : x * y * z < 0 := mul_neg_of_pos_of_neg hxyP hzN
  have hL : (m : Int) * (x * y * z) < 0 := mul_neg_of_pos_of_neg hmI hxyzN
  have hsum : 0 < x * y + y * z + z * x := by nlinarith
  have hR : 0 < (n : Int) * (x * y + y * z + z * x) := mul_pos hnI hsum
  rw [heq] at hL
  linarith

/-- Flipping all three signs does not preserve the equation. -/
theorem schinzelZ_not_neg_all {m n : Nat} {x y z : Int}
    (h : IsSchinzelZ m n x y z) (hm : 0 < m) :
    ¬ IsSchinzelZ m n (-x) (-y) (-z) := by
  obtain ⟨hx, hy, hz, heq⟩ := h
  intro hneg
  obtain ⟨_, _, _, heq'⟩ := hneg
  have hL : (m : Int) * ((-x) * (-y) * (-z)) = -((m : Int) * (x * y * z)) := by ring
  have heq2 : -((m : Int) * (x * y * z)) = (m : Int) * (x * y * z) := by
    calc -((m : Int) * (x * y * z))
        = (m : Int) * ((-x) * (-y) * (-z)) := hL.symm
      _ = (n : Int) * ((-x) * (-y) + (-y) * (-z) + (-z) * (-x)) := heq'
      _ = (n : Int) * (x * y + y * z + z * x) := by ring
      _ = (m : Int) * (x * y * z) := heq.symm
  have hne : (m : Int) * (x * y * z) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm.ne') (mul_ne_zero (mul_ne_zero hx hy) hz)
  omega

/-- **BL (3.6), integer points.**  For any nonzero real solution the smallest
    coordinate satisfies `m |u_min| ≤ 3 n`.  This is Jahnel–Schindler strong
    obstruction at infinity: both real components are unbounded, but the
    minimum is boxed. -/
theorem schinzelZ_min_le {m n : Nat} {x y z : Int}
    (h : IsSchinzelZ m n x y z) (hm : 0 < m)
    (hxy : x.natAbs ≤ y.natAbs) (hyz : y.natAbs ≤ z.natAbs) :
    m * x.natAbs ≤ 3 * n := by
  obtain ⟨hx, hy, hz, heq⟩ := h
  have hsum :
      (x * y + y * z + z * x).natAbs ≤
        x.natAbs * y.natAbs + y.natAbs * z.natAbs + z.natAbs * x.natAbs := by
    have hassoc : x * y + y * z + z * x = x * y + (y * z + z * x) := by ring
    rw [hassoc]
    have h1 := Int.natAbs_add_le (x * y) (y * z + z * x)
    have h2 := Int.natAbs_add_le (y * z) (z * x)
    have h3 := Nat.add_le_add_left h2 (x * y).natAbs
    have : (x * y).natAbs + ((y * z).natAbs + (z * x).natAbs) =
        x.natAbs * y.natAbs + y.natAbs * z.natAbs + z.natAbs * x.natAbs := by
      simp only [Int.natAbs_mul]; ring
    exact h1.trans (h3.trans this.le)
  have hxy_le : x.natAbs * y.natAbs ≤ y.natAbs * z.natAbs := by
    have : x.natAbs * y.natAbs ≤ z.natAbs * y.natAbs :=
      Nat.mul_le_mul_right y.natAbs (hxy.trans hyz)
    rwa [Nat.mul_comm z.natAbs y.natAbs] at this
  have hzx_le : z.natAbs * x.natAbs ≤ y.natAbs * z.natAbs := by
    have : z.natAbs * x.natAbs ≤ z.natAbs * y.natAbs :=
      Nat.mul_le_mul_left z.natAbs hxy
    rwa [Nat.mul_comm z.natAbs y.natAbs] at this
  have h3 : (x * y + y * z + z * x).natAbs ≤ 3 * (y.natAbs * z.natAbs) := by
    calc (x * y + y * z + z * x).natAbs
        ≤ x.natAbs * y.natAbs + y.natAbs * z.natAbs + z.natAbs * x.natAbs := hsum
      _ ≤ y.natAbs * z.natAbs + y.natAbs * z.natAbs + y.natAbs * z.natAbs :=
          Nat.add_le_add (Nat.add_le_add hxy_le (Nat.le_refl _)) hzx_le
      _ = 3 * (y.natAbs * z.natAbs) := by ring
  have heqAbs : m * (x * y * z).natAbs = n * (x * y + y * z + z * x).natAbs := by
    have hcongr := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using hcongr
  have hxyz : (x * y * z).natAbs = x.natAbs * y.natAbs * z.natAbs := by
    simp only [Int.natAbs_mul]
  have : m * x.natAbs * y.natAbs * z.natAbs ≤ 3 * n * y.natAbs * z.natAbs := by
    calc m * x.natAbs * y.natAbs * z.natAbs
        = m * (x * y * z).natAbs := by rw [hxyz]; ring
      _ = n * (x * y + y * z + z * x).natAbs := heqAbs
      _ ≤ n * (3 * (y.natAbs * z.natAbs)) := Nat.mul_le_mul_left n h3
      _ = 3 * n * y.natAbs * z.natAbs := by ring
  have hyz0 : 0 < y.natAbs * z.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hy) (Int.natAbs_pos.mpr hz)
  have hmul : (m * x.natAbs) * (y.natAbs * z.natAbs) ≤
      (3 * n) * (y.natAbs * z.natAbs) := by
    convert this using 1 <;> ring
  exact Nat.le_of_mul_le_mul_right hmul hyz0

theorem esZ_min_le {n : Nat} {x y z : Int} (h : IsESZ n x y z)
    (hxy : x.natAbs ≤ y.natAbs) (hyz : y.natAbs ≤ z.natAbs) :
    4 * x.natAbs ≤ 3 * n :=
  schinzelZ_min_le h (by decide : (0 : Nat) < 4) hxy hyz

/-- Clearing the two-variable equation: `(r y − s)(r z − s) = s²` with
    `r = m x − n` and `s = n x`.  When `r = 0` this is the excluded locus
    `y = −z`.  Divisors of `s²` are finite, which is the rest of Lemma 3.10. -/
theorem schinzelZ_factor {m n : Nat} {x y z : Int}
    (h : IsSchinzelZ m n x y z) :
    (((m : Int) * x - n) * y - (n : Int) * x) *
      (((m : Int) * x - n) * z - (n : Int) * x) = ((n : Int) * x) ^ 2 := by
  obtain ⟨_, _, _, heq⟩ := h
  have heq' : (m : Int) * x * y * z = (n : Int) * (x * y + y * z + z * x) := by
    convert heq using 1 <;> ring
  have h' : ((m : Int) * x - n) * (y * z) = (n : Int) * x * (y + z) := by
    calc ((m : Int) * x - n) * (y * z)
        = (m : Int) * x * y * z - (n : Int) * y * z := by ring
      _ = (n : Int) * (x * y + y * z + z * x) - (n : Int) * y * z := by rw [heq']
      _ = (n : Int) * x * (y + z) := by ring
  calc (((m : Int) * x - n) * y - (n : Int) * x) *
        (((m : Int) * x - n) * z - (n : Int) * x)
      = ((m : Int) * x - n) * (((m : Int) * x - n) * (y * z) -
          (n : Int) * x * (y + z)) + ((n : Int) * x) ^ 2 := by ring
    _ = ((m : Int) * x - n) * 0 + ((n : Int) * x) ^ 2 := by rw [h']; ring
    _ = ((n : Int) * x) ^ 2 := by ring

/-- The first factor of Lemma 3.10 divides `s²`. -/
theorem schinzelZ_coord_dvd {m n : Nat} {x y z : Int}
    (h : IsSchinzelZ m n x y z) :
    ((m : Int) * x - n) * y - (n : Int) * x ∣ ((n : Int) * x) ^ 2 :=
  ⟨((m : Int) * x - n) * z - (n : Int) * x, (schinzelZ_factor h).symm⟩

/-! ## Octant repair (not QED)

The converse of `schinzelZ_factor` in the positive octant: a pair of
positive divisors `d, e` of `s²` with `d e = s²` and `r ∣ d+s`, `r ∣ e+s`
produces a natural-number point at this `x`.  Existence of such a pair
as `n` varies is Erdős–Straus.  The mixed-sign first coordinate
`x = (n-1)/2` does not always admit one (fails at `n = 13`).  The slice
`x = (n+3)/4`, `r = 3` does admit one for every `n ≡ 5 (mod 8)`, and
for those `n ≡ 1 (mod 4)` whose `s` has a prime factor `≡ 2 (mod 3)`.
The complementary set includes hard primes (e.g. `2521`).  Chaining more
moduli is covering densification and is not pursued. -/

/-- **Octant repair at a fixed `x`.**  Not existence of the divisor pair. -/
theorem es_of_s2_divisor {n x d e : Nat}
    (hx : 0 < x) (hn : 0 < n) (hd : 0 < d) (he : 0 < e)
    (hrlt : n < 4 * x)
    (hde : d * e = n * x * (n * x))
    (hdy : 4 * x - n ∣ d + n * x)
    (hez : 4 * x - n ∣ e + n * x) :
    IsES n x ((d + n * x) / (4 * x - n)) ((e + n * x) / (4 * x - n)) := by
  set r := 4 * x - n
  set s := n * x
  set y := (d + s) / r
  set z := (e + s) / r
  have hrpos : 0 < r := Nat.sub_pos_of_lt hrlt
  have _spos : 0 < s := Nat.mul_pos hn hx
  have hry : r * y = d + s := Nat.mul_div_cancel' (by simpa [r, s] using hdy)
  have hrz : r * z = e + s := Nat.mul_div_cancel' (by simpa [r, s] using hez)
  have hy0 : 0 < y := by
    refine Nat.pos_of_ne_zero ?_
    intro h0
    have : r * y = 0 := by rw [h0, Nat.mul_zero]
    rw [hry] at this
    exact (Nat.add_pos_left hd s).ne' this
  have hz0 : 0 < z := by
    refine Nat.pos_of_ne_zero ?_
    intro h0
    have : r * z = 0 := by rw [h0, Nat.mul_zero]
    rw [hrz] at this
    exact (Nat.add_pos_left he s).ne' this
  refine ⟨hx, hy0, hz0, ?_⟩
  have hexp : (d + s) * (e + s) = s * (d + e + 2 * s) := by
    have hss : d * e = s * s := by simpa [s] using hde
    calc (d + s) * (e + s)
        = d * e + s * (d + e) + s * s := by ring
      _ = s * s + s * (d + e) + s * s := by rw [hss]
      _ = s * (d + e + 2 * s) := by ring
  have h4xs : 4 * x * s = n * (s + x * r) := by
    have hnr : n + r = 4 * x := Nat.add_sub_of_le hrlt.le
    calc 4 * x * s = (n + r) * s := by rw [hnr]
      _ = n * s + r * s := by ring
      _ = n * (s + x * r) := by ring
  have key : 4 * x * (d + s) * (e + s) =
      n * (x * r * (d + s) + (d + s) * (e + s) + x * r * (e + s)) := by
    have h1 : 4 * x * (d + s) * (e + s) = 4 * x * ((d + s) * (e + s)) := by ring
    have h2 : 4 * x * ((d + s) * (e + s)) = 4 * x * (s * (d + e + 2 * s)) := by
      rw [hexp]
    have h3 : 4 * x * (s * (d + e + 2 * s)) = 4 * x * s * (d + e + 2 * s) := by ring
    have h4 : 4 * x * s * (d + e + 2 * s) = n * (s + x * r) * (d + e + 2 * s) := by
      rw [h4xs]
    have h5 : n * (s + x * r) * (d + e + 2 * s) =
        n * (s * (d + e + 2 * s) + x * r * (d + e + 2 * s)) := by ring
    have h6 : n * (s * (d + e + 2 * s) + x * r * (d + e + 2 * s)) =
        n * ((d + s) * (e + s) + x * r * (d + s) + x * r * (e + s)) := by
      rw [← hexp]; ring
    have h7 : n * ((d + s) * (e + s) + x * r * (d + s) + x * r * (e + s)) =
        n * (x * r * (d + s) + (d + s) * (e + s) + x * r * (e + s)) := by ring
    exact (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))
  have hL : r * r * (4 * (x * y * z)) = 4 * x * (d + s) * (e + s) := by
    calc r * r * (4 * (x * y * z)) = 4 * x * (r * y) * (r * z) := by ring
      _ = 4 * x * (d + s) * (e + s) := by rw [hry, hrz]
  have hR : r * r * (n * (x * y + y * z + z * x)) =
      n * (x * r * (d + s) + (d + s) * (e + s) + x * r * (e + s)) := by
    calc r * r * (n * (x * y + y * z + z * x))
        = n * (x * (r * y) * r + (r * y) * (r * z) + x * (r * z) * r) := by ring
      _ = n * (x * r * (d + s) + (d + s) * (e + s) + x * r * (e + s)) := by
          rw [hry, hrz]; ring
  have hmul : r * (r * (4 * (x * y * z))) =
      r * (r * (n * (x * y + y * z + z * x))) := by
    convert (hL.trans (key.trans hR.symm)) using 1 <;> ring
  exact Nat.eq_of_mul_eq_mul_left hrpos
    (Nat.eq_of_mul_eq_mul_left hrpos hmul)

lemma n_one_mod_four_add3 {n : Nat} (h : n % 4 = 1) :
    n + 3 = 4 * ((n + 3) / 4) := by
  have : 4 ∣ n + 3 := by omega
  exact (Nat.mul_div_cancel' this).symm

lemma n_one_mod_four_r3 {n : Nat} (h : n % 4 = 1) :
    4 * ((n + 3) / 4) - n = 3 := by
  have := n_one_mod_four_add3 h
  omega

lemma n_one_mod_four_x_pos {n : Nat} (hn : 5 ≤ n) (h : n % 4 = 1) :
    0 < (n + 3) / 4 := by omega

lemma n_one_mod_four_r_pos {n : Nat} (h : n % 4 = 1) :
    n < 4 * ((n + 3) / 4) := by
  have := n_one_mod_four_add3 h
  omega

/-- Slice `x = (n+3)/4`, `r = 3`, using the divisor `d = 3` when `3 ∣ s`. -/
theorem es_r3_of_div3 {n : Nat} (hn : 5 ≤ n) (h4 : n % 4 = 1)
    (h3 : 3 ∣ n * ((n + 3) / 4)) :
    IsES n ((n + 3) / 4)
      ((3 + n * ((n + 3) / 4)) / 3)
      ((n * ((n + 3) / 4) * (n * ((n + 3) / 4)) / 3
        + n * ((n + 3) / 4)) / 3) := by
  set x := (n + 3) / 4
  set s := n * x
  have hx : 0 < x := n_one_mod_four_x_pos hn h4
  have hn0 : 0 < n := by omega
  have hrlt : n < 4 * x := n_one_mod_four_r_pos h4
  have hr3 : 4 * x - n = 3 := n_one_mod_four_r3 h4
  have hs3 : 3 ∣ s := by simpa [s, x] using h3
  obtain ⟨t, ht⟩ := hs3
  have hde : 3 * (t * t * 3) = s * s := by rw [ht]; ring
  have hdy : 4 * x - n ∣ 3 + s := by
    rw [hr3]; exact ⟨t + 1, by rw [ht]; ring⟩
  have hez : 4 * x - n ∣ t * t * 3 + s := by
    rw [hr3]; exact ⟨t * t + t, by rw [ht]; ring⟩
  have htpos : 0 < t := by
    have hspos : 0 < s := Nat.mul_pos hn0 hx
    rw [ht] at hspos
    exact Nat.pos_of_mul_pos_left hspos
  have hepos : 0 < t * t * 3 :=
    Nat.mul_pos (Nat.mul_pos htpos htpos) (by decide : 0 < 3)
  have hsol := es_of_s2_divisor hx hn0 (by decide : 0 < 3) hepos hrlt
    (by simpa [x, s] using hde) (by simpa [x, s] using hdy)
    (by simpa [x, s] using hez)
  have hss : s * s / 3 = t * t * 3 := by
    rw [ht]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 3) (by ring)
  simpa [x, s, hr3, hss] using hsol

/-- Slice `x = (n+3)/4`, `r = 3`, using a prime factor `q ≡ 2 (mod 3)` of `s`
    when `3 ∤ s`.  Fails for some `n ≡ 1 (mod 8)` (e.g. `73`, `2521`). -/
theorem es_r3_of_two_mod_three {n q : Nat} (hn : 5 ≤ n) (h4 : n % 4 = 1)
    (hq : Nat.Prime q) (hq3 : q % 3 = 2)
    (hdvd : q ∣ n * ((n + 3) / 4))
    (hnot3 : ¬ 3 ∣ n * ((n + 3) / 4)) :
    IsES n ((n + 3) / 4)
      ((q + n * ((n + 3) / 4)) / 3)
      ((n * ((n + 3) / 4) * (n * ((n + 3) / 4)) / q
        + n * ((n + 3) / 4)) / 3) := by
  set x := (n + 3) / 4
  set s := n * x
  have hx : 0 < x := n_one_mod_four_x_pos hn h4
  have hn0 : 0 < n := by omega
  have hrlt : n < 4 * x := n_one_mod_four_r_pos h4
  have hr3 : 4 * x - n = 3 := n_one_mod_four_r3 h4
  have hq0 : 0 < q := hq.pos
  have hs : s = n * x := rfl
  have hqdv : q ∣ s := by simpa [s, x] using hdvd
  have hq3n : ¬ 3 ∣ s := by simpa [s, x] using hnot3
  have hde : q * (s * s / q) = s * s :=
    Nat.mul_div_cancel' (hqdv.mul_right s)
  have hsm : s % 3 = 1 := by
    have hx4 := n_one_mod_four_add3 h4
    have hxmod : x % 3 = n % 3 := by
      have hL : (4 * x) % 3 = x % 3 := by
        have h41 : (4 : Nat) % 3 = 1 := rfl
        calc (4 * x) % 3 = (4 % 3 * (x % 3)) % 3 := Nat.mul_mod 4 x 3
          _ = (1 * (x % 3)) % 3 := by rw [h41]
          _ = x % 3 := by rw [Nat.one_mul, Nat.mod_mod]
      have hR : (n + 3) % 3 = n % 3 := by omega
      have : (4 * x) % 3 = (n + 3) % 3 := by rw [hx4.symm]
      omega
    have hsq : s % 3 = (n % 3 * (n % 3)) % 3 := by
      calc s % 3 = (n * x) % 3 := rfl
        _ = (n % 3 * (x % 3)) % 3 := Nat.mul_mod n x 3
        _ = (n % 3 * (n % 3)) % 3 := by rw [hxmod]
    have hn3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hn3 with hn0' | hn1 | hn2
    · have hs0 : s % 3 = 0 := by rw [hsq, hn0']
      exact False.elim (hq3n (Nat.dvd_of_mod_eq_zero hs0))
    · rw [hsq, hn1]
    · rw [hsq, hn2]
  have hdy : 4 * x - n ∣ q + s := by
    rw [hr3]
    have : (q + s) % 3 = 0 := by
      calc (q + s) % 3 = (q % 3 + s % 3) % 3 := Nat.add_mod q s 3
        _ = (2 + 1) % 3 := by rw [hq3, hsm]
        _ = 0 := rfl
    exact Nat.dvd_of_mod_eq_zero this
  have hez : 4 * x - n ∣ s * s / q + s := by
    rw [hr3]
    obtain ⟨t, ht⟩ := hqdv
    have heval : s * s / q = q * t * t :=
      Nat.div_eq_of_eq_mul_left hq0 (by rw [ht]; ring)
    have hst : s % 3 = (q % 3 * (t % 3)) % 3 := by
      rw [ht]; exact Nat.mul_mod q t 3
    have htmod : t % 3 = 2 := by
      have hprod : (2 * (t % 3)) % 3 = 1 := by
        have := hst
        rw [hq3, hsm] at this
        exact this.symm
      have ht3 : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by
        have := Nat.mod_lt t (by decide : 0 < 3)
        omega
      rcases ht3 with h0 | h1 | h2
      · rw [h0] at hprod
        exact absurd hprod (by decide : ¬ (0 : Nat) = 1)
      · rw [h1] at hprod
        exact absurd hprod (by decide : ¬ (2 : Nat) = 1)
      · exact h2
    have ht1 : 3 ∣ t + 1 :=
      Nat.dvd_of_mod_eq_zero (by
        calc (t + 1) % 3 = (t % 3 + 1 % 3) % 3 := Nat.add_mod t 1 3
          _ = (2 + 1) % 3 := by rw [htmod]
          _ = 0 := rfl)
    obtain ⟨u, hu⟩ := ht1
    refine ⟨q * t * u, ?_⟩
    calc s * s / q + s = q * t * t + s := by rw [heval]
      _ = q * t * t + q * t := by rw [ht]
      _ = q * t * (t + 1) := by ring
      _ = q * t * (3 * u) := by rw [hu]
      _ = 3 * (q * t * u) := by ring
  have hspos : 0 < s := Nat.mul_pos hn0 hx
  have hepos : 0 < s * s / q :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hspos hspos) (hqdv.mul_right s)) hq0
  simpa [x, s, hr3] using
    es_of_s2_divisor hx hn0 hq0 hepos hrlt (by simpa [x, s] using hde)
      (by simpa [x, s] using hdy) (by simpa [x, s] using hez)

/-- Geometric re-proof of the classical `8t+5` identity: on this class `s` is
    even, so either `3 ∣ s` (use `d = 3`) or `2 ∣ s` with `2 ≡ 2 (mod 3)`. -/
theorem es_five_mod_eight_of_repair (t : Nat) :
    ∃ x y z, IsES (8 * t + 5) x y z := by
  have h4 : (8 * t + 5) % 4 = 1 := by omega
  have hn : 5 ≤ 8 * t + 5 := by omega
  set n := 8 * t + 5
  have hx : (n + 3) / 4 = 2 * t + 2 := by omega
  by_cases h3 : 3 ∣ n * ((n + 3) / 4)
  · exact ⟨_, _, _, es_r3_of_div3 hn h4 h3⟩
  · have h2 : 2 ∣ n * ((n + 3) / 4) := by
      rw [hx]
      exact dvd_mul_of_dvd_right (by exact ⟨t + 1, by ring⟩) n
    exact ⟨_, _, _,
      es_r3_of_two_mod_three hn h4 Nat.prime_two (by decide) h2 h3⟩

/-- The `r = 3` slice occupies the positive octant whenever `s` is divisible
    by `3` or by a prime `≡ 2 (mod 3)`.  This is not Erdős–Straus: the
    complementary class is inhabited (e.g. `73`, `2521`). -/
theorem es_of_r3_slice {n : Nat} (hn : 5 ≤ n) (h4 : n % 4 = 1)
    (h : 3 ∣ n * ((n + 3) / 4) ∨
      ∃ q, Nat.Prime q ∧ q % 3 = 2 ∧ q ∣ n * ((n + 3) / 4)) :
    ∃ x y z, IsES n x y z := by
  rcases h with h3 | ⟨q, hq, hq3, hdvd⟩
  · exact ⟨_, _, _, es_r3_of_div3 hn h4 h3⟩
  · by_cases h3 : 3 ∣ n * ((n + 3) / 4)
    · exact ⟨_, _, _, es_r3_of_div3 hn h4 h3⟩
    · exact ⟨_, _, _, es_r3_of_two_mod_three hn h4 hq hq3 hdvd h3⟩

/-- The `r = 3` repair is not Erdős–Straus: at `n = 73`, `s = 19 · 73`
    has only prime factors `≡ 1 (mod 3)`. -/
theorem r3_slice_obstructed_at_73 :
    ¬ (3 ∣ 73 * ((73 + 3) / 4) ∨
      ∃ q, Nat.Prime q ∧ q % 3 = 2 ∧ q ∣ 73 * ((73 + 3) / 4)) := by
  have hs : 73 * ((73 + 3) / 4) = 19 * 73 := by decide
  intro h
  rcases h with h3 | ⟨q, hq, hq3, hdvd⟩
  · have : ¬ 3 ∣ 19 * 73 := by decide
    exact this (by simpa [hs] using h3)
  · have hqmul : q ∣ 19 * 73 := by simpa [hs] using hdvd
    have hpr19 : Nat.Prime 19 := by decide
    have hpr73 : Nat.Prime 73 := by decide
    have hcases : q ∣ 19 ∨ q ∣ 73 := (Nat.Prime.dvd_mul hq).mp hqmul
    rcases hcases with h19 | h73'
    · have hqeq : q = 19 := (Nat.prime_dvd_prime_iff_eq hq hpr19).mp h19
      rw [hqeq] at hq3
      exact absurd hq3 (by decide : ¬ (19 : Nat) % 3 = 2)
    · have hqeq : q = 73 := (Nat.prime_dvd_prime_iff_eq hq hpr73).mp h73'
      rw [hqeq] at hq3
      exact absurd hq3 (by decide : ¬ (73 : Nat) % 3 = 2)

/-- Even `n = 2 t` has a positive integer point `(2t, 2t, t)`. -/
theorem esZ_of_even {t : Nat} (ht : 0 < t) :
    IsESZ (2 * t) (2 * t : Int) (2 * t : Int) (t : Int) := by
  refine ⟨by omega, by omega, by omega, ?_⟩
  simp [Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Odd `n = 2 k + 1` has the classical mixed-sign point
    `4/n = 1/k + 1/(k+1) − 1/(n k (k+1))`.  This occupies `U_n(Z)`
    independently of the conjecture, and lies off the positive octant. -/
theorem esZ_of_odd {k : Nat} (hk : 0 < k) :
    IsESZ (2 * k + 1) (k : Int) (k + 1 : Int)
      (-((2 * k + 1 : Int) * k * (k + 1))) := by
  have hkI : (0 : Int) < k := by exact_mod_cast hk
  have hnI : (0 : Int) < (2 * k + 1 : Int) := by
    have : 0 < 2 * k + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hk1 : (0 : Int) < (k : Int) + 1 := by
    have : 0 < k + 1 := Nat.succ_pos k
    exact_mod_cast this
  have hprod : (0 : Int) < (2 * k + 1 : Int) * k * (k + 1) :=
    mul_pos (mul_pos hnI hkI) hk1
  have hz : (-((2 * k + 1 : Int) * k * (k + 1))) ≠ 0 :=
    neg_ne_zero.mpr hprod.ne'
  refine ⟨by omega, by omega, hz, ?_⟩
  simp [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem esZ_of_odd_not_pos {k : Nat} (hk : 0 < k) :
    ¬ (0 < (k : Int) ∧ 0 < (k + 1 : Int) ∧
        0 < -((2 * k + 1 : Int) * k * (k + 1))) := by
  intro h
  have hkI : (0 : Int) < k := by exact_mod_cast hk
  have hnI : (0 : Int) < (2 * k + 1 : Int) := by
    have : 0 < 2 * k + 1 := Nat.succ_pos _
    exact_mod_cast this
  have hk1 : (0 : Int) < (k : Int) + 1 := by
    have : 0 < k + 1 := Nat.succ_pos k
    exact_mod_cast this
  have hprod : (0 : Int) < (2 * k + 1 : Int) * k * (k + 1) :=
    mul_pos (mul_pos hnI hkI) hk1
  have : 0 < -((2 * k + 1 : Int) * k * (k + 1)) := h.2.2
  nlinarith

/-- **Hypothesis 3 of TUB-EP, nonempty.**  `U_n(Z)` is nonempty for every
    `n ≥ 2`.  Even `n` uses a positive point; odd `n` uses mixed signs. -/
theorem esZ_nonempty {n : Nat} (hn : 2 ≤ n) : ∃ x y z, IsESZ n x y z := by
  rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
  · have ht : 2 * (n / 2) = n := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hev)
    have ht0 : 0 < n / 2 := by omega
    have hpt := esZ_of_even ht0
    rw [ht] at hpt
    exact ⟨_, _, _, hpt⟩
  · have hk : 0 < n / 2 := by omega
    have hn' : 2 * (n / 2) + 1 = n :=
      Nat.two_mul_div_two_add_one_of_odd (Nat.odd_iff.mpr hodd)
    have hpt := esZ_of_odd hk
    rw [hn'] at hpt
    exact ⟨_, _, _, hpt⟩

/-- Real invariant of α = (−u₁/u₃, −u₂/u₃).  Clearing the positive square
    `u₃²` does not change signs, so this is `(−u₁/u₃, −u₂/u₃)_∞`. -/
def invInfES (x y z : Int) : Int :=
  hilbertInf (-x * z) (-y * z)

theorem invInfES_same_sign_iff {x y z : Int}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (-x * z < 0 ∧ -y * z < 0) ↔
      (0 < x ∧ 0 < y ∧ 0 < z) ∨ (x < 0 ∧ y < 0 ∧ z < 0) := by
  constructor
  · intro ⟨hxz, hyz⟩
    have hxsz : 0 < x * z := by nlinarith
    have hysz : 0 < y * z := by nlinarith
    rcases lt_trichotomy z 0 with hzN | hz0 | hzP
    · exact Or.inr ⟨by nlinarith, by nlinarith, hzN⟩
    · exact (hz hz0).elim
    · exact Or.inl ⟨by nlinarith, by nlinarith, hzP⟩
  · intro h
    rcases h with ⟨hxP, hyP, hzP⟩ | ⟨hxN, hyN, hzN⟩
    · constructor <;> nlinarith
    · constructor <;> nlinarith

theorem invInfES_eq_neg_one_iff {x y z : Int}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    invInfES x y z = -1 ↔
      (0 < x ∧ 0 < y ∧ 0 < z) ∨ (x < 0 ∧ y < 0 ∧ z < 0) := by
  unfold invInfES hilbertInf
  constructor
  · intro h
    by_cases hcond : -x * z < 0 ∧ -y * z < 0
    · exact (invInfES_same_sign_iff hx hy hz).1 hcond
    · rw [if_neg hcond] at h
      cases h
  · intro h
    have hcond : -x * z < 0 ∧ -y * z < 0 :=
      (invInfES_same_sign_iff hx hy hz).2 h
    rw [if_pos hcond]

/-- **BL Lemma 3.1 on the Z-model.**  The real invariant is −1 exactly on
    the two same-sign octants; the all-negative octant is empty, so −1
    detects the positive component. -/
theorem invInfES_pos {x y z : Int} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    invInfES x y z = -1 :=
  (invInfES_eq_neg_one_iff hx.ne' hy.ne' hz.ne').2 (Or.inl ⟨hx, hy, hz⟩)

theorem invInfES_of_esZ_pos {n : Nat} {x y z : Int}
    (_h : IsESZ n x y z) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    invInfES x y z = -1 :=
  invInfES_pos hx hy hz

/-- **Theorem 1.5 at the real place.**  A mixed-sign integer point has
    inv_∞ α = +1. -/
theorem invInfES_of_esZ_mixed {n : Nat} {x y z : Int}
    (h : IsESZ n x y z) (hmix : ¬ (0 < x ∧ 0 < y ∧ 0 < z)) :
    invInfES x y z = 1 := by
  have hneg : ¬ (x < 0 ∧ y < 0 ∧ z < 0) :=
    schinzelZ_not_all_neg h (by decide : (0 : Nat) < 4)
  obtain ⟨hx, hy, hz, _⟩ := h
  unfold invInfES hilbertInf
  split_ifs with hcond
  · rcases (invInfES_same_sign_iff hx hy hz).1 hcond with hpos | halln
    · exact (hmix hpos).elim
    · exact (hneg halln).elim
  · rfl

theorem invInfES_odd_mixed {k : Nat} (hk : 0 < k) :
    invInfES (k : Int) (k + 1 : Int)
      (-((2 * k + 1 : Int) * k * (k + 1))) = 1 :=
  invInfES_of_esZ_mixed (esZ_of_odd hk) (esZ_of_odd_not_pos hk)

/-- Positive rational points in the octant exist for every `n > 0`:
    `(n, n, n/2)`.  Strong approximation off infinity recovers rationals,
    not integers; this is why Cao–Xu does not imply ES. -/
theorem esQ_pos (n : Nat) (hn : 0 < n) :
    (4 : ℚ) / n = 1 / (n : ℚ) + 1 / (n : ℚ) + 1 / ((n : ℚ) / 2) := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- Z-model facts TUB-EP may consume.  All are theorems in this file.
    Bright–Loughran Theorem 1.8 is not a field: it is not formalized here,
    and this structure does not claim it. -/
structure TubEpConsumed : Prop where
  nonempty :
    ∀ n : Nat, 2 ≤ n → ∃ x y z, IsESZ n x y z
  box :
    ∀ n : Nat, ∀ x y z : Int, IsESZ n x y z →
      x.natAbs ≤ y.natAbs → y.natAbs ≤ z.natAbs → 4 * x.natAbs ≤ 3 * n
  inv_pos :
    ∀ x y z : Int, 0 < x → 0 < y → 0 < z → invInfES x y z = -1
  inv_mixed :
    ∀ n : Nat, ∀ x y z : Int,
      IsESZ n x y z → ¬ (0 < x ∧ 0 < y ∧ 0 < z) → invInfES x y z = 1
  pos_rationals :
    ∀ n : Nat, 0 < n →
      (4 : ℚ) / n = 1 / (n : ℚ) + 1 / (n : ℚ) + 1 / ((n : ℚ) / 2)

/-- Assembly of the consumed facts.  Not TUB-EP, and not `ErdosStraus`. -/
def tub_ep_consumed : TubEpConsumed where
  nonempty := fun _ hn => esZ_nonempty hn
  box := fun _ _ _ _ h hxy hyz => esZ_min_le h hxy hyz
  inv_pos := fun _ _ _ hx hy hz => invInfES_pos hx hy hz
  inv_mixed := fun _ _ _ _ h hmix => invInfES_of_esZ_mixed h hmix
  pos_rationals := esQ_pos

/-- **BL Lemma 3.5** (exact-one prohibition). A good odd prime cannot divide
    exactly one coordinate of a natural-number solution. -/
theorem lemma35_not_exact_one {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (_hq2 : q ≠ 2) (hqn : ¬ q ∣ n)
    (hx : q ∣ x) (hy : ¬ q ∣ y) (hz : ¬ q ∣ z) : False := by
  obtain ⟨hx0, hy0, hz0, heq⟩ := hES
  have hL : q ∣ 4 * x * y * z :=
    hx.trans ⟨4 * y * z, by ring⟩
  have hR : ¬ q ∣ n * (x * y + y * z + z * x) := by
    intro h
    rcases (Nat.Prime.dvd_mul (show Nat.Prime q from Fact.out)).mp h with hn | hsum
    · exact hqn hn
    · have hxy : q ∣ x * y := hx.trans ⟨y, by ring⟩
      have hzx : q ∣ z * x := hx.trans ⟨z, by ring⟩
      have hyz : ¬ q ∣ y * z := by
        intro h'
        rcases (Nat.Prime.dvd_mul (show Nat.Prime q from Fact.out)).mp h' with h' | h'
        · exact hy h'
        · exact hz h'
      have hsum' : x * y + y * z + z * x = x * y + (y * z + z * x) := by ring
      have hsum2 : q ∣ x * y + (y * z + z * x) := by rwa [hsum'] at hsum
      have hmid : q ∣ y * z + z * x := (Nat.dvd_add_iff_right hxy).mpr hsum2
      have : q ∣ y * z := (Nat.dvd_add_iff_left hzx).mpr hmid
      exact hyz this
  have : q ∣ n * (x * y + y * z + z * x) := by
    rw [← heq]; convert hL using 1; ring
  exact hR this

/-- The three cyclic permutations of Lemma 3.5's exact-one prohibition. -/
theorem lemma35_not_exact_one_any {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hq2 : q ≠ 2) (hqn : ¬ q ∣ n) :
    ¬ (q ∣ x ∧ ¬ q ∣ y ∧ ¬ q ∣ z) ∧
    ¬ (q ∣ y ∧ ¬ q ∣ x ∧ ¬ q ∣ z) ∧
    ¬ (q ∣ z ∧ ¬ q ∣ x ∧ ¬ q ∣ y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨hx, hy, hz⟩; exact lemma35_not_exact_one hES hq2 hqn hx hy hz
  · intro ⟨hy, hx, hz⟩
    -- relabel (x,y,z) ↦ (y,x,z)
    have hES' : IsES n y x z := by
      obtain ⟨hx0, hy0, hz0, heq⟩ := hES
      refine ⟨hy0, hx0, hz0, ?_⟩
      convert heq using 1 <;> ring
    exact lemma35_not_exact_one hES' hq2 hqn hy hx hz
  · intro ⟨hz, hx, hy⟩
    have hES' : IsES n z x y := by
      obtain ⟨hx0, hy0, hz0, heq⟩ := hES
      refine ⟨hz0, hx0, hy0, ?_⟩
      convert heq using 1 <;> ring
    exact lemma35_not_exact_one hES' hq2 hqn hz hx hy

/-- **BL Lemma 3.5**, units case: if a good odd prime divides none of the
    coordinates, both Hilbert arguments are units and the invariant is 1. -/
theorem lemma35_units {q n x y z : Nat} [Fact q.Prime]
    (_hES : IsES n x y z) (_hq2 : q ≠ 2) (_hqn : ¬ q ∣ n)
    (_hx : ¬ q ∣ x) (_hy : ¬ q ∣ y) (_hz : ¬ q ∣ z) :
    hilbertOdd q 0 0 (x % q) (y % q) = 1 := by
  unfold hilbertOdd
  have h0 : ¬ (0 % 2 = 1 ∧ 0 % 2 = 1 ∧ q % 4 = 3) := by omega
  rw [if_neg h0]
  simp

/-- **BL Lemma 3.5** (divisibility dichotomy): a good odd prime either
    divides none of the coordinates or divides at least two.
    The exact-one case is prohibited. -/
theorem lemma35_nat {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hq2 : q ≠ 2) (hqn : ¬ q ∣ n) :
    (¬ q ∣ x ∧ ¬ q ∣ y ∧ ¬ q ∣ z) ∨
    ((q ∣ x ∧ q ∣ y) ∨ (q ∣ y ∧ q ∣ z) ∨ (q ∣ z ∧ q ∣ x)) := by
  have hperm := lemma35_not_exact_one_any (q := q) hES hq2 hqn
  by_cases hx : q ∣ x
  · by_cases hy : q ∣ y
    · exact Or.inr (Or.inl ⟨hx, hy⟩)
    · by_cases hz : q ∣ z
      · exact Or.inr (Or.inr (Or.inr ⟨hz, hx⟩))
      · exact False.elim (hperm.1 ⟨hx, hy, hz⟩)
  · by_cases hy : q ∣ y
    · by_cases hz : q ∣ z
      · exact Or.inr (Or.inr (Or.inl ⟨hy, hz⟩))
      · exact False.elim (hperm.2.1 ⟨hy, hx, hz⟩)
    · by_cases hz : q ∣ z
      · exact False.elim (hperm.2.2 ⟨hz, hx, hy⟩)
      · exact Or.inl ⟨hx, hy, hz⟩

lemma isES_swap_xy {n x y z : Nat} (h : IsES n x y z) : IsES n y x z := by
  have ⟨hx, hy, hz, heq⟩ := h
  refine ⟨hy, hx, hz, ?_⟩
  convert heq using 1 <;> ring

lemma isES_swap_yz {n x y z : Nat} (h : IsES n x y z) : IsES n x z y := by
  have ⟨hx, hy, hz, heq⟩ := h
  refine ⟨hx, hz, hy, ?_⟩
  convert heq using 1 <;> ring

lemma es_n_pos {n x y z : Nat} (h : IsES n x y z) : 0 < n := by
  have ⟨hx, hy, hz, heq⟩ := h
  have hpos : 0 < 4 * (x * y * z) :=
    Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos hx hy) hz)
  have hn : n ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at heq
    exact Nat.ne_of_gt hpos heq
  exact Nat.pos_of_ne_zero hn

lemma unitPart_mul {p n : Nat} [Fact p.Prime] :
    p ^ padicValNat p n * (n / p ^ padicValNat p n) = n :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

lemma unitPart_not_dvd {p n : Nat} [Fact p.Prime] (hn : n ≠ 0) :
    ¬ p ∣ n / p ^ padicValNat p n := by
  intro h
  have hnm : p ^ padicValNat p n * (n / p ^ padicValNat p n) = n := unitPart_mul
  have : p ^ (padicValNat p n + 1) ∣ n := by
    rw [Nat.pow_succ]
    exact (Nat.mul_dvd_mul_left _ h).trans (by rw [hnm])
  exact pow_succ_padicValNat_not_dvd hn this

lemma padicValNat_add_ge_min {p a b : Nat} [Fact p.Prime]
    (ha : a ≠ 0) (_hb : b ≠ 0) :
    min (padicValNat p a) (padicValNat p b) ≤ padicValNat p (a + b) := by
  have hnz : ((a + b : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero ha) b))
  have hsum : (a : ℚ) + (b : ℚ) ≠ 0 := by simpa using hnz
  have h := padicValRat.min_le_padicValRat_add (p := p) (q := (a : ℚ)) (r := (b : ℚ)) hsum
  have hQ : (a : ℚ) + (b : ℚ) = (a + b : ℕ) := by simp
  rw [hQ, padicValRat.of_nat, padicValRat.of_nat, padicValRat.of_nat] at h
  exact Int.ofNat_le.mp (by simpa [Nat.cast_min] using h)

lemma padicValNat_add_of_lt {p a b : Nat} [Fact p.Prime]
    (ha : a ≠ 0) (hb : b ≠ 0) (h : padicValNat p a < padicValNat p b) :
    padicValNat p (a + b) = padicValNat p a := by
  have hnz : ((a + b : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero ha) b))
  have hsum : (a : ℚ) + (b : ℚ) ≠ 0 := by simpa using hnz
  have hR := padicValRat.add_eq_min (p := p) (q := (a : ℚ)) (r := (b : ℚ)) hsum
    (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)
    (by simpa [padicValRat.of_nat] using (ne_of_lt h))
  have hQ : (a : ℚ) + (b : ℚ) = (a + b : ℕ) := by simp
  have : (padicValNat p (a + b) : ℤ) = padicValNat p a := by
    calc (padicValNat p (a + b) : ℤ)
        = padicValRat p (a + b : ℕ) := by rw [padicValRat.of_nat]
      _ = padicValRat p ((a : ℚ) + b) := by rw [← hQ]
      _ = min (padicValRat p a) (padicValRat p b) := hR
      _ = min (padicValNat p a : ℤ) (padicValNat p b) := by
          simp [padicValRat.of_nat]
      _ = padicValNat p a := min_eq_left (Int.ofNat_le.mpr (le_of_lt h))
  exact_mod_cast this

lemma pow_add_three (q a b c : Nat) :
    q ^ a * q ^ b * q ^ c = q ^ (a + b + c) := by
  rw [Nat.pow_add, Nat.pow_add, mul_assoc]

/-- BL Lemma 3.2 on a Nat solution at a good prime: after ordering the
    valuations, two consecutive ones agree. -/
theorem lemma32_sorted {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hqn : ¬ q ∣ n)
    (hord : padicValNat q x ≤ padicValNat q y ∧ padicValNat q y ≤ padicValNat q z) :
    padicValNat q x = padicValNat q y ∨ padicValNat q y = padicValNat q z := by
  have ⟨hx, hy, hz, heq⟩ := hES
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hy0 : y ≠ 0 := Nat.ne_of_gt hy
  have hz0 : z ≠ 0 := Nat.ne_of_gt hz
  let vx := padicValNat q x
  let vy := padicValNat q y
  let vz := padicValNat q z
  let rx := x / q ^ vx
  let ry := y / q ^ vy
  let rz := z / q ^ vz
  have hsplitx : q ^ vx * rx = x := by simpa [vx, rx] using (unitPart_mul (p := q) (n := x))
  have hsplity : q ^ vy * ry = y := by simpa [vy, ry] using (unitPart_mul (p := q) (n := y))
  have hsplitz : q ^ vz * rz = z := by simpa [vz, rz] using (unitPart_mul (p := q) (n := z))
  have hnZ : ¬ (q : ℤ) ∣ (n : ℤ) := mt Int.natCast_dvd_natCast.mp hqn
  have h1 : ¬ (q : ℤ) ∣ (rx : ℤ) :=
    mt Int.natCast_dvd_natCast.mp (by simpa [vx, rx] using unitPart_not_dvd (p := q) hx0)
  have h2 : ¬ (q : ℤ) ∣ (ry : ℤ) :=
    mt Int.natCast_dvd_natCast.mp (by simpa [vy, ry] using unitPart_not_dvd (p := q) hy0)
  have hL : 4 * (x * y * z) = 4 * (rx * ry * rz) * q ^ (vx + vy + vz) := by
    calc
      4 * (x * y * z)
          = 4 * ((q ^ vx * rx) * (q ^ vy * ry) * (q ^ vz * rz)) := by
            rw [hsplitx, hsplity, hsplitz]
      _ = 4 * (rx * ry * rz) * (q ^ vx * q ^ vy * q ^ vz) := by ring
      _ = 4 * (rx * ry * rz) * q ^ (vx + vy + vz) := by rw [pow_add_three]
  have hxyP : x * y = rx * ry * q ^ (vx + vy) := by
    calc
      x * y = (q ^ vx * rx) * (q ^ vy * ry) := by rw [hsplitx, hsplity]
      _ = rx * ry * (q ^ vx * q ^ vy) := by ring
      _ = rx * ry * q ^ (vx + vy) := by rw [Nat.pow_add]
  have hyzP : y * z = ry * rz * q ^ (vy + vz) := by
    calc
      y * z = (q ^ vy * ry) * (q ^ vz * rz) := by rw [hsplity, hsplitz]
      _ = ry * rz * (q ^ vy * q ^ vz) := by ring
      _ = ry * rz * q ^ (vy + vz) := by rw [Nat.pow_add]
  have hzxP : z * x = rz * rx * q ^ (vz + vx) := by
    calc
      z * x = (q ^ vz * rz) * (q ^ vx * rx) := by rw [hsplitz, hsplitx]
      _ = rz * rx * (q ^ vz * q ^ vx) := by ring
      _ = rz * rx * q ^ (vz + vx) := by rw [Nat.pow_add]
  have hR : n * (x * y + y * z + z * x) =
      n * (rx * ry * q ^ (vx + vy) + ry * rz * q ^ (vy + vz)
        + rz * rx * q ^ (vz + vx)) := by
    rw [hxyP, hyzP, hzxP]
  have heqN : 4 * (rx * ry * rz) * q ^ (vx + vy + vz) =
      n * (rx * ry * q ^ (vx + vy) + ry * rz * q ^ (vy + vz)
        + rz * rx * q ^ (vz + vx)) := by
    rw [← hL, heq, hR]
  have heqZ :
      4 * ((rx : ℤ) * ry * rz) * (q : ℤ) ^ (vx + vy + vz) =
        (n : ℤ) * ((rx : ℤ) * ry * (q : ℤ) ^ (vx + vy)
          + (ry : ℤ) * rz * (q : ℤ) ^ (vy + vz)
          + (rz : ℤ) * rx * (q : ℤ) ^ (vz + vx)) := by
    exact_mod_cast heqN
  have heq32 :
      4 * ((rx : ℤ) * ry * rz) * (q : ℤ) ^ (vx + vy + vz) =
        (n : ℤ) * ((rx : ℤ) * ry * (q : ℤ) ^ (vx + vy + 0))
        + (n : ℤ) * ((rx : ℤ) * rz * (q : ℤ) ^ (vx + vz + 0))
        + (n : ℤ) * ((ry : ℤ) * rz * (q : ℤ) ^ (vy + vz + 0)) := by
    convert heqZ using 1
    ring
  have hord' : vx ≤ vy ∧ vy ≤ vz := hord
  simpa [vx, vy, vz] using
    lemma32_of_prime q Fact.out (n : ℤ) (rx : ℤ) (ry : ℤ) (rz : ℤ)
      0 vx vy vz (by omega) hnZ h1 h2 hord' heq32

/-- **BL Lemma 3.2** on a Nat solution: some two coordinates have equal
    `q`-adic valuation, so their ratio is a `q`-adic unit. -/
theorem lemma35_exists_unit_ratio {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hqn : ¬ q ∣ n) :
    padicValNat q x = padicValNat q y ∨
    padicValNat q y = padicValNat q z ∨
    padicValNat q z = padicValNat q x := by
  rcases le_total (padicValNat q x) (padicValNat q y) with hxy | hyx
  · rcases le_total (padicValNat q y) (padicValNat q z) with hyz | hzy
    · exact (lemma32_sorted hES hqn ⟨hxy, hyz⟩).imp_right Or.inl
    · rcases le_total (padicValNat q x) (padicValNat q z) with hxz | hzx
      · -- vx ≤ vz ≤ vy
        have h := lemma32_sorted (isES_swap_yz hES) hqn ⟨hxz, hzy⟩
        rcases h with h | h
        · exact Or.inr (Or.inr h.symm)
        · exact Or.inr (Or.inl h.symm)
      · -- vz ≤ vx ≤ vy
        have h := lemma32_sorted
          (isES_swap_xy (isES_swap_yz hES)) hqn ⟨hzx, hxy⟩
        rcases h with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
  · rcases le_total (padicValNat q z) (padicValNat q x) with hzx | hxz
    · rcases le_total (padicValNat q y) (padicValNat q z) with hyz | hzy
      · -- vy ≤ vz ≤ vx
        have h := lemma32_sorted
          (isES_swap_yz (isES_swap_xy hES)) hqn ⟨hyz, hzx⟩
        rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · -- vz ≤ vy ≤ vx
        have h := lemma32_sorted
          (isES_swap_yz (isES_swap_xy (isES_swap_yz hES))) hqn ⟨hzy, hyx⟩
        rcases h with h | h
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inl h.symm
    · -- vy ≤ vx ≤ vz  (since ¬ vz ≤ vx, i.e. vx ≤ vz, and vy ≤ vx)
      have h := lemma32_sorted (isES_swap_xy hES) hqn ⟨hyx, hxz⟩
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h.symm)

/-- Serre's odd-place formula (BL Lemma 3.4) on a Nat point with
    `v_q(y) = v_q(z)`, so `y/z` is a `q`-adic unit. -/
def lemma35InvAt (q x y z : Nat) [Fact q.Prime] : ℤ :=
  legendreSym q
      (-((y / q ^ padicValNat q y : Nat) : ℤ) *
        ((z / q ^ padicValNat q z : Nat) : ℤ)) ^
    ((padicValNat q x + padicValNat q z) % 2)

lemma lemma35_v_left {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hq2 : q ≠ 2) :
    padicValNat q (4 * (x * y * z)) =
      padicValNat q x + padicValNat q y + padicValNat q z := by
  have ⟨hx, hy, hz, _⟩ := hES
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hy0 : y ≠ 0 := Nat.ne_of_gt hy
  have hz0 : z ≠ 0 := Nat.ne_of_gt hz
  have h4 : padicValNat q 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by
      intro h
      have : q ∣ 2 * 2 := h
      rcases (Nat.Prime.dvd_mul Fact.out).mp this with h | h
      · exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
      · exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h))
  have hxyz : x * y * z ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero hx0 hy0) hz0
  rw [padicValNat.mul (by decide : (4 : Nat) ≠ 0) hxyz, h4, zero_add,
    padicValNat.mul (Nat.mul_ne_zero hx0 hy0) hz0,
    padicValNat.mul hx0 hy0]

lemma lemma35_v_right {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hqn : ¬ q ∣ n) :
    padicValNat q (n * (x * y + y * z + z * x)) =
      padicValNat q (x * y + y * z + z * x) := by
  have ⟨hx, hy, hz, heq⟩ := hES
  have hn0 : n ≠ 0 := Nat.ne_of_gt (es_n_pos hES)
  have hsum0 : x * y + y * z + z * x ≠ 0 := by
    have : 0 < x * y := Nat.mul_pos hx hy
    omega
  rw [padicValNat.mul hn0 hsum0, padicValNat.eq_zero_of_not_dvd hqn, zero_add]

/-- **BL Lemma 3.5**, evaluation: if `y/z` is a unit then the invariant is 1.
    Equal valuations make the Lemma 3.4 exponent even; unequal valuations
    force `-y/z ≡ 1 (mod q)` from the ES equation. -/
theorem lemma35_inv_one {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hq2 : q ≠ 2) (hqn : ¬ q ∣ n)
    (hunit : padicValNat q y = padicValNat q z) :
    lemma35InvAt (q := q) x y z = 1 := by
  have ⟨hx, hy, hz, heq⟩ := hES
  have hx0 : x ≠ 0 := Nat.ne_of_gt hx
  have hy0 : y ≠ 0 := Nat.ne_of_gt hy
  have hz0 : z ≠ 0 := Nat.ne_of_gt hz
  have hxy0 : x * y ≠ 0 := Nat.mul_ne_zero hx0 hy0
  have hyz0 : y * z ≠ 0 := Nat.mul_ne_zero hy0 hz0
  have hzx0 : z * x ≠ 0 := Nat.mul_ne_zero hz0 hx0
  have hvL := lemma35_v_left hES hq2
  have hvR := lemma35_v_right hES hqn
  have hveq : padicValNat q (4 * (x * y * z)) =
      padicValNat q (x * y + y * z + z * x) := by
    have : 4 * (x * y * z) = n * (x * y + y * z + z * x) := heq
    rw [this, hvR]
  rw [hvL] at hveq
  let vx := padicValNat q x
  let vy := padicValNat q y
  let vz := padicValNat q z
  let ry := y / q ^ vy
  let rz := z / q ^ vz
  have hsplity : q ^ vy * ry = y := by simpa [vy, ry] using (unitPart_mul (p := q) (n := y))
  have hsplitz : q ^ vz * rz = z := by simpa [vz, rz] using (unitPart_mul (p := q) (n := z))
  have hry : ¬ q ∣ ry := by simpa [vy, ry] using unitPart_not_dvd (p := q) hy0
  have hrz : ¬ q ∣ rz := by simpa [vz, rz] using unitPart_not_dvd (p := q) hz0
  have hyzeq : vy = vz := hunit
  by_cases heqval : vx = vz
  · have heven : (padicValNat q x + padicValNat q z) % 2 = 0 := by
      simpa [vx, vz] using (by omega : (vx + vz) % 2 = 0)
    simp only [lemma35InvAt, heven, pow_zero]
  · have hvxlt : vx < vz := by
      by_contra hnot
      have hlt : vz < vx :=
        (lt_or_eq_of_le (Nat.le_of_not_gt hnot)).resolve_right (Ne.symm heqval)
      have hvxy : padicValNat q (x * y) = vx + vy := padicValNat.mul hx0 hy0
      have hvyz : padicValNat q (y * z) = vy + vz := padicValNat.mul hy0 hz0
      have hvzx : padicValNat q (z * x) = vz + vx := padicValNat.mul hz0 hx0
      have hxy_gt : padicValNat q (y * z) < padicValNat q (x * y) := by
        rw [hvyz, hvxy]; omega
      have hzx_gt : padicValNat q (y * z) < padicValNat q (z * x) := by
        rw [hvyz, hvzx]; omega
      have hsumxz_ne : x * y + z * x ≠ 0 :=
        Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero hxy0) _)
      have hge : padicValNat q (y * z) < padicValNat q (x * y + z * x) :=
        lt_of_lt_of_le (lt_min hxy_gt hzx_gt)
          (by
            have := padicValNat_add_ge_min (p := q) hxy0 hzx0
            simpa [add_comm] using this)
      have hsum : padicValNat q (x * y + y * z + z * x) = padicValNat q (y * z) := by
        have hre : x * y + y * z + z * x = y * z + (x * y + z * x) := by ring
        rw [hre, padicValNat_add_of_lt (p := q) hyz0 hsumxz_ne hge]
      have : vx + vy + vz = vy + vz := by
        rw [hveq, hsum, padicValNat.mul hy0 hz0]
      omega
    have hsplityz : y + z = q ^ vz * (ry + rz) := by
      calc
        y + z = q ^ vy * ry + q ^ vz * rz := by rw [hsplity, hsplitz]
        _ = q ^ vz * ry + q ^ vz * rz := by rw [hyzeq]
        _ = q ^ vz * (ry + rz) := by ring
    have hdiv : q ∣ ry + rz := by
      by_contra hnd
      have hvyzsum : padicValNat q (y + z) = vz := by
        have hne : ry + rz ≠ 0 := by
          intro h0
          have : q ∣ ry + rz := by rw [h0]; exact Nat.dvd_zero _
          exact hnd this
        have hq0 : q ≠ 0 := Nat.ne_of_gt (Nat.Prime.pos Fact.out)
        have hmul := padicValNat.mul (p := q) (pow_ne_zero vz hq0) hne
        have hvpow : padicValNat q (q ^ vz) = vz := padicValNat.prime_pow _
        have hvunit : padicValNat q (ry + rz) = 0 := padicValNat.eq_zero_of_not_dvd hnd
        rw [hsplityz, hmul, hvpow, hvunit, add_zero]
      have hvxsum : padicValNat q (x * (y + z)) = vx + vz := by
        have hys : y + z ≠ 0 := Nat.ne_of_gt (Nat.add_pos_left hy _)
        rw [padicValNat.mul hx0 hys, hvyzsum]
      have hvyz : padicValNat q (y * z) = vy + vz := padicValNat.mul hy0 hz0
      have hlt' : padicValNat q (x * (y + z)) < padicValNat q (y * z) := by
        rw [hvxsum, hvyz]; omega
      have hre : x * y + y * z + z * x = x * (y + z) + y * z := by ring
      have hsum : padicValNat q (x * y + y * z + z * x) = vx + vz := by
        have hxz : x * (y + z) ≠ 0 :=
          Nat.mul_ne_zero hx0 (Nat.ne_of_gt (Nat.add_pos_left hy _))
        rw [hre, padicValNat_add_of_lt (p := q) hxz hyz0 hlt', hvxsum]
      have : vx + vy + vz = vx + vz := by
        rw [hveq, hsum]
      omega
    have hcast : ((-(ry : ℤ) * (rz : ℤ) : ℤ) : ZMod q) =
        (rz : ZMod q) * (rz : ZMod q) := by
      have hadd : ((ry + rz : Nat) : ZMod q) = 0 :=
        (ZMod.natCast_eq_zero_iff (ry + rz) q).2 hdiv
      have hneg : (ry : ZMod q) = -(rz : ZMod q) :=
        eq_neg_of_add_eq_zero_left (by simpa using hadd)
      push_cast
      rw [hneg]
      ring
    have hr0 : (rz : ZMod q) ≠ 0 := by
      intro hz
      exact hrz ((ZMod.natCast_eq_zero_iff rz q).1 hz)
    have harg : ((-(ry : ℤ) * (rz : ℤ) : ℤ) : ZMod q) ≠ 0 := by
      rw [hcast]
      exact mul_ne_zero hr0 hr0
    have hleg : legendreSym q (-(ry : ℤ) * rz) = 1 :=
      (legendreSym.eq_one_iff (p := q) harg).2 ⟨(rz : ZMod q), by rw [hcast]⟩
    have hform : lemma35InvAt (q := q) x y z =
        legendreSym q (-(ry : ℤ) * rz) ^ ((vx + vz) % 2) := by
      simp only [lemma35InvAt, vx, vz, ry, rz, vy]
    rw [hform, hleg, one_pow]

/-- **BL Lemma 3.5** on a Nat solution: at a good odd prime a unit ratio
    exists, and Serre's formula on any such ratio is 1. -/
theorem lemma35 {q n x y z : Nat} [Fact q.Prime]
    (hES : IsES n x y z) (hq2 : q ≠ 2) (hqn : ¬ q ∣ n) :
    (padicValNat q x = padicValNat q y ∨
      padicValNat q y = padicValNat q z ∨
      padicValNat q z = padicValNat q x) ∧
    (padicValNat q y = padicValNat q z → lemma35InvAt (q := q) x y z = 1) ∧
    (padicValNat q z = padicValNat q x → lemma35InvAt (q := q) y z x = 1) ∧
    (padicValNat q x = padicValNat q y → lemma35InvAt (q := q) z x y = 1) :=
  ⟨lemma35_exists_unit_ratio hES hqn,
    fun h => lemma35_inv_one hES hq2 hqn h,
    fun h => lemma35_inv_one (isES_swap_yz (isES_swap_xy hES)) hq2 hqn h,
    fun h => lemma35_inv_one (isES_swap_xy (isES_swap_yz hES)) hq2 hqn h⟩

/-- Existence of a quadratic non-residue mod an odd prime. -/
theorem exists_legendre_neg (q : Nat) [Fact q.Prime] (hq2 : q ≠ 2) :
    ∃ a : ℤ, legendreSym q a = -1 := by
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod q) hchar
  refine ⟨a.val, ?_⟩
  have hcast : ((a.val : ℤ) : ZMod q) = a := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [legendreSym.eq_neg_one_iff, hcast]
  exact ha

/-- **BL Lemma 3.6**, residue form. Both values of `(-u₂/u₃ / p)` occur
    among units of `𝔽_p` (take `u₃ = 1` and vary `u₂`). -/
theorem lemma36_residues {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ u2 : ℤ, ((u2 : ZMod p) ≠ 0) ∧ legendreSym p (-u2) = ε := by
  rcases hε with rfl | rfl
  · refine ⟨-1, ?_, ?_⟩
    · intro h
      have hneg : ((-1 : ℤ) : ZMod p) = 0 := h
      rw [Int.cast_neg, neg_eq_zero] at hneg
      have hdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).1 (by simpa using hneg)
      exact Nat.Prime.ne_one Fact.out (Nat.dvd_one.mp hdvd)
    · have hone : ((1 : ℤ) : ZMod p) ≠ 0 := by
        intro hz
        have hdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).1 (by simpa using hz)
        exact Nat.Prime.ne_one Fact.out (Nat.dvd_one.mp hdvd)
      have : legendreSym p (1 : ℤ) = 1 :=
        (legendreSym.eq_one_iff (p := p) hone).2 ⟨(1 : ZMod p), by simp⟩
      simpa [neg_neg]
  · obtain ⟨a, ha⟩ := exists_legendre_neg p hp2
    refine ⟨-a, ?_, ?_⟩
    · intro h
      have ha0 : (a : ZMod p) = 0 := by
        have : ((-a : ℤ) : ZMod p) = 0 := h
        rw [Int.cast_neg] at this
        exact neg_eq_zero.mp this
      have : ¬ IsSquare (a : ZMod p) := (legendreSym.eq_neg_one_iff (p := p)).1 ha
      exact this ⟨0, by simp [ha0]⟩
    · simpa [neg_neg]

/-! ## BL Lemma 3.6: Hensel lift to `ℤ_p`

For `p ‖ n` write `n = p n'` and `u₁ = p a₁`.  The ES equation reduces
mod `p` to the three planes `(4a₁ - n') u₂ u₃ ≡ 0`.  On the plane
`4a₁ ≡ n'` with `u₂ u₃` units the `a₁`-derivative is `4 u₂ u₃ ≢ 0`,
so Hensel lifts the residue to a `ℤ_p`-point.  Both Legendre values of
`(-u₂/u₃ / p)` occur (Lemma 3.6 residue form); Lemma 3.4 then makes
`inv_p` surjective.  The general case `v_p(n) ≥ 1` is a rescaling. -/

lemma odd_prime_not_dvd_four {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ p ∣ 4 := by
  intro h
  have : p ∣ 2 * 2 := h
  rcases (Nat.Prime.dvd_mul Fact.out).mp this with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)

lemma four_ne_zero_mod {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2) :
    (4 : ZMod p) ≠ 0 := by
  intro h
  exact odd_prime_not_dvd_four hp2 ((ZMod.natCast_eq_zero_iff 4 p).1 (by simpa using h))

lemma zmod_ne_zero_iff_not_dvd (p : Nat) [Fact p.Prime] (z : ℤ) :
    ((z : ZMod p) ≠ 0) ↔ ¬ (p : ℤ) ∣ z := by
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma exists_a1_plane {p n' : Nat} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ a1 : ℤ, (p : ℤ) ∣ 4 * a1 - n' := by
  have h4 : (4 : ZMod p) ≠ 0 := four_ne_zero_mod hp2
  set r : ZMod p := (4 : ZMod p)⁻¹ * (n' : ZMod p)
  refine ⟨(r.val : ℤ), ?_⟩
  have hcast : ((4 * (r.val : ℤ) - (n' : ℤ) : ℤ) : ZMod p) =
      (4 : ZMod p) * r - (n' : ZMod p) := by
    trans (4 : ZMod p) * (r.val : ZMod p) - (n' : ZMod p)
    · simp
    · rw [ZMod.natCast_zmod_val]
  have h0 : (4 : ZMod p) * r - (n' : ZMod p) = 0 := by
    simp only [r]
    field_simp [h4]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (hcast.trans h0)

/-- Residue data of BL (3.3): `4a₁ ≡ n' (mod p)`, units `u₂, u₃`, and
    a prescribed value of `(-u₂/u₃ / p)`. -/
theorem lemma36_residue_plane {p n' : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (_hn' : ¬ p ∣ n') (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ a1 u2 u3 : ℤ,
      ¬ (p : ℤ) ∣ u2 ∧ ¬ (p : ℤ) ∣ u3 ∧ u3 = 1 ∧
      (p : ℤ) ∣ 4 * a1 - n' ∧
      legendreSym p (-u2) = ε := by
  obtain ⟨a1, ha1⟩ := exists_a1_plane (p := p) (n' := n') hp2
  obtain ⟨u2, hu2, hleg⟩ := lemma36_residues (p := p) hp2 ε hε
  refine ⟨a1, u2, 1, (zmod_ne_zero_iff_not_dvd p u2).1 hu2, ?_, rfl, ha1, hleg⟩
  intro h
  have hdvd : p ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using h)
  exact Nat.Prime.ne_one Fact.out (Nat.dvd_one.mp hdvd)

/-- Linear polynomial in `a₁` obtained by fixing unit residues `u₂, u₃`. -/
def lemma36Coeff (p n' : Nat) (u2 u3 : ℤ) : ℤ :=
  4 * u2 * u3 - (n' * p : ℤ) * (u2 + u3)

lemma lemma36_coeff_eval (p n' : Nat) (u2 u3 a1 : ℤ) :
    lemma36Coeff p n' u2 u3 * a1 - (n' : ℤ) * u2 * u3 =
      4 * a1 * u2 * u3 - (n' : ℤ) * (p * a1 * u2 + p * a1 * u3 + u2 * u3) := by
  simp [lemma36Coeff]
  ring

lemma lemma36_eval_dvd_of_plane {p n' : Nat} [Fact p.Prime]
    {a1 u2 u3 : ℤ} (hplane : (p : ℤ) ∣ 4 * a1 - n') :
    (p : ℤ) ∣ lemma36Coeff p n' u2 u3 * a1 - (n' : ℤ) * u2 * u3 := by
  rw [lemma36_coeff_eval]
  have hrewrite :
      4 * a1 * u2 * u3 - (n' : ℤ) * (p * a1 * u2 + p * a1 * u3 + u2 * u3) =
        (4 * a1 - n') * (u2 * u3) - (n' : ℤ) * p * a1 * (u2 + u3) := by ring
  rw [hrewrite]
  exact Int.dvd_sub (hplane.mul_right (u2 * u3))
    ⟨(n' : ℤ) * a1 * (u2 + u3), by ring⟩

lemma lemma36_coeff_unit {p n' : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    {u2 u3 : ℤ} (hu2 : ¬ (p : ℤ) ∣ u2) (hu3 : ¬ (p : ℤ) ∣ u3) :
    ¬ (p : ℤ) ∣ lemma36Coeff p n' u2 u3 := by
  intro h
  have hP : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hpterm : (p : ℤ) ∣ (n' * p : ℤ) * (u2 + u3) :=
    dvd_mul_of_dvd_left ⟨(n' : ℤ), by ring⟩ _
  have h4 : (p : ℤ) ∣ 4 * u2 * u3 := by
    have : lemma36Coeff p n' u2 u3 + (n' * p : ℤ) * (u2 + u3) = 4 * u2 * u3 := by
      unfold lemma36Coeff
      ring
    rw [← this]
    exact dvd_add h hpterm
  have h4u : (p : ℤ) ∣ 4 * u2 :=
    (hP.dvd_or_dvd h4).elim id (fun h3 => False.elim (hu3 h3))
  have h4' : (p : ℤ) ∣ (4 : ℤ) :=
    (hP.dvd_or_dvd h4u).elim id (fun h2 => False.elim (hu2 h2))
  have : p ∣ 4 := Int.natCast_dvd_natCast.mp (by simpa using h4')
  exact odd_prime_not_dvd_four hp2 this

/-- The ES equation over `ℤ_p`. -/
def IsESPadic {p : Nat} [Fact p.Prime] (n : Nat) (u1 u2 u3 : ℤ_[p]) : Prop :=
  4 * u1 * u2 * u3 = (n : ℤ_[p]) * (u1 * u2 + u2 * u3 + u3 * u1)

/-- Scaling all three coordinates by `m` scales the denominator `n` by `m`. -/
lemma isESPadic_scale_n {p : Nat} [Fact p.Prime] {n : Nat} {u1 u2 u3 : ℤ_[p]}
    (h : IsESPadic n u1 u2 u3) (m : Nat) :
    IsESPadic (m * n) ((m : ℤ_[p]) * u1) ((m : ℤ_[p]) * u2) ((m : ℤ_[p]) * u3) := by
  unfold IsESPadic at h ⊢
  calc
    4 * ((m : ℤ_[p]) * u1) * ((m : ℤ_[p]) * u2) * ((m : ℤ_[p]) * u3)
        = (m : ℤ_[p]) * (m : ℤ_[p]) * (m : ℤ_[p]) * (4 * u1 * u2 * u3) := by ring
    _ = (m : ℤ_[p]) * (m : ℤ_[p]) * (m : ℤ_[p]) *
          ((n : ℤ_[p]) * (u1 * u2 + u2 * u3 + u3 * u1)) := by rw [h]
    _ = ((m * n : Nat) : ℤ_[p]) *
          (((m : ℤ_[p]) * u1) * ((m : ℤ_[p]) * u2)
            + ((m : ℤ_[p]) * u2) * ((m : ℤ_[p]) * u3)
            + ((m : ℤ_[p]) * u3) * ((m : ℤ_[p]) * u1)) := by
        push_cast; ring

section Lemma36Hensel
open Polynomial

noncomputable def lemma36PolyZp {p : Nat} [Fact p.Prime] (n' : Nat) (u2 u3 : ℤ) :
    Polynomial ℤ_[p] :=
  C (lemma36Coeff p n' u2 u3 : ℤ_[p]) * X
    - C ((n' : ℤ) * u2 * u3 : ℤ_[p])

lemma lemma36PolyZp_eval {p : Nat} [Fact p.Prime] (n' : Nat) (u2 u3 : ℤ)
    (a : ℤ_[p]) :
    (lemma36PolyZp (p := p) n' u2 u3).aeval a =
      (lemma36Coeff p n' u2 u3 : ℤ_[p]) * a
        - ((n' : ℤ) * u2 * u3 : ℤ_[p]) := by
  simp [lemma36PolyZp, aeval_sub, aeval_mul, aeval_X]

lemma lemma36PolyZp_deriv {p : Nat} [Fact p.Prime] (n' : Nat) (u2 u3 : ℤ)
    (a : ℤ_[p]) :
    (lemma36PolyZp (p := p) n' u2 u3).derivative.aeval a =
      (lemma36Coeff p n' u2 u3 : ℤ_[p]) := by
  simp [lemma36PolyZp, derivative_sub, derivative_mul, derivative_X]

lemma lemma36_aeval_of_int {p : Nat} [Fact p.Prime] (n' : Nat) (u2 u3 a1 : ℤ) :
    (lemma36PolyZp (p := p) n' u2 u3).aeval (a1 : ℤ_[p]) =
      ((lemma36Coeff p n' u2 u3 * a1 - (n' : ℤ) * u2 * u3 : ℤ) : ℤ_[p]) := by
  rw [lemma36PolyZp_eval]
  push_cast
  ring

lemma padicInt_norm_eq_one_of_not_dvd {p : Nat} [Fact p.Prime] {z : ℤ}
    (h : ¬ (p : ℤ) ∣ z) : ‖(z : ℤ_[p])‖ = 1 := by
  have hlt : ¬ ‖(z : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_intCast_lt_one_iff]
    exact h
  have hle : 1 ≤ ‖(z : ℤ_[p])‖ := le_of_not_gt hlt
  exact PadicInt.one_le_norm_iff.mp hle

/-- **BL Lemma 3.6**, exact-divides case `p ‖ n`. Both Legendre values of
    `(-u₂/u₃ / p)` occur on `ℤ_p`-points with `p ‖ u₁` and `p ∤ u₂ u₃`. -/
theorem lemma36_hensel {p n' : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn' : ¬ p ∣ n') (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ (a1 : ℤ_[p]) (u2 u3 : ℤ),
      IsESPadic (p * n') ((p : ℤ_[p]) * a1) (u2 : ℤ_[p]) (u3 : ℤ_[p]) ∧
      ¬ (p : ℤ) ∣ u2 ∧ ¬ (p : ℤ) ∣ u3 ∧ u3 = 1 ∧
      IsUnit a1 ∧
      legendreSym p (-u2) = ε := by
  obtain ⟨a1₀, u2, u3, hu2, hu3, hu3one, hplane, hleg⟩ :=
    lemma36_residue_plane (p := p) (n' := n') hp2 hn' ε hε
  set F := lemma36PolyZp (p := p) n' u2 u3
  set a : ℤ_[p] := (a1₀ : ℤ_[p])
  have hF : ‖F.aeval a‖ < 1 := by
    rw [lemma36_aeval_of_int, PadicInt.norm_intCast_lt_one_iff]
    exact lemma36_eval_dvd_of_plane hplane
  have hder : ‖F.derivative.aeval a‖ = 1 := by
    rw [lemma36PolyZp_deriv]
    exact padicInt_norm_eq_one_of_not_dvd (lemma36_coeff_unit hp2 hu2 hu3)
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hder]
    simpa using hF
  obtain ⟨z, hz0, hdist, _, _⟩ := hensels_lemma hnorm
  have ha1_not : ¬ (p : ℤ) ∣ a1₀ := by
    intro h
    have h4a : (p : ℤ) ∣ 4 * a1₀ := dvd_mul_of_dvd_right h 4
    have : (p : ℤ) ∣ (n' : ℤ) := by
      have hsub := Int.dvd_sub h4a hplane
      convert hsub using 1
      ring
    exact hn' (Int.natCast_dvd_natCast.mp (by simpa using this))
  have ha_unit : ‖a‖ = 1 := padicInt_norm_eq_one_of_not_dvd ha1_not
  have hz_unit : IsUnit z := by
    rw [PadicInt.isUnit_iff]
    have hza : ‖z - a‖ < 1 := by
      rwa [hder] at hdist
    have hne : ‖z - a‖ ≠ ‖a‖ := ne_of_lt (hza.trans_eq ha_unit.symm)
    have hz : z = (z - a) + a := (sub_add_cancel z a).symm
    rw [hz, PadicInt.norm_add_eq_max_of_ne hne, ha_unit, max_eq_right (le_of_lt hza)]
  have hroot : (lemma36Coeff p n' u2 u3 : ℤ_[p]) * z =
      ((n' : ℤ) * u2 * u3 : ℤ_[p]) := by
    have h := lemma36PolyZp_eval (p := p) n' u2 u3 z
    exact sub_eq_zero.mp (h.symm.trans hz0)
  have hES : IsESPadic (p * n') ((p : ℤ_[p]) * z) (u2 : ℤ_[p]) (u3 : ℤ_[p]) := by
    unfold IsESPadic
    have hc : (lemma36Coeff p n' u2 u3 : ℤ_[p]) =
        (4 : ℤ_[p]) * u2 * u3
          - (n' : ℤ_[p]) * (p : ℤ_[p]) * ((u2 : ℤ_[p]) + u3) := by
      simp only [lemma36Coeff]
      push_cast
      ring
    have hexp :
        ((4 : ℤ_[p]) * (u2 : ℤ_[p]) * (u3 : ℤ_[p])
          - (n' : ℤ_[p]) * (p : ℤ_[p]) * ((u2 : ℤ_[p]) + u3)) * z
        = (n' : ℤ_[p]) * (u2 : ℤ_[p]) * (u3 : ℤ_[p]) := by
      rw [← hc]; exact hroot
    have hexp' :
        (4 : ℤ_[p]) * z * (u2 : ℤ_[p]) * (u3 : ℤ_[p])
          = (n' : ℤ_[p]) *
              ((p : ℤ_[p]) * z * u2 + (p : ℤ_[p]) * z * u3
                + (u2 : ℤ_[p]) * u3) := by
      rw [sub_mul, sub_eq_iff_eq_add] at hexp
      calc
        (4 : ℤ_[p]) * z * (u2 : ℤ_[p]) * (u3 : ℤ_[p])
            = (4 : ℤ_[p]) * (u2 : ℤ_[p]) * (u3 : ℤ_[p]) * z := by ring
        _ = (n' : ℤ_[p]) * (u2 : ℤ_[p]) * (u3 : ℤ_[p])
              + (n' : ℤ_[p]) * (p : ℤ_[p]) * ((u2 : ℤ_[p]) + u3) * z := hexp
        _ = (n' : ℤ_[p]) *
              ((p : ℤ_[p]) * z * u2 + (p : ℤ_[p]) * z * u3
                + (u2 : ℤ_[p]) * u3) := by ring
    calc
      4 * ((p : ℤ_[p]) * z) * (u2 : ℤ_[p]) * (u3 : ℤ_[p])
          = (p : ℤ_[p]) * (4 * z * u2 * u3) := by ring
      _ = (p : ℤ_[p]) * ((n' : ℤ_[p]) *
            ((p : ℤ_[p]) * z * u2 + (p : ℤ_[p]) * z * u3 + u2 * u3)) := by
            rw [hexp']
      _ = ((p * n' : Nat) : ℤ_[p]) *
            (((p : ℤ_[p]) * z) * u2 + (u2 : ℤ_[p]) * u3
              + (u3 : ℤ_[p]) * ((p : ℤ_[p]) * z)) := by
            push_cast; ring
  refine ⟨z, u2, u3, hES, hu2, hu3, hu3one, hz_unit, hleg⟩

/-- **BL Lemma 3.6.** For an odd prime `p | n`, both values of the p-adic
    invariant occur on `ℤ_p`-points.  After rescaling to the exact-divides
    model, Lemma 3.4 evaluates the invariant as `(-u₂/u₃ / p)`. -/
theorem lemma36 {p n : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn0 : n ≠ 0) (hpn : p ∣ n) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ u1 u2 u3 : ℤ_[p],
      IsESPadic n u1 u2 u3 ∧
      ∃ u2₀ : ℤ, ¬ (p : ℤ) ∣ u2₀ ∧ legendreSym p (-u2₀) = ε := by
  have hb : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn0 hpn
  set b := padicValNat p n
  set n' := n / p ^ b
  have hnp : n = p ^ b * n' := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hn'p : ¬ p ∣ n' := by
    intro h
    have : p ^ (b + 1) ∣ n := by
      rw [hnp, Nat.pow_succ]
      exact Nat.mul_dvd_mul_left _ h
    exact pow_succ_padicValNat_not_dvd hn0 this
  obtain ⟨a1, u2, u3, hES, hu2, _hu3, _hu3one, _hunit, hleg⟩ :=
    lemma36_hensel (p := p) (n' := n') hp2 hn'p ε hε
  have hsplit : n = p ^ (b - 1) * (p * n') := by
    have : p ^ b = p ^ (b - 1) * p := by
      refine (congrArg (fun k => p ^ k) (Nat.sub_add_cancel hb).symm).trans ?_
      rw [Nat.pow_add, Nat.pow_one]
    rw [hnp, this]
    ring
  refine ⟨((p ^ (b - 1) : Nat) : ℤ_[p]) * ((p : ℤ_[p]) * a1),
    ((p ^ (b - 1) : Nat) : ℤ_[p]) * u2, ((p ^ (b - 1) : Nat) : ℤ_[p]) * u3,
    ?_, u2, hu2, hleg⟩
  have hES' := isESPadic_scale_n hES (p ^ (b - 1))
  rwa [hsplit]

end Lemma36Hensel

/-- `(-1)^{k}` is `-1` iff `k` is odd. -/
lemma neg_one_pow_even_odd (k : Nat) :
    ((-1 : ℤ) ^ k = -1 ↔ k % 2 = 1) ∧ ((-1 : ℤ) ^ k = 1 ↔ k % 2 = 0) := by
  have := BL.sign_pow_parity (-1) (Or.inr rfl) k
  constructor
  · constructor
    · intro h
      have hm : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hm with hm | hm
      · rw [this, hm, Int.pow_zero] at h; exact absurd h (by decide)
      · exact hm
    · intro h; rw [this, h, Int.pow_one]
  · constructor
    · intro h
      have hm : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hm with hm | hm
      · exact hm
      · rw [this, hm, Int.pow_one] at h; exact absurd h (by decide)
    · intro h; rw [this, h, Int.pow_zero]

/-- For odd `n`, `n ≡ 3 (mod 4)` iff `n/2` is odd. -/
lemma odd_div2_mod2 {n : Nat} (hodd : n % 2 = 1) :
    (n / 2) % 2 = 1 ↔ n % 4 = 3 := by
  have hlt : n % 4 < 4 := Nat.mod_lt n (by omega)
  have h24 : (n % 4) % 2 = 1 := by
    have hmod : (n % 4) % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)
    rwa [hodd] at hmod
  have hn4 : n % 4 = 1 ∨ n % 4 = 3 := by
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases this with h | h | h | h
    · rw [h] at h24; cases h24
    · exact Or.inl h
    · rw [h] at h24; cases h24
    · exact Or.inr h
  rcases hn4 with h1 | h3
  · revert h1
    generalize hk : n / 4 = k
    intro h1
    have hdecomp : n = 4 * k + 1 := by
      have := Nat.div_add_mod n 4
      rw [hk, h1] at this
      exact this.symm
    have hdiv : n / 2 = 2 * k := by
      have hn : n = 2 * (2 * k) + 1 := by rw [hdecomp]; ring
      rw [hn, Nat.mul_add_div (by omega : (2 : Nat) > 0) (2 * k) 1]
      simp
    simp [hdiv, h1, Nat.mul_mod_right]
  · revert h3
    generalize hk : n / 4 = k
    intro h3
    have hdecomp : n = 4 * k + 3 := by
      have := Nat.div_add_mod n 4
      rw [hk, h3] at this
      exact this.symm
    have hdiv : n / 2 = 2 * k + 1 := by
      have hn : n = 2 * (2 * k + 1) + 1 := by rw [hdecomp]; ring
      rw [hn, Nat.mul_add_div (by omega : (2 : Nat) > 0) (2 * k + 1) 1]
    simp [hdiv, h3, Nat.add_mod, Nat.mul_mod_right]

lemma mul_mod2_odd (a b : Nat) :
    (a * b) % 2 = 1 ↔ a % 2 = 1 ∧ b % 2 = 1 := by
  rw [Nat.mul_mod]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-- For odd natural numbers, the 2-adic Hilbert symbol equals `(-1)^{a/2 · b/2}`. -/
theorem hilbert2Odd_eq_pow_odd {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    hilbert2Odd a b = (-1 : ℤ) ^ (a / 2 * (b / 2)) := by
  have hodd : (a / 2 * (b / 2)) % 2 = 1 ↔ a % 4 = 3 ∧ b % 4 = 3 := by
    rw [mul_mod2_odd, odd_div2_mod2 ha, odd_div2_mod2 hb]
  have haZ : (a : ℤ) % 4 = ↑(a % 4) := (Int.natCast_mod a 4).symm
  have hbZ : (b : ℤ) % 4 = ↑(b % 4) := (Int.natCast_mod b 4).symm
  simp only [hilbert2Odd, haZ, hbZ]
  by_cases h : a % 4 = 3 ∧ b % 4 = 3
  · have hpow : (a / 2 * (b / 2)) % 2 = 1 := hodd.mpr h
    have hif : ↑(a % 4) = (3 : ℤ) ∧ ↑(b % 4) = (3 : ℤ) := by exact_mod_cast h
    rw [if_pos hif, (neg_one_pow_even_odd _).1.2 hpow]
  · have hpow : (a / 2 * (b / 2)) % 2 = 0 := by
      have hm : (a / 2 * (b / 2)) % 2 = 0 ∨ (a / 2 * (b / 2)) % 2 = 1 :=
        Nat.mod_two_eq_zero_or_one _
      rcases hm with hm | hm
      · exact hm
      · exact False.elim (h (hodd.mp hm))
    have hif : ¬ (↑(a % 4) = (3 : ℤ) ∧ ↑(b % 4) = (3 : ℤ)) := by exact_mod_cast h
    rw [if_neg hif, (neg_one_pow_even_odd _).2.2 hpow]

/-- For odd primes, the 2-adic Hilbert symbol equals `(-1)^{p/2 · q/2}`. -/
theorem hilbert2Odd_eq_pow {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    hilbert2Odd p q = (-1 : ℤ) ^ (p / 2 * (q / 2)) :=
  hilbert2Odd_eq_pow_odd
    ((Nat.Prime.eq_two_or_odd Fact.out).resolve_left hp2)
    ((Nat.Prime.eq_two_or_odd Fact.out).resolve_left hq2)

/-- **Hilbert reciprocity for a pair of distinct odd primes**, discharged
    by Mathlib quadratic reciprocity.  This is the odd-place content of
    `InvariantData.reciprocity`: `(p,q)_p (p,q)_q (p,q)_2 (p,q)_∞ = 1`. -/
theorem hilbert_reciprocity_odd_primes {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hne : p ≠ q) :
    legendreSym q p * legendreSym p q *
      hilbert2Odd p q * hilbertInf p q = 1 := by
  have hInf : hilbertInf (p : ℤ) (q : ℤ) = 1 := by
    have hppos : (0 : ℤ) < p := by
      have : 2 ≤ p := Nat.Prime.two_le Fact.out
      omega
    have hqpos : (0 : ℤ) < q := by
      have : 2 ≤ q := Nat.Prime.two_le Fact.out
      omega
    simp [hilbertInf]
  have hQR := quadratic_reciprocity_odd hp2 hq2 hne
  have h2 := hilbert2Odd_eq_pow (p := p) (q := q) hp2 hq2
  rw [hInf, mul_one, h2]
  have hsq : ((-1 : ℤ) ^ (p / 2 * (q / 2))) *
      ((-1 : ℤ) ^ (p / 2 * (q / 2))) = 1 := by
    rw [← Int.pow_add]
    have heq : p / 2 * (q / 2) + p / 2 * (q / 2) = 2 * (p / 2 * (q / 2)) := by ring
    rw [heq, pow_mul, pow_two]
    simp
  calc
    legendreSym q p * legendreSym p q * ((-1 : ℤ) ^ (p / 2 * (q / 2)))
        = ((-1 : ℤ) ^ (p / 2 * (q / 2))) *
            ((-1 : ℤ) ^ (p / 2 * (q / 2))) := by rw [hQR]
    _ = 1 := hsq

lemma hilbertInf_nat (a b : Nat) : hilbertInf (a : ℤ) (b : ℤ) = 1 := by
  simp [hilbertInf]

lemma jacobiSym_sq_one {a : ℤ} {b : Nat} (h : a.gcd b = 1) :
    jacobiSym a b * jacobiSym a b = 1 := by
  rcases jacobiSym.eq_one_or_neg_one h with hJ | hJ <;> rw [hJ] <;> decide

/-- **Hilbert reciprocity for odd coprime positive integers.**  The product
    `(a,b)_a (a,b)_b (a,b)_2 (a,b)_∞` of explicit-formula symbols is 1,
    by Mathlib Jacobi quadratic reciprocity.  This is the odd-odd content
    of Hilbert's product formula on `ℚ`; signs, 2-powers, and common prime
    factors remain for a general pair of rationals. -/
theorem hilbert_reciprocity_odd_coprime {a b : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hcop : Nat.Coprime a b) :
    jacobiSym a b * jacobiSym b a * hilbert2Odd a b * hilbertInf a b = 1 := by
  have haO : Odd a := Nat.odd_iff.mpr ha
  have hbO : Odd b := Nat.odd_iff.mpr hb
  have hInf := hilbertInf_nat a b
  have h2 := hilbert2Odd_eq_pow_odd ha hb
  have hQR := jacobiSym.quadratic_reciprocity haO hbO
  have hgba : ((b : ℤ).gcd a = 1) := by
    simpa [Int.gcd_natCast_natCast, Nat.gcd_comm] using hcop.gcd_eq_one
  have hsq := jacobiSym_sq_one (a := (b : ℤ)) (b := a) hgba
  rw [hInf, mul_one, h2, hQR]
  calc
    ((-1 : ℤ) ^ (a / 2 * (b / 2)) * jacobiSym b a) * jacobiSym b a *
        ((-1 : ℤ) ^ (a / 2 * (b / 2)))
        = ((-1 : ℤ) ^ (a / 2 * (b / 2))) * ((-1 : ℤ) ^ (a / 2 * (b / 2))) *
            (jacobiSym b a * jacobiSym b a) := by ring
    _ = 1 := by
        rw [hsq]
        rw [← Int.pow_add]
        have heq : a / 2 * (b / 2) + a / 2 * (b / 2) = 2 * (a / 2 * (b / 2)) := by ring
        rw [heq, pow_mul, pow_two]
        simp

/-- Serre's explicit odd-prime Hilbert symbol of two natural numbers, using
    Mathlib's `legendreSym`.  For a pair of odd coprime integers this is the
    local factor of `jacobiSym`. -/
def hilbertSerre (p a b : Nat) [Fact p.Prime] : ℤ :=
  (if padicValNat p a % 2 = 1 ∧ padicValNat p b % 2 = 1 ∧ p % 4 = 3
    then -1 else 1) *
    (legendreSym p (a / p ^ padicValNat p a : Nat)) ^ padicValNat p b *
    (legendreSym p (b / p ^ padicValNat p b : Nat)) ^ padicValNat p a

theorem hilbertSerre_of_not_dvd_right {p a b : Nat} [Fact p.Prime]
    (hb : ¬ p ∣ b) :
    hilbertSerre p a b = (legendreSym p b) ^ padicValNat p a := by
  have hβ : padicValNat p b = 0 := padicValNat.eq_zero_of_not_dvd hb
  have hif : ¬ (padicValNat p a % 2 = 1 ∧ (0 : Nat) % 2 = 1 ∧ p % 4 = 3) := by omega
  simp only [hilbertSerre, hβ, pow_zero, mul_one]
  rw [if_neg hif, one_mul, Nat.div_one]

theorem hilbertSerre_of_not_dvd_left {p a b : Nat} [Fact p.Prime]
    (ha : ¬ p ∣ a) :
    hilbertSerre p a b = (legendreSym p a) ^ padicValNat p b := by
  have hα : padicValNat p a = 0 := padicValNat.eq_zero_of_not_dvd ha
  have hif : ¬ ((0 : Nat) % 2 = 1 ∧ padicValNat p b % 2 = 1 ∧ p % 4 = 3) := by omega
  simp only [hilbertSerre, hα, pow_zero]
  rw [if_neg hif, one_mul, Nat.div_one, mul_one]

theorem hilbertSerre_units {p a b : Nat} [Fact p.Prime]
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) :
    hilbertSerre p a b = 1 := by
  rw [hilbertSerre_of_not_dvd_right hb]
  have hα : padicValNat p a = 0 := padicValNat.eq_zero_of_not_dvd ha
  rw [hα, pow_zero]

/-- At an odd prime not dividing `b`, Serre's symbol is the Jacobi factor
    `J(b | p^{v_p(a)})`. -/
theorem hilbertSerre_eq_jacobi_pow {p a b : Nat} [Fact p.Prime]
    (hb : ¬ p ∣ b) :
    hilbertSerre p a b = jacobiSym b (p ^ padicValNat p a) := by
  rw [hilbertSerre_of_not_dvd_right hb, jacobiSym.pow_right,
    jacobiSym.legendreSym.to_jacobiSym]

/-- For coprime arguments, Serre's symbol at `p` is the Legendre contribution
    of whichever of `a,b` is divisible by `p` (and `1` if neither is). -/
theorem hilbertSerre_coprime {p a b : Nat} [Fact p.Prime]
    (hcop : Nat.Coprime a b) :
    hilbertSerre p a b =
      if p ∣ a then (legendreSym p b) ^ padicValNat p a
      else (legendreSym p a) ^ padicValNat p b := by
  by_cases ha : p ∣ a
  · have hb : ¬ p ∣ b := by
      intro hb
      have : p ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
      rw [hcop.gcd_eq_one] at this
      exact Nat.Prime.not_dvd_one Fact.out this
    rw [if_pos ha, hilbertSerre_of_not_dvd_right hb]
  · rw [if_neg ha, hilbertSerre_of_not_dvd_left ha]

lemma odd_mod4 {n : Nat} (h : n % 2 = 1) : n % 4 = 1 ∨ n % 4 = 3 := by
  have h24 : (n % 4) % 2 = 1 := by
    have : (n % 4) % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)
    rwa [h] at this
  have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases this with h0 | h1 | h2 | h3
  · rw [h0] at h24; cases h24
  · exact Or.inl h1
  · rw [h2] at h24; cases h24
  · exact Or.inr h3

lemma hilbert2Odd_mul_self (a b : ℤ) :
    hilbert2Odd a b * hilbert2Odd a b = 1 := by
  simp only [hilbert2Odd]
  split_ifs <;> decide

lemma nat_neg_mod4 {n : Nat} (h : n % 2 = 1) :
    (-(n : ℤ)) % 4 = 3 ∧ n % 4 = 1 ∨
    (-(n : ℤ)) % 4 = 1 ∧ n % 4 = 3 := by
  have hn : (n : ℤ) % 4 = ↑(n % 4) := (Int.natCast_mod n 4).symm
  rcases odd_mod4 h with h1 | h3
  · refine Or.inl ⟨?_, h1⟩
    have : (n : ℤ) % 4 = 1 := by rw [hn]; exact_mod_cast h1
    omega
  · refine Or.inr ⟨?_, h3⟩
    have : (n : ℤ) % 4 = 3 := by rw [hn]; exact_mod_cast h3
    omega

lemma hilbert2Odd_nat {a b : Nat} :
    hilbert2Odd (a : ℤ) (b : ℤ) =
      if a % 4 = 3 ∧ b % 4 = 3 then -1 else 1 := by
  simp only [hilbert2Odd]
  have haZ : (a : ℤ) % 4 = ↑(a % 4) := (Int.natCast_mod a 4).symm
  have hbZ : (b : ℤ) % 4 = ↑(b % 4) := (Int.natCast_mod b 4).symm
  rw [haZ, hbZ]
  by_cases h : a % 4 = 3 ∧ b % 4 = 3
  · have : ↑(a % 4) = (3 : ℤ) ∧ ↑(b % 4) = (3 : ℤ) := by exact_mod_cast h
    rw [if_pos this, if_pos h]
  · have : ¬ (↑(a % 4) = (3 : ℤ) ∧ ↑(b % 4) = (3 : ℤ)) := by exact_mod_cast h
    rw [if_neg this, if_neg h]

lemma hilbert2Odd_neg_nat {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) =
      if a % 4 = 1 ∧ b % 4 = 1 then -1 else 1 := by
  simp only [hilbert2Odd]
  by_cases h : a % 4 = 1 ∧ b % 4 = 1
  · have ha3 : (-(a : ℤ)) % 4 = 3 :=
      (nat_neg_mod4 ha).elim (fun h' => h'.1) (fun h' => False.elim (by omega))
    have hb3 : (-(b : ℤ)) % 4 = 3 :=
      (nat_neg_mod4 hb).elim (fun h' => h'.1) (fun h' => False.elim (by omega))
    rw [if_pos ⟨ha3, hb3⟩, if_pos h]
  · have : ¬ ((-(a : ℤ)) % 4 = 3 ∧ (-(b : ℤ)) % 4 = 3) := by
      intro ⟨ha3, hb3⟩
      have ha1 : a % 4 = 1 :=
        (nat_neg_mod4 ha).elim (fun h' => h'.2) (fun h' => False.elim (by omega))
      have hb1 : b % 4 = 1 :=
        (nat_neg_mod4 hb).elim (fun h' => h'.2) (fun h' => False.elim (by omega))
      exact h ⟨ha1, hb1⟩
    rw [if_neg this, if_neg h]

lemma chi4_mul_hilbert2_neg {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    χ₄ a * χ₄ b * hilbert2Odd a b * hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) = -1 := by
  rw [hilbert2Odd_nat, hilbert2Odd_neg_nat ha hb]
  rcases odd_mod4 ha with ha1 | ha3 <;> rcases odd_mod4 hb with hb1 | hb3
  · rw [χ₄_nat_one_mod_four ha1, χ₄_nat_one_mod_four hb1]
    simp [ha1, hb1]
  · rw [χ₄_nat_one_mod_four ha1, χ₄_nat_three_mod_four hb3]
    simp [ha1, hb3]
  · rw [χ₄_nat_three_mod_four ha3, χ₄_nat_one_mod_four hb1]
    simp [ha3, hb1]
  · rw [χ₄_nat_three_mod_four ha3, χ₄_nat_three_mod_four hb3]
    simp [ha3, hb3]

/-- **Hilbert reciprocity for a pair of negative odd coprime integers.**
    This is the ES local-symbol product on the odd parts of `-x/z`, `-y/z`
    (positive octant): `∏_v (-a,-b)_v = 1` with Serre/Jacobi at odd places,
    `hilbert2Odd` at 2, and `hilbertInf` at `ℝ`.  Remaining for a general
    pair of rationals are 2-powers in the arguments. -/
theorem hilbert_reciprocity_neg_odd_coprime {a b : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hcop : Nat.Coprime a b) :
    jacobiSym (-(a : ℤ)) b * jacobiSym (-(b : ℤ)) a *
      hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) *
      hilbertInf (-(a : ℤ)) (-(b : ℤ)) = 1 := by
  have haO : Odd a := Nat.odd_iff.mpr ha
  have hbO : Odd b := Nat.odd_iff.mpr hb
  have hapos : 0 < a := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hbpos : 0 < b := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hInf : hilbertInf (-(a : ℤ)) (-(b : ℤ)) = -1 := by
    simp [hilbertInf]; omega
  have hJa : jacobiSym (-(a : ℤ)) b =
      jacobiSym (-1) b * jacobiSym a b := by
    rw [show (-(a : ℤ) = (-1) * a) by ring, jacobiSym.mul_left]
  have hJb : jacobiSym (-(b : ℤ)) a =
      jacobiSym (-1) a * jacobiSym b a := by
    rw [show (-(b : ℤ) = (-1) * b) by ring, jacobiSym.mul_left]
  have hχa : jacobiSym (-1) a = χ₄ a := jacobiSym.at_neg_one haO
  have hχb : jacobiSym (-1) b = χ₄ b := jacobiSym.at_neg_one hbO
  have hpos := hilbert_reciprocity_odd_coprime ha hb hcop
  have hInfpos := hilbertInf_nat a b
  rw [hInfpos, mul_one] at hpos
  have hsq := hilbert2Odd_mul_self (a : ℤ) (b : ℤ)
  have hJ : jacobiSym a b * jacobiSym b a = hilbert2Odd a b := by
    calc
      jacobiSym a b * jacobiSym b a
          = jacobiSym a b * jacobiSym b a * 1 := by rw [mul_one]
      _ = jacobiSym a b * jacobiSym b a *
            (hilbert2Odd a b * hilbert2Odd a b) := by rw [hsq]
      _ = (jacobiSym a b * jacobiSym b a * hilbert2Odd a b) *
            hilbert2Odd a b := by ring
      _ = 1 * hilbert2Odd a b := by rw [hpos]
      _ = hilbert2Odd a b := one_mul _
  rw [hJa, hJb, hχa, hχb, hInf]
  calc
    (χ₄ b * jacobiSym a b) * (χ₄ a * jacobiSym b a) *
        hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) * (-1)
        = χ₄ a * χ₄ b * (jacobiSym a b * jacobiSym b a) *
            hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) * (-1) := by ring
    _ = χ₄ a * χ₄ b * hilbert2Odd a b *
            hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) * (-1) := by rw [hJ]
    _ = -1 * (-1) := by rw [chi4_mul_hilbert2_neg ha hb]
    _ = 1 := by ring

lemma chi8_sq_one {n : Nat} (h : n % 2 = 1) : χ₈ n * χ₈ n = 1 := by
  rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ n % 2 = 0)]
  split_ifs <;> decide

lemma chi8_pow_two {n : Nat} (h : n % 2 = 1) (k : Nat) :
    (χ₈ n : ℤ) ^ (2 * k) = 1 := by
  rw [pow_mul, pow_two, chi8_sq_one h, one_pow]

lemma chi8_pow_mul_self {n : Nat} (h : n % 2 = 1) (k : Nat) :
    (χ₈ n : ℤ) ^ k * χ₈ n ^ k = 1 := by
  rw [← pow_add, ← two_mul, chi8_pow_two h k]

lemma chi8_neg_zmod {n : Nat} (h : n % 2 = 1) :
    χ₈ (-(n : ZMod 8)) = χ₈ n := by
  have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  have hn : (n : ZMod 8) = ((n % 8 : ℕ) : ZMod 8) :=
    (ZMod.natCast_mod n 8).symm
  rw [hn]
  rcases h8 with h1 | h3 | h5 | h7
  · rw [h1]; decide
  · rw [h3]; decide
  · rw [h5]; decide
  · rw [h7]; decide

lemma chi8_neg {n : Nat} (h : n % 2 = 1) : χ₈ (-(n : ℤ)) = χ₈ n := by
  have harg : ((n : ℤ) : ZMod 8) = (n : ZMod 8) := Int.cast_natCast n
  refine (congrArg (χ₈ : ZMod 8 → ℤ) (congrArg Neg.neg harg)).trans ?_
  exact chi8_neg_zmod h

lemma jacobiSym_pow2 {s b : Nat} (hb : Odd b) :
    jacobiSym ((2 : ℤ) ^ s) b = χ₈ b ^ s := by
  rw [jacobiSym.pow_left, jacobiSym.at_two hb]

/-- 2-adic Hilbert symbol of `(2^s a, 2^t b)` for odd `a,b`:
    `(a,b)_2 · (2,b)_2^s · (2,a)_2^t`, with `(2,u)_2 = χ₈(u)`. -/
def hilbert2Pow (s t : Nat) (a b : ℤ) : ℤ :=
  hilbert2Odd a b * χ₈ b ^ s * χ₈ a ^ t

/-- Supplementary Hilbert reciprocity `(2,a)_odd (2,a)_2 (2,a)_∞ = 1`
    for odd `a`. -/
theorem hilbert_reciprocity_two_odd {a : Nat} (ha : a % 2 = 1) :
    jacobiSym (2 : ℤ) a * χ₈ a * hilbertInf (2 : ℤ) a = 1 := by
  have haO : Odd a := Nat.odd_iff.mpr ha
  have hapos : 0 < a := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hInf : hilbertInf (2 : ℤ) a = 1 := by simp [hilbertInf]
  rw [jacobiSym.at_two haO, hInf, mul_one, chi8_sq_one ha]

/-- **Hilbert reciprocity for `(2^s a, 2^t b)`** with `a,b` odd and coprime.
    The odd-place product is `J(2^s a | b) J(2^t b | a)`; the 2-adic symbol
    is `hilbert2Pow`.  This is the 2-power content of the ES ratios
    `-x/z`, `-y/z` after Lemma 3.8. -/
theorem hilbert_reciprocity_two_pow {a b s t : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hcop : Nat.Coprime a b) :
    jacobiSym ((2 : ℤ) ^ s * a) b * jacobiSym ((2 : ℤ) ^ t * b) a *
      hilbert2Pow s t a b * hilbertInf ((2 : ℤ) ^ s * a) ((2 : ℤ) ^ t * b) = 1 := by
  have haO : Odd a := Nat.odd_iff.mpr ha
  have hbO : Odd b := Nat.odd_iff.mpr hb
  have hapos : 0 < a := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hbpos : 0 < b := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hInf : hilbertInf ((2 : ℤ) ^ s * a) ((2 : ℤ) ^ t * b) = 1 := by
    simp [hilbertInf]
  have hJa : jacobiSym ((2 : ℤ) ^ s * a) b =
      χ₈ b ^ s * jacobiSym a b := by
    rw [jacobiSym.mul_left, jacobiSym_pow2 hbO]
  have hJb : jacobiSym ((2 : ℤ) ^ t * b) a =
      χ₈ a ^ t * jacobiSym b a := by
    rw [jacobiSym.mul_left, jacobiSym_pow2 haO]
  have hpos := hilbert_reciprocity_odd_coprime ha hb hcop
  have hInfpos := hilbertInf_nat a b
  rw [hInfpos, mul_one] at hpos
  rw [hJa, hJb, hInf]
  simp only [hilbert2Pow]
  calc
    (χ₈ b ^ s * jacobiSym a b) * (χ₈ a ^ t * jacobiSym b a) *
        (hilbert2Odd a b * χ₈ b ^ s * χ₈ a ^ t) * (1 : ℤ)
        = (jacobiSym a b * jacobiSym b a * hilbert2Odd a b) *
            (χ₈ a ^ t * χ₈ a ^ t) * (χ₈ b ^ s * χ₈ b ^ s) := by ring
    _ = 1 * 1 * 1 := by
        rw [hpos, chi8_pow_mul_self ha t, chi8_pow_mul_self hb s]
    _ = 1 := by ring

/-- **Hilbert reciprocity for a pair of negative 2-power times odd coprime
    integers.**  On the Lemma 3.8 shape, `-x/z` and `-y/z` have this form
    in the numerators (equal 2-valuation `s`).  Common odd factors in the
    denominator remain for a general pair of rationals. -/
theorem hilbert_reciprocity_neg_two_pow {a b s : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hcop : Nat.Coprime a b) :
    jacobiSym (-((2 : ℤ) ^ s * a)) b * jacobiSym (-((2 : ℤ) ^ s * b)) a *
      hilbert2Pow s s (-(a : ℤ)) (-(b : ℤ)) *
      hilbertInf (-((2 : ℤ) ^ s * a)) (-((2 : ℤ) ^ s * b)) = 1 := by
  have haO : Odd a := Nat.odd_iff.mpr ha
  have hbO : Odd b := Nat.odd_iff.mpr hb
  have hapos : 0 < a := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hbpos : 0 < b := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hInf : hilbertInf (-((2 : ℤ) ^ s * a)) (-((2 : ℤ) ^ s * b)) = -1 := by
    simp [hilbertInf]; omega
  have hJa : jacobiSym (-((2 : ℤ) ^ s * a)) b =
      jacobiSym (-(a : ℤ)) b * χ₈ b ^ s := by
    rw [show (-((2 : ℤ) ^ s * a) = -(a : ℤ) * (2 : ℤ) ^ s) by ring,
      jacobiSym.mul_left, jacobiSym_pow2 hbO]
  have hJb : jacobiSym (-((2 : ℤ) ^ s * b)) a =
      jacobiSym (-(b : ℤ)) a * χ₈ a ^ s := by
    rw [show (-((2 : ℤ) ^ s * b) = -(b : ℤ) * (2 : ℤ) ^ s) by ring,
      jacobiSym.mul_left, jacobiSym_pow2 haO]
  have hodd := hilbert_reciprocity_neg_odd_coprime ha hb hcop
  have hInfodd : hilbertInf (-(a : ℤ)) (-(b : ℤ)) = -1 := by
    simp [hilbertInf]; omega
  rw [hInfodd] at hodd
  have hχa := chi8_neg ha
  have hχb := chi8_neg hb
  rw [hJa, hJb, hInf]
  unfold hilbert2Pow
  simp only [Int.cast_neg]
  rw [hχa, hχb]
  calc
    (jacobiSym (-(a : ℤ)) b * χ₈ b ^ s) *
        (jacobiSym (-(b : ℤ)) a * χ₈ a ^ s) *
        (hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) * χ₈ b ^ s * χ₈ a ^ s) * (-1)
        = (jacobiSym (-(a : ℤ)) b * jacobiSym (-(b : ℤ)) a *
            hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) * (-1)) *
          (χ₈ a ^ s * χ₈ a ^ s) * (χ₈ b ^ s * χ₈ b ^ s) := by ring
    _ = 1 * 1 * 1 := by
        rw [hodd, chi8_pow_mul_self ha s, chi8_pow_mul_self hb s]
    _ = 1 := by ring

lemma hilbert2Odd_comm (a b : ℤ) : hilbert2Odd a b = hilbert2Odd b a := by
  simp only [hilbert2Odd, and_comm]

lemma chi4_sq_one {n : Nat} (h : n % 2 = 1) : χ₄ n * χ₄ n = 1 := by
  rcases odd_mod4 h with h1 | h3
  · rw [χ₄_nat_one_mod_four h1]; decide
  · rw [χ₄_nat_three_mod_four h3]; decide

lemma hilbert2Odd_self {c : Nat} (hc : c % 2 = 1) :
    hilbert2Odd c c = χ₄ c := by
  rw [hilbert2Odd_nat]
  rcases odd_mod4 hc with h1 | h3
  · have : ¬ (c % 4 = 3 ∧ c % 4 = 3) := by omega
    rw [if_neg this, χ₄_nat_one_mod_four h1]
  · rw [if_pos ⟨h3, h3⟩, χ₄_nat_three_mod_four h3]

/-- Hilbert reciprocity for `(c,c)`: the odd-place product is `χ₄ c`. -/
theorem hilbert_reciprocity_self {c : Nat} (hc : c % 2 = 1) :
    χ₄ c * hilbert2Odd c c * hilbertInf c c = 1 := by
  have hInf : hilbertInf (c : ℤ) c = 1 := by simp [hilbertInf]
  rw [hilbert2Odd_self hc, hInf, mul_one, chi4_sq_one hc]

lemma hilbert2Odd_neg_pos {a c : Nat} (ha : a % 2 = 1) (hc : c % 2 = 1) :
    hilbert2Odd (-(a : ℤ)) c =
      if a % 4 = 1 ∧ c % 4 = 3 then -1 else 1 := by
  simp only [hilbert2Odd]
  by_cases h : a % 4 = 1 ∧ c % 4 = 3
  · have ha3 : (-(a : ℤ)) % 4 = 3 :=
      (nat_neg_mod4 ha).elim (fun h' => h'.1) (fun h' => False.elim (by omega))
    have hc3 : (c : ℤ) % 4 = 3 := by exact_mod_cast h.2
    rw [if_pos ⟨ha3, hc3⟩, if_pos h]
  · have : ¬ ((-(a : ℤ)) % 4 = 3 ∧ (c : ℤ) % 4 = 3) := by
      intro ⟨ha3, hc3⟩
      have ha1 : a % 4 = 1 :=
        (nat_neg_mod4 ha).elim (fun h' => h'.2) (fun h' => False.elim (by omega))
      have hc3n : c % 4 = 3 := by exact_mod_cast hc3
      exact h ⟨ha1, hc3n⟩
    rw [if_neg this, if_neg h]

lemma chi4_mul_hilbert2_neg_pos {a c : Nat} (ha : a % 2 = 1) (hc : c % 2 = 1) :
    χ₄ c * hilbert2Odd a c * hilbert2Odd (-(a : ℤ)) c = 1 := by
  rw [hilbert2Odd_nat, hilbert2Odd_neg_pos ha hc]
  rcases odd_mod4 ha with ha1 | ha3 <;> rcases odd_mod4 hc with hc1 | hc3
  · rw [χ₄_nat_one_mod_four hc1]; simp [ha1, hc1]
  · rw [χ₄_nat_three_mod_four hc3]; simp [ha1, hc3]
  · rw [χ₄_nat_one_mod_four hc1]; simp [ha3, hc1]
  · rw [χ₄_nat_three_mod_four hc3]; simp [ha3, hc3]

/-- Hilbert reciprocity for a mixed-sign odd coprime pair `(-a, c)`. -/
theorem hilbert_reciprocity_neg_pos_odd_coprime {a c : Nat}
    (ha : a % 2 = 1) (hc : c % 2 = 1) (hcop : Nat.Coprime a c) :
    jacobiSym (-(a : ℤ)) c * jacobiSym c a *
      hilbert2Odd (-(a : ℤ)) c * hilbertInf (-(a : ℤ)) c = 1 := by
  have hcO : Odd c := Nat.odd_iff.mpr hc
  have hapos : 0 < a := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hcpos : 0 < c := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hInf : hilbertInf (-(a : ℤ)) c = 1 := by simp [hilbertInf]
  have hJa : jacobiSym (-(a : ℤ)) c = χ₄ c * jacobiSym a c := by
    rw [jacobiSym.neg _ hcO]
  have hpos := hilbert_reciprocity_odd_coprime ha hc hcop
  have hInfpos := hilbertInf_nat a c
  rw [hInfpos, mul_one] at hpos
  have hsq := hilbert2Odd_mul_self (a : ℤ) c
  have hJ : jacobiSym a c * jacobiSym c a = hilbert2Odd a c := by
    calc
      jacobiSym a c * jacobiSym c a
          = jacobiSym a c * jacobiSym c a * 1 := by rw [mul_one]
      _ = jacobiSym a c * jacobiSym c a *
            (hilbert2Odd a c * hilbert2Odd a c) := by rw [hsq]
      _ = (jacobiSym a c * jacobiSym c a * hilbert2Odd a c) *
            hilbert2Odd a c := by ring
      _ = 1 * hilbert2Odd a c := by rw [hpos]
      _ = hilbert2Odd a c := one_mul _
  rw [hJa, hInf]
  calc
    (χ₄ c * jacobiSym a c) * jacobiSym c a *
        hilbert2Odd (-(a : ℤ)) c * (1 : ℤ)
        = χ₄ c * (jacobiSym a c * jacobiSym c a) *
            hilbert2Odd (-(a : ℤ)) c := by ring
    _ = χ₄ c * hilbert2Odd a c * hilbert2Odd (-(a : ℤ)) c := by rw [hJ]
    _ = 1 := chi4_mul_hilbert2_neg_pos ha hc

/-- Hilbert reciprocity for `(-2^s a, c)` with `a,c` odd coprime. -/
theorem hilbert_reciprocity_neg_pos_two_pow {a c s : Nat}
    (ha : a % 2 = 1) (hc : c % 2 = 1) (hcop : Nat.Coprime a c) :
    jacobiSym (-((2 : ℤ) ^ s * a)) c * jacobiSym c a *
      hilbert2Pow s 0 (-(a : ℤ)) c *
      hilbertInf (-((2 : ℤ) ^ s * a)) c = 1 := by
  have hcO : Odd c := Nat.odd_iff.mpr hc
  have hapos : 0 < a := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hcpos : 0 < c := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hInf : hilbertInf (-((2 : ℤ) ^ s * a)) c = 1 := by simp [hilbertInf]
  have hJa : jacobiSym (-((2 : ℤ) ^ s * a)) c =
      jacobiSym (-(a : ℤ)) c * χ₈ c ^ s := by
    rw [show (-((2 : ℤ) ^ s * a) = -(a : ℤ) * (2 : ℤ) ^ s) by ring,
      jacobiSym.mul_left, jacobiSym_pow2 hcO]
  have hodd := hilbert_reciprocity_neg_pos_odd_coprime ha hc hcop
  have hInfodd : hilbertInf (-(a : ℤ)) c = 1 := by simp [hilbertInf]
  rw [hInfodd, mul_one] at hodd
  have hc8 : χ₈ (c : ℤ) = χ₈ c :=
    congrArg (χ₈ : ZMod 8 → ℤ) (Int.cast_natCast c)
  rw [hJa, hInf]
  unfold hilbert2Pow
  simp only [pow_zero, mul_one]
  rw [hc8]
  calc
    (jacobiSym (-(a : ℤ)) c * χ₈ c ^ s) * jacobiSym c a *
        (hilbert2Odd (-(a : ℤ)) c * χ₈ c ^ s)
        = (jacobiSym (-(a : ℤ)) c * jacobiSym c a *
            hilbert2Odd (-(a : ℤ)) c) *
          (χ₈ c ^ s * χ₈ c ^ s) := by ring
    _ = 1 * 1 := by rw [hodd, chi8_pow_mul_self hc s]
    _ = 1 := by ring

/-- Odd-place product of `(a/c, b/c)` by bimultiplicativity. -/
def hilbertOddRatio (a b c : Nat) : ℤ :=
  jacobiSym a b * jacobiSym b a *
    jacobiSym a c * jacobiSym c a *
    jacobiSym c b * jacobiSym b c *
    χ₄ c

/-- 2-adic Hilbert symbol of `(a/c, b/c)`. -/
def hilbert2Ratio (a b c : ℤ) : ℤ :=
  hilbert2Odd a b * hilbert2Odd a c * hilbert2Odd c b * hilbert2Odd c c

/-- **Hilbert reciprocity for an odd ratio `(a/c, b/c)`** with pairwise
    coprime odd `a,b,c`. -/
theorem hilbert_reciprocity_odd_ratio {a b c : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    hilbertOddRatio a b c * hilbert2Ratio a b c * hilbertInf a b = 1 := by
  have habP := hilbert_reciprocity_odd_coprime ha hb hab
  have hacP := hilbert_reciprocity_odd_coprime ha hc hac
  have hbcP := hilbert_reciprocity_odd_coprime hb hc hbc
  have hccP := hilbert_reciprocity_self hc
  have hInfab := hilbertInf_nat a b
  have hInfac := hilbertInf_nat a c
  have hInfbc := hilbertInf_nat b c
  have hInfcc : hilbertInf (c : ℤ) c = 1 := by simp [hilbertInf]
  rw [hInfab, mul_one] at habP
  rw [hInfac, mul_one] at hacP
  rw [hInfbc, mul_one] at hbcP
  rw [hInfcc, mul_one] at hccP
  have hcomm : hilbert2Odd (c : ℤ) b = hilbert2Odd b c := hilbert2Odd_comm _ _
  rw [hInfab]
  simp only [hilbertOddRatio, hilbert2Ratio, hcomm]
  calc
    jacobiSym a b * jacobiSym b a *
        jacobiSym a c * jacobiSym c a *
        jacobiSym c b * jacobiSym b c *
        χ₄ c *
        (hilbert2Odd a b * hilbert2Odd a c * hilbert2Odd b c * hilbert2Odd c c) *
        (1 : ℤ)
        = (jacobiSym a b * jacobiSym b a * hilbert2Odd a b) *
            (jacobiSym a c * jacobiSym c a * hilbert2Odd a c) *
            (jacobiSym b c * jacobiSym c b * hilbert2Odd b c) *
            (χ₄ c * hilbert2Odd c c) := by ring
    _ = 1 * 1 * 1 * 1 := by rw [habP, hacP, hbcP, hccP]
    _ = 1 := by ring

/-- Odd-place product of `(-a/c, -b/c)`. -/
def hilbertOddRatioNeg (a b c : Nat) : ℤ :=
  jacobiSym (-(a : ℤ)) b * jacobiSym (-(b : ℤ)) a *
    jacobiSym (-(a : ℤ)) c * jacobiSym c a *
    jacobiSym c b * jacobiSym (-(b : ℤ)) c *
    χ₄ c

/-- **Hilbert reciprocity for `(-a/c, -b/c)`** — the ES ratio of odd parts
    after cancelling 2-powers, under pairwise coprimeness. -/
theorem hilbert_reciprocity_neg_ratio {a b c : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    hilbertOddRatioNeg a b c * hilbert2Ratio (-(a : ℤ)) (-(b : ℤ)) c *
      hilbertInf (-(a : ℤ)) (-(b : ℤ)) = 1 := by
  have habP := hilbert_reciprocity_neg_odd_coprime ha hb hab
  have hacP := hilbert_reciprocity_neg_pos_odd_coprime ha hc hac
  have hbcP := hilbert_reciprocity_neg_pos_odd_coprime hb hc hbc
  have hccP := hilbert_reciprocity_self hc
  have hInfab : hilbertInf (-(a : ℤ)) (-(b : ℤ)) = -1 := by
    simp [hilbertInf]; omega
  have hInfac : hilbertInf (-(a : ℤ)) c = 1 := by simp [hilbertInf]
  have hInfbc : hilbertInf (-(b : ℤ)) c = 1 := by simp [hilbertInf]
  have hInfcc : hilbertInf (c : ℤ) c = 1 := by simp [hilbertInf]
  rw [hInfab] at habP
  rw [hInfac, mul_one] at hacP
  rw [hInfbc, mul_one] at hbcP
  rw [hInfcc, mul_one] at hccP
  have hcomm : hilbert2Odd c (-(b : ℤ)) = hilbert2Odd (-(b : ℤ)) c :=
    hilbert2Odd_comm _ _
  rw [hInfab]
  simp only [hilbertOddRatioNeg, hilbert2Ratio, hcomm]
  calc
    jacobiSym (-(a : ℤ)) b * jacobiSym (-(b : ℤ)) a *
        jacobiSym (-(a : ℤ)) c * jacobiSym c a *
        jacobiSym c b * jacobiSym (-(b : ℤ)) c *
        χ₄ c *
        (hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) * hilbert2Odd (-(a : ℤ)) c *
          hilbert2Odd (-(b : ℤ)) c * hilbert2Odd c c) * (-1)
        = (jacobiSym (-(a : ℤ)) b * jacobiSym (-(b : ℤ)) a *
            hilbert2Odd (-(a : ℤ)) (-(b : ℤ)) * (-1)) *
          (jacobiSym (-(a : ℤ)) c * jacobiSym c a *
            hilbert2Odd (-(a : ℤ)) c) *
          (jacobiSym (-(b : ℤ)) c * jacobiSym c b *
            hilbert2Odd (-(b : ℤ)) c) *
          (χ₄ c * hilbert2Odd c c) := by ring
    _ = 1 * 1 * 1 * 1 := by rw [habP, hacP, hbcP, hccP]
    _ = 1 := by ring

/-- **Hilbert reciprocity for the ES 3.8 ratio** `(-2^s a/c, -2^s b/c)`
    with pairwise coprime odd unit parts.  This is the local-symbol product
    of `-x/z`, `-y/z` after extracting the 2-adic shape, when `r₁,r₂,r₃`
    are pairwise coprime. -/
theorem hilbert_reciprocity_es_ratio {a b c s : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    jacobiSym (-((2 : ℤ) ^ s * a)) b * jacobiSym (-((2 : ℤ) ^ s * b)) a *
      jacobiSym (-((2 : ℤ) ^ s * a)) c * jacobiSym c a *
      jacobiSym c b * jacobiSym (-((2 : ℤ) ^ s * b)) c *
      χ₄ c *
      hilbert2Pow s s (-(a : ℤ)) (-(b : ℤ)) *
      hilbert2Pow s 0 (-(a : ℤ)) c *
      hilbert2Pow 0 s c (-(b : ℤ)) *
      hilbert2Odd c c *
      hilbertInf (-((2 : ℤ) ^ s * a)) (-((2 : ℤ) ^ s * b)) = 1 := by
  have habP := hilbert_reciprocity_neg_two_pow ha hb hab (s := s)
  have hacP := hilbert_reciprocity_neg_pos_two_pow ha hc hac (s := s)
  have hbcP := hilbert_reciprocity_neg_pos_two_pow hb hc hbc (s := s)
  have hccP := hilbert_reciprocity_self hc
  have hInfab : hilbertInf (-((2 : ℤ) ^ s * a)) (-((2 : ℤ) ^ s * b)) = -1 := by
    simp [hilbertInf]; omega
  have hInfcc : hilbertInf (c : ℤ) c = 1 := by simp [hilbertInf]
  have hacInf : hilbertInf (-((2 : ℤ) ^ s * a)) c = 1 := by simp [hilbertInf]
  have hbcInf : hilbertInf (-((2 : ℤ) ^ s * b)) c = 1 := by simp [hilbertInf]
  rw [hInfab] at habP
  rw [hacInf, mul_one] at hacP
  rw [hbcInf, mul_one] at hbcP
  rw [hInfcc, mul_one] at hccP
  have h2comm : hilbert2Pow 0 s c (-(b : ℤ)) =
      hilbert2Pow s 0 (-(b : ℤ)) c := by
    simp only [hilbert2Pow, pow_zero, mul_one]
    rw [hilbert2Odd_comm]
  rw [hInfab, h2comm]
  calc
    jacobiSym (-((2 : ℤ) ^ s * a)) b * jacobiSym (-((2 : ℤ) ^ s * b)) a *
        jacobiSym (-((2 : ℤ) ^ s * a)) c * jacobiSym c a *
        jacobiSym c b * jacobiSym (-((2 : ℤ) ^ s * b)) c *
        χ₄ c *
        hilbert2Pow s s (-(a : ℤ)) (-(b : ℤ)) *
        hilbert2Pow s 0 (-(a : ℤ)) c *
        hilbert2Pow s 0 (-(b : ℤ)) c *
        hilbert2Odd c c * (-1)
        = (jacobiSym (-((2 : ℤ) ^ s * a)) b *
            jacobiSym (-((2 : ℤ) ^ s * b)) a *
            hilbert2Pow s s (-(a : ℤ)) (-(b : ℤ)) * (-1)) *
          (jacobiSym (-((2 : ℤ) ^ s * a)) c * jacobiSym c a *
            hilbert2Pow s 0 (-(a : ℤ)) c) *
          (jacobiSym (-((2 : ℤ) ^ s * b)) c * jacobiSym c b *
            hilbert2Pow s 0 (-(b : ℤ)) c) *
          (χ₄ c * hilbert2Odd c c) := by ring
    _ = 1 * 1 * 1 * 1 := by rw [habP, hacP, hbcP, hccP]
    _ = 1 := by ring

lemma odd_mul_mod4 {x y : Nat} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    (x * y) % 4 = 1 ∧ (x % 4 = 1 ∧ y % 4 = 1 ∨ x % 4 = 3 ∧ y % 4 = 3) ∨
    (x * y) % 4 = 3 ∧ (x % 4 = 1 ∧ y % 4 = 3 ∨ x % 4 = 3 ∧ y % 4 = 1) := by
  rcases odd_mod4 hx with hx1 | hx3 <;> rcases odd_mod4 hy with hy1 | hy3
  · refine Or.inl ⟨?_, Or.inl ⟨hx1, hy1⟩⟩
    rw [Nat.mul_mod, hx1, hy1]
  · refine Or.inr ⟨?_, Or.inl ⟨hx1, hy3⟩⟩
    rw [Nat.mul_mod, hx1, hy3]
  · refine Or.inr ⟨?_, Or.inr ⟨hx3, hy1⟩⟩
    rw [Nat.mul_mod, hx3, hy1]
  · refine Or.inl ⟨?_, Or.inr ⟨hx3, hy3⟩⟩
    rw [Nat.mul_mod, hx3, hy3]

/-- The 2-adic formula is bimultiplicative in the left odd argument. -/
lemma hilbert2Odd_mul_left {x y z : Nat}
    (hx : x % 2 = 1) (hy : y % 2 = 1) :
    hilbert2Odd (x * y : Nat) z = hilbert2Odd x z * hilbert2Odd y z := by
  rw [hilbert2Odd_nat, hilbert2Odd_nat, hilbert2Odd_nat]
  by_cases hz : z % 4 = 3
  · rcases odd_mul_mod4 hx hy with ⟨hxy1, hxy1'⟩ | ⟨hxy3, hxy3'⟩
    · have hL : ¬ ((x * y) % 4 = 3 ∧ z % 4 = 3) := fun h => by omega
      rw [if_neg hL]
      rcases hxy1' with ⟨hx1, hy1⟩ | ⟨hx3, hy3⟩
      · have hxN : ¬ (x % 4 = 3 ∧ z % 4 = 3) := fun h => by omega
        have hyN : ¬ (y % 4 = 3 ∧ z % 4 = 3) := fun h => by omega
        rw [if_neg hxN, if_neg hyN]; rfl
      · have hxY : x % 4 = 3 ∧ z % 4 = 3 := ⟨hx3, hz⟩
        have hyY : y % 4 = 3 ∧ z % 4 = 3 := ⟨hy3, hz⟩
        rw [if_pos hxY, if_pos hyY]; rfl
    · have hL : (x * y) % 4 = 3 ∧ z % 4 = 3 := ⟨hxy3, hz⟩
      rw [if_pos hL]
      rcases hxy3' with ⟨hx1, hy3⟩ | ⟨hx3, hy1⟩
      · have hxN : ¬ (x % 4 = 3 ∧ z % 4 = 3) := fun h => by omega
        have hyY : y % 4 = 3 ∧ z % 4 = 3 := ⟨hy3, hz⟩
        rw [if_neg hxN, if_pos hyY]; rfl
      · have hxY : x % 4 = 3 ∧ z % 4 = 3 := ⟨hx3, hz⟩
        have hyN : ¬ (y % 4 = 3 ∧ z % 4 = 3) := fun h => by omega
        rw [if_pos hxY, if_neg hyN]; rfl
  · have hxyN : ¬ ((x * y) % 4 = 3 ∧ z % 4 = 3) := fun h => hz h.2
    have hxN : ¬ (x % 4 = 3 ∧ z % 4 = 3) := fun h => hz h.2
    have hyN : ¬ (y % 4 = 3 ∧ z % 4 = 3) := fun h => hz h.2
    rw [if_neg hxyN, if_neg hxN, if_neg hyN]; rfl

lemma hilbert2Odd_mul_right {x y z : Nat}
    (hy : y % 2 = 1) (hz : z % 2 = 1) :
    hilbert2Odd x (y * z : Nat) = hilbert2Odd x y * hilbert2Odd x z := by
  rw [hilbert2Odd_comm (x : ℤ) (y * z : Nat), hilbert2Odd_comm (x : ℤ) y,
    hilbert2Odd_comm (x : ℤ) z]
  exact hilbert2Odd_mul_left hy hz

lemma odd_sq_mod4 {k : Nat} (h : k % 2 = 1) : (k ^ 2) % 4 = 1 := by
  rcases odd_mod4 h with h1 | h3
  · rw [Nat.pow_two, Nat.mul_mod, h1]
  · rw [Nat.pow_two, Nat.mul_mod, h3]

lemma odd_sq_odd {k : Nat} (h : k % 2 = 1) : (k ^ 2) % 2 = 1 := by
  rw [Nat.pow_two, Nat.mul_mod, h]

lemma hilbert2Odd_sq {k b : Nat} (hk : k % 2 = 1) :
    hilbert2Odd (k ^ 2 : Nat) b = 1 := by
  rw [hilbert2Odd_nat]
  have : ¬ (k ^ 2 % 4 = 3 ∧ b % 4 = 3) := fun h => by
    have := odd_sq_mod4 hk; omega
  rw [if_neg this]

lemma hilbert2Odd_mul_sq {k a b : Nat} (hk : k % 2 = 1) (ha : a % 2 = 1) :
    hilbert2Odd (k ^ 2 * a : Nat) b = hilbert2Odd a b := by
  rw [hilbert2Odd_mul_left (odd_sq_odd hk) ha, hilbert2Odd_sq hk, one_mul]

lemma hilbert2Odd_mul_sq_right {k a b : Nat} (hk : k % 2 = 1) (hb : b % 2 = 1) :
    hilbert2Odd a (k ^ 2 * b : Nat) = hilbert2Odd a b := by
  rw [hilbert2Odd_comm (a : ℤ) (k ^ 2 * b : Nat), hilbert2Odd_comm (a : ℤ) b]
  exact hilbert2Odd_mul_sq hk hb

lemma hilbert2Odd_cancel_sqs {s r x y : Nat}
    (hs : s % 2 = 1) (hr : r % 2 = 1) (hx : x % 2 = 1) (hy : y % 2 = 1) :
    hilbert2Odd (s ^ 2 * x : Nat) (r ^ 2 * y : Nat) = hilbert2Odd x y := by
  rw [hilbert2Odd_mul_sq hs hx, hilbert2Odd_mul_sq_right hr hy]

/-- Odd-place product of `(t a, t b)` when `t` is a shared odd factor
    coprime to both cofactors.  Jacobi of the unreduced pair vanishes when
    `gcd > 1`; the expansion is the correct odd-place contribution. -/
def hilbertOddShared (t a b : Nat) : ℤ :=
  χ₄ t *
    jacobiSym t b * jacobiSym b t *
    jacobiSym a t * jacobiSym t a *
    jacobiSym a b * jacobiSym b a

lemma hilbert2Odd_shared {t a b : Nat}
    (ht : t % 2 = 1) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    hilbert2Odd (t * a : Nat) (t * b : Nat) =
      hilbert2Odd t t * hilbert2Odd t b * hilbert2Odd a t * hilbert2Odd a b := by
  rw [hilbert2Odd_mul_left ht ha (z := t * b),
    hilbert2Odd_mul_right (x := t) ht hb,
    hilbert2Odd_mul_right (x := a) ht hb]
  ring

/-- **Hilbert reciprocity for a shared odd factor.**  For pairwise coprime
    odd `t,a,b`, the local product of `(t a, t b)` is 1. -/
theorem hilbert_reciprocity_shared {t a b : Nat}
    (ht : t % 2 = 1) (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hta : Nat.Coprime t a) (htb : Nat.Coprime t b) (hab : Nat.Coprime a b) :
    hilbertOddShared t a b * hilbert2Odd (t * a : Nat) (t * b : Nat) *
      hilbertInf (t * a : Nat) (t * b : Nat) = 1 := by
  have httP := hilbert_reciprocity_self ht
  have htbP := hilbert_reciprocity_odd_coprime ht hb htb
  have hatP := hilbert_reciprocity_odd_coprime ha ht hta.symm
  have habP := hilbert_reciprocity_odd_coprime ha hb hab
  have hInf := hilbertInf_nat (t * a) (t * b)
  rw [hilbertInf_nat t t, mul_one] at httP
  rw [hilbertInf_nat t b, mul_one] at htbP
  rw [hilbertInf_nat a t, mul_one] at hatP
  rw [hilbertInf_nat a b, mul_one] at habP
  rw [hInf, hilbert2Odd_shared ht ha hb]
  simp only [hilbertOddShared]
  calc
    χ₄ t *
        jacobiSym t b * jacobiSym b t *
        jacobiSym a t * jacobiSym t a *
        jacobiSym a b * jacobiSym b a *
        (hilbert2Odd t t * hilbert2Odd t b * hilbert2Odd a t * hilbert2Odd a b) *
        (1 : ℤ)
        = (χ₄ t * hilbert2Odd t t) *
            (jacobiSym t b * jacobiSym b t * hilbert2Odd t b) *
            (jacobiSym a t * jacobiSym t a * hilbert2Odd a t) *
            (jacobiSym a b * jacobiSym b a * hilbert2Odd a b) := by ring
    _ = 1 * 1 * 1 * 1 := by rw [httP, htbP, hatP, habP]
    _ = 1 := by ring

/-- Squares cancel in Jacobi on the left when coprime to the right argument. -/
lemma jacobiSym_mul_sq_left {k a b : Nat} (hkb : Nat.Coprime k b) :
    jacobiSym (k ^ 2 * a : Nat) b = jacobiSym a b := by
  have hgcdk : ((k : ℤ).gcd b = 1) := by
    simpa [Int.gcd_natCast_natCast] using hkb.gcd_eq_one
  rw [Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym.sq_one' hgcdk, one_mul]

lemma jacobiSym_mul_sq_right {k a b : Nat}
    (hkpos : 0 < k) (hapos : 0 < a) (hkb : Nat.Coprime k b) :
    jacobiSym b (k ^ 2 * a) = jacobiSym b a := by
  have hk2 : k ^ 2 ≠ 0 := Nat.ne_of_gt (Nat.pow_pos hkpos)
  have ha0 : a ≠ 0 := Nat.ne_of_gt hapos
  have hgba : ((b : ℤ).gcd k = 1) := by
    simpa [Int.gcd_natCast_natCast, Nat.gcd_comm] using hkb.gcd_eq_one
  rw [jacobiSym.mul_right' (b : ℤ) hk2 ha0, jacobiSym.pow_right, jacobiSym.sq_one hgba, one_mul]

/-- **Squares cancel on the left in the coprime Jacobi product.**  An odd
    square is `1 (mod 4)`, so `(k² a, b)_2 = (a,b)_2`, and Jacobi agrees
    when `k` is coprime to `b`. -/
theorem hilbert_reciprocity_sq_left {k a b : Nat}
    (hk : k % 2 = 1) (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hab : Nat.Coprime a b) (hkb : Nat.Coprime k b) :
    jacobiSym (k ^ 2 * a : Nat) b * jacobiSym b (k ^ 2 * a) *
      hilbert2Odd (k ^ 2 * a : Nat) b * hilbertInf (k ^ 2 * a : Nat) b = 1 := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hapos : 0 < a := Nat.pos_of_ne_zero (by intro h; subst h; omega)
  have hpos := hilbert_reciprocity_odd_coprime ha hb hab
  rw [hilbertInf_nat a b, mul_one] at hpos
  rw [jacobiSym_mul_sq_left hkb, jacobiSym_mul_sq_right hkpos hapos hkb,
    hilbert2Odd_mul_sq hk ha, hilbertInf_nat (k ^ 2 * a) b, mul_one, hpos]

/-- Independent odd squares cancel in the 2-adic symbol, so
    `(s² t a, r² t b)` has the same 2-adic factor as `(t a, t b)`. -/
theorem hilbert_reciprocity_shared_sqs {s r t a b : Nat}
    (hs : s % 2 = 1) (hr : r % 2 = 1)
    (ht : t % 2 = 1) (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hta : Nat.Coprime t a) (htb : Nat.Coprime t b) (hab : Nat.Coprime a b) :
    hilbertOddShared t a b *
      hilbert2Odd (s ^ 2 * t * a : Nat) (r ^ 2 * t * b : Nat) *
      hilbertInf (s ^ 2 * t * a : Nat) (r ^ 2 * t * b : Nat) = 1 := by
  have hsh := hilbert_reciprocity_shared ht ha hb hta htb hab
  rw [hilbertInf_nat (t * a) (t * b), mul_one] at hsh
  have htaodd : (t * a) % 2 = 1 := (mul_mod2_odd t a).mpr ⟨ht, ha⟩
  have htbodd : (t * b) % 2 = 1 := (mul_mod2_odd t b).mpr ⟨ht, hb⟩
  have hx : s ^ 2 * t * a = s ^ 2 * (t * a) := by ring
  have hy : r ^ 2 * t * b = r ^ 2 * (t * b) := by ring
  rw [hilbertInf_nat (s ^ 2 * t * a) (r ^ 2 * t * b), mul_one, hx, hy,
    hilbert2Odd_cancel_sqs hs hr htaodd htbodd, hsh]

/-- Shared odd factor after cancelling a common odd square. -/
theorem hilbert_reciprocity_shared_sq {s t a b : Nat}
    (hs : s % 2 = 1) (ht : t % 2 = 1) (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hta : Nat.Coprime t a) (htb : Nat.Coprime t b) (hab : Nat.Coprime a b) :
    hilbertOddShared t a b *
      hilbert2Odd (s ^ 2 * t * a : Nat) (s ^ 2 * t * b : Nat) *
      hilbertInf (s ^ 2 * t * a : Nat) (s ^ 2 * t * b : Nat) = 1 :=
  hilbert_reciprocity_shared_sqs hs hs ht ha hb hta htb hab

lemma odd_of_dvd_odd {d n : Nat} (hn : n % 2 = 1) (hd : d ∣ n) : d % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
  · have : n % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h0) hd)
    omega
  · exact h1

lemma odd_pos {n : Nat} (h : n % 2 = 1) : 0 < n :=
  Nat.pos_of_ne_zero (by intro h0; subst h0; omega)

/-- Maximal square factor of an odd positive integer: `n = k² m` with
    `m` square-free and both factors odd. -/
lemma exists_odd_sq_kernel {n : Nat} (hn : n % 2 = 1) :
    ∃ k m, k % 2 = 1 ∧ m % 2 = 1 ∧ Squarefree m ∧ k ^ 2 * m = n := by
  obtain ⟨m, k, _, _, hkm, hsq⟩ := Nat.sq_mul_squarefree_of_pos (odd_pos hn)
  have hkodd : k % 2 = 1 := by
    have h2 : (k ^ 2) % 2 = 1 :=
      ((mul_mod2_odd (k ^ 2) m).mp (by rw [hkm]; exact hn)).1
    rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
    · rw [Nat.pow_two, Nat.mul_mod, hk0] at h2; cases h2
    · exact hk1
  have hmodd : m % 2 = 1 :=
    ((mul_mod2_odd (k ^ 2) m).mp (by rw [hkm]; exact hn)).2
  exact ⟨k, m, hkodd, hmodd, hsq, hkm⟩

lemma coprime_div_gcd {α β : Nat} (h : 0 < Nat.gcd α β) :
    Nat.Coprime (α / Nat.gcd α β) (β / Nat.gcd α β) := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_div (Nat.gcd_dvd_left α β) (Nat.gcd_dvd_right α β),
    Nat.div_self h]

/-- Every pair of odd positive integers is `s² t a` and `r² t b` with
    `t,a,b` pairwise coprime and odd.  The shared kernel `t` is the gcd of
    the square-free parts, hence coprime to both cofactors. -/
theorem exists_shared_odd_kernel {A B : Nat}
    (hA : A % 2 = 1) (hB : B % 2 = 1) :
    ∃ s r t a b,
      s % 2 = 1 ∧ r % 2 = 1 ∧ t % 2 = 1 ∧ a % 2 = 1 ∧ b % 2 = 1 ∧
      Nat.Coprime t a ∧ Nat.Coprime t b ∧ Nat.Coprime a b ∧
      s ^ 2 * t * a = A ∧ r ^ 2 * t * b = B := by
  obtain ⟨s, α, hs, hα, hαsq, hsA⟩ := exists_odd_sq_kernel hA
  obtain ⟨r, β, hr, hβ, hβsq, hrB⟩ := exists_odd_sq_kernel hB
  set t := Nat.gcd α β with htDef
  set a := α / t with haDef
  set b := β / t with hbDef
  have hαpos : 0 < α := odd_pos hα
  have htpos : 0 < t := Nat.gcd_pos_of_pos_left β hαpos
  have hta_mul : t * a = α := by
    rw [haDef, htDef]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_left α β)
  have htb_mul : t * b = β := by
    rw [hbDef, htDef]; exact Nat.mul_div_cancel' (Nat.gcd_dvd_right α β)
  have htodd : t % 2 = 1 := odd_of_dvd_odd hα (by rw [htDef]; exact Nat.gcd_dvd_left α β)
  have haodd : a % 2 = 1 :=
    ((mul_mod2_odd t a).mp (by rw [hta_mul]; exact hα)).2
  have hbodd : b % 2 = 1 :=
    ((mul_mod2_odd t b).mp (by rw [htb_mul]; exact hβ)).2
  have hta : Nat.Coprime t a :=
    Nat.coprime_of_squarefree_mul (by rw [hta_mul]; exact hαsq)
  have htb : Nat.Coprime t b :=
    Nat.coprime_of_squarefree_mul (by rw [htb_mul]; exact hβsq)
  have hab : Nat.Coprime a b := by
    rw [haDef, hbDef, htDef]; exact coprime_div_gcd htpos
  refine ⟨s, r, t, a, b, hs, hr, htodd, haodd, hbodd, hta, htb, hab, ?_, ?_⟩
  · calc s ^ 2 * t * a = s ^ 2 * (t * a) := by ring
      _ = s ^ 2 * α := by rw [hta_mul]
      _ = A := hsA
  · calc r ^ 2 * t * b = r ^ 2 * (t * b) := by ring
      _ = r ^ 2 * β := by rw [htb_mul]
      _ = B := hrB

/-- **Hilbert reciprocity for odd positive integers.**  After cancelling
    squares, any shared odd prime is absorbed into a kernel `t` coprime to
    both cofactors, and the local product is 1. -/
theorem hilbert_reciprocity_odd_integers {A B : Nat}
    (hA : A % 2 = 1) (hB : B % 2 = 1) :
    ∃ t a b,
      t % 2 = 1 ∧ a % 2 = 1 ∧ b % 2 = 1 ∧
      Nat.Coprime t a ∧ Nat.Coprime t b ∧ Nat.Coprime a b ∧
      hilbertOddShared t a b * hilbert2Odd A B * hilbertInf A B = 1 := by
  obtain ⟨s, r, t, a, b, hs, hr, ht, ha, hb, hta, htb, hab, hAeq, hBeq⟩ :=
    exists_shared_odd_kernel hA hB
  refine ⟨t, a, b, ht, ha, hb, hta, htb, hab, ?_⟩
  rw [← hAeq, ← hBeq]
  exact hilbert_reciprocity_shared_sqs hs hr ht ha hb hta htb hab

/-- Reciprocity discharge of the Bright–Loughran anatomy: with Lemmas 3.1,
    3.5 (good places trivial), and 3.8 (inv₂ = 1 for odd n), Hilbert
    reciprocity forces inv_p = −1.  The odd-place identity is
    `hilbert_reciprocity_odd_primes`; the odd-integer identities are
    `hilbert_reciprocity_odd_coprime`,
    `hilbert_reciprocity_odd_integers` (shared kernel after cancelling
    squares), `hilbert_reciprocity_neg_odd_coprime`,
    `hilbert_reciprocity_neg_two_pow`, and
    `hilbert_reciprocity_es_ratio`. -/
theorem thm12_discharged (H : InvariantData)
    (hInf : H.invInf = -1) (h2 : H.inv2 = 1) (hGood : H.invGood = 1) :
    H.invP = -1 :=
  bl_thm12_prime_anatomy H hInf h2 hGood

/-- A natural-number ES solution at an odd prime supplies the local signs
    of Lemmas 3.1 and 3.5; Lemma 3.8 supplies inv₂ once `H.inv2` is identified
    with Serre's formula on the solution's 2-adic shape
    (`lemma38_of_nat_solution`). Reciprocity then yields Yamamoto's condition. -/
theorem yamamoto_of_nat_solution {p x y z : Nat} [Fact p.Prime]
    (hES : IsES p x y z) (_hp2 : p ≠ 2)
    (H : InvariantData)
    (h38 : H.inv2 = 1)
    (hInf : H.invInf = hilbertInf (-(x : ℤ)) (-(y : ℤ)))
    (hGood : H.invGood = 1) :
    H.invP = -1 := by
  have h31 : H.invInf = -1 := by
    rw [hInf]; exact lemma31_of_isES hES
  exact thm12_discharged H h31 h38 hGood

/-! ## BL Lemma 3.8 on a Nat solution (odd n)

The finite check `lemma38_check_true` is in `BrightLoughran.lean`.  What
follows is the missing valuation analysis of BL §3.3.4: an odd-n solution
has 2-adic shape `(2^{s+e} r₁, 2^{s+e} r₂, 2^e r₃)` with `rᵢ` odd and
`s ≥ 1`, the key congruence (BL 3.4) holds, and Serre's 2-adic invariant
is therefore 1.  Identifying `InvariantData.inv2` with that Serre value
is the remaining interface glue for `yamamoto_of_nat_solution`. -/

lemma v2_of_odd {n : Nat} (h : n % 2 = 1) : padicValNat 2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega)

lemma pow2_ne_zero (k : Nat) : (2 : Nat) ^ k ≠ 0 :=
  Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < (2 : Nat)))

lemma add_ne_zero_left {a b : Nat} (ha : a ≠ 0) : a + b ≠ 0 :=
  Nat.ne_of_gt (Nat.add_pos_left (Nat.pos_of_ne_zero ha) b)

lemma pow2_mul (a b : Nat) : 2 ^ a * 2 ^ b = 2 ^ (a + b) :=
  (Nat.pow_add 2 a b).symm

lemma isES_cycle {n x y z : Nat} (h : IsES n x y z) : IsES n y z x := by
  have ⟨hx, hy, hz, heq⟩ := h
  refine ⟨hy, hz, hx, ?_⟩
  convert heq using 1 <;> ring

lemma v2_four : padicValNat 2 4 = 2 := by
  have h2 : (2 : Nat) ≠ 0 := by decide
  rw [show (4 : Nat) = 2 * 2 from rfl, padicValNat.mul h2 h2, padicValNat_self]

lemma even_pow2_of_pos {k : Nat} (hk : 1 ≤ k) : (2 ^ k) % 2 = 0 := by
  have : k = k - 1 + 1 := by omega
  rw [this, Nat.pow_succ, Nat.mul_comm, Nat.mul_mod_right]

lemma oddPart_mul {n : Nat} (_hn : n ≠ 0) :
    2 ^ padicValNat 2 n * (n / 2 ^ padicValNat 2 n) = n :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

lemma oddPart_odd {n : Nat} (hn : n ≠ 0) :
    (n / 2 ^ padicValNat 2 n) % 2 = 1 := by
  set k := padicValNat 2 n
  set m := n / 2 ^ k
  have hnm : 2 ^ k * m = n := by
    simpa [k, m] using oddPart_mul hn
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hnm
    exact hn hnm.symm
  rcases Nat.mod_two_eq_zero_or_one m with hev | hodd
  · have hdvd : 2 ∣ m := Nat.dvd_of_mod_eq_zero hev
    obtain ⟨t, ht⟩ := hdvd
    have : 2 ^ (k + 1) ∣ n := by
      refine ⟨t, ?_⟩
      rw [← hnm, ht, Nat.pow_succ]
      ring
    exact absurd this (pow_succ_padicValNat_not_dvd hn)
  · exact hodd

lemma v2_add_of_lt {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : padicValNat 2 a < padicValNat 2 b) :
    padicValNat 2 (a + b) = padicValNat 2 a := by
  set va := padicValNat 2 a
  set vb := padicValNat 2 b
  set oa := a / 2 ^ va
  set ob := b / 2 ^ vb
  have ha' : 2 ^ va * oa = a := by simpa [va, oa] using oddPart_mul ha
  have hb' : 2 ^ vb * ob = b := by simpa [vb, ob] using oddPart_mul hb
  have hoa : oa % 2 = 1 := by simpa [va, oa] using oddPart_odd ha
  have hob : ob % 2 = 1 := by simpa [vb, ob] using oddPart_odd hb
  have hsplit : 2 ^ vb = 2 ^ va * 2 ^ (vb - va) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt h)]
  have hsum : a + b = 2 ^ va * (oa + 2 ^ (vb - va) * ob) := by
    calc
      a + b = 2 ^ va * oa + 2 ^ vb * ob := by rw [ha', hb']
      _ = 2 ^ va * oa + 2 ^ va * 2 ^ (vb - va) * ob := by rw [hsplit]
      _ = 2 ^ va * (oa + 2 ^ (vb - va) * ob) := by ring
  have hge : 1 ≤ vb - va := Nat.succ_le_of_lt (Nat.sub_pos_of_lt h)
  have hparen_odd : (oa + 2 ^ (vb - va) * ob) % 2 = 1 := by
    have heven : (2 ^ (vb - va) * ob) % 2 = 0 := by
      rw [Nat.mul_mod, even_pow2_of_pos hge]
      simp
    omega
  have hparen0 : oa + 2 ^ (vb - va) * ob ≠ 0 := by
    intro h0
    have : (oa + 2 ^ (vb - va) * ob) % 2 = 0 := by rw [h0]
    omega
  have h2pow : (2 : Nat) ^ va ≠ 0 := pow2_ne_zero va
  rw [hsum, padicValNat.mul h2pow hparen0, padicValNat.prime_pow, v2_of_odd hparen_odd,
    add_zero]

lemma v2_add_ge_min {a b : Nat} (ha : a ≠ 0) (_hb : b ≠ 0) :
    min (padicValNat 2 a) (padicValNat 2 b) ≤ padicValNat 2 (a + b) := by
  have hsum0 : a + b ≠ 0 := add_ne_zero_left ha
  have hva := pow_padicValNat_dvd (p := 2) (n := a)
  have hvb := pow_padicValNat_dvd (p := 2) (n := b)
  have hmin_a : 2 ^ min (padicValNat 2 a) (padicValNat 2 b) ∣ a :=
    (pow_dvd_pow (2 : Nat) (min_le_left _ _)).trans hva
  have hmin_b : 2 ^ min (padicValNat 2 a) (padicValNat 2 b) ∣ b :=
    (pow_dvd_pow (2 : Nat) (min_le_right _ _)).trans hvb
  have hdvd : 2 ^ min (padicValNat 2 a) (padicValNat 2 b) ∣ a + b :=
    Nat.dvd_add hmin_a hmin_b
  exact (padicValNat_dvd_iff_le hsum0).1 hdvd

lemma v2_add_three_unique_min {a b c : Nat}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hba : padicValNat 2 a < padicValNat 2 b)
    (hca : padicValNat 2 a < padicValNat 2 c) :
    padicValNat 2 (a + b + c) = padicValNat 2 a := by
  have hbc0 : b + c ≠ 0 := add_ne_zero_left hb
  have hmin : min (padicValNat 2 b) (padicValNat 2 c) ≤ padicValNat 2 (b + c) :=
    v2_add_ge_min hb hc
  have hlt : padicValNat 2 a < padicValNat 2 (b + c) := by
    have : padicValNat 2 a < min (padicValNat 2 b) (padicValNat 2 c) :=
      lt_min hba hca
    omega
  have hassoc : a + b + c = a + (b + c) := by ring
  rw [hassoc, v2_add_of_lt ha hbc0 hlt]

lemma v2_four_mul {x y z : Nat} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    padicValNat 2 (4 * (x * y * z)) =
      2 + padicValNat 2 x + padicValNat 2 y + padicValNat 2 z := by
  have h4 : (4 : Nat) ≠ 0 := by decide
  have hxy : x * y ≠ 0 := Nat.mul_ne_zero hx hy
  have hxyz : x * y * z ≠ 0 := Nat.mul_ne_zero hxy hz
  rw [padicValNat.mul h4 hxyz, v2_four, padicValNat.mul hxy hz, padicValNat.mul hx hy]
  ring

lemma es_v2_balance {n x y z : Nat} (hES : IsES n x y z) (hodd : n % 2 = 1) :
    2 + padicValNat 2 x + padicValNat 2 y + padicValNat 2 z =
      padicValNat 2 (x * y + y * z + z * x) := by
  have ⟨hx, hy, hz, heq⟩ := hES
  have hx0 : x ≠ 0 := Nat.pos_iff_ne_zero.mp hx
  have hy0 : y ≠ 0 := Nat.pos_iff_ne_zero.mp hy
  have hz0 : z ≠ 0 := Nat.pos_iff_ne_zero.mp hz
  have hn0 : n ≠ 0 := by intro h; subst h; omega
  have hsum0 : x * y + y * z + z * x ≠ 0 := by
    intro h0
    have heq0 : 4 * (x * y * z) = 0 := by rw [heq, h0, Nat.mul_zero]
    have hxyz : x * y * z = 0 := by
      rcases Nat.mul_eq_zero.mp heq0 with h4 | hxyz
      · cases h4
      · exact hxyz
    simp at hxyz
    omega
  have hL := v2_four_mul hx0 hy0 hz0
  have hR : padicValNat 2 (n * (x * y + y * z + z * x)) =
      padicValNat 2 (x * y + y * z + z * x) := by
    rw [padicValNat.mul hn0 hsum0, v2_of_odd hodd, zero_add]
  rw [← hL, heq, hR]

lemma exists_unique_min_pair {vx vy vz : Nat}
    (hxy : vx ≠ vy) (hyz : vy ≠ vz) (hzx : vz ≠ vx) :
    (vx + vy < vy + vz ∧ vx + vy < vz + vx) ∨
    (vy + vz < vx + vy ∧ vy + vz < vz + vx) ∨
    (vz + vx < vx + vy ∧ vz + vx < vy + vz) := by omega

lemma es_odd_not_all_vals_eq {n x y z : Nat}
    (hES : IsES n x y z) (hodd : n % 2 = 1) :
    ¬ (padicValNat 2 x = padicValNat 2 y ∧
       padicValNat 2 y = padicValNat 2 z) := by
  intro ⟨hxy, hyz⟩
  have ⟨hx, hy, hz, _⟩ := hES
  have hx0 : x ≠ 0 := Nat.pos_iff_ne_zero.mp hx
  have hy0 : y ≠ 0 := Nat.pos_iff_ne_zero.mp hy
  have hz0 : z ≠ 0 := Nat.pos_iff_ne_zero.mp hz
  set k := padicValNat 2 x
  have hyk : padicValNat 2 y = k := hxy.symm
  have hzk : padicValNat 2 z = k := (hxy.trans hyz).symm
  set ox := x / 2 ^ k
  set oy := y / 2 ^ k
  set oz := z / 2 ^ k
  have hx' : 2 ^ k * ox = x := by
    simpa [k, ox] using oddPart_mul hx0
  have hy' : 2 ^ k * oy = y := by
    have := oddPart_mul hy0
    rw [hyk] at this
    simpa [oy] using this
  have hz' : 2 ^ k * oz = z := by
    have := oddPart_mul hz0
    rw [hzk] at this
    simpa [oz] using this
  have hox : ox % 2 = 1 := by simpa [k, ox] using oddPart_odd hx0
  have hoy : oy % 2 = 1 := by
    have := oddPart_odd hy0
    rw [hyk] at this
    simpa [oy] using this
  have hoz : oz % 2 = 1 := by
    have := oddPart_odd hz0
    rw [hzk] at this
    simpa [oz] using this
  have hpowkk : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
    rw [pow2_mul]; ring
  have hxy' : x * y = 2 ^ (2 * k) * (ox * oy) := by
    rw [← hx', ← hy']
    calc
      2 ^ k * ox * (2 ^ k * oy) = 2 ^ k * 2 ^ k * (ox * oy) := by ring
      _ = 2 ^ (2 * k) * (ox * oy) := by rw [hpowkk]
  have hyz' : y * z = 2 ^ (2 * k) * (oy * oz) := by
    rw [← hy', ← hz']
    calc
      2 ^ k * oy * (2 ^ k * oz) = 2 ^ k * 2 ^ k * (oy * oz) := by ring
      _ = 2 ^ (2 * k) * (oy * oz) := by rw [hpowkk]
  have hzx' : z * x = 2 ^ (2 * k) * (oz * ox) := by
    rw [← hz', ← hx']
    calc
      2 ^ k * oz * (2 ^ k * ox) = 2 ^ k * 2 ^ k * (oz * ox) := by ring
      _ = 2 ^ (2 * k) * (oz * ox) := by rw [hpowkk]
  have hsum :
      x * y + y * z + z * x =
        2 ^ (2 * k) * (ox * oy + oy * oz + oz * ox) := by
    rw [hxy', hyz', hzx']
    ring
  have hunits : (ox * oy + oy * oz + oz * ox) % 2 = 1 := by
    have h1 : (ox * oy) % 2 = 1 := by rw [Nat.mul_mod, hox, hoy]
    have h2 : (oy * oz) % 2 = 1 := by rw [Nat.mul_mod, hoy, hoz]
    have h3 : (oz * ox) % 2 = 1 := by rw [Nat.mul_mod, hoz, hox]
    omega
  have hparen0 : ox * oy + oy * oz + oz * ox ≠ 0 := by
    intro h0
    have : (ox * oy + oy * oz + oz * ox) % 2 = 0 := by rw [h0]
    omega
  have h2pow : (2 : Nat) ^ (2 * k) ≠ 0 := pow2_ne_zero (2 * k)
  have hvsum : padicValNat 2 (x * y + y * z + z * x) = 2 * k := by
    rw [hsum, padicValNat.mul h2pow hparen0, padicValNat.prime_pow,
      v2_of_odd hunits, add_zero]
  have hbal := es_v2_balance hES hodd
  rw [hyk, hzk, hvsum] at hbal
  omega

lemma es_odd_not_all_vals_distinct {n x y z : Nat}
    (hES : IsES n x y z) (hodd : n % 2 = 1) :
    padicValNat 2 x = padicValNat 2 y ∨
    padicValNat 2 y = padicValNat 2 z ∨
    padicValNat 2 z = padicValNat 2 x := by
  have ⟨hx, hy, hz, _⟩ := hES
  have hx0 : x ≠ 0 := Nat.pos_iff_ne_zero.mp hx
  have hy0 : y ≠ 0 := Nat.pos_iff_ne_zero.mp hy
  have hz0 : z ≠ 0 := Nat.pos_iff_ne_zero.mp hz
  by_cases hxy : padicValNat 2 x = padicValNat 2 y
  · exact Or.inl hxy
  · by_cases hyz : padicValNat 2 y = padicValNat 2 z
    · exact Or.inr (Or.inl hyz)
    · by_cases hzx : padicValNat 2 z = padicValNat 2 x
      · exact Or.inr (Or.inr hzx)
      · exfalso
        have hxyP : x * y ≠ 0 := Nat.mul_ne_zero hx0 hy0
        have hyzP : y * z ≠ 0 := Nat.mul_ne_zero hy0 hz0
        have hzxP : z * x ≠ 0 := Nat.mul_ne_zero hz0 hx0
        have vxy : padicValNat 2 (x * y) =
            padicValNat 2 x + padicValNat 2 y := padicValNat.mul hx0 hy0
        have vyz : padicValNat 2 (y * z) =
            padicValNat 2 y + padicValNat 2 z := padicValNat.mul hy0 hz0
        have vzx : padicValNat 2 (z * x) =
            padicValNat 2 z + padicValNat 2 x := padicValNat.mul hz0 hx0
        have hbal := es_v2_balance hES hodd
        rcases exists_unique_min_pair hxy hyz hzx with hA | hB | hC
        · have h1 : padicValNat 2 (x * y) < padicValNat 2 (y * z) := by
            rw [vxy, vyz]; omega
          have h2 : padicValNat 2 (x * y) < padicValNat 2 (z * x) := by
            rw [vxy, vzx]; omega
          have hv := v2_add_three_unique_min hxyP hyzP hzxP h1 h2
          rw [hv, vxy] at hbal
          omega
        · have hsum' : x * y + y * z + z * x = y * z + z * x + x * y := by ring
          have h1 : padicValNat 2 (y * z) < padicValNat 2 (z * x) := by
            rw [vyz, vzx]; omega
          have h2 : padicValNat 2 (y * z) < padicValNat 2 (x * y) := by
            rw [vyz, vxy]; omega
          have hv := v2_add_three_unique_min hyzP hzxP hxyP h1 h2
          rw [hsum', hv, vyz] at hbal
          omega
        · have hsum' : x * y + y * z + z * x = z * x + x * y + y * z := by ring
          have h1 : padicValNat 2 (z * x) < padicValNat 2 (x * y) := by
            rw [vzx, vxy]; omega
          have h2 : padicValNat 2 (z * x) < padicValNat 2 (y * z) := by
            rw [vzx, vyz]; omega
          have hv := v2_add_three_unique_min hzxP hxyP hyzP h1 h2
          rw [hsum', hv, vzx] at hbal
          omega

lemma es_odd_pair_not_smaller {n x y z : Nat}
    (hES : IsES n x y z) (hodd : n % 2 = 1)
    (hxy : padicValNat 2 x = padicValNat 2 y)
    (hlt : padicValNat 2 x < padicValNat 2 z) : False := by
  have ⟨hx, hy, hz, _⟩ := hES
  have hx0 : x ≠ 0 := Nat.pos_iff_ne_zero.mp hx
  have hy0 : y ≠ 0 := Nat.pos_iff_ne_zero.mp hy
  have hz0 : z ≠ 0 := Nat.pos_iff_ne_zero.mp hz
  have hxyP : x * y ≠ 0 := Nat.mul_ne_zero hx0 hy0
  have hyzP : y * z ≠ 0 := Nat.mul_ne_zero hy0 hz0
  have hzxP : z * x ≠ 0 := Nat.mul_ne_zero hz0 hx0
  have vxy : padicValNat 2 (x * y) =
      padicValNat 2 x + padicValNat 2 y := padicValNat.mul hx0 hy0
  have vyz : padicValNat 2 (y * z) =
      padicValNat 2 y + padicValNat 2 z := padicValNat.mul hy0 hz0
  have vzx : padicValNat 2 (z * x) =
      padicValNat 2 z + padicValNat 2 x := padicValNat.mul hz0 hx0
  have h1 : padicValNat 2 (x * y) < padicValNat 2 (y * z) := by
    rw [vxy, vyz, hxy]; omega
  have h2 : padicValNat 2 (x * y) < padicValNat 2 (z * x) := by
    rw [vxy, vzx, hxy]; omega
  have hv := v2_add_three_unique_min hxyP hyzP hzxP h1 h2
  have hbal := es_v2_balance hES hodd
  rw [hv, vxy, hxy] at hbal
  omega

/-- On an odd-n solution, exactly two of the 2-adic valuations agree, and
    the third is strictly smaller.  After permuting, this is the BL shape
    with `s ≥ 1`. -/
theorem es_odd_two_adic_vals {n x y z : Nat}
    (hES : IsES n x y z) (hodd : n % 2 = 1) :
    (padicValNat 2 x = padicValNat 2 y ∧
      padicValNat 2 z < padicValNat 2 x) ∨
    (padicValNat 2 y = padicValNat 2 z ∧
      padicValNat 2 x < padicValNat 2 y) ∨
    (padicValNat 2 z = padicValNat 2 x ∧
      padicValNat 2 y < padicValNat 2 z) := by
  have hne := es_odd_not_all_vals_eq hES hodd
  have hpair := es_odd_not_all_vals_distinct hES hodd
  rcases hpair with hxy | hyz | hzx
  · have hneq : padicValNat 2 z ≠ padicValNat 2 x := by
      intro h
      exact hne ⟨hxy, hxy.symm.trans h.symm⟩
    have hord : padicValNat 2 z < padicValNat 2 x ∨
        padicValNat 2 x < padicValNat 2 z := Nat.lt_or_gt_of_ne hneq
    rcases hord with hlt | hgt
    · exact Or.inl ⟨hxy, hlt⟩
    · exact False.elim (es_odd_pair_not_smaller hES hodd hxy hgt)
  · have hES' : IsES n y z x := by
      obtain ⟨hx, hy, hz, heq⟩ := hES
      refine ⟨hy, hz, hx, ?_⟩
      convert heq using 1 <;> ring
    have hneq : padicValNat 2 x ≠ padicValNat 2 y := by
      intro h
      exact hne ⟨h, hyz⟩
    have hord : padicValNat 2 x < padicValNat 2 y ∨
        padicValNat 2 y < padicValNat 2 x := Nat.lt_or_gt_of_ne hneq
    rcases hord with hlt | hgt
    · exact Or.inr (Or.inl ⟨hyz, hlt⟩)
    · exact False.elim (es_odd_pair_not_smaller hES' hodd hyz hgt)
  · have hES' : IsES n z x y := by
      obtain ⟨hx, hy, hz, heq⟩ := hES
      refine ⟨hz, hx, hy, ?_⟩
      convert heq using 1 <;> ring
    have hneq : padicValNat 2 y ≠ padicValNat 2 z := by
      intro h
      exact hne ⟨hzx.symm.trans h.symm, h⟩
    have hord : padicValNat 2 y < padicValNat 2 z ∨
        padicValNat 2 z < padicValNat 2 y := Nat.lt_or_gt_of_ne hneq
    rcases hord with hlt | hgt
    · exact Or.inr (Or.inr ⟨hzx, hlt⟩)
    · exact False.elim (es_odd_pair_not_smaller hES' hodd hzx hgt)

lemma odd_mul_mod8_zero {n m : Nat} (hodd : n % 2 = 1)
    (h : (n * m) % 8 = 0) : m % 8 = 0 := by
  have hn : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have hlt : n % 8 < 8 := Nat.mod_lt n (by omega)
    have hpar : (n % 8) % 2 = 1 := by
      have : (n % 8) % 2 = n % 2 := Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)
      rwa [hodd] at this
    omega
  have : ((n % 8) * (m % 8)) % 8 = 0 := by
    rw [← Nat.mul_mod, h]
  have hm : m % 8 < 8 := Nat.mod_lt m (by omega)
  rcases hn with h1 | h3 | h5 | h7
  · rw [h1] at this; omega
  · rw [h3] at this; omega
  · rw [h5] at this; omega
  · rw [h7] at this; omega

lemma eight_dvd_pow2 {k : Nat} (h : 3 ≤ k) : 8 ∣ 2 ^ k := by
  have : (8 : Nat) = 2 ^ 3 := rfl
  rw [this]
  exact pow_dvd_pow (2 : Nat) h

/-- The key congruence (BL 3.4) and even Serre exponent on a single
    2-adic shape `(2^{s+e} r₁, 2^{s+e} r₂, 2^e r₃)`. -/
theorem lemma38_of_two_adic_shape {n r1 r2 r3 s e : Nat}
    (hES : IsES n (2 ^ (s + e) * r1) (2 ^ (s + e) * r2) (2 ^ e * r3))
    (hodd : n % 2 = 1)
    (hr1 : r1 % 2 = 1) (hr2 : r2 % 2 = 1) (hr3 : r3 % 2 = 1)
    (hs : 1 ≤ s) :
    serreInv2 ((r1 : Int) % 8) ((r2 : Int) % 8) ((r3 : Int) % 8)
      ((s % 2 : Nat) : Int) = 1 := by
  have ⟨hx, hy, hz, heq⟩ := hES
  have hprod :
      (2 ^ (s + e) * r1) * (2 ^ (s + e) * r2) * (2 ^ e * r3) =
        2 ^ (2 * s + 3 * e) * (r1 * r2 * r3) := by
    have hp : 2 ^ (s + e) * 2 ^ (s + e) * 2 ^ e = 2 ^ (2 * s + 3 * e) := by
      rw [pow2_mul, pow2_mul]
      congr 1
      ring
    calc
      2 ^ (s + e) * r1 * (2 ^ (s + e) * r2) * (2 ^ e * r3)
          = (2 ^ (s + e) * 2 ^ (s + e) * 2 ^ e) * (r1 * r2 * r3) := by ring
      _ = 2 ^ (2 * s + 3 * e) * (r1 * r2 * r3) := by rw [hp]
  have hLHS : 4 * ((2 ^ (s + e) * r1) * (2 ^ (s + e) * r2) * (2 ^ e * r3)) =
      2 ^ (2 * s + 3 * e + 2) * (r1 * r2 * r3) := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, hprod, ← mul_assoc, pow2_mul]
    congr 1
    ring
  have hxyP : (2 ^ (s + e) * r1) * (2 ^ (s + e) * r2) =
      2 ^ (2 * s + 2 * e) * (r1 * r2) := by
    have hp : 2 ^ (s + e) * 2 ^ (s + e) = 2 ^ (2 * s + 2 * e) := by
      rw [pow2_mul]; congr 1; ring
    calc
      2 ^ (s + e) * r1 * (2 ^ (s + e) * r2)
          = 2 ^ (s + e) * 2 ^ (s + e) * (r1 * r2) := by ring
      _ = 2 ^ (2 * s + 2 * e) * (r1 * r2) := by rw [hp]
  have hyzP : (2 ^ (s + e) * r2) * (2 ^ e * r3) =
      2 ^ (s + 2 * e) * (r2 * r3) := by
    have hp : 2 ^ (s + e) * 2 ^ e = 2 ^ (s + 2 * e) := by
      rw [pow2_mul]; congr 1; ring
    calc
      2 ^ (s + e) * r2 * (2 ^ e * r3)
          = 2 ^ (s + e) * 2 ^ e * (r2 * r3) := by ring
      _ = 2 ^ (s + 2 * e) * (r2 * r3) := by rw [hp]
  have hzxP : (2 ^ e * r3) * (2 ^ (s + e) * r1) =
      2 ^ (s + 2 * e) * (r3 * r1) := by
    have hp : 2 ^ e * 2 ^ (s + e) = 2 ^ (s + 2 * e) := by
      rw [pow2_mul]; congr 1; ring
    calc
      2 ^ e * r3 * (2 ^ (s + e) * r1)
          = 2 ^ e * 2 ^ (s + e) * (r3 * r1) := by ring
      _ = 2 ^ (s + 2 * e) * (r3 * r1) := by rw [hp]
  have hsplit : 2 ^ (2 * s + 2 * e) = 2 ^ (s + 2 * e) * 2 ^ s := by
    rw [pow2_mul]; congr 1; ring
  set inner := 2 ^ s * r1 * r2 + (r1 + r2) * r3
  have hsum :
      (2 ^ (s + e) * r1) * (2 ^ (s + e) * r2) +
        (2 ^ (s + e) * r2) * (2 ^ e * r3) +
        (2 ^ e * r3) * (2 ^ (s + e) * r1) =
      2 ^ (s + 2 * e) * inner := by
    rw [hxyP, hyzP, hzxP, hsplit]
    simp [inner]
    ring
  have hcancel : n * inner = 2 ^ (s + e + 2) * (r1 * r2 * r3) := by
    have hpow0 : 0 < 2 ^ (s + 2 * e) := Nat.pow_pos (by omega)
    have heq' :
        2 ^ (s + 2 * e) * (2 ^ (s + e + 2) * (r1 * r2 * r3)) =
          2 ^ (s + 2 * e) * (n * inner) := by
      have : 2 ^ (2 * s + 3 * e + 2) * (r1 * r2 * r3) =
          n * (2 ^ (s + 2 * e) * inner) := by
        rw [← hLHS, heq, hsum]
      have hexp : 2 * s + 3 * e + 2 = (s + 2 * e) + (s + e + 2) := by ring
      rw [hexp, Nat.pow_add] at this
      convert this using 1 <;> ring
    exact Nat.mul_left_cancel hpow0 heq'.symm
  have hge : 3 ≤ s + e + 2 := by omega
  have hdvd8 : 8 ∣ n * inner := by
    have hL : 8 ∣ 2 ^ (s + e + 2) * (r1 * r2 * r3) :=
      (eight_dvd_pow2 hge).trans ⟨r1 * r2 * r3, rfl⟩
    rwa [hcancel]
  have hmod : (n * inner) % 8 = 0 := Nat.mod_eq_zero_of_dvd hdvd8
  have hinner : inner % 8 = 0 := odd_mul_mod8_zero hodd hmod
  have ha : ((r1 : Int) % 8) ∈ oddRes :=
    mem_oddRes_of_odd _ (by
      have := Int.natCast_mod r1 2
      rw [hr1] at this
      simpa using this.symm)
  have hb : ((r2 : Int) % 8) ∈ oddRes :=
    mem_oddRes_of_odd _ (by
      have := Int.natCast_mod r2 2
      rw [hr2] at this
      simpa using this.symm)
  have hc : ((r3 : Int) % 8) ∈ oddRes :=
    mem_oddRes_of_odd _ (by
      have := Int.natCast_mod r3 2
      rw [hr3] at this
      simpa using this.symm)
  have hts := pow2_mod8 s hs
  have hcong :
      (((2 : Int) ^ s % 8) * ((r1 : Int) % 8) * ((r2 : Int) % 8) +
        (((r1 : Int) % 8) + ((r2 : Int) % 8)) * ((r3 : Int) % 8)) % 8 = 0 := by
    have hm : (2 ^ s * r1 * r2 + (r1 + r2) * r3) % 8 = 0 := by
      simpa [inner] using hinner
    have hN : ((2 ^ s * r1 * r2 + (r1 + r2) * r3 : Nat) : Int) % 8 = 0 :=
      by exact_mod_cast hm
    have hcast : ((2 ^ s * r1 * r2 + (r1 + r2) * r3 : Nat) : Int) =
        (2 : Int) ^ s * r1 * r2 + ((r1 : Int) + r2) * r3 := by
      push_cast
      rfl
    have hred :
        ((2 : Int) ^ s * r1 * r2 + ((r1 : Int) + r2) * r3) % 8 =
          (((2 : Int) ^ s % 8) * ((r1 : Int) % 8) * ((r2 : Int) % 8) +
            (((r1 : Int) % 8) + ((r2 : Int) % 8)) * ((r3 : Int) % 8)) % 8 := by
      simp [Int.mul_emod, Int.add_emod]
    rw [← hred, ← hcast]
    exact hN
  exact serreInv2_eq_one_of_residue _ _ _ _ _ ha hb hc hts hcong

lemma lemma38_exists_of_shape {n x y z : Nat}
    (hES : IsES n x y z) (hodd : n % 2 = 1)
    (hxy : padicValNat 2 x = padicValNat 2 y)
    (hlt : padicValNat 2 z < padicValNat 2 x) :
    ∃ a b c sm : Int,
      a ∈ oddRes ∧ b ∈ oddRes ∧ c ∈ oddRes ∧
      (sm = 0 ∨ sm = 1) ∧
      serreInv2 a b c sm = 1 := by
  have ⟨hx, hy, hz, _⟩ := hES
  have hx0 : x ≠ 0 := Nat.pos_iff_ne_zero.mp hx
  have hy0 : y ≠ 0 := Nat.pos_iff_ne_zero.mp hy
  have hz0 : z ≠ 0 := Nat.pos_iff_ne_zero.mp hz
  let e := padicValNat 2 z
  let s := padicValNat 2 x - padicValNat 2 z
  let r1 := x / 2 ^ padicValNat 2 x
  let r2 := y / 2 ^ padicValNat 2 x
  let r3 := z / 2 ^ padicValNat 2 z
  have hs : 1 ≤ s := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
  have hse : s + e = padicValNat 2 x := Nat.sub_add_cancel (Nat.le_of_lt hlt)
  have hxeq : x = 2 ^ (s + e) * r1 := by
    rw [hse]; exact (oddPart_mul hx0).symm
  have hyeq : y = 2 ^ (s + e) * r2 := by
    have hse' : s + e = padicValNat 2 y := hse.trans hxy
    have hr2 : r2 = y / 2 ^ padicValNat 2 y := by
      change y / 2 ^ padicValNat 2 x = y / 2 ^ padicValNat 2 y
      rw [hxy]
    rw [hse', hr2]
    exact (oddPart_mul hy0).symm
  have hzeq : z = 2 ^ e * r3 := (oddPart_mul hz0).symm
  have hr1 : r1 % 2 = 1 := oddPart_odd hx0
  have hr2 : r2 % 2 = 1 := by
    change y / 2 ^ padicValNat 2 x % 2 = 1
    rw [hxy]
    exact oddPart_odd hy0
  have hr3 : r3 % 2 = 1 := oddPart_odd hz0
  have hES' : IsES n (2 ^ (s + e) * r1) (2 ^ (s + e) * r2) (2 ^ e * r3) := by
    rw [← hxeq, ← hyeq, ← hzeq]; exact hES
  refine ⟨(r1 : Int) % 8, (r2 : Int) % 8, (r3 : Int) % 8,
    ((s % 2 : Nat) : Int), ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_oddRes_of_odd _ (by
      have := Int.natCast_mod r1 2; rw [hr1] at this; simpa using this.symm)
  · exact mem_oddRes_of_odd _ (by
      have := Int.natCast_mod r2 2; rw [hr2] at this; simpa using this.symm)
  · exact mem_oddRes_of_odd _ (by
      have := Int.natCast_mod r3 2; rw [hr3] at this; simpa using this.symm)
  · rcases Nat.mod_two_eq_zero_or_one s with h0 | h1
    · simp [h0]
    · simp [h1]
  · exact lemma38_of_two_adic_shape hES' hodd hr1 hr2 hr3 hs

/-- **BL Lemma 3.8** on a natural-number solution at odd `n`: after extracting
    the 2-adic shape of BL §3.3.4, Serre's 2-adic invariant is 1. -/
theorem lemma38_of_nat_solution {n x y z : Nat}
    (hES : IsES n x y z) (hodd : n % 2 = 1) :
    ∃ a b c sm : Int,
      a ∈ oddRes ∧ b ∈ oddRes ∧ c ∈ oddRes ∧
      (sm = 0 ∨ sm = 1) ∧
      serreInv2 a b c sm = 1 := by
  rcases es_odd_two_adic_vals hES hodd with hxy | hyz | hzx
  · exact lemma38_exists_of_shape hES hodd hxy.1 hxy.2
  · exact lemma38_exists_of_shape (isES_cycle hES) hodd hyz.1 hyz.2
  · exact lemma38_exists_of_shape (isES_cycle (isES_cycle hES)) hodd hzx.1 hzx.2

/-- Local signs of a Nat ES solution at an odd prime: inv_∞ = −1 (Lemma 3.1)
    and inv₂ = 1 (Lemma 3.8).  Combined with Lemma 3.5 at good places and
    `hilbert_reciprocity_odd_coprime`, Hilbert reciprocity forces the p-adic
    symbol once it is identified with Serre's formula. -/
theorem es_local_signs {p x y z : Nat} [Fact p.Prime]
    (hES : IsES p x y z) (hp2 : p ≠ 2) :
    hilbertInf (-(x : ℤ)) (-(y : ℤ)) = -1 ∧
    ∃ a b c sm : ℤ, serreInv2 a b c sm = 1 := by
  refine ⟨lemma31_of_isES hES, ?_⟩
  obtain ⟨a, b, c, sm, _, _, _, _, h⟩ :=
    lemma38_of_nat_solution hES
      ((Nat.Prime.eq_two_or_odd Fact.out).resolve_left hp2)
  exact ⟨a, b, c, sm, h⟩

/-! ## Norm-form bridge: d=1 shifts and `x² + 4y²` -/

/-- Values of the principal form of discriminant −16. -/
def RepresentedX2p4Y2 (n : Nat) : Prop :=
  ∃ x y : Nat, n = x ^ 2 + 4 * y ^ 2

/-- An odd 3-mod-4-free number is a sum of two squares, hence of the form
    `x² + 4y²`. -/
theorem odd_three_mod_four_free_is_form {n : Nat} (_hpos : 0 < n)
    (hodd : n % 2 = 1)
    (hfree : ThreeModFourFree n) :
    RepresentedX2p4Y2 n := by
  have hsq : ∃ x y : Nat, n = x ^ 2 + y ^ 2 := by
    refine (Nat.eq_sq_add_sq_iff).mpr ?_
    intro q hq hq3
    have hqP : IsPrime q := isPrime_iff_prime.mpr (Nat.prime_of_mem_primeFactors hq)
    have hdvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq
    exact False.elim (hfree q hqP hdvd hq3)
  obtain ⟨x, y, hxy⟩ := hsq
  have sq_mod2 : ∀ t : Nat, t ^ 2 % 2 = t % 2 := by
    intro t
    have : t % 2 = 0 ∨ t % 2 = 1 := Nat.mod_two_eq_zero_or_one t
    rcases this with h | h <;> rw [Nat.pow_two, Nat.mul_mod, h]
  have hpar : x % 2 = 0 ∨ y % 2 = 0 := by
    have : (x ^ 2 + y ^ 2) % 2 = 1 := by rw [← hxy]; exact hodd
    rw [Nat.add_mod, sq_mod2, sq_mod2] at this
    have hx2 : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
    have hy2 : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
    omega
  rcases hpar with hx | hy
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hx
    refine ⟨y, k, ?_⟩
    subst hk
    rw [hxy, Nat.pow_two, Nat.pow_two]
    ring
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hy
    refine ⟨x, k, ?_⟩
    subst hk
    rw [hxy, Nat.pow_two, Nat.pow_two]
    ring

/-- The totally-split condition at bound `D`: every shift `p + 4a²` (`a ≤ D`)
    is 3-mod-4-free, hence (being odd for hard `p`) represented by
    `x² + 4y²`.  Distinct from the d=1 escapee set (plan §4s). -/
def D1ShiftForm (p D : Nat) : Prop :=
  ∀ a, 0 < a → a ≤ D → ThreeModFourFree (p + 4 * a * a)

theorem d1_shift_odd {p a : Nat} (h8 : p % 2 = 1) :
    (p + 4 * a * a) % 2 = 1 := by
  have h4 : 4 * a * a % 2 = 0 := by
    rw [show 4 * a * a = 4 * (a * a) from by ring, Nat.mul_mod]
    simp
  rw [Nat.add_mod, h4, h8]

/-- **Bridge.** The totally-split condition at bound `D` implies every shift
    is simultaneously represented by the form `x² + 4y²`. -/
theorem d1_escapee_shifts_are_forms {p D : Nat}
    (hp : 0 < p) (h8 : p % 2 = 1)
    (hform : D1ShiftForm p D) :
    ∀ a, 0 < a → a ≤ D → RepresentedX2p4Y2 (p + 4 * a * a) := by
  intro a ha hA
  have hpos : 0 < p + 4 * a * a := Nat.add_pos_left hp (4 * a * a)
  exact odd_three_mod_four_free_is_form hpos (d1_shift_odd h8) (hform a ha hA)

/-- d=1, a=1 landing is exactly the failure of 3-mod-4-freeness of `p+4`. -/
theorem d1_a1_iff_not_free {p : Nat} (_hp : 0 < p) :
    (∃ q, 3 ≤ q ∧ (q + 1) % 4 = 0 ∧ q ∣ p + 4) ↔ ¬ ThreeModFourFree (p + 4) := by
  constructor
  · intro ⟨q, hq3, hmod, hdvd⟩ hfree
    exact not_d1_a1_of_free hfree hq3 hmod hdvd
  · intro hfree
    simp only [ThreeModFourFree, not_forall] at hfree
    obtain ⟨q, hqP, hdvd, hq3⟩ := hfree
    have hq4 : q % 4 = 3 := by simpa using hq3
    have hq2 : 2 ≤ q := hqP.1
    have hq3' : 3 ≤ q := by omega
    have hmod : (q + 1) % 4 = 0 := by omega
    exact ⟨q, hq3', hmod, hdvd⟩

