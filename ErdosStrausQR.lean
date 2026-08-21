/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  Layer B (Mathlib).  See README.md.

  Build via `lake build` against the pinned Mathlib.  Discharges the
  Layer-A reciprocity interface (`BL.InvariantData.reciprocity`) and
  identifies `IsPrime` with `Nat.Prime`.

  1. `IsPrime` ↔ `Nat.Prime`.
  2. Yamamoto fingerprint: Type-I witness with prime modulus `q = 4ad − 1`
     forces `(p / q) = (−a / q)`; if `a` is a square and `q ≡ 3 (mod 4)`
     then `(p / q) = −1` (Schinzel/Mordell Type-I obstruction).
  3. Quadratic reciprocity as the odd-place discharge of Bright–Loughran §4;
     verified instances at `p = 1009`.
  4. `BL.lemma32` specialised to `Nat.Prime`.

  Hilbert symbols are not in Mathlib, so `InvariantData.reciprocity` remains
  an interface; the odd-odd content it reduces to is proved here.
  Hard-class residues as literal squares `1², 11², …` is
  `ES.hardClass_residue_sq` in the core file.
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import ErdosStraus
import BrightLoughran

open ZMod ES BL

/-! ## `IsPrime` is Mathlib's `Nat.Prime` -/

theorem isPrime_iff_prime {p : Nat} : IsPrime p ↔ Nat.Prime p := by
  constructor
  · intro h; exact Nat.prime_def.mpr h
  · intro h; exact Nat.prime_def.mp h

theorem exists_prime_factor_mathlib (n : Nat) (hn : 2 ≤ n) :
    ∃ p, Nat.Prime p ∧ p ∣ n :=
  Nat.exists_prime_and_dvd (by omega)

theorem landingHypothesis_prime :
    LandingHypothesis ↔
      ∀ p : Nat, Nat.Prime p → ∃ a c d m, Witness p a c d m := by
  constructor
  · intro H p hp; exact H p (isPrime_iff_prime.mpr hp)
  · intro H p hp; exact H p (isPrime_iff_prime.mp hp)

theorem landing_below_10000_prime {p : Nat} (hp : Nat.Prime p) (h : p < 10000) :
    ∃ a c d m, Witness p a c d m :=
  landing_below_10000 (isPrime_iff_prime.mpr hp) h

/-! ## Yamamoto fingerprint (Type I) -/

lemma legendreSym_eq_of_cast {q : Nat} [Fact q.Prime] {a b : ℤ}
    (h : (a : ZMod q) = (b : ZMod q)) :
    legendreSym q a = legendreSym q b := by
  simp [legendreSym, h]

theorem typeI_legendre {p a d m q : Nat} [Fact q.Prime]
    (hw : Witness p a 1 d m) (hq : q = 4 * a * d - 1)
    (_hpq : ((p : ℤ) : ZMod q) ≠ 0) :
    legendreSym q p = legendreSym q (-(a : ℤ)) := by
  have hEq : (4 * a * d - 1) * m = p + a := witness_typeI hw
  have hdvd : q ∣ p + a := ⟨m, by rw [hq]; exact hEq.symm⟩
  have hsum : ((p + a : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (p + a) q).2 hdvd
  have hadd : (p : ZMod q) + (a : ZMod q) = 0 := by
    simpa [Nat.cast_add] using hsum
  have hneg : (p : ZMod q) = -(a : ZMod q) := eq_neg_of_add_eq_zero_left hadd
  apply legendreSym_eq_of_cast
  rw [Int.cast_neg]
  simpa using hneg

/-- **Schinzel/Yamamoto Type-I obstruction.** A covering witness with prime
    modulus `q = 4ad − 1 ≡ 3 (mod 4)` and square `a` forces `p` to be a
    quadratic non-residue mod `q`. -/
theorem typeI_nonresidue_of_square_a {p a d m q : Nat} [Fact q.Prime]
    (hw : Witness p a 1 d m) (hq : q = 4 * a * d - 1)
    (hq3 : q % 4 = 3) (ha : IsSquare (a : ℤ))
    (hpq : ((p : ℤ) : ZMod q) ≠ 0) (hq2 : q ≠ 2) :
    legendreSym q p = -1 := by
  have hmain := typeI_legendre hw hq hpq
  have hneg : legendreSym q (-(a : ℤ)) =
      legendreSym q (-1) * legendreSym q a := by
    rw [show (-(a : ℤ) = (-1) * a) by ring, legendreSym.mul]
  have hneg1 : legendreSym q (-1) = -1 := by
    rw [legendreSym.at_neg_one hq2, χ₄_nat_three_mod_four hq3]
  have ha0 : ((a : ℤ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvd : q ∣ a := (ZMod.natCast_eq_zero_iff a q).1 (by simpa using hz)
    obtain ⟨ha', _hc, hd', _hm, _hw⟩ := hw
    have hqa : q ∣ 4 * a * d := dvd_trans hdvd ⟨4 * d, by ring⟩
    have hqid : q ∣ 4 * a * d - 1 := by rw [hq]
    have h1 : q ∣ 1 := by
      have := Nat.dvd_sub hqa hqid
      have hsub : 4 * a * d - (4 * a * d - 1) = 1 := by
        have : 1 ≤ 4 * a * d := by
          have : 0 < 4 * a * d := Nat.mul_pos (Nat.mul_pos (by omega) ha') hd'
          omega
        omega
      rwa [hsub] at this
    exact Nat.Prime.ne_one (show Nat.Prime q from Fact.out) (Nat.dvd_one.mp h1)
  have hasq : legendreSym q a = 1 :=
    (legendreSym.eq_one_iff (p := q) ha0).2 (by
      obtain ⟨r, hr⟩ := ha
      refine ⟨(r : ZMod q), ?_⟩
      simp [hr])
  calc
    legendreSym q p = legendreSym q (-(a : ℤ)) := hmain
    _ = legendreSym q (-1) * legendreSym q a := hneg
    _ = -1 * 1 := by rw [hneg1, hasq]
    _ = -1 := by ring

/-! ## Quadratic reciprocity: odd-place BL interface -/

theorem quadratic_reciprocity_odd
    {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hne : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hne

lemma prime_11 : Nat.Prime 11 :=
  isPrime_iff_prime.mp (isPrimeB_iff.mp (by native_decide : isPrimeB 11 = true))

lemma prime_1009 : Nat.Prime 1009 :=
  isPrime_iff_prime.mp (isPrimeB_iff.mp (by native_decide : isPrimeB 1009 = true))

private theorem fact_prime_eleven : Fact (Nat.Prime 11) := ⟨prime_11⟩
private theorem fact_prime_1009 : Fact (Nat.Prime 1009) := ⟨prime_1009⟩

attribute [local instance] fact_prime_eleven fact_prime_1009

theorem thm12_instance_1009_mathlib :
    legendreSym 1009 ((1009 - (3 * 92) % 1009) % 1009 : ℕ) = -1 := by
  native_decide

theorem witness_fingerprint_1009_mathlib :
    legendreSym 11 (1009 : ℤ) = -1 := by
  native_decide

theorem witness_1009_typeI_symbol :
    legendreSym 11 (1009 : ℤ) = legendreSym 11 (-3) := by
  have hw : Witness 1009 3 1 1 92 :=
    ⟨by omega, by omega, by omega, by omega, by decide⟩
  have hq : (11 : Nat) = 4 * 3 * 1 - 1 := by decide
  have hpq : ((1009 : ℤ) : ZMod 11) ≠ 0 := by decide
  simpa using typeI_legendre (q := 11) hw hq hpq

set_option maxRecDepth 100000 in
theorem reciprocity_1009_11 :
    legendreSym 1009 11 = legendreSym 11 1009 := by
  have hp4 : (1009 : ℕ) % 4 = 1 := by native_decide
  have hq2 : (11 : ℕ) ≠ 2 := by native_decide
  exact legendreSym.quadratic_reciprocity_one_mod_four (p := 1009) (q := 11) hp4 hq2

/-! ## Lemma 3.2 at a Mathlib prime -/

theorem lemma32_of_prime (p : Nat) (hp : Nat.Prime p)
    (n' a1 a2 a3 : ℤ) (b b1 b2 b3 : Nat) (hb : b ≤ 1)
    (hn : ¬ (p : ℤ) ∣ n') (h1 : ¬ (p : ℤ) ∣ a1) (h2 : ¬ (p : ℤ) ∣ a2)
    (hord : b1 ≤ b2 ∧ b2 ≤ b3)
    (heq : 4 * (a1 * a2 * a3) * (p : ℤ) ^ (b1 + b2 + b3)
         = n' * (a1 * a2 * (p : ℤ) ^ (b1 + b2 + b))
           + n' * (a1 * a3 * (p : ℤ) ^ (b1 + b3 + b))
           + n' * (a2 * a3 * (p : ℤ) ^ (b2 + b3 + b))) :
    b1 = b2 ∨ b2 = b3 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine BL.lemma32 (p := (p : ℤ)) (hp := by exact_mod_cast hp.pos) ?_ n' a1 a2 a3
    b b1 b2 b3 hb hn h1 h2 hord heq
  intro x y hxy
  exact (Prime.dvd_mul hpZ).mp hxy
