/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  Layer A (core).  See README.md.

  Bare Lean ≥ 4.33.0, no imports.  Axioms: propext, Quot.sound, plus
  Lean.ofReduceBool for the native_decide instances (see README audit).
  Mathlib-backed reciprocity, `Nat.Prime` equivalence, and the identification
  of the six hard classes with quadratic residues live in Layer B
  (`ErdosStrausQR.lean`).

  Contents:
  1. `IsES n x y z`   : cleared-denominator form of 4/n = 1/x + 1/y + 1/z.
  2. `Witness n a c d m` : the derived covering condition  c·n + a + m = 4acdm
     (equivalently q = 4acd − 1 divides c·n + a, with m the cofactor).
  3. `witness_sound`  : a witness yields the explicit solution
     (x, y, z) = (adm, n·acd, n·cdm).                       [main identity]
  4. `scale`          : a solution for p lifts to any multiple of p.
  5. `exists_prime_factor` : every n ≥ 2 has a prime factor (self-contained).
  6. `LandingHypothesis`   : every prime has a witness (Track B's open target).
  7. `conditional_qed`     : LandingHypothesis → Erdős–Straus.   [machine-checked]
  8. Bounded search `hasWitness` + soundness, and `native_decide` verification
     that every prime below 10000 has a witness (instance of the hypothesis).
  9. Boolean–Prop bridges: `isPrimeB_iff`, `isHardClass_iff`, and the genuine
     instance `landing_below_10000` of the landing hypothesis on [2, 10000).
-/

namespace ES

/-- `4/n = 1/x + 1/y + 1/z` in cleared form, with positivity. -/
def IsES (n x y z : Nat) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * (x*y*z) = n * (x*y + y*z + z*x)

/-- The covering witness condition, subtraction-free:
    `c·n + a + m = 4·a·c·d·m`, i.e. `(4acd − 1) · m = c·n + a`. -/
def Witness (n a c d m : Nat) : Prop :=
  0 < a ∧ 0 < c ∧ 0 < d ∧ 0 < m ∧ c*n + a + m = 4*(a*c*d*m)

theorem mul_pos' {x y : Nat} (hx : 0 < x) (hy : 0 < y) : 0 < x * y :=
  Nat.mul_pos hx hy

/-- The witness equation is equivalent to `q · m = c·n + a` with `q = 4acd − 1`. -/
theorem witness_cofactor {n a c d m : Nat} (h : Witness n a c d m) :
    (4 * a * c * d - 1) * m = c * n + a := by
  obtain ⟨ha, hc, hd, hm, hw⟩ := h
  have hq1 : 1 ≤ 4 * a * c * d := by
    have : 0 < 4 * a * c * d :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) ha) hc) hd
    omega
  have hassoc : 4 * (a * c * d * m) = (4 * a * c * d) * m := by
    simp [Nat.mul_assoc]
  have hsum : c * n + a + m = (4 * a * c * d) * m := by
    rw [hw, hassoc]
  have hsplit : (4 * a * c * d) * m = (4 * a * c * d - 1) * m + m := by
    have h2 : (4 * a * c * d - 1) + 1 = 4 * a * c * d := Nat.sub_add_cancel hq1
    calc (4 * a * c * d) * m
        = ((4 * a * c * d - 1) + 1) * m := by rw [h2]
      _ = (4 * a * c * d - 1) * m + m := by rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Type I (`c = 1`): `q · m = n + a` with `q = 4ad − 1`. -/
theorem witness_typeI {n a d m : Nat} (h : Witness n a 1 d m) :
    (4 * a * d - 1) * m = n + a := by
  have := witness_cofactor h
  simpa [Nat.mul_one, Nat.one_mul] using this

/-- The witness modulus `q = 4acd − 1` is always coprime to `c`. -/
theorem gcd_witness_c {a c d : Nat} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    Nat.gcd (4 * a * c * d - 1) c = 1 := by
  have hle : 1 ≤ 4 * a * c * d := by
    have : 0 < 4 * a * c * d :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) ha) hc) hd
    omega
  have g4 : Nat.gcd (4 * a * c * d - 1) c ∣ 4 * a * c * d :=
    Nat.dvd_trans (Nat.gcd_dvd_right _ _) ⟨4 * a * d, by
      simp [Nat.mul_comm, Nat.mul_left_comm]⟩
  have gq : Nat.gcd (4 * a * c * d - 1) c ∣ 4 * a * c * d - 1 :=
    Nat.gcd_dvd_left _ _
  have g1 : Nat.gcd (4 * a * c * d - 1) c ∣ 1 := by
    have hsub : 4 * a * c * d - (4 * a * c * d - 1) = 1 := by omega
    have := Nat.dvd_sub g4 gq
    rwa [hsub] at this
  exact Nat.dvd_one.mp g1

/-- **Main identity.** A witness yields the explicit Erdős–Straus solution
    `4/n = 1/(adm) + 1/(n·acd) + 1/(n·cdm)`. -/
theorem witness_sound {n a c d m : Nat} (hn : 0 < n)
    (h : Witness n a c d m) :
    IsES n (a*d*m) (n*(a*c*d)) (n*(c*d*m)) := by
  obtain ⟨ha, hc, hd, hm, hw⟩ := h
  refine ⟨mul_pos' (mul_pos' ha hd) hm,
          mul_pos' hn (mul_pos' (mul_pos' ha hc) hd),
          mul_pos' hn (mul_pos' (mul_pos' hc hd) hm), ?_⟩
  -- Multiply the witness equation by n²·a·c·d²·m; the goal is that equation
  -- after distribution and AC-normalization.
  have key : (c*n + a + m) * (n*n*a*c*d*d*m)
           = (4*(a*c*d*m)) * (n*n*a*c*d*d*m) := by rw [hw]
  simp only [Nat.add_mul, Nat.mul_add] at key ⊢
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at key ⊢
  omega

/-- Witness solutions are Bright–Loughran Type-2: the last two coordinates
    are multiples of `n`, with unit parts `acd` and `cdm`. -/
theorem witness_type2 {n a c d m : Nat} (hn : 0 < n) (h : Witness n a c d m) :
    IsES n (a * d * m) (n * (a * c * d)) (n * (c * d * m)) ∧
      n ∣ n * (a * c * d) ∧ n ∣ n * (c * d * m) :=
  ⟨witness_sound hn h, Nat.dvd_mul_right n _, Nat.dvd_mul_right n _⟩

/-! ## One-slot family (Elsholtz–Tao Type I)

Elsholtz–Tao Type II is the existing `Witness` (n divides two coordinates).
Type I is the complementary shape: n divides exactly one coordinate.  This is
the plan's second covering family `n ≡ −f (mod 4ad)` with `f ∣ 4a²d+1`. -/

/-- One-slot covering parameters: `n + f = 4adm` and `f ∣ 4a²d + 1`,
    with `b = m·e − a > 0` for `e = (4a²d+1)/f`. -/
def OneSlot (n a d f m : Nat) : Prop :=
  0 < n ∧ 0 < a ∧ 0 < d ∧ 0 < f ∧ 0 < m ∧
    f ∣ 4 * a * a * d + 1 ∧
    n + f = 4 * a * d * m ∧
    a < m * ((4 * a * a * d + 1) / f)

theorem gcd_oneSlot_f {a d f : Nat} (_ha : 0 < a) (_hd : 0 < d)
    (h : f ∣ 4 * a * a * d + 1) :
    Nat.gcd f (4 * a * d) = 1 := by
  have g_f : Nat.gcd f (4 * a * d) ∣ 4 * a * a * d + 1 :=
    Nat.dvd_trans (Nat.gcd_dvd_left _ _) h
  have g_mod : Nat.gcd f (4 * a * d) ∣ 4 * a * d := Nat.gcd_dvd_right _ _
  have g_sq : Nat.gcd f (4 * a * d) ∣ 4 * a * a * d :=
    Nat.dvd_trans g_mod ⟨a, by simp [Nat.mul_comm, Nat.mul_left_comm]⟩
  have g1 : Nat.gcd f (4 * a * d) ∣ 1 := by
    have hsub : (4 * a * a * d + 1) - 4 * a * a * d = 1 := by omega
    have := Nat.dvd_sub g_f g_sq
    rwa [hsub] at this
  exact Nat.dvd_one.mp g1

theorem oneSlot_key {n a d f m : Nat} (h : OneSlot n a d f m) :
    4 * a * (m * ((4 * a * a * d + 1) / f) - a) * m * d
      = n * (a + (m * ((4 * a * a * d + 1) / f) - a)) + m := by
  obtain ⟨_, _, _, hf, hm, hdiv, hnm, hbpos⟩ := h
  let e := (4 * a * a * d + 1) / f
  let b := m * e - a
  change 4 * a * b * m * d = n * (a + b) + m
  have hef : e * f = 4 * a * a * d + 1 := Nat.div_mul_cancel hdiv
  have hle : a ≤ m * e := Nat.le_of_lt hbpos
  have hab : a + b = m * e := by
    rw [Nat.add_comm]; exact Nat.sub_add_cancel hle
  have hf1 : 1 ≤ e * f := by
    have he0 : 0 < e := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _) hdiv) hf
    have : 0 < e * f := Nat.mul_pos he0 hf
    omega
  have h4eq : 4 * a * a * d = e * f - 1 :=
    (Nat.add_sub_cancel (4 * a * a * d) 1).symm.trans
      (congrArg (fun t => t - 1) hef.symm)
  have hdist : 4 * a * (m * e - a) = 4 * a * (m * e) - 4 * a * a :=
    Nat.mul_sub_left_distrib (4 * a) (m * e) a
  have hdist' : 4 * a * (m * e - a) * d
      = 4 * a * (m * e) * d - 4 * a * a * d := by
    rw [hdist, Nat.mul_sub_right_distrib]
  have hcancel : 4 * a * b * d = n * e + 1 := by
    change 4 * a * (m * e - a) * d = n * e + 1
    rw [hdist']
    have hL : 4 * a * (m * e) * d = e * (4 * a * d * m) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have : e * (4 * a * d * m) - (e * f - 1) = n * e + 1 := by
      rw [← hnm]
      have hsub : e * (n + f) - (e * f - 1) = e * n + 1 := by
        rw [Nat.mul_add]
        have hassoc : e * n + e * f - (e * f - 1)
            = e * n + (e * f - (e * f - 1)) :=
          Nat.add_sub_assoc (Nat.sub_le (e * f) 1) (e * n)
        rw [hassoc]
        have h1 : e * f - (e * f - 1) = 1 := by
          apply (Nat.sub_eq_iff_eq_add (Nat.sub_le _ _)).2
          rw [Nat.add_comm]
          exact (Nat.sub_add_cancel hf1).symm
        rw [h1]
      simpa [Nat.mul_comm] using hsub
    rw [hL, h4eq]
    exact this
  have hR : n * (a + b) + m = m * (n * e + 1) := by
    rw [hab]
    calc n * (m * e) + m
        = n * m * e + m := by simp [Nat.mul_assoc]
      _ = m * (n * e) + m * 1 := by
          simp [Nat.mul_left_comm, Nat.mul_assoc]
      _ = m * (n * e + 1) := by simp [Nat.mul_add]
  have hL : 4 * a * b * m * d = m * (4 * a * b * d) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hL, hcancel, hR]

/-- **One-slot identity.** Parameters yield
    `4/n = 1/(abd n) + 1/(acd) + 1/(bcd)` with `c = m`, `e = (4a²d+1)/f`,
    `b = me − a`. -/
theorem oneSlot_sound {n a d f m : Nat} (h : OneSlot n a d f m) :
    IsES n
      (a * (m * ((4 * a * a * d + 1) / f) - a) * d * n)
      (a * m * d)
      ((m * ((4 * a * a * d + 1) / f) - a) * m * d) := by
  obtain ⟨hn, ha, hd, hf, hm, hdiv, hnm, hbpos⟩ := h
  have hb0 : 0 < m * ((4 * a * a * d + 1) / f) - a := Nat.sub_pos_of_lt hbpos
  refine ⟨mul_pos' (mul_pos' (mul_pos' ha hb0) hd) hn,
          mul_pos' (mul_pos' ha hm) hd,
          mul_pos' (mul_pos' hb0 hm) hd, ?_⟩
  have hkey := oneSlot_key ⟨hn, ha, hd, hf, hm, hdiv, hnm, hbpos⟩
  -- Multiply the one-slot identity by `a·b·m·d²·n` to recover `4xyz = n(xy+yz+zx)`.
  have key :
      (4 * a * (m * ((4 * a * a * d + 1) / f) - a) * m * d) *
        (a * (m * ((4 * a * a * d + 1) / f) - a) * m * d * d * n)
    = (n * (a + (m * ((4 * a * a * d + 1) / f) - a)) + m) *
        (a * (m * ((4 * a * a * d + 1) / f) - a) * m * d * d * n) := by
    rw [hkey]
  simp only [Nat.add_mul, Nat.mul_add] at key ⊢
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at key ⊢
  omega

theorem oneSlot_es {n a d f m : Nat} (h : OneSlot n a d f m) :
    ∃ x y z, IsES n x y z :=
  ⟨_, _, _, oneSlot_sound h⟩

/-- **Scaling.** A solution for `p` lifts to a solution for `p*t`. -/
theorem scale {p x y z : Nat} (t : Nat) (ht : 0 < t)
    (h : IsES p x y z) : IsES (p*t) (t*x) (t*y) (t*z) := by
  obtain ⟨hx, hy, hz, he⟩ := h
  refine ⟨mul_pos' ht hx, mul_pos' ht hy, mul_pos' ht hz, ?_⟩
  -- Multiply `he` by t³.
  have key : (4 * (x*y*z)) * (t*t*t) = (p * (x*y + y*z + z*x)) * (t*t*t) := by
    rw [he]
  simp only [Nat.add_mul, Nat.mul_add] at key ⊢
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at key ⊢
  omega

/-- Primality, spelled out (core Lean has no `Nat.Prime`). -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ q : Nat, q ∣ p → q = 1 ∨ q = p

/-- Every `n ≥ 2` has a prime factor. Bounded induction, core-only. -/
theorem exists_prime_factor_aux :
    ∀ k n : Nat, n ≤ k → 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n := by
  intro k
  induction k with
  | zero => intro n hn h2; omega
  | succ k ih =>
    intro n hn h2
    by_cases hp : ∀ q : Nat, q ∣ n → q = 1 ∨ q = n
    · exact ⟨n, ⟨h2, hp⟩, Nat.dvd_refl n⟩
    · obtain ⟨q, hq'⟩ := Classical.not_forall.mp hp
      obtain ⟨hq, hq2⟩ := Classical.not_imp.mp hq'
      obtain ⟨hq1, hqn⟩ := not_or.mp hq2
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · subst h0
          have : n = 0 := Nat.eq_zero_of_zero_dvd hq
          omega
        · exact h0
      have hqle : q ≤ n := Nat.le_of_dvd (by omega) hq
      have hqlt : q < n := Nat.lt_of_le_of_ne hqle hqn
      have hq2' : 2 ≤ q := by omega
      obtain ⟨p, hp', hpq⟩ := ih q (by omega) hq2'
      exact ⟨p, hp', Nat.dvd_trans hpq hq⟩

theorem exists_prime_factor (n : Nat) (hn : 2 ≤ n) :
    ∃ p, IsPrime p ∧ p ∣ n :=
  exists_prime_factor_aux n n (Nat.le_refl n) hn

/-- Euclid's lemma, from the core definition of `IsPrime`. -/
theorem IsPrime.dvd_or_dvd {p m n : Nat} (hp : IsPrime p) (h : p ∣ m * n) :
    p ∣ m ∨ p ∣ n := by
  have hd : Nat.gcd p m ∣ p := Nat.gcd_dvd_left p m
  rcases hp.2 (Nat.gcd p m) hd with h1 | hp'
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  · exact Or.inl (hp' ▸ Nat.gcd_dvd_right p m)

/-- **The open target (Track B).** Every prime admits a covering witness.
    This is the Landing Lemma / covering statement; proving it closes ES. -/
def LandingHypothesis : Prop :=
  ∀ p : Nat, IsPrime p → ∃ a c d m, Witness p a c d m

/-- The Erdős–Straus conjecture. -/
def ErdosStraus : Prop :=
  ∀ n : Nat, 2 ≤ n → ∃ x y z, IsES n x y z

/-- **Conditional QED.** The Landing Hypothesis implies Erdős–Straus. -/
theorem conditional_qed (H : LandingHypothesis) : ErdosStraus := by
  intro n hn
  obtain ⟨p, hp, hpn⟩ := exists_prime_factor n hn
  obtain ⟨t, ht⟩ := hpn
  have hp0 : 0 < p := by have := hp.1; omega
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp at ht; omega
    · exact h0
  obtain ⟨a, c, d, m, hw⟩ := H p hp
  have hsol := witness_sound hp0 hw
  have := scale t ht0 hsol
  rw [← ht] at this
  exact ⟨_, _, _, this⟩

/-! ## Bounded verification -/

/-- Bounded witness search: does some `a,c,d ≤ B` give `(4acd−1) ∣ c·n + a`? -/
def hasWitness (n B : Nat) : Bool :=
  (List.range' 1 B).any fun a =>
    (List.range' 1 B).any fun c =>
      (List.range' 1 B).any fun d =>
        (c*n + a) % (4*a*c*d - 1) == 0

/-- Soundness of the bounded search. -/
theorem hasWitness_sound {n B : Nat} (h : hasWitness n B = true) :
    ∃ a c d m, Witness n a c d m := by
  unfold hasWitness at h
  simp only [List.any_eq_true, List.mem_range'_1] at h
  obtain ⟨a, ⟨ha1, _⟩, c, ⟨hc1, _⟩, d, ⟨hd1, _⟩, hmod⟩ := h
  have ha : 0 < a := ha1
  have hc : 0 < c := hc1
  have hd : 0 < d := hd1
  -- positivity of 4*a*c*d in its literal left-associated parse
  have h4a : 0 < 4*a := by omega
  have hQ : 0 < 4*a*c*d := mul_pos' (mul_pos' h4a hc) hd
  -- extract the divisibility
  have hmod' : (c*n + a) % (4*a*c*d - 1) = 0 := by
    have := of_decide_eq_true (by exact hmod)
    exact this
  have hdvd : (4*a*c*d - 1) ∣ (c*n + a) := Nat.dvd_of_mod_eq_zero hmod'
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp at hm
      omega
    · exact h0
  refine ⟨a, c, d, m, ha, hc, hd, hm0, ?_⟩
  -- c*n + a + m = ((4acd − 1) + 1)*m = 4acd*m = 4*(a*c*d*m)
  have step1 : c*n + a + m = (4*a*c*d - 1)*m + m := by omega
  have step2 : (4*a*c*d - 1)*m + m = ((4*a*c*d - 1) + 1)*m :=
    (Nat.succ_mul (4*a*c*d - 1) m).symm
  have step3 : (4*a*c*d - 1) + 1 = 4*a*c*d := by omega
  have step4 : 4*a*c*d*m = 4*(a*c*d*m) := by
    simp [Nat.mul_assoc]
  rw [step1, step2, step3, step4]

/-- Trial-division primality test. `List.range' 2 (n-2)` is `[2, …, n-1]`. -/
def isPrimeB (n : Nat) : Bool :=
  2 ≤ n && ((List.range' 2 (n-2)).all fun q => n % q != 0)

/-- The Boolean primality test matches `IsPrime`. Without this, the
    `native_decide` range checks below would not instantiate `LandingHypothesis`. -/
theorem isPrimeB_iff {n : Nat} : isPrimeB n = true ↔ IsPrime n := by
  unfold isPrimeB IsPrime
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨h2, hall⟩ := h
    refine ⟨h2, ?_⟩
    intro q hq
    by_cases h1 : q = 1
    · exact Or.inl h1
    · by_cases hnq : q = n
      · exact Or.inr hnq
      · exfalso
        have npos : 0 < n := by omega
        have qpos : 0 < q := by
          rcases Nat.eq_zero_or_pos q with h0 | h0
          · subst h0
            have : n = 0 := Nat.eq_zero_of_zero_dvd hq
            omega
          · exact h0
        have qle : q ≤ n := Nat.le_of_dvd npos hq
        have qlt : q < n := Nat.lt_of_le_of_ne qle hnq
        have q2 : 2 ≤ q := by omega
        have hmem : q ∈ List.range' 2 (n - 2) := by
          rw [List.mem_range'_1]
          exact ⟨q2, by omega⟩
        have hneq : (n % q != 0) = true := hall q hmem
        have hmod : n % q ≠ 0 := by
          simpa using hneq
        exact hmod (Nat.mod_eq_zero_of_dvd hq)
  · intro ⟨h2, hdiv⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨h2, ?_⟩
    intro q hmem
    have ⟨q2, qlt⟩ := (List.mem_range'_1).1 hmem
    have hnz : n % q ≠ 0 := by
      intro hz
      have hdvd : q ∣ n := Nat.dvd_of_mod_eq_zero hz
      have hcases := hdiv q hdvd
      omega
    simpa using hnz

/-- **Machine-checked instance of the Landing Hypothesis**: every prime
    below 10000 has a covering witness with parameters ≤ 25. -/
theorem primes_below_10000_covered :
    ((List.range 10000).all fun p => !(isPrimeB p) || hasWitness p 25) = true := by
  native_decide

/-- **Genuine landing instance:** every `IsPrime` below 10000 has a covering witness.
    This is the Prop-level content of `primes_below_10000_covered`. -/
theorem landing_below_10000 {p : Nat} (hp : IsPrime p) (h : p < 10000) :
    ∃ a c d m, Witness p a c d m := by
  have hall := List.all_eq_true.mp primes_below_10000_covered p (List.mem_range.mpr h)
  have hpr : isPrimeB p = true := isPrimeB_iff.mpr hp
  simp only [Bool.or_eq_true] at hall
  rcases hall with hf | hw
  · have : isPrimeB p = false := by
      simpa using hf
    simp [hpr] at this
  · exact hasWitness_sound hw

/-- The hard residue classes mod 840 (quadratic residues). -/
def isHardClass (p : Nat) : Bool :=
  [1, 121, 169, 289, 361, 529].contains (p % 840)

/-- Track B empirics, machine-checked: every hard-class prime below 10000
    has a covering witness with parameters ≤ 25. -/
theorem hard_primes_below_10000_covered :
    ((List.range 10000).all fun p =>
      !(isPrimeB p && isHardClass p) || hasWitness p 25) = true := by
  native_decide

/-- Explicit worked example: the smallest hard prime, p = 1009, with witness
    (a,c,d,m) = (3,1,1,92):  4/1009 = 1/276 + 1/3027 + 1/92828. -/
theorem es_1009 : IsES 1009 276 3027 92828 := by
  have hw : Witness 1009 3 1 1 92 := by
    refine ⟨by omega, by omega, by omega, by omega, by decide⟩
  have := witness_sound (n := 1009) (by omega) hw
  simpa using this

set_option maxRecDepth 100000 in
/-- Kernel-checked (no native code): every prime below 100 has a witness. -/
theorem primes_below_100_covered_kernel :
    ((List.range 100).all fun p => !(isPrimeB p) || hasWitness p 12) = true := by
  decide

/-! ## The Mordell easy classes: formal reduction of ES to n ≡ 1 (mod 4) -/

/-- Polynomial witness for the whole class n ≡ 3 (mod 4):
    (a,c,d,m) = (1, 2, t+1, 1). -/
theorem witness_three_mod_four (t : Nat) : Witness (4*t+3) 1 2 (t+1) 1 := by
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  simp only [Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-- ES for n ≡ 3 (mod 4), via the witness. -/
theorem es_three_mod_four (t : Nat) : ∃ x y z, IsES (4*t+3) x y z :=
  ⟨_, _, _, witness_sound (by omega) (witness_three_mod_four t)⟩

/-- ES for n = 2, from the witness (1,1,1,1): `4/2 = 1/1 + 1/2 + 1/2`. -/
theorem es_two : IsES 2 (1*1*1) (2*(1*1*1)) (2*(1*1*1)) := by
  have hw : Witness 2 1 1 1 1 :=
    ⟨by omega, by omega, by omega, by omega, by decide⟩
  exact witness_sound (by omega) hw

/-- ES for every even n ≥ 2, by scaling the solution for 2. -/
theorem es_even (t : Nat) (ht : 0 < t) : ∃ x y z, IsES (2*t) x y z :=
  ⟨_, _, _, scale t ht es_two⟩

/-- **Formal Mordell reduction.** ES holds for every `n ≥ 2` with
    `n % 4 ≠ 1`; the conjecture is open only on `n ≡ 1 (mod 4)`. -/
theorem es_of_not_one_mod_four {n : Nat} (hn : 2 ≤ n) (h : n % 4 ≠ 1) :
    ∃ x y z, IsES n x y z := by
  have h4 : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h0 | h2 | h3
  · obtain ⟨t, ht⟩ : ∃ t, n = 2*t := ⟨n/2, by omega⟩
    have ht0 : 0 < t := by omega
    exact ht ▸ es_even t ht0
  · obtain ⟨t, ht⟩ : ∃ t, n = 2*t := ⟨n/2, by omega⟩
    have ht0 : 0 < t := by omega
    exact ht ▸ es_even t ht0
  · obtain ⟨t, ht⟩ : ∃ t, n = 4*t+3 := ⟨n/4, by omega⟩
    exact ht ▸ es_three_mod_four t

/-! ## The full Mordell suite: reduction to the six hard classes mod 840 -/

/-- n ≡ 2 (mod 3): witness (1,1,1,s+1), i.e. q = 3. -/
theorem w_two_mod_three (s : Nat) : Witness (3*s+2) 1 1 1 (s+1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- n ≡ 5 (mod 8): witness (1,1,t+1,2) — the classical 8t+5 identity. -/
theorem w_five_mod_eight (t : Nat) : Witness (8*t+5) 1 1 (t+1) 2 :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- n ≡ 3 (mod 7): witness (1,2,1,2s+1), q = 7. -/
theorem w_three_mod_seven (s : Nat) : Witness (7*s+3) 1 2 1 (2*s+1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- n ≡ 5 (mod 7): witness (2,1,1,s+1), q = 7. -/
theorem w_five_mod_seven (s : Nat) : Witness (7*s+5) 2 1 1 (s+1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- n ≡ 6 (mod 7): witness (1,1,2,s+1), q = 7. -/
theorem w_six_mod_seven (s : Nat) : Witness (7*s+6) 1 1 2 (s+1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- n ≡ 7 (mod 15): witness (1,2,2,2s+1), q = 15; covers 2 (mod 5) ∩ 1 (mod 3). -/
theorem w_seven_mod_fifteen (s : Nat) : Witness (15*s+7) 1 2 2 (2*s+1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- n ≡ 13 (mod 15): witness (2,1,2,s+1), q = 15; covers 3 (mod 5) ∩ 1 (mod 3). -/
theorem w_thirteen_mod_fifteen (s : Nat) : Witness (15*s+13) 2 1 2 (s+1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- ES from a witness in a residue class, packaged. -/
theorem es_of_witness {n a c d m : Nat} (hn : 0 < n) (h : Witness n a c d m) :
    ∃ x y z, IsES n x y z :=
  ⟨_, _, _, witness_sound hn h⟩

/-- The six hard residue classes mod 840 (as a Prop). -/
def HardClass (n : Nat) : Prop :=
  n % 840 = 1 ∨ n % 840 = 121 ∨ n % 840 = 169 ∨
  n % 840 = 289 ∨ n % 840 = 361 ∨ n % 840 = 529

theorem isHardClass_iff (n : Nat) :
    isHardClass n = true ↔ HardClass n := by
  constructor
  · intro h
    unfold isHardClass at h
    by_cases h1 : n % 840 = 1
    · exact Or.inl h1
    · by_cases h2 : n % 840 = 121
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : n % 840 = 169
        · exact Or.inr (Or.inr (Or.inl h3))
        · by_cases h4 : n % 840 = 289
          · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
          · by_cases h5 : n % 840 = 361
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
            · by_cases h6 : n % 840 = 529
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))
              · have e1 : (n % 840 == 1) = false := by simp [beq_iff_eq, h1]
                have e2 : (n % 840 == 121) = false := by simp [beq_iff_eq, h2]
                have e3 : (n % 840 == 169) = false := by simp [beq_iff_eq, h3]
                have e4 : (n % 840 == 289) = false := by simp [beq_iff_eq, h4]
                have e5 : (n % 840 == 361) = false := by simp [beq_iff_eq, h5]
                have e6 : (n % 840 == 529) = false := by simp [beq_iff_eq, h6]
                simp [List.contains, List.elem, e1, e2, e3, e4, e5, e6] at h
  · intro h
    unfold isHardClass HardClass at *
    rcases h with h | h | h | h | h | h <;> simp [h]

/-- The six hard classes are the square residues 1², 11², 13², 17², 19², 23²
    modulo 840 — the Schinzel/Mordell quadratic-residue obstruction, as a
    definitional fact. -/
theorem hardClass_residue_sq {n : Nat} (h : HardClass n) :
    n % 840 = 1 * 1 ∨ n % 840 = 11 * 11 ∨ n % 840 = 13 * 13 ∨
    n % 840 = 17 * 17 ∨ n % 840 = 19 * 19 ∨ n % 840 = 23 * 23 := h

/-- Hard-class residues are `1 (mod 8)` and `1 (mod 3)`. -/
theorem hardClass_mod {n : Nat} (h : HardClass n) :
    n % 8 = 1 ∧ n % 3 = 1 := by
  rcases h with h | h | h | h | h | h <;> omega

/-- Hard classes occupy only three residues mod 7 (the squares 1², 2², 4²). -/
theorem hard_mod7 {n : Nat} (h : HardClass n) :
    n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 4 := by
  rcases h with h | h | h | h | h | h <;> omega

/-- `3` and `7` divide `840`, so a hard class fixes `p` modulo both.
    `11` does not, so `p mod 11` is not rigid (see `not_classRough_1009_a3`). -/
theorem three_dvd_840 : 3 ∣ 840 := ⟨280, rfl⟩
theorem seven_dvd_840 : 7 ∣ 840 := ⟨120, rfl⟩
theorem eleven_not_dvd_840 : ¬ 11 ∣ 840 := by
  intro h
  have : 840 % 11 = 0 := Nat.mod_eq_zero_of_dvd h
  omega

theorem eq_two_of_dvd_two {q : Nat} (hP : IsPrime q) (h : q ∣ 2) : q = 2 := by
  have : q ≤ 2 := Nat.le_of_dvd (Nat.succ_pos 1) h
  obtain ⟨h2, _⟩ := hP
  omega

theorem eq_three_of_dvd_three {q : Nat} (hP : IsPrime q) (h : q ∣ 3) : q = 3 := by
  have hle : q ≤ 3 := Nat.le_of_dvd (by omega) h
  have hcases : q = 2 ∨ q = 3 := by obtain ⟨h2, _⟩ := hP; omega
  rcases hcases with h2 | h3
  · have : 3 % 2 = 0 := Nat.mod_eq_zero_of_dvd (h2 ▸ h)
    omega
  · exact h3

theorem eq_five_of_dvd_five {q : Nat} (hP : IsPrime q) (h : q ∣ 5) : q = 5 := by
  have hle : q ≤ 5 := Nat.le_of_dvd (by omega) h
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by obtain ⟨h2, _⟩ := hP; omega
  rcases hcases with h2 | h3 | h4 | h5
  · have : 5 % 2 = 0 := Nat.mod_eq_zero_of_dvd (h2 ▸ h); omega
  · have : 5 % 3 = 0 := Nat.mod_eq_zero_of_dvd (h3 ▸ h); omega
  · have : 5 % 4 = 0 := Nat.mod_eq_zero_of_dvd (h4 ▸ h); omega
  · exact h5

theorem eq_seven_of_dvd_seven {q : Nat} (hP : IsPrime q) (h : q ∣ 7) : q = 7 := by
  have hle : q ≤ 7 := Nat.le_of_dvd (by omega) h
  have hcases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by
    obtain ⟨h2, _⟩ := hP; omega
  rcases hcases with h2 | h3 | h4 | h5 | h6 | h7
  · have : 7 % 2 = 0 := Nat.mod_eq_zero_of_dvd (h2 ▸ h); omega
  · have : 7 % 3 = 0 := Nat.mod_eq_zero_of_dvd (h3 ▸ h); omega
  · have : 7 % 4 = 0 := Nat.mod_eq_zero_of_dvd (h4 ▸ h); omega
  · have : 7 % 5 = 0 := Nat.mod_eq_zero_of_dvd (h5 ▸ h); omega
  · have : 7 % 6 = 0 := Nat.mod_eq_zero_of_dvd (h6 ▸ h); omega
  · exact h7

/-- The only prime divisors of `840 = 8·3·5·7` are `2, 3, 5, 7`. -/
theorem prime_dvd_840 {q : Nat} (hP : IsPrime q) (h : q ∣ 840) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
  have e : 840 = 8 * (3 * (5 * 7)) := by decide
  rw [e] at h
  rcases hP.dvd_or_dvd h with h8 | h105
  · have e8 : 8 = 2 * 4 := rfl
    rw [e8] at h8
    rcases hP.dvd_or_dvd h8 with h2 | h4
    · exact Or.inl (eq_two_of_dvd_two hP h2)
    · have e4 : 4 = 2 * 2 := rfl
      rw [e4] at h4
      rcases hP.dvd_or_dvd h4 with h2 | h2'
      · exact Or.inl (eq_two_of_dvd_two hP h2)
      · exact Or.inl (eq_two_of_dvd_two hP h2')
  · rcases hP.dvd_or_dvd h105 with h3 | h35
    · exact Or.inr (Or.inl (eq_three_of_dvd_three hP h3))
    · rcases hP.dvd_or_dvd h35 with h5 | h7
      · exact Or.inr (Or.inr (Or.inl (eq_five_of_dvd_five hP h5)))
      · exact Or.inr (Or.inr (Or.inr (eq_seven_of_dvd_seven hP h7)))

/-- Hard-class primes below 10000 land (Prop-level). -/
theorem hard_landing_below_10000 {p : Nat}
    (hp : IsPrime p) (_hh : HardClass p) (h : p < 10000) :
    ∃ a c d m, Witness p a c d m :=
  landing_below_10000 hp h

set_option maxHeartbeats 3200000 in
/-- CRT fact (finite check): residues that survive all the identity classes
    are exactly the six hard classes. -/
theorem crt_hard :
    ∀ r : Nat, r < 840 → r % 8 = 1 → r % 3 = 1 →
      (r % 5 = 1 ∨ r % 5 = 4) → (r % 7 = 1 ∨ r % 7 = 2 ∨ r % 7 = 4) →
      (r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529) := by
  omega

set_option maxHeartbeats 4000000 in
/-- CRT: the surviving residue constraints force membership in a hard class. -/
theorem mod840_hard (p : Nat) (h8 : p % 8 = 1) (h3 : p % 3 = 1)
    (h5 : p % 5 = 1 ∨ p % 5 = 4) (h7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) :
    HardClass p := by
  unfold HardClass
  omega

set_option maxHeartbeats 1600000 in
/-- **Every prime outside the six hard classes satisfies ES.** -/
theorem es_prime_not_hard {p : Nat} (hp : IsPrime p) (h : ¬ HardClass p) :
    ∃ x y z, IsES p x y z := by
  have h2 : 2 ≤ p := hp.1
  -- even prime
  by_cases he : p % 2 = 0
  · have : (2:Nat) ∣ p := Nat.dvd_of_mod_eq_zero he
    have h2' := hp.2 2 this
    have hp2 : p = 2 := by omega
    subst hp2
    exact ⟨_, _, _, es_two⟩
  -- p ≡ 3 (mod 4)
  by_cases h43 : p % 4 = 3
  · obtain ⟨t, ht⟩ : ∃ t, p = 4*t+3 := ⟨p/4, by omega⟩
    rw [ht]; exact es_three_mod_four t
  -- p ≡ 5 (mod 8)
  by_cases h85 : p % 8 = 5
  · obtain ⟨t, ht⟩ : ∃ t, p = 8*t+5 := ⟨p/8, by omega⟩
    rw [ht]; exact es_of_witness (by omega) (w_five_mod_eight t)
  -- now p ≡ 1 (mod 8)
  have h81 : p % 8 = 1 := by omega
  -- p ≡ 2 (mod 3)
  by_cases h32 : p % 3 = 2
  · obtain ⟨s, hs⟩ : ∃ s, p = 3*s+2 := ⟨p/3, by omega⟩
    rw [hs]; exact es_of_witness (by omega) (w_two_mod_three s)
  -- p ≡ 0 (mod 3) forces p = 3, contradicting p ≡ 1 (mod 8)
  by_cases h30 : p % 3 = 0
  · have : (3:Nat) ∣ p := Nat.dvd_of_mod_eq_zero h30
    have h3' := hp.2 3 this
    omega
  have h31 : p % 3 = 1 := by omega
  -- p ≡ 2 (mod 5): with p ≡ 1 (mod 3) gives p ≡ 7 (mod 15)
  by_cases h52 : p % 5 = 2
  · obtain ⟨s, hs⟩ : ∃ s, p = 15*s+7 := ⟨p/15, by omega⟩
    rw [hs]; exact es_of_witness (by omega) (w_seven_mod_fifteen s)
  -- p ≡ 3 (mod 5): gives p ≡ 13 (mod 15)
  by_cases h53 : p % 5 = 3
  · obtain ⟨s, hs⟩ : ∃ s, p = 15*s+13 := ⟨p/15, by omega⟩
    rw [hs]; exact es_of_witness (by omega) (w_thirteen_mod_fifteen s)
  -- p ≡ 0 (mod 5) forces p = 5, contradicting p ≡ 1 (mod 8)
  by_cases h50 : p % 5 = 0
  · have : (5:Nat) ∣ p := Nat.dvd_of_mod_eq_zero h50
    have h5' := hp.2 5 this
    omega
  have h51 : p % 5 = 1 ∨ p % 5 = 4 := by omega
  -- p ≡ 3, 5, 6 (mod 7)
  by_cases h73 : p % 7 = 3
  · obtain ⟨s, hs⟩ : ∃ s, p = 7*s+3 := ⟨p/7, by omega⟩
    rw [hs]; exact es_of_witness (by omega) (w_three_mod_seven s)
  by_cases h75 : p % 7 = 5
  · obtain ⟨s, hs⟩ : ∃ s, p = 7*s+5 := ⟨p/7, by omega⟩
    rw [hs]; exact es_of_witness (by omega) (w_five_mod_seven s)
  by_cases h76 : p % 7 = 6
  · obtain ⟨s, hs⟩ : ∃ s, p = 7*s+6 := ⟨p/7, by omega⟩
    rw [hs]; exact es_of_witness (by omega) (w_six_mod_seven s)
  -- p ≡ 0 (mod 7) forces p = 7, contradicting p ≡ 1 (mod 8)
  by_cases h70 : p % 7 = 0
  · have : (7:Nat) ∣ p := Nat.dvd_of_mod_eq_zero h70
    have h7' := hp.2 7 this
    omega
  have h7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by omega
  -- all identity classes exhausted: p must be in a hard class — contradiction
  exact absurd (mod840_hard p h81 h31 h51 h7) h

/-- **The sharpened open target.** ES for the hard-class primes only. -/
def HardLandingHypothesis : Prop :=
  ∀ p : Nat, IsPrime p → HardClass p → ∃ x y z, IsES p x y z

/-- **Conditional QED, sharpened.** ES follows from the hypothesis restricted
    to primes in the six hard residue classes mod 840. -/
theorem conditional_qed_hard (H : HardLandingHypothesis) : ErdosStraus := by
  intro n hn
  obtain ⟨p, hp, hpn⟩ := exists_prime_factor n hn
  obtain ⟨t, ht⟩ := hpn
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp at ht; have := hp.1; omega
    · exact h0
  have hsol : ∃ x y z, IsES p x y z := by
    by_cases hh : HardClass p
    · exact H p hp hh
    · exact es_prime_not_hard hp hh
  obtain ⟨x, y, z, hxyz⟩ := hsol
  have := scale t ht0 hxyz
  rw [← ht] at this
  exact ⟨_, _, _, this⟩

/-- Covering-landing is sufficient for hard landing, but not necessary:
    `HardLandingHypothesis` asks only for solutions, not witnesses.
    Bright–Loughran geometry occupies this gap (see `ErdosStrausBLRoute.lean`). -/
theorem landing_implies_hard_landing (H : LandingHypothesis) :
    HardLandingHypothesis := by
  intro p hp _
  obtain ⟨a, c, d, m, hw⟩ := H p hp
  exact ⟨_, _, _, witness_sound (by have := hp.1; omega) hw⟩

/-! ## Verified frontier: ES for every n < 100000 -/

/-- Bounded proper-factor test: some `q` with `2 ≤ q < 350`, `q² ≤ n`,
    `q < n`, `q ∣ n`. (350 > √100000, so this finds a factor of any
    composite in range.) -/
def properFactor (n : Nat) : Bool :=
  (List.range' 2 348).any fun q =>
    decide (q*q ≤ n) && (decide (q < n) && (n % q == 0))

/-- Certificate check: `n` has a proper factor or a covering witness. -/
def okay (n : Nat) : Bool :=
  properFactor n || hasWitness n 25

/-- Soundness of the proper-factor test. -/
theorem properFactor_sound {n : Nat} (h : properFactor n = true) :
    ∃ q, 2 ≤ q ∧ q < n ∧ q ∣ n := by
  unfold properFactor at h
  simp only [List.any_eq_true, List.mem_range'_1, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨q, ⟨hq2, _⟩, _, hlt, hmod⟩ := h
  exact ⟨q, hq2, hlt, Nat.dvd_of_mod_eq_zero hmod⟩

/-- **Machine-checked certificate for the range.** Every `2 ≤ n < 100000`
    has a proper factor or a covering witness. -/
theorem okay_below_100000 :
    ((List.range 100000).all fun n => decide (n < 2) || okay n) = true := by
  native_decide

/-- Bridge: extract the per-`n` certificate from the range check. -/
theorem okay_of_lt {n : Nat} (h2 : 2 ≤ n) (h : n < 100000) : okay n = true := by
  have hh := List.all_eq_true.mp okay_below_100000 n (List.mem_range.mpr h)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hh
  rcases hh with h' | h'
  · omega
  · exact h'

/-- **ES verified for every n below 100000**, by strong induction on the
    certificate: a witness closes the case directly; a proper factor recurses. -/
theorem es_below_100000_aux :
    ∀ k n : Nat, n ≤ k → 2 ≤ n → n < 100000 → ∃ x y z, IsES n x y z := by
  intro k
  induction k with
  | zero => intro n hn h2 _; omega
  | succ k ih =>
    intro n hn h2 hN
    have hok := okay_of_lt h2 hN
    unfold okay at hok
    simp only [Bool.or_eq_true] at hok
    rcases hok with hf | hw
    · -- proper factor: recurse and scale
      obtain ⟨q, hq2, hqn, hqdvd⟩ := properFactor_sound hf
      obtain ⟨t, ht⟩ := hqdvd
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; simp at ht; omega
        · exact h0
      obtain ⟨x, y, z, hxyz⟩ := ih q (by omega) hq2 (by omega)
      have := scale t ht0 hxyz
      rw [← ht] at this
      exact ⟨_, _, _, this⟩
    · -- covering witness: direct
      obtain ⟨a, c, d, m, hwit⟩ := hasWitness_sound hw
      exact ⟨_, _, _, witness_sound (by omega) hwit⟩

/-- **ES holds for every `2 ≤ n < 100000`.** -/
theorem es_below_100000 {n : Nat} (h2 : 2 ≤ n) (h : n < 100000) :
    ∃ x y z, IsES n x y z :=
  es_below_100000_aux n n (Nat.le_refl n) h2 h

end ES

/-! # Covering system layer (roadmap Steps 1–2, 18 Aug 2026)

The explicit ES covering system, `covering_sound`, the cardinality-to-QED
bridge, and the statement-first analytic interface.  Everything below is
proved; the interface `AnalyticSurvivorBound` is a *definition* (a Prop),
deliberately unproven — the single load-bearing analytic target, stated
before any attempt to prove it (roadmap §12, Step 2). -/

namespace ES.Covering
open ES

/-- Parameters (a,c,d) cover n iff q = 4acd − 1 divides c·n + a
(equivalently: the witness equation is solvable in m). -/
def coversB (a c d n : Nat) : Bool :=
  (c*n + a) % (4*a*c*d - 1) == 0

/-- The level-A covering system: a, c ≤ A and d ≤ 5. -/
def coveredB (A n : Nat) : Bool :=
  (List.range A).any fun a' =>
    (List.range A).any fun c' =>
      (List.range 5).any fun d' =>
        coversB (a'+1) (c'+1) (d'+1) n

def Covered (A n : Nat) : Prop := coveredB A n = true
def Survivor (A n : Nat) : Prop := ¬ Covered A n

instance (A n : Nat) : Decidable (Covered A n) := by
  unfold Covered; infer_instance

instance (A n : Nat) : Decidable (Survivor A n) := by
  unfold Survivor; infer_instance

/-- **covering_sound** (Step 1): being covered yields a witness. -/
theorem covering_sound {A n : Nat} (h : Covered A n) :
    ∃ a c d m, Witness n a c d m := by
  unfold Covered coveredB at h
  rw [List.any_eq_true] at h
  obtain ⟨a', _, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨c', _, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨d', _, h⟩ := h
  unfold coversB at h
  rw [Nat.beq_eq_true_eq] at h
  have ha : 0 < a'+1 := Nat.succ_pos a'
  have hc : 0 < c'+1 := Nat.succ_pos c'
  have hd : 0 < d'+1 := Nat.succ_pos d'
  have hq1 : 1 ≤ 4*(a'+1)*(c'+1)*(d'+1) := by
    have h4 : 0 < 4*(a'+1)*(c'+1)*(d'+1) :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) ha) hc) hd
    omega
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hm
    · exact h0
  refine ⟨a'+1, c'+1, d'+1, m, ha, hc, hd, hmpos, ?_⟩
  have key : (4*(a'+1)*(c'+1)*(d'+1) - 1)*m + m
           = (4*(a'+1)*(c'+1)*(d'+1))*m := by
    have h2 : (4*(a'+1)*(c'+1)*(d'+1) - 1) + 1
            = 4*(a'+1)*(c'+1)*(d'+1) := Nat.sub_add_cancel hq1
    calc (4*(a'+1)*(c'+1)*(d'+1) - 1)*m + m
        = ((4*(a'+1)*(c'+1)*(d'+1) - 1) + 1)*m := by
          rw [Nat.add_mul, Nat.one_mul]
      _ = (4*(a'+1)*(c'+1)*(d'+1))*m := by rw [h2]
  rw [hm, key]
  simp [Nat.mul_assoc]

/-- `coversB` produces a witness. -/
theorem coversB_sound {a c d n : Nat} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (h : coversB a c d n = true) : ∃ m, Witness n a c d m := by
  unfold coversB at h
  rw [Nat.beq_eq_true_eq] at h
  have hq1 : 1 ≤ 4 * a * c * d := by
    have : 0 < 4 * a * c * d :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) ha) hc) hd
    omega
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hm; omega
    · exact h0
  refine ⟨m, ha, hc, hd, hmpos, ?_⟩
  have key : (4 * a * c * d - 1) * m + m = (4 * a * c * d) * m := by
    have h2 : (4 * a * c * d - 1) + 1 = 4 * a * c * d := Nat.sub_add_cancel hq1
    calc (4 * a * c * d - 1) * m + m
        = ((4 * a * c * d - 1) + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
      _ = (4 * a * c * d) * m := by rw [h2]
  rw [hm, key]
  simp [Nat.mul_assoc]

/-- A single box cell being true implies `Covered`. -/
theorem covered_of_coversB {A a c d n : Nat}
    (ha : 1 ≤ a ∧ a ≤ A) (hc : 1 ≤ c ∧ c ≤ A) (hd : 1 ≤ d ∧ d ≤ 5)
    (h : coversB a c d n = true) : Covered A n := by
  unfold Covered coveredB
  rw [List.any_eq_true]
  refine ⟨a - 1, List.mem_range.mpr (by omega), ?_⟩
  rw [List.any_eq_true]
  refine ⟨c - 1, List.mem_range.mpr (by omega), ?_⟩
  rw [List.any_eq_true]
  refine ⟨d - 1, List.mem_range.mpr (by omega), ?_⟩
  have ha1 : a - 1 + 1 = a := by omega
  have hc1 : c - 1 + 1 = c := by omega
  have hd1 : d - 1 + 1 = d := by omega
  simpa [ha1, hc1, hd1] using h

/-- **Survivor bundle (AP form).** A survivor avoids every covering cell in the box. -/
theorem survivor_not_coversB {A n a c d : Nat} (hs : Survivor A n)
    (ha : 1 ≤ a ∧ a ≤ A) (hc : 1 ≤ c ∧ c ≤ A) (hd : 1 ≤ d ∧ d ≤ 5) :
    coversB a c d n = false := by
  cases hcov : coversB a c d n with
  | false => rfl
  | true => exact absurd (covered_of_coversB ha hc hd hcov) hs

/-- Type-I cells (`c = 1`) in the box: a survivor is not a Type-I witness. -/
theorem survivor_not_typeI_witness {A n a d m : Nat} (hA : 1 ≤ A)
    (hs : Survivor A n) (ha : 1 ≤ a ∧ a ≤ A) (hd : 1 ≤ d ∧ d ≤ 5) :
    ¬ Witness n a 1 d m := by
  intro hw
  have hcov : coversB a 1 d n = true := by
    unfold coversB
    have hcof := witness_cofactor hw
    have hmod : (n + a) % (4 * a * d - 1) = 0 := by
      have hdvd : (4 * a * d - 1) ∣ (n + a) := ⟨m, by
        simpa [Nat.mul_one, Nat.one_mul] using hcof.symm⟩
      exact Nat.mod_eq_zero_of_dvd hdvd
    simp [beq_iff_eq, Nat.mul_one, Nat.one_mul, hmod]
  have hc : 1 ≤ 1 ∧ 1 ≤ A := ⟨Nat.le_refl 1, hA⟩
  have := survivor_not_coversB hs ha hc hd
  simp [hcov] at this

/-- **Survivor Type-I AP bundle** (roadmap §9, elementary form):
    `p ≢ −a (mod 4ad − 1)` for every Type-I cell in the box. -/
theorem survivor_typeI_aps {A n a d : Nat} (hA : 1 ≤ A) (hs : Survivor A n)
    (ha : 1 ≤ a ∧ a ≤ A) (hd : 1 ≤ d ∧ d ≤ 5) :
    (n + a) % (4 * a * d - 1) ≠ 0 := by
  have hfalse := survivor_not_coversB (c := 1) hs ha ⟨Nat.le_refl 1, hA⟩ hd
  unfold coversB at hfalse
  intro hmod
  simp [beq_iff_eq, Nat.mul_one, Nat.one_mul] at hfalse
  exact hfalse hmod

/-- One-slot covering at level `A`. -/
def OneSlotCovered (A n : Nat) : Prop :=
  ∃ a d f m, a ≤ A ∧ 0 < a ∧ d ≤ 5 ∧ OneSlot n a d f m

theorem oneSlotCovered_es {A n : Nat} (h : OneSlotCovered A n) :
    ∃ x y z, IsES n x y z := by
  obtain ⟨a, d, f, m, _, _, _, hslot⟩ := h
  exact oneSlot_es hslot

/-- Hybrid covering: existing two-slot box, or the one-slot family. -/
def HybridCovered (A n : Nat) : Prop := Covered A n ∨ OneSlotCovered A n

theorem hybrid_covering_sound {A n : Nat} (hn : 0 < n) (h : HybridCovered A n) :
    ∃ x y z, IsES n x y z := by
  rcases h with h | h
  · obtain ⟨a, c, d, m, hw⟩ := covering_sound h
    exact ⟨_, _, _, witness_sound hn hw⟩
  · exact oneSlotCovered_es h

/-- Weaker large-prime target: every large hard prime is hybrid-covered.
    Easier than `AnalyticSurvivorBound` because the one-slot family is extra mass. -/
def HybridSurvivorBound (Alevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p → HybridCovered (Alevel p) p

theorem hard_landing_of_hybrid
    (Alevel : Nat → Nat) (X0 : Nat)
    (hbig : HybridSurvivorBound Alevel X0)
    (hsmall : ∀ p : Nat, p < X0 → IsPrime p → HardClass p →
      ∃ x y z, IsES p x y z) :
    HardLandingHypothesis := by
  intro p hp hhard
  rcases Nat.lt_or_ge p X0 with hlt | hge
  · exact hsmall p hlt hp hhard
  · have hn : 0 < p := by
      obtain ⟨h2, _⟩ := hp
      omega
    exact hybrid_covering_sound hn (hbig p hge hp hhard)

theorem erdos_straus_of_hybrid
    (Alevel : Nat → Nat) (X0 : Nat)
    (hbig : HybridSurvivorBound Alevel X0)
    (hsmall : ∀ p : Nat, p < X0 → IsPrime p → HardClass p →
      ∃ x y z, IsES p x y z) :
    ErdosStraus :=
  conditional_qed_hard (hard_landing_of_hybrid Alevel X0 hbig hsmall)

/-- Survivor count on [lo, hi). -/
def survivorCount (A lo hi : Nat) : Nat :=
  ((List.range (hi - lo)).filter fun i => decide (Survivor A (lo + i))).length

/-- **Cardinality-to-QED bridge** (Step 1): an empty count kills all
survivors in the interval. -/
theorem no_survivors_of_card_eq_zero {A lo hi : Nat}
    (h : survivorCount A lo hi = 0) :
    ∀ n, lo ≤ n → n < hi → ¬ Survivor A n := by
  unfold survivorCount at h
  intro n hlo hhi hs
  have hmem : (n - lo) ∈ (List.range (hi - lo)).filter
      (fun i => decide (Survivor A (lo + i))) := by
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    show decide (Survivor A (lo + (n - lo))) = true
    have heq : lo + (n - lo) = n := by omega
    rw [heq]
    exact decide_eq_true hs
  have := List.length_pos_of_mem hmem
  omega

/-- **The analytic interface** (Step 2, statement-first): the weakest
sufficient target.  `Alevel` is the level schedule (intended
A(x) = exp(c√log x) with κc² > 1); the claim is zero survivors among hard
primes above a threshold.  THIS IS THE SINGLE LOAD-BEARING UNPROVEN TARGET;
see the roadmap §5 (k-budget invariant) for its honest difficulty. -/
def AnalyticSurvivorBound (Alevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p → Covered (Alevel p) p

/-- **The assembled bridge**: analytic interface + finite closure ⟹ the
hard landing hypothesis, hence (via `conditional_qed_hard`) Erdős–Straus. -/
theorem hard_landing_of_interface
    (Alevel : Nat → Nat) (X0 : Nat)
    (hbig : AnalyticSurvivorBound Alevel X0)
    (hsmall : ∀ p : Nat, p < X0 → IsPrime p → HardClass p →
      ∃ x y z, IsES p x y z) :
    HardLandingHypothesis := by
  intro p hp hhard
  rcases Nat.lt_or_ge p X0 with hlt | hge
  · exact hsmall p hlt hp hhard
  · obtain ⟨a, c, d, m, hw⟩ := covering_sound (hbig p hge hp hhard)
    have hn : 0 < p := by
      obtain ⟨h2, _⟩ := hp
      omega
    exact ⟨_, _, _, witness_sound hn hw⟩

/-- **The end-state schema**: with the interface and finite closure supplied,
Erdős–Straus follows.  The final unconditional theorem is this with both
hypotheses discharged — the first by the Layer-B mathematics, the second by
finite certificate at the explicit X₀. -/
theorem erdos_straus_of_interface
    (Alevel : Nat → Nat) (X0 : Nat)
    (hbig : AnalyticSurvivorBound Alevel X0)
    (hsmall : ∀ p : Nat, p < X0 → IsPrime p → HardClass p →
      ∃ x y z, IsES p x y z) :
    ErdosStraus :=
  conditional_qed_hard (hard_landing_of_interface Alevel X0 hbig hsmall)

/-! ### Divisor-form coordinates (the "LandingLemma" duality, 18 Aug 2026)

The divisor criterion  q ∣ p + 4a²d,  q ≡ −1 (mod 4ad)  is the covering box
in dual coordinates: c := (q+1)/(4ad) gives q = 4acd − 1 and q ∣ c·p + a.
Proved below.  CAUTION (plan §4q): with a FIXED (a,d)-bound the divisor
landing statement is heuristically FALSE — shifted values all of whose prime
factors avoid the −1 progressions have density (log x)^{−c(D₀)}, giving
infinitely many exceptions for every fixed box; the bound must grow with p,
and the required rate exp(c√log x) reproduces `AnalyticSurvivorBound`'s
schedule.  The two interfaces are equivalent formulations at the same
marginal constant. -/

/-- **Divisor-form equivalence** (the "LandingLemma" coordinates): a divisor
q ≡ −1 (mod 4ad) of p + 4a²d yields a witness, via c := (q+1)/(4ad).
This proves the divisor formulation IS the covering box's free-c slot:
q = 4acd − 1 and q ∣ c·p + a.  Hence retargeting the interface to the
divisor form changes coordinates, not content. -/
theorem divisor_form_sound {a d q p : Nat}
    (ha : 0 < a) (hd : 0 < d) (_hp : 0 < p) (hq3 : 3 ≤ q)
    (hmod : (q + 1) % (4*a*d) = 0)
    (hdvd : q ∣ p + 4*(a*a*d)) :
    ∃ a' c' d' m', Witness p a' c' d' m' := by
  -- c := (q+1)/(4ad) ≥ 1
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod   -- q+1 = (4ad)*c
  have h4ad : 0 < 4*a*d := by
    have := Nat.mul_pos (Nat.mul_pos (by omega : 0 < 4) ha) hd
    omega
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at hc
    · exact h0
  -- key identity: c*(p + 4a²d) = (c*p + a) + a*q
  have hkey : c*(p + 4*(a*a*d)) = (c*p + a) + a*q := by
    have e1 : c*(4*(a*a*d)) = a*((4*a*d)*c) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e2 : (4*a*d)*c = q + 1 := hc.symm
    calc c*(p + 4*(a*a*d)) = c*p + c*(4*(a*a*d)) := by rw [Nat.mul_add]
      _ = c*p + a*((4*a*d)*c) := by rw [e1]
      _ = c*p + a*(q+1) := by rw [e2]
      _ = c*p + (a*q + a) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (a*q)]
      _ = (c*p + a) + a*q := by omega
  -- q divides c*p + a
  have hdvd2 : q ∣ c*p + a := by
    obtain ⟨s, hs⟩ := hdvd
    have hexp : c*(p + 4*(a*a*d)) = q*(c*s) := by
      rw [hs]; simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hqt : q*(c*s) = (c*p + a) + a*q := by rw [← hexp, hkey]
    have hq0 : 0 < q := by omega
    have h1 : a*q ≤ q*(c*s) := by omega
    have hta : a ≤ c*s := by
      by_cases hle : a ≤ c*s
      · exact hle
      · exfalso
        have hlt : c*s < a := Nat.lt_of_not_le hle
        have : q*(c*s) < q*a := by
          have := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hlt)
          have hq1 : q*(c*s) + q ≤ q*a := by
            rw [← Nat.mul_succ]; exact this
          omega
        have hqa' : q*a = a*q := Nat.mul_comm q a
        omega
    have hsplit : q*(c*s - a) + q*a = q*(c*s) := by
      rw [← Nat.mul_add]; congr 1; omega
    refine ⟨c*s - a, ?_⟩
    have hqa : q*a = a*q := Nat.mul_comm q a
    omega
  -- q = 4acd − 1, so the covering divisibility holds; build the witness
  have hq : 4*a*c*d - 1 = q := by
    have : 4*a*c*d = q + 1 := by
      calc 4*a*c*d = (4*a*d)*c := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = q + 1 := hc.symm
    omega
  obtain ⟨m, hm⟩ := hdvd2
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hm; omega
    · exact h0
  refine ⟨a, c, d, m, ha, hcpos, hd, hmpos, ?_⟩
  have hq1 : 1 ≤ 4*a*c*d := by omega
  have key : (4*a*c*d - 1)*m + m = (4*a*c*d)*m := by
    have h2 : (4*a*c*d - 1) + 1 = 4*a*c*d := Nat.sub_add_cancel hq1
    calc (4*a*c*d - 1)*m + m = ((4*a*c*d - 1) + 1)*m := by
          rw [Nat.add_mul, Nat.one_mul]
      _ = (4*a*c*d)*m := by rw [h2]
  have hm' : c*p + a = (4*a*c*d - 1)*m := by rw [hq]; exact hm
  rw [hm', key]
  simp [Nat.mul_assoc]


/-- Divisor-form analytic interface (growing bound `Dlevel`). -/
def DivisorLandingBound (Dlevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p →
    ∃ a d q, 0 < a ∧ 0 < d ∧ a ≤ Dlevel p ∧ d ≤ Dlevel p ∧
      3 ≤ q ∧ (q + 1) % (4*a*d) = 0 ∧ q ∣ p + 4*(a*a*d)

/-- The divisor interface implies the hard landing hypothesis. -/
theorem hard_landing_of_divisor_interface
    (Dlevel : Nat → Nat) (X0 : Nat)
    (hbig : DivisorLandingBound Dlevel X0)
    (hsmall : ∀ p : Nat, p < X0 → IsPrime p → HardClass p →
      ∃ x y z, IsES p x y z) :
    HardLandingHypothesis := by
  intro p hp hhard
  rcases Nat.lt_or_ge p X0 with hlt | hge
  · exact hsmall p hlt hp hhard
  · obtain ⟨a, d, q, ha, hd, _, _, hq3, hmod, hdvd⟩ := hbig p hge hp hhard
    have hn : 0 < p := by obtain ⟨h2, _⟩ := hp; omega
    obtain ⟨a', c', d', m', hw⟩ :=
      divisor_form_sound ha hd hn hq3 hmod hdvd
    exact ⟨_, _, _, witness_sound hn hw⟩

/-- **The DFI dictionary** (last coordinate change): for d = 1 the divisor
condition is verbatim a root of the quadratic congruence ν² ≡ −p:
q ∣ p + 4a² ↔ q ∣ (2a)² + p. -/
theorem dfi_dictionary_d1 (q p a : Nat) :
    q ∣ p + 4*(a*a) ↔ q ∣ (2*a)*(2*a) + p := by
  have h : (2*a)*(2*a) + p = p + 4*(a*a) := by
    have : (2*a)*(2*a) = 4*(a*a) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  rw [h]

/-- Shifted-value identity: (2ad)² + pd = d·(p + 4a²d). -/
theorem dfi_shift_identity (p a d : Nat) :
    (2 * a * d) * (2 * a * d) + p * d = d * (p + 4 * (a * a * d)) := by
  have hsq : (2 * a * d) * (2 * a * d) = 4 * (a * a * (d * d)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hrd : d * (4 * (a * a * d)) = 4 * (a * a * (d * d)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  calc
    (2 * a * d) * (2 * a * d) + p * d
        = 4 * (a * a * (d * d)) + p * d := by rw [hsq]
    _ = p * d + 4 * (a * a * (d * d)) := Nat.add_comm _ _
    _ = d * p + d * (4 * (a * a * d)) := by
        rw [Nat.mul_comm p d, ← hrd]
    _ = d * (p + 4 * (a * a * d)) := (Nat.mul_add _ _ _).symm

/-- Forward DFI dictionary (no coprimality): a divisor of the shift divides
    the quadratic congruence (2ad)² + pd. -/
theorem dfi_dictionary_forward {q p a d : Nat}
    (hdvd : q ∣ p + 4 * (a * a * d)) :
    q ∣ (2 * a * d) * (2 * a * d) + p * d := by
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨d * k, ?_⟩
  have hid := dfi_shift_identity p a d
  rw [hid, hk]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- **DFI dictionary, general d.** q ∣ p + 4a²d iff (2ad)² ≡ −pd (mod q),
    provided `gcd(q,d) = 1`. -/
theorem dfi_dictionary {q p a d : Nat} (hcop : Nat.Coprime q d) :
    q ∣ p + 4 * (a * a * d) ↔
      q ∣ (2 * a * d) * (2 * a * d) + p * d := by
  constructor
  · exact dfi_dictionary_forward
  · intro h
    have : q ∣ d * (p + 4 * (a * a * d)) := by
      rwa [← dfi_shift_identity p a d]
    exact hcop.dvd_of_dvd_mul_left this

/-- d=1 landing: a modulus `q ≡ −1 (mod 4a)` dividing `p + 4a²`. -/
theorem d1_landing {a q p : Nat}
    (ha : 0 < a) (hp : 0 < p) (hq3 : 3 ≤ q)
    (hmod : (q + 1) % (4 * a) = 0)
    (hdvd : q ∣ p + 4 * (a * a)) :
    ∃ a' c' d' m', Witness p a' c' d' m' := by
  have hmod' : (q + 1) % (4 * a * 1) = 0 := by simpa using hmod
  have hdvd' : q ∣ p + 4 * (a * a * 1) := by simpa using hdvd
  exact divisor_form_sound (d := 1) ha (by omega) hp hq3 hmod' hdvd'

/-- Alignment `q ≡ −1 (mod 4a)` forces `q ≡ 3 (mod 4)`. -/
theorem mod4_eq_three_of_d1_aligned {a q : Nat}
    (_ha : 0 < a) (hmod : (q + 1) % (4 * a) = 0) :
    q % 4 = 3 := by
  have h4a : 4 * a ∣ q + 1 := Nat.dvd_of_mod_eq_zero hmod
  have h4 : 4 ∣ 4 * a := Nat.dvd_mul_right 4 a
  have : 4 ∣ q + 1 := Nat.dvd_trans h4 h4a
  have : (q + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd this
  have : q % 4 < 4 := Nat.mod_lt q (by omega)
  omega

/-- Conversely, `q ≢ 3 (mod 4)` cannot be an aligned modulus (e.g. `q = 13`). -/
theorem not_aligned_of_not_mod4_three {a q : Nat} (ha : 0 < a)
    (h : q % 4 ≠ 3) (hmod : (q + 1) % (4 * a) = 0) : False :=
  h (mod4_eq_three_of_d1_aligned ha hmod)

/-- The cofactor `t` in `q + 1 = 4at` is coprime to `q`. -/
theorem coprime_d1_cofactor {a q t : Nat}
    (hqt : q + 1 = 4 * a * t) :
    Nat.Coprime q t := by
  have hg : Nat.gcd q t ∣ q := Nat.gcd_dvd_left q t
  have ht : t ∣ q + 1 := ⟨4 * a, by rw [Nat.mul_comm, hqt]⟩
  have hg1 : Nat.gcd q t ∣ q + 1 := Nat.dvd_trans (Nat.gcd_dvd_right q t) ht
  have hone : Nat.gcd q t ∣ 1 := (Nat.dvd_add_iff_right (n := 1) hg).mpr hg1
  exact Nat.eq_one_of_dvd_one hone

/-- Key identity: `t·(p+4a²) = (t·p + a) + a·q` when `q+1 = 4at`. -/
theorem d1_cofactor_identity (a q p t : Nat)
    (hqt : q + 1 = 4 * a * t) :
    t * (p + 4 * (a * a)) = (t * p + a) + a * q := by
  have e1 : t * (4 * (a * a)) = a * (4 * a * t) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  calc t * (p + 4 * (a * a))
      = t * p + t * (4 * (a * a)) := Nat.mul_add _ _ _
    _ = t * p + a * (4 * a * t) := by rw [e1]
    _ = t * p + a * (q + 1) := by rw [hqt]
    _ = t * p + (a * q + a) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (a * q)]
    _ = (t * p + a) + a * q := by omega

/-- **d=1 cofactor dictionary.** With `q+1 = 4at`, `q ∣ p+4a²` iff `q ∣ tp+a`. -/
theorem d1_aligned_divides_iff {a q p t : Nat}
    (hqt : q + 1 = 4 * a * t) :
    q ∣ p + 4 * (a * a) ↔ q ∣ t * p + a := by
  have hid := d1_cofactor_identity a q p t hqt
  have hcop := coprime_d1_cofactor hqt
  constructor
  · intro h
    have htmul : q ∣ t * (p + 4 * (a * a)) := Nat.dvd_mul_left_of_dvd h t
    have hsum : q ∣ (t * p + a) + a * q := by rwa [← hid]
    exact (Nat.dvd_add_iff_left (m := t * p + a) (Nat.dvd_mul_left q a)).mpr hsum
  · intro h
    have hsum : q ∣ (t * p + a) + a * q := Nat.dvd_add h (Nat.dvd_mul_left q a)
    have htmul : q ∣ t * (p + 4 * (a * a)) := by rwa [← hid] at hsum
    exact hcop.dvd_of_dvd_mul_left htmul

/-- `q ≡ 3 (mod 4)` is coprime to 4. -/
theorem coprime_of_mod4_eq_three {q : Nat} (h : q % 4 = 3) :
    Nat.Coprime q 4 := by
  have hg : Nat.gcd q 4 ∣ 4 := Nat.gcd_dvd_right q 4
  have hle : Nat.gcd q 4 ≤ 4 := Nat.le_of_dvd (by omega) hg
  have hpos : 0 < Nat.gcd q 4 := Nat.gcd_pos_of_pos_right q (by omega)
  have hvals : Nat.gcd q 4 = 1 ∨ Nat.gcd q 4 = 2 ∨ Nat.gcd q 4 = 3 ∨ Nat.gcd q 4 = 4 := by
    omega
  rcases hvals with h1 | h2 | h3 | h4g
  · exact h1
  · exfalso
    have : 2 ∣ q :=
      Nat.dvd_trans (h2 ▸ Nat.dvd_refl 2) (Nat.gcd_dvd_left q 4)
    have : q % 2 = 0 := Nat.mod_eq_zero_of_dvd this
    omega
  · exfalso
    have : 3 ∣ 4 := Nat.dvd_trans (h3 ▸ Nat.dvd_refl 3) hg
    have : 4 % 3 = 0 := Nat.mod_eq_zero_of_dvd this
    omega
  · exfalso
    have : 4 ∣ q := h4g ▸ Nat.gcd_dvd_left q 4
    have : q % 4 = 0 := Nat.mod_eq_zero_of_dvd this
    omega

/-- t=1 identity: `4(p+a) = (4p+1) + q` when `q+1 = 4a`. -/
theorem d1_t1_four_p_identity (a q p : Nat) (hqt : q + 1 = 4 * a) :
    4 * (p + a) = (4 * p + 1) + q := by
  calc 4 * (p + a)
      = 4 * p + 4 * a := Nat.mul_add _ _ _
    _ = 4 * p + (q + 1) := by rw [hqt]
    _ = (4 * p + 1) + q := by omega

/-- **t=1 dictionary.** With `q+1 = 4a`, `q ∣ 4p+1` iff `q ∣ p+a`. -/
theorem d1_t1_four_p_plus_one_iff {a q p : Nat}
    (hqt : q + 1 = 4 * a) (h3 : q % 4 = 3) :
    q ∣ 4 * p + 1 ↔ q ∣ p + a := by
  have hid := d1_t1_four_p_identity a q p hqt
  have hcop := coprime_of_mod4_eq_three h3
  constructor
  · intro h
    have hsum : q ∣ 4 * (p + a) := by
      have : q ∣ (4 * p + 1) + q := Nat.dvd_add h (Nat.dvd_refl q)
      rwa [← hid] at this
    exact hcop.dvd_of_dvd_mul_left hsum
  · intro h
    have h4 : q ∣ 4 * (p + a) := Nat.dvd_mul_left_of_dvd h 4
    have hsum : q ∣ (4 * p + 1) + q := by rwa [hid] at h4
    exact (Nat.dvd_add_iff_left (m := 4 * p + 1) (Nat.dvd_refl q)).mpr hsum

/-- Linear combination: `(4p+1) + 16a² = 4(p+4a²) + 1`. -/
theorem four_p_plus_one_shift_sum (p a : Nat) :
    (4 * p + 1) + 16 * (a * a) = 4 * (p + 4 * (a * a)) + 1 := by
  have : 16 * (a * a) = 4 * (4 * (a * a)) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- Any common divisor of `4p+1` and `p+4a²` divides `16a² − 1`. -/
theorem dvd_sixteen_sq_sub_one_of_common {q p a : Nat} (ha : 0 < a)
    (h1 : q ∣ 4 * p + 1) (h2 : q ∣ p + 4 * (a * a)) :
    q ∣ 16 * (a * a) - 1 := by
  have h4 : q ∣ 4 * (p + 4 * (a * a)) := Nat.dvd_mul_left_of_dvd h2 4
  have h16 : 1 ≤ 16 * (a * a) := by
    have : 1 ≤ a * a := Nat.mul_le_mul ha ha
    omega
  have hL : 4 * (p + 4 * (a * a)) = (4 * p + 1) + (16 * (a * a) - 1) := by
    have hr : 4 * (p + 4 * (a * a)) = 4 * p + 4 * (4 * (a * a)) := Nat.mul_add _ _ _
    have h16' : 4 * (4 * (a * a)) = 16 * (a * a) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hr, h16']
    calc 4 * p + 16 * (a * a)
        = 4 * p + ((16 * (a * a) - 1) + 1) := by rw [Nat.sub_add_cancel h16]
      _ = 4 * p + (1 + (16 * (a * a) - 1)) := by rw [Nat.add_comm (16 * (a * a) - 1)]
      _ = (4 * p + 1) + (16 * (a * a) - 1) := (Nat.add_assoc _ _ _).symm
  have hsub : q ∣ 4 * (p + 4 * (a * a)) - (4 * p + 1) := Nat.dvd_sub h4 h1
  have hid : 4 * (p + 4 * (a * a)) - (4 * p + 1) = 16 * (a * a) - 1 := by
    rw [hL, Nat.add_sub_cancel_left]
  rwa [hid] at hsub

/-- A factor `q ≡ 3 (mod 4)` of `4p+1` with `7 ≤ q` and `q+1 ≤ 4D`
    is a t=1 remainder slot at `a = (q+1)/4`. -/
theorem d1_t1_slot_of_four_p_plus_one {p q D : Nat}
    (h3 : q % 4 = 3) (hq7 : 7 ≤ q) (hD : q + 1 ≤ 4 * D)
    (hdvd : q ∣ 4 * p + 1) :
    ∃ a t q', 2 ≤ a ∧ a ≤ D ∧ 0 < t ∧ 3 ≤ q' ∧
      q' + 1 = 4 * a * t ∧ q' ∣ t * p + a := by
  let a := (q + 1) / 4
  have hmod : (q + 1) % 4 = 0 := by omega
  have hqt : q + 1 = 4 * a :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
  have ha2 : 2 ≤ a := by
    have : 8 ≤ q + 1 := by omega
    have : 8 ≤ 4 * a := by rw [← hqt]; exact this
    omega
  have hA : a ≤ D := by
    have : 4 * a ≤ 4 * D := by
      rw [← hqt]; exact hD
    omega
  have hq3 : 3 ≤ q := by omega
  have hpa : q ∣ p + a := (d1_t1_four_p_plus_one_iff hqt h3).mp hdvd
  have ht : q + 1 = 4 * a * 1 := by simpa using hqt
  exact ⟨a, 1, q, ha2, hA, by omega, hq3, ht, by simpa using hpa⟩

/-- **Point-landing family** (character shadow): any residue class
    `p ≡ −4a²d (mod q)` with `q ≡ −1 (mod 4ad)` lands. -/
theorem point_landing {a d q p : Nat}
    (ha : 0 < a) (hd : 0 < d) (hp : 0 < p) (hq3 : 3 ≤ q)
    (hmod : (q + 1) % (4 * a * d) = 0)
    (hres : (p + 4 * (a * a * d)) % q = 0) :
    ∃ a' c' d' m', Witness p a' c' d' m' :=
  divisor_form_sound ha hd hp hq3 hmod (Nat.dvd_of_mod_eq_zero hres)

/-- **Deterministic point-landing** (one instance of the family): a hard
    prime p ≡ 8 (mod 11) is covered via (a, d, q) = (3, 1, 11). -/
theorem point_landing_11 {p : Nat} (hp : 0 < p) (h : p % 11 = 8) :
    ∃ a' c' d' m', Witness p a' c' d' m' := by
  have hres : (p + 4 * (3 * 3 * 1)) % 11 = 0 := by omega
  exact point_landing (a := 3) (d := 1) (q := 11)
    (by omega) (by omega) hp (by omega) (by decide) hres

/-! ### 3-mod-4-free shifts (the totally-split monoid) -/

/-- A number whose odd prime factors are all `1 (mod 4)`.  Odd such numbers
    are represented by `x² + 4y²` (Fermat); this is the totally-split monoid. -/
def ThreeModFourFree (n : Nat) : Prop :=
  ∀ q, IsPrime q → q ∣ n → q % 4 ≠ 3

/-- A divisor `q ≡ 3 (mod 4)` of `p+4` is a d=1, a=1 landing. -/
theorem d1_a1_of_three_mod_four_factor {p q : Nat}
    (hp : 0 < p) (h2 : 2 ≤ q) (h3 : q % 4 = 3) (hdvd : q ∣ p + 4) :
    ∃ a' c' d' m', Witness p a' c' d' m' := by
  have hq3 : 3 ≤ q := by omega
  have hmod : (q + 1) % (4 * 1 * 1) = 0 := by omega
  have hdvd' : q ∣ p + 4 * (1 * 1 * 1) := by simpa using hdvd
  exact divisor_form_sound (a := 1) (d := 1) (q := q)
    (by omega) (by omega) hp hq3 hmod hdvd'

theorem IsPrime.ne_two_odd {r : Nat} (hr : IsPrime r) (hne2 : r ≠ 2) :
    r % 2 = 1 := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := Nat.mod_two_eq_zero_or_one r
  rcases hmod with hev | hodd
  · have h2 : 2 ∣ r := Nat.dvd_of_mod_eq_zero hev
    have h2eq : 2 = 1 ∨ 2 = r := hr.2 2 h2
    rcases h2eq with h | h
    · omega
    · exact False.elim (hne2 h.symm)
  · exact hodd

theorem IsPrime.ne_two_mod4 {r : Nat} (hr : IsPrime r) (hne2 : r ≠ 2) :
    r % 4 = 1 ∨ r % 4 = 3 := by
  have hodd := IsPrime.ne_two_odd hr hne2
  have hlt : r % 4 < 4 := Nat.mod_lt r (by
    have : 2 ≤ r := hr.1
    omega)
  have h24 : (r % 4) % 2 = r % 2 := Nat.mod_mod_of_dvd r (show 2 ∣ 4 by decide)
  rw [hodd] at h24
  have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases this with h | h | h | h
  · rw [h] at h24; cases h24
  · exact Or.inl h
  · rw [h] at h24; cases h24
  · exact Or.inr h

/-- Any `q ≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`. -/
theorem exists_three_mod_four_prime_factor (q : Nat)
    (hq2 : 2 ≤ q) (hq3 : q % 4 = 3) :
    ∃ r, IsPrime r ∧ r ∣ q ∧ r % 4 = 3 :=
  Nat.strongRecOn (motive := fun n =>
      2 ≤ n → n % 4 = 3 → ∃ r, IsPrime r ∧ r ∣ n ∧ r % 4 = 3) q
    (fun q ih hq2 hq3 => by
      obtain ⟨r, hr, hrdvd⟩ := exists_prime_factor q hq2
      have hne2 : r ≠ 2 := by
        intro h; subst h
        have : q % 2 = 0 := Nat.mod_eq_zero_of_dvd hrdvd
        omega
      rcases IsPrime.ne_two_mod4 hr hne2 with h1 | h3r
      · have hmul : (q / r) * r = q := Nat.div_mul_cancel hrdvd
        have hrpos : 1 < r := by
          have : 2 ≤ r := hr.1
          omega
        have hqr_ne0 : q / r ≠ 0 := by
          intro h0
          rw [h0, Nat.zero_mul] at hmul
          omega
        have hqr_ne1 : q / r ≠ 1 := by
          intro h1'
          rw [h1', Nat.one_mul] at hmul
          have : r % 4 = 3 := by
            rw [hmul]; exact hq3
          omega
        have hqr2 : 2 ≤ q / r := by
          have : 0 < q / r := Nat.pos_of_ne_zero hqr_ne0
          omega
        have hlt : q / r < q := Nat.div_lt_self (by omega) hrpos
        have hmod : (q / r) % 4 = 3 := by
          have : ((q / r) % 4 * (r % 4)) % 4 = q % 4 := by
            rw [← Nat.mul_mod, hmul]
          rw [h1, hq3] at this
          have hlt' : (q / r) % 4 < 4 := Nat.mod_lt _ (by omega)
          omega
        obtain ⟨s, hs, hsdvd, hs3⟩ := ih (q / r) hlt hqr2 hmod
        refine ⟨s, hs, ?_, hs3⟩
        exact Nat.dvd_trans hsdvd ⟨r, hmul.symm⟩
      · exact ⟨r, hr, hrdvd, h3r⟩) hq2 hq3

/-- No d=1, a=1 landing when `p+4` is 3-mod-4-free. -/
theorem not_d1_a1_of_free {p q : Nat} (hfree : ThreeModFourFree (p + 4))
    (hq3 : 3 ≤ q) (hmod : (q + 1) % 4 = 0) (hdvd : q ∣ p + 4) : False := by
  have hq2 : 2 ≤ q := by omega
  have hq4 : q % 4 = 3 := by omega
  obtain ⟨r, hr, hrdvd, hr3⟩ := exists_three_mod_four_prime_factor q hq2 hq4
  exact hfree r hr (Nat.dvd_trans hrdvd hdvd) hr3

/-- Failure of 3-mod-4-freeness is a 3-mod-4 prime factor. -/
theorem not_threeModFourFree_iff (n : Nat) :
    ¬ ThreeModFourFree n ↔ ∃ q, IsPrime q ∧ q ∣ n ∧ q % 4 = 3 := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Classical.not_forall.mp h
    obtain ⟨hP, hq⟩ := Classical.not_imp.mp hq
    obtain ⟨hdvd, hne⟩ := Classical.not_imp.mp hq
    refine ⟨q, hP, hdvd, ?_⟩
    exact Classical.not_not.mp hne
  · intro ⟨q, hP, hdvd, h3⟩ hfree
    exact hfree q hP hdvd h3

/-- If `p+4` is not totally-split, the d=1 bound holds already at `a = 1`. -/
theorem d1_slot_of_not_a1_free {p D : Nat}
    (_hp : 0 < p) (hD : 1 ≤ D)
    (h : ¬ ThreeModFourFree (p + 4)) :
    ∃ a q, 0 < a ∧ a ≤ D ∧ 3 ≤ q ∧
      (q + 1) % (4 * a) = 0 ∧ q ∣ p + 4 * (a * a) := by
  obtain ⟨q, hP, hdvd, h3⟩ := (not_threeModFourFree_iff (p + 4)).mp h
  have hq3 : 3 ≤ q := by
    have : 2 ≤ q := hP.1
    omega
  have hmod : (q + 1) % (4 * 1) = 0 := by omega
  have hdvd' : q ∣ p + 4 * (1 * 1) := by simpa using hdvd
  exact ⟨1, q, by omega, hD, hq3, hmod, hdvd'⟩

/-- **Class-roughness** of the slot `(p, a)`: `p+4a²` has no divisor
    `q ≡ −1 (mod 4a)`.  This is the 0/1 multiplicative indicator `F` in the
    Henriot/Nair–Tenenbaum setup for the family `Q_a = X + 4a²`.  Strictly
    weaker than 3-mod-4-freeness (unaligned 3-mod-4 factors are allowed). -/
def ClassRough (p a : Nat) : Prop :=
  ∀ q, 3 ≤ q → (q + 1) % (4 * a) = 0 → ¬ q ∣ p + 4 * (a * a)

theorem classRough_of_threeModFourFree {p a : Nat} (ha : 0 < a)
    (h : ThreeModFourFree (p + 4 * (a * a))) :
    ClassRough p a := by
  intro q hq3 hmod hdvd
  have h4 : q % 4 = 3 := mod4_eq_three_of_d1_aligned ha hmod
  obtain ⟨r, hr, hrdvd, hr3⟩ :=
    exists_three_mod_four_prime_factor q (by omega) h4
  exact h r hr (Nat.dvd_trans hrdvd hdvd) hr3

theorem not_classRough_iff {p a : Nat} :
    ¬ ClassRough p a ↔
      ∃ q, 3 ≤ q ∧ (q + 1) % (4 * a) = 0 ∧ q ∣ p + 4 * (a * a) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Classical.not_forall.mp h
    obtain ⟨hq3, hq⟩ := Classical.not_imp.mp hq
    obtain ⟨hmod, hne⟩ := Classical.not_imp.mp hq
    exact ⟨q, hq3, hmod, Classical.not_not.mp hne⟩
  · intro ⟨q, hq3, hmod, hdvd⟩ hrough
    exact hrough q hq3 hmod hdvd

/-- Failure of class-roughness is failure of 3-mod-4-freeness (aligned
    divisors are `≡ 3 (mod 4)`), but not conversely. -/
theorem not_threeModFourFree_of_not_classRough {p a : Nat} (ha : 0 < a)
    (h : ¬ ClassRough p a) :
    ¬ ThreeModFourFree (p + 4 * (a * a)) := by
  intro hfree
  exact h (classRough_of_threeModFourFree ha hfree)

/-- Hard primes below 10000 satisfy ES (via the covering certificate). -/
theorem hard_es_below_10000 {p : Nat}
    (hp : IsPrime p) (h : p < 10000) :
    ∃ x y z, IsES p x y z :=
  es_below_100000 hp.1 (Nat.lt_trans h (by decide : (10000 : Nat) < 100000))

/-- QED from the growing-bound divisor interface, finite range discharged. -/
theorem erdos_straus_of_divisor_landing
    (Dlevel : Nat → Nat)
    (h : DivisorLandingBound Dlevel 10000) :
    ErdosStraus :=
  conditional_qed_hard <|
    hard_landing_of_divisor_interface Dlevel 10000 h fun _p hlt hp _ =>
      hard_es_below_10000 hp hlt

/-- QED from the analytic covering interface, finite range discharged. -/
theorem erdos_straus_of_analytic_landing
    (Alevel : Nat → Nat)
    (h : AnalyticSurvivorBound Alevel 10000) :
    ErdosStraus :=
  erdos_straus_of_interface Alevel 10000 h fun _p hlt hp _ =>
    hard_es_below_10000 hp hlt

/-- QED from the hybrid covering interface, finite range discharged. -/
theorem erdos_straus_of_hybrid_landing
    (Alevel : Nat → Nat)
    (h : HybridSurvivorBound Alevel 10000) :
    ErdosStraus :=
  erdos_straus_of_hybrid Alevel 10000 h fun _p hlt hp _ =>
    hard_es_below_10000 hp hlt

/-- Hard primes miss the first aligned modulus: `3 ∤ p+4`. -/
theorem hard_not_d1_a1_q3 {p : Nat} (h : HardClass p) : ¬ 3 ∣ p + 4 := by
  have h3 : p % 3 = 1 := (hardClass_mod h).2
  intro hdvd
  have : (p + 4) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  omega

/-- d=1 slice of the divisor interface (the first DFI experiment). -/
def D1DivisorLandingBound (Dlevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p →
    ∃ a q, 0 < a ∧ a ≤ Dlevel p ∧ 3 ≤ q ∧
      (q + 1) % (4 * a) = 0 ∧ q ∣ p + 4 * (a * a)

/-- d=1 landing implies the two-parameter divisor interface (`d = 1`). -/
theorem divisor_landing_of_d1
    (Dlevel : Nat → Nat) (X0 : Nat)
    (hD : ∀ p, X0 ≤ p → 1 ≤ Dlevel p)
    (h : D1DivisorLandingBound Dlevel X0) :
    DivisorLandingBound Dlevel X0 := by
  intro p hge hp hhard
  obtain ⟨a, q, ha, hA, hq3, hmod, hdvd⟩ := h p hge hp hhard
  refine ⟨a, 1, q, ha, by omega, hA, hD p hge, hq3, ?_, ?_⟩
  · simpa using hmod
  · simpa using hdvd

/-- QED from the d=1 growing-bound divisor interface. -/
theorem erdos_straus_of_d1_divisor_landing
    (Dlevel : Nat → Nat)
    (hD : ∀ p, 10000 ≤ p → 1 ≤ Dlevel p)
    (h : D1DivisorLandingBound Dlevel 10000) :
    ErdosStraus :=
  erdos_straus_of_divisor_landing Dlevel
    (divisor_landing_of_d1 Dlevel 10000 hD h)

/-- Remaining d=1 obligation: a=1-split hard primes still land at some `a ≥ 2`.
    (The a=1 totally-split set is nonempty — the d=1 escapees — so this is
    strictly weaker than asking every hard prime to split at a=1.) -/
def D1Remainder (Dlevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p →
    ThreeModFourFree (p + 4) →
      ∃ a q, 2 ≤ a ∧ a ≤ Dlevel p ∧ 3 ≤ q ∧
        (q + 1) % (4 * a) = 0 ∧ q ∣ p + 4 * (a * a)

/-- Split: non-split `p+4` lands at a=1; the rest is `D1Remainder`. -/
theorem D1DivisorLandingBound_of_remainder
    (Dlevel : Nat → Nat) (X0 : Nat)
    (hD : ∀ p, X0 ≤ p → 1 ≤ Dlevel p)
    (hrem : D1Remainder Dlevel X0) :
    D1DivisorLandingBound Dlevel X0 := by
  intro p hge hp hhard
  by_cases hfree : ThreeModFourFree (p + 4)
  · obtain ⟨a, q, ha2, hA, hq3, hmod, hdvd⟩ := hrem p hge hp hhard hfree
    exact ⟨a, q, by omega, hA, hq3, hmod, hdvd⟩
  · have hn : 0 < p := by obtain ⟨h2, _⟩ := hp; omega
    exact d1_slot_of_not_a1_free hn (hD p hge) hfree

/-- QED from the d=1 remainder (a=1-split hard primes at growing `a ≥ 2`). -/
theorem erdos_straus_of_d1_remainder
    (Dlevel : Nat → Nat)
    (hD : ∀ p, 10000 ≤ p → 1 ≤ Dlevel p)
    (h : D1Remainder Dlevel 10000) :
    ErdosStraus :=
  erdos_straus_of_d1_divisor_landing Dlevel hD
    (D1DivisorLandingBound_of_remainder Dlevel 10000 hD h)

/-- Parametric form of `D1Remainder`: some `a ≥ 2` and cofactor `t`
    with `q + 1 = 4at` and `q ∣ tp + a`. -/
def D1RemainderParam (Dlevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p →
    ThreeModFourFree (p + 4) →
      ∃ a t q, 2 ≤ a ∧ a ≤ Dlevel p ∧ 0 < t ∧ 3 ≤ q ∧
        q + 1 = 4 * a * t ∧ q ∣ t * p + a

theorem D1Remainder_iff_param (Dlevel : Nat → Nat) (X0 : Nat) :
    D1Remainder Dlevel X0 ↔ D1RemainderParam Dlevel X0 := by
  constructor
  · intro h p hge hp hhard hfree
    obtain ⟨a, q, ha2, hA, hq3, hmod, hdvd⟩ := h p hge hp hhard hfree
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hmod
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0; omega
      · exact h0
    exact ⟨a, t, q, ha2, hA, htpos, hq3, ht,
      (d1_aligned_divides_iff ht).mp hdvd⟩
  · intro h p hge hp hhard hfree
    obtain ⟨a, t, q, ha2, hA, _htpos, hq3, ht, hdvd⟩ := h p hge hp hhard hfree
    have hmod : (q + 1) % (4 * a) = 0 :=
      Nat.mod_eq_zero_of_dvd ⟨t, ht⟩
    exact ⟨a, q, ha2, hA, hq3, hmod,
      (d1_aligned_divides_iff ht).mpr hdvd⟩

/-- QED from the parametric d=1 remainder (`q ∣ tp + a` with `q + 1 = 4at`). -/
theorem erdos_straus_of_d1_remainder_param
    (Dlevel : Nat → Nat)
    (hD : ∀ p, 10000 ≤ p → 1 ≤ Dlevel p)
    (h : D1RemainderParam Dlevel 10000) :
    ErdosStraus :=
  erdos_straus_of_d1_remainder Dlevel hD
    ((D1Remainder_iff_param Dlevel 10000).mpr h)

/-- t=1 slice of the remainder: a 3-mod-4 factor of `4p+1` in `[7, 4D]`.
    Sufficient, not necessary — `4p+1` may be 3-mod-4-free, or all such
    factors may exceed `4D`. -/
def D1FourPPlusOneBound (Dlevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p →
    ThreeModFourFree (p + 4) →
      ∃ q, 7 ≤ q ∧ q % 4 = 3 ∧ q + 1 ≤ 4 * Dlevel p ∧ q ∣ 4 * p + 1

theorem D1RemainderParam_of_four_p_plus_one
    (Dlevel : Nat → Nat) (X0 : Nat)
    (h : D1FourPPlusOneBound Dlevel X0) :
    D1RemainderParam Dlevel X0 := by
  intro p hge hp hhard hfree
  obtain ⟨q, hq7, h3, hDq, hdvd⟩ := h p hge hp hhard hfree
  exact d1_t1_slot_of_four_p_plus_one h3 hq7 hDq hdvd

/-- QED from a 3-mod-4 factor of `4p+1` at growing `D`. -/
theorem erdos_straus_of_d1_four_p_plus_one
    (Dlevel : Nat → Nat)
    (hD : ∀ p, 10000 ≤ p → 1 ≤ Dlevel p)
    (h : D1FourPPlusOneBound Dlevel 10000) :
    ErdosStraus :=
  erdos_straus_of_d1_remainder_param Dlevel hD
    (D1RemainderParam_of_four_p_plus_one Dlevel 10000 h)

/-! ### Henriot / Nair–Tenenbaum interface (door (b), d=1 family)

The published bounds are mean-value statements for short sums of a
multiplicative `F` along a polynomial family.  For `Q_a = X + 4a²` the
correct `F` is class-roughness, not 3-mod-4-freeness: only an *aligned*
factor lands.  A uniform bound with `M(p) + 1 < D(p)` empties the
exceptional set and is QED.  A mean-value bound that only saves a power
on the exceptional *count* (plan §4h.4) is a record candidate and is
**not** wired to `ErdosStraus`. -/

/-- Odd integers are coprime to 4. -/
theorem coprime_four_of_odd {q : Nat} (h : q % 2 = 1) : Nat.Coprime q 4 := by
  have hg : Nat.gcd q 4 ∣ 4 := Nat.gcd_dvd_right q 4
  have hle : Nat.gcd q 4 ≤ 4 := Nat.le_of_dvd (by omega) hg
  have hpos : 0 < Nat.gcd q 4 := Nat.gcd_pos_of_pos_right q (by omega)
  have hvals : Nat.gcd q 4 = 1 ∨ Nat.gcd q 4 = 2 ∨ Nat.gcd q 4 = 3 ∨ Nat.gcd q 4 = 4 := by
    omega
  rcases hvals with h1 | h2 | h3 | h4g
  · exact h1
  · exfalso
    have : 2 ∣ q :=
      Nat.dvd_trans (h2 ▸ Nat.dvd_refl 2) (Nat.gcd_dvd_left q 4)
    have : q % 2 = 0 := Nat.mod_eq_zero_of_dvd this
    omega
  · exfalso
    have : 3 ∣ 4 := Nat.dvd_trans (h3 ▸ Nat.dvd_refl 3) hg
    have : 4 % 3 = 0 := Nat.mod_eq_zero_of_dvd this
    omega
  · exfalso
    have : 2 ∣ q :=
      Nat.dvd_trans (by decide : 2 ∣ 4) (h4g ▸ Nat.gcd_dvd_left q 4)
    have : q % 2 = 0 := Nat.mod_eq_zero_of_dvd this
    omega

/-- Difference of two d=1 shifts: `(p+4a²) − (p+4b²) = 4(a²−b²)` for `b ≤ a`. -/
theorem shift_sub {p a b : Nat} (hba : b ≤ a) :
    (p + 4 * (a * a)) - (p + 4 * (b * b)) = 4 * (a * a - b * b) := by
  have hsq : b * b ≤ a * a := Nat.mul_le_mul hba hba
  have h4 : 4 * (b * b) ≤ 4 * (a * a) := Nat.mul_le_mul_left 4 hsq
  have hdist : 4 * (a * a - b * b) = 4 * (a * a) - 4 * (b * b) :=
    Nat.mul_sub_left_distrib 4 (a * a) (b * b)
  have hid : p + 4 * (a * a) =
      (p + 4 * (b * b)) + (4 * (a * a) - 4 * (b * b)) := by omega
  calc (p + 4 * (a * a)) - (p + 4 * (b * b))
      = 4 * (a * a) - 4 * (b * b) := by
        have := Nat.add_sub_cancel_left (p + 4 * (b * b)) (4 * (a * a) - 4 * (b * b))
        rw [← hid] at this
        exact this
    _ = 4 * (a * a - b * b) := hdist.symm

/-- A common prime factor of two shifts divides `4(a²−b²)`. -/
theorem dvd_four_sq_diff {q p a b : Nat} (hba : b ≤ a)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b)) :
    q ∣ 4 * (a * a - b * b) := by
  have hsub : q ∣ (p + 4 * (a * a)) - (p + 4 * (b * b)) := Nat.dvd_sub ha hb
  rwa [shift_sub (p := p) hba] at hsub

/-- **Local density ρ ≤ 2 (two classes).** An odd prime dividing two
    shifts `p+4a²`, `p+4b²` (`b ≤ a`) divides `a−b` or `a+b`.
    This is Hensel/ρ for the family `Q_a = X + 4a²` (plan §4h.2). -/
theorem odd_prime_shift_classes {q p a b : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2) (hba : b ≤ a)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b)) :
    q ∣ (a - b) ∨ q ∣ (a + b) := by
  have hodd := IsPrime.ne_two_odd hP hne2
  have hcop := coprime_four_of_odd hodd
  have h4 : q ∣ 4 * (a * a - b * b) := dvd_four_sq_diff hba ha hb
  have hsq : q ∣ (a * a - b * b) := hcop.dvd_of_dvd_mul_left h4
  have hfact : a * a - b * b = (a + b) * (a - b) :=
    Nat.mul_self_sub_mul_self_eq a b
  have hmul : q ∣ (a + b) * (a - b) := by rwa [hfact] at hsq
  exact (hP.dvd_or_dvd hmul).symm

/-- Three distinct hits by the same odd prime span at least `q`.
    Hence at most two hits in any interval of length `q` (ρ ≤ 2). -/
theorem three_shift_hits_span {q p a b c : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hab : a < b) (hbc : b < c)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b))
    (hc : q ∣ p + 4 * (c * c)) :
    q ≤ c - a := by
  have ab := odd_prime_shift_classes (a := b) (b := a) hP hne2
    (Nat.le_of_lt hab) hb ha
  have ac := odd_prime_shift_classes (a := c) (b := a) hP hne2
    (Nat.le_of_lt (Nat.lt_trans hab hbc)) hc ha
  rcases ab with hdiff | hsum
  · have hpos : 0 < b - a := Nat.sub_pos_of_lt hab
    have hqle : q ≤ b - a := Nat.le_of_dvd hpos hdiff
    have hspan : b - a ≤ c - a :=
      Nat.sub_le_sub_right (Nat.le_of_lt hbc) a
    exact Nat.le_trans hqle hspan
  · rcases ac with hacd | hacs
    · have hpos : 0 < c - a := Nat.sub_pos_of_lt (Nat.lt_trans hab hbc)
      exact Nat.le_of_dvd hpos hacd
    · have hacs' : q ∣ a + c := by rw [Nat.add_comm]; exact hacs
      have hsum' : q ∣ a + b := by rw [Nat.add_comm]; exact hsum
      have hsub : q ∣ (a + c) - (a + b) := Nat.dvd_sub hacs' hsum'
      have hid : (a + c) - (a + b) = c - b := by omega
      have hcb : q ∣ c - b := by rwa [hid] at hsub
      have hpos : 0 < c - b := Nat.sub_pos_of_lt hbc
      have hqle : q ≤ c - b := Nat.le_of_dvd hpos hcb
      have hspan : c - b ≤ c - a := Nat.sub_le_sub_left (Nat.le_of_lt hab) c
      exact Nat.le_trans hqle hspan

/-- **ρ ≤ 2 on short intervals.** An odd prime cannot divide `p+4a²` for
    three distinct `a` in an interval of length `q`. -/
theorem no_three_hits_in_interval_len_q {q p a b c : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hab : a < b) (hbc : b < c) (hspan : c < a + q)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b))
    (hc : q ∣ p + 4 * (c * c)) :
    False := by
  have hle := three_shift_hits_span hP hne2 hab hbc ha hb hc
  have hlt : c - a < q := by omega
  omega

/-- **Hub bound.** An odd prime dividing two distinct shifts in the box
    `[·, D]` is `≤ 2D` (it divides `a−b` or `a+b`). -/
theorem hub_prime_le_two_mul_D {q p a b D : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hba : b < a) (haD : a ≤ D)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b)) :
    q ≤ 2 * D := by
  have hcls := odd_prime_shift_classes hP hne2 (Nat.le_of_lt hba) ha hb
  have hbD : b ≤ D := Nat.le_trans (Nat.le_of_lt hba) haD
  rcases hcls with hdiff | hsum
  · have hpos : 0 < a - b := Nat.sub_pos_of_lt hba
    have hqle : q ≤ a - b := Nat.le_of_dvd hpos hdiff
    have hle : a - b ≤ D := Nat.le_trans (Nat.sub_le a b) haD
    omega
  · have hpos : 0 < a + b := by omega
    have hqle : q ≤ a + b := Nat.le_of_dvd hpos hsum
    have hle : a + b ≤ D + D := Nat.add_le_add haD hbD
    omega

/-- **Uniqueness of large prime factors.** If `q > 2D`, it divides
    `p+4a²` for at most one `a ≤ D`. -/
theorem at_most_one_hit_of_q_gt_two_D {q p a b D : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hba : b < a) (haD : a ≤ D) (hgt : 2 * D < q)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b)) :
    False := by
  have := hub_prime_le_two_mul_D hP hne2 hba haD ha hb
  omega

/-- **ρ ≤ 2 on the whole box.** If `q > D`, then `q` divides `p+4a²`
    for at most two values `a ≤ D`. -/
theorem at_most_two_hits_in_box {q p a b c D : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hab : a < b) (hbc : b < c) (hD : c ≤ D) (hgt : D < q)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b))
    (hc : q ∣ p + 4 * (c * c)) :
    False := by
  have hspan := three_shift_hits_span hP hne2 hab hbc ha hb hc
  have hle : c - a ≤ D := Nat.le_trans (Nat.sub_le c a) hD
  omega

/-- Five distinct hits span at least `2q` (two steps of the ρ ≤ 2 packing). -/
theorem five_hits_span_two_q {q p a b c d e : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b))
    (hc : q ∣ p + 4 * (c * c)) (hd : q ∣ p + 4 * (d * d))
    (he : q ∣ p + 4 * (e * e)) :
    2 * q ≤ e - a := by
  have hca := three_shift_hits_span hP hne2 hab hbc ha hb hc
  have hec := three_shift_hits_span (a := c) (b := d) (c := e)
    hP hne2 hcd hde hc hd he
  have : (c - a) + (e - c) = e - a := by omega
  omega

/-- If `2q > D`, then `q` hits at most four slots in `[·, D]`. -/
theorem at_most_four_hits_of_q_gt_half_D {q p a b c d e D : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (heD : e ≤ D) (hgt : D < 2 * q)
    (ha : q ∣ p + 4 * (a * a)) (hb : q ∣ p + 4 * (b * b))
    (hc : q ∣ p + 4 * (c * c)) (hd : q ∣ p + 4 * (d * d))
    (he : q ∣ p + 4 * (e * e)) :
    False := by
  have hspan := five_hits_span_two_q hP hne2 hab hbc hcd hde ha hb hc hd he
  have hle : e - a ≤ D := Nat.le_trans (Nat.sub_le e a) heD
  omega

/-- Strictly increasing on `{0,…,n−1}` implies `f 0 ≤ f n`. -/
theorem strict_mono_le {f : Nat → Nat} {n : Nat}
    (h : ∀ i, i < n → f i < f (i + 1)) : f 0 ≤ f n := by
  induction n with
  | zero => exact Nat.le_refl (f 0)
  | succ n ih =>
    have ih' := ih (fun i hi => h i (by omega))
    have hlast : f n < f (n + 1) := h n (by omega)
    exact Nat.le_trans ih' (Nat.le_of_lt hlast)

/-- **ρ ≤ 2 packing.** `2k+1` strictly increasing hits span at least `kq`. -/
theorem odd_hits_span {q p : Nat} (hP : IsPrime q) (hne2 : q ≠ 2) :
    ∀ (k : Nat) (f : Nat → Nat),
      (∀ i, i < 2 * k → f i < f (i + 1)) →
      (∀ i, i ≤ 2 * k → q ∣ p + 4 * (f i * f i)) →
      k * q ≤ f (2 * k) - f 0 := by
  intro k
  induction k with
  | zero =>
    intro f _ _
    simp [Nat.zero_mul, Nat.sub_self]
  | succ k ih =>
    intro f hmono hhits
    have h01 : f 0 < f 1 := hmono 0 (by omega)
    have h12 : f 1 < f 2 := hmono 1 (by omega)
    have hspan := three_shift_hits_span (a := f 0) (b := f 1) (c := f 2)
      hP hne2 h01 h12 (hhits 0 (by omega)) (hhits 1 (by omega))
      (hhits 2 (by omega))
    have ih' := ih (fun i => f (i + 2))
      (fun i hi => hmono (i + 2) (by omega))
      (fun i hi => hhits (i + 2) (by omega))
    have hle02 : f 0 ≤ f 2 :=
      strict_mono_le (f := f) (n := 2) (fun i hi => hmono i (by omega))
    have hle2e : f 2 ≤ f (2 * k + 2) :=
      strict_mono_le (f := fun i => f (i + 2)) (n := 2 * k)
        (fun i hi => hmono (i + 2) (by omega))
    have hsum : (f 2 - f 0) + (f (2 * k + 2) - f 2) =
        f (2 * k + 2) - f 0 := by omega
    have hidx : 2 * Nat.succ k = 2 * k + 2 := by omega
    rw [hidx, Nat.succ_mul]
    calc k * q + q
        = q + k * q := Nat.add_comm _ _
      _ ≤ (f 2 - f 0) + (f (2 * k + 2) - f 2) := Nat.add_le_add hspan ih'
      _ = f (2 * k + 2) - f 0 := hsum

/-- `2k+1` hits in `[·, D]` force `kq ≤ D`. -/
theorem odd_hits_in_box {q p D : Nat} (hP : IsPrime q) (hne2 : q ≠ 2)
    (k : Nat) (f : Nat → Nat)
    (hmono : ∀ i, i < 2 * k → f i < f (i + 1))
    (hhits : ∀ i, i ≤ 2 * k → q ∣ p + 4 * (f i * f i))
    (hD : f (2 * k) ≤ D) :
    k * q ≤ D := by
  have hspan := odd_hits_span hP hne2 k f hmono hhits
  have : f (2 * k) - f 0 ≤ D := Nat.le_trans (Nat.sub_le _ _) hD
  omega

/-- If `kq > D`, then `q` has at most `2k` hits in `[·, D]`. -/
theorem odd_hits_impossible_of_kq_gt_D {q p D : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (k : Nat) (f : Nat → Nat)
    (hmono : ∀ i, i < 2 * k → f i < f (i + 1))
    (hhits : ∀ i, i ≤ 2 * k → q ∣ p + 4 * (f i * f i))
    (hD : f (2 * k) ≤ D) (hgt : D < k * q) : False := by
  have := odd_hits_in_box hP hne2 k f hmono hhits hD
  omega

/-- `(D/q + 1) q > D`. -/
theorem div_succ_mul_gt {D q : Nat} (hq : 0 < q) :
    D < (D / q + 1) * q := by
  have hmod : D % q < q := Nat.mod_lt D hq
  have hsplit : q * (D / q) + D % q = D := Nat.div_add_mod D q
  calc D
      = q * (D / q) + D % q := hsplit.symm
    _ < q * (D / q) + q := Nat.add_lt_add_left hmod _
    _ = D / q * q + q := by rw [Nat.mul_comm q]
    _ = (D / q + 1) * q := by rw [Nat.add_mul, Nat.one_mul]

/-- **Global packing (plan §4h.2).** At most `2(D/q+1)` hits in `[·, D]`:
    `2(D/q+1)+1` strictly increasing hits are impossible. -/
theorem odd_hits_impossible_div_succ {q p D : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (f : Nat → Nat)
    (hmono : ∀ i, i < 2 * (D / q + 1) → f i < f (i + 1))
    (hhits : ∀ i, i ≤ 2 * (D / q + 1) → q ∣ p + 4 * (f i * f i))
    (hD : f (2 * (D / q + 1)) ≤ D) : False := by
  have hq : 0 < q := by obtain ⟨h2, _⟩ := hP; omega
  exact odd_hits_impossible_of_kq_gt_D hP hne2 (D / q + 1) f
    hmono hhits hD (div_succ_mul_gt hq)

/-- A large aligned prime factor is a unique landing in the box. -/
theorem unique_large_aligned_landing {q p a b D : Nat}
    (hP : IsPrime q) (hne2 : q ≠ 2)
    (hba : b < a) (haD : a ≤ D) (hgt : 2 * D < q)
    (_hmod : (q + 1) % (4 * a) = 0)
    (hdvd : q ∣ p + 4 * (a * a))
    (hbdvd : q ∣ p + 4 * (b * b)) :
    False :=
  at_most_one_hit_of_q_gt_two_D hP hne2 hba haD hgt hdvd hbdvd

/-- Alignment `q ≡ −1 (mod 4a)` forces `a ∣ (q+1)/4`, so a fixed `q`
    can land only at divisors of `(q+1)/4`. -/
theorem aligned_dvd_half_succ {a q : Nat}
    (hmod : (q + 1) % (4 * a) = 0) :
    a ∣ (q + 1) / 4 := by
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hmod
  have h4 : 4 ∣ q + 1 :=
    Nat.dvd_trans (Nat.dvd_mul_right 4 a) ⟨t, ht⟩
  have hL : 4 * ((q + 1) / 4) = q + 1 := Nat.mul_div_cancel' h4
  have hR : 4 * (a * t) = q + 1 := by
    rw [← Nat.mul_assoc]; exact ht.symm
  have heq : (q + 1) / 4 = a * t :=
    Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4) (hL.trans hR.symm)
  exact ⟨t, heq⟩

theorem not_classRough_of_aligned_dvd {p a q : Nat}
    (hq3 : 3 ≤ q) (hmod : (q + 1) % (4 * a) = 0)
    (hdvd : q ∣ p + 4 * (a * a)) :
    ¬ ClassRough p a := fun h => h q hq3 hmod hdvd

/-- Alignment forces `4a ≤ q+1`. -/
theorem aligned_mul_le_succ {a q : Nat} (_ha : 0 < a)
    (hmod : (q + 1) % (4 * a) = 0) :
    4 * a ≤ q + 1 :=
  Nat.le_of_dvd (Nat.succ_pos q) (Nat.dvd_of_mod_eq_zero hmod)

/-- Alignment `q ≡ −1 (mod 4a)` forces `q` odd. -/
theorem aligned_odd {a q : Nat} (_ha : 0 < a)
    (hmod : (q + 1) % (4 * a) = 0) : q % 2 = 1 := by
  have h4 : 4 * a ∣ q + 1 := Nat.dvd_of_mod_eq_zero hmod
  have h2 : 2 ∣ 4 * a := ⟨2 * a, by omega⟩
  have : (q + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2 h4)
  omega

/-- Alignment forces the slot `a` to be a divisor of `(q+1)/4`, hence `a ≤ (q+1)/4`. -/
theorem aligned_slot_le {a q : Nat} (ha : 0 < a)
    (hmod : (q + 1) % (4 * a) = 0) :
    a ≤ (q + 1) / 4 :=
  (Nat.le_div_iff_mul_le (by omega : 0 < 4)).mpr (by
    rw [Nat.mul_comm]
    exact aligned_mul_le_succ ha hmod)

/-- Alignment at a positive modulus forces `0 < a`. -/
theorem aligned_pos {a q : Nat} (hq : 3 ≤ q)
    (hmod : (q + 1) % (4 * a) = 0) : 0 < a := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    have : (q + 1) % 0 = q + 1 := Nat.mod_zero (q + 1)
    omega
  · exact h0

theorem dvd_two_pos {a : Nat} (ha : 0 < a) (h : a ∣ 2) : a = 1 ∨ a = 2 := by
  have : a ≤ 2 := Nat.le_of_dvd (by omega) h
  omega

theorem dvd_three_pos {a : Nat} (ha : 0 < a) (h : a ∣ 3) : a = 1 ∨ a = 3 := by
  have hle : a ≤ 3 := Nat.le_of_dvd (by omega) h
  have hcases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases hcases with h1 | h2 | h3
  · exact Or.inl h1
  · have : 3 % 2 = 0 := Nat.mod_eq_zero_of_dvd (h2 ▸ h)
    omega
  · exact Or.inr h3

/-- The aligned slots of `q = 7` are `a = 1` and `a = 2`. -/
theorem aligned_slots_q7 {a : Nat} (ha : 0 < a)
    (hmod : (7 + 1) % (4 * a) = 0) : a = 1 ∨ a = 2 := by
  have hdiv := aligned_dvd_half_succ hmod
  have h2 : (7 + 1) / 4 = 2 := by decide
  rw [h2] at hdiv
  exact dvd_two_pos ha hdiv

/-- The aligned slots of `q = 11` are `a = 1` and `a = 3`. -/
theorem aligned_slots_q11 {a : Nat} (ha : 0 < a)
    (hmod : (11 + 1) % (4 * a) = 0) : a = 1 ∨ a = 3 := by
  have hdiv := aligned_dvd_half_succ hmod
  have h3 : (11 + 1) / 4 = 3 := by decide
  rw [h3] at hdiv
  exact dvd_three_pos ha hdiv

/-- Hard primes miss every aligned `q = 7` landing (hub conditioning). -/
theorem hard_not_aligned_q7 {p a : Nat} (h : HardClass p)
    (hmod : (7 + 1) % (4 * a) = 0) :
    ¬ 7 ∣ p + 4 * (a * a) := by
  have ha : 0 < a := aligned_pos (by omega : 3 ≤ 7) hmod
  rcases aligned_slots_q7 ha hmod with ha1 | ha2
  · subst ha1
    intro hdvd
    have : (p + 4) % 7 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hm := hard_mod7 h
    omega
  · subst ha2
    intro hdvd
    have : (p + 4 * (2 * 2)) % 7 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hm := hard_mod7 h
    omega

theorem dvd_five_pos {a : Nat} (ha : 0 < a) (h : a ∣ 5) : a = 1 ∨ a = 5 := by
  have hle : a ≤ 5 := Nat.le_of_dvd (by omega) h
  have hcases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · have : 5 % 2 = 0 := Nat.mod_eq_zero_of_dvd (h2 ▸ h)
    omega
  · have : 5 % 3 = 0 := Nat.mod_eq_zero_of_dvd (h3 ▸ h)
    omega
  · have : 5 % 4 = 0 := Nat.mod_eq_zero_of_dvd (h4 ▸ h)
    omega
  · exact Or.inr h5

/-- The aligned slots of `q = 3` are only `a = 1`. -/
theorem aligned_slots_q3 {a : Nat} (ha : 0 < a)
    (hmod : (3 + 1) % (4 * a) = 0) : a = 1 := by
  have hdiv := aligned_dvd_half_succ hmod
  have h1 : (3 + 1) / 4 = 1 := by decide
  rw [h1] at hdiv
  exact Nat.eq_one_of_dvd_one hdiv

/-- The aligned slots of `q = 19` are `a = 1` and `a = 5`. -/
theorem aligned_slots_q19 {a : Nat} (ha : 0 < a)
    (hmod : (19 + 1) % (4 * a) = 0) : a = 1 ∨ a = 5 := by
  have hdiv := aligned_dvd_half_succ hmod
  have h5 : (19 + 1) / 4 = 5 := by decide
  rw [h5] at hdiv
  exact dvd_five_pos ha hdiv

/-- Hard primes miss every aligned `q = 3` landing. -/
theorem hard_not_aligned_q3 {p a : Nat} (h : HardClass p)
    (hmod : (3 + 1) % (4 * a) = 0) :
    ¬ 3 ∣ p + 4 * (a * a) := by
  have ha : 0 < a := aligned_pos (by omega : 3 ≤ 3) hmod
  have ha1 := aligned_slots_q3 ha hmod
  subst ha1
  exact hard_not_d1_a1_q3 h

/-- `1009` is hard and `≡ 8 (mod 11)`, so aligned `q = 11` at `a = 3` lands.
    Unlike `3` and `7`, the prime `11` is active on the hard classes. -/
theorem hard_1009 : HardClass 1009 := by
  unfold HardClass
  omega

theorem one_zero_zero_nine_mod11 : 1009 % 11 = 8 := by decide

theorem not_classRough_1009_a3 : ¬ ClassRough 1009 3 :=
  not_classRough_of_aligned_dvd (q := 11) (by omega)
    (by decide : (11 + 1) % (4 * 3) = 0)
    (by decide : 11 ∣ 1009 + 4 * (3 * 3))

/-- An aligned prime divisor of `840` is `3` or `7` (`2` and `5` are `≢ 3 (mod 4)`). -/
theorem prime_dvd_840_aligned {q a : Nat} (hP : IsPrime q) (ha : 0 < a)
    (hdvd : q ∣ 840) (hmod : (q + 1) % (4 * a) = 0) :
    q = 3 ∨ q = 7 := by
  have h4 := mod4_eq_three_of_d1_aligned ha hmod
  rcases prime_dvd_840 hP hdvd with h2 | h3 | h5 | h7
  · subst h2; omega
  · exact Or.inl h3
  · subst h5; omega
  · exact Or.inr h7

/-- Hard primes miss every aligned prime that divides `840`. -/
theorem hard_not_aligned_prime_dvd_840 {p a q : Nat}
    (h : HardClass p) (hP : IsPrime q) (ha : 0 < a)
    (hdvd : q ∣ 840) (hmod : (q + 1) % (4 * a) = 0) :
    ¬ q ∣ p + 4 * (a * a) := by
  rcases prime_dvd_840_aligned hP ha hdvd hmod with h3 | h7
  · subst h3; exact hard_not_aligned_q3 h hmod
  · subst h7; exact hard_not_aligned_q7 h hmod

/-- Concrete d=1 remainder landing: `1009` at `a = 3`, `q = 11`. -/
theorem d1_remainder_witness_1009 {D : Nat} (hD : 3 ≤ D) :
    ∃ a q, 2 ≤ a ∧ a ≤ D ∧ 3 ≤ q ∧
      (q + 1) % (4 * a) = 0 ∧ q ∣ 1009 + 4 * (a * a) :=
  ⟨3, 11, by omega, hD, by omega,
    by decide, by decide⟩

/-- Inner slots: hub-sized aligned moduli (`q ≤ 2D`) are possible. -/
def D1InnerSlot (a D : Nat) : Prop := 4 * a ≤ 2 * D + 1

/-- Outer slots: only aligned moduli `q > 2D` can land. -/
def D1OuterSlot (a D : Nat) : Prop := 2 * D + 1 < 4 * a

theorem inner_or_outer (a D : Nat) :
    D1InnerSlot a D ∨ D1OuterSlot a D := by
  rcases Nat.lt_or_ge (2 * D + 1) (4 * a) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- An aligned hub-sized modulus can land only at an inner slot. -/
theorem hub_aligned_is_inner {a q D : Nat} (ha : 0 < a)
    (hle : q ≤ 2 * D) (hmod : (q + 1) % (4 * a) = 0) :
    D1InnerSlot a D := by
  have : 4 * a ≤ q + 1 := aligned_mul_le_succ ha hmod
  exact Nat.le_trans this (Nat.succ_le_succ hle)

/-- An outer slot cannot have an aligned divisor `≤ B`. -/
theorem no_aligned_le_of_outer {a q B : Nat}
    (houter : B + 1 < 4 * a)
    (hmod : (q + 1) % (4 * a) = 0) (hq : q ≤ B) : False := by
  have ha : 0 < a := by omega
  have : 4 * a ≤ q + 1 := aligned_mul_le_succ ha hmod
  omega

/-- Class-roughness fails by a hub-sized aligned divisor or a large one. -/
theorem not_classRough_split {p a B : Nat} :
    ¬ ClassRough p a ↔
      (∃ q, 3 ≤ q ∧ q ≤ B ∧ (q + 1) % (4 * a) = 0 ∧
          q ∣ p + 4 * (a * a)) ∨
      (∃ q, 3 ≤ q ∧ B < q ∧ (q + 1) % (4 * a) = 0 ∧
          q ∣ p + 4 * (a * a)) := by
  constructor
  · intro h
    obtain ⟨q, hq3, hmod, hdvd⟩ := not_classRough_iff.mp h
    rcases Nat.lt_or_ge B q with hgt | hle
    · exact Or.inr ⟨q, hq3, hgt, hmod, hdvd⟩
    · exact Or.inl ⟨q, hq3, hle, hmod, hdvd⟩
  · intro h
    rcases h with ⟨q, hq3, _, hmod, hdvd⟩ | ⟨q, hq3, _, hmod, hdvd⟩
    · exact not_classRough_of_aligned_dvd hq3 hmod hdvd
    · exact not_classRough_of_aligned_dvd hq3 hmod hdvd

/-- Outer landing is a large aligned factor (hence unique in the box
    if that factor is an odd prime `> 2D`). -/
theorem outer_not_classRough_is_large {p a B : Nat}
    (houter : B + 1 < 4 * a) (h : ¬ ClassRough p a) :
    ∃ q, 3 ≤ q ∧ B < q ∧ (q + 1) % (4 * a) = 0 ∧
      q ∣ p + 4 * (a * a) := by
  rcases (not_classRough_split (p := p) (a := a) (B := B)).mp h with hsmall | hlarge
  · obtain ⟨q, _, hqB, hmod, _⟩ := hsmall
    exact False.elim (no_aligned_le_of_outer houter hmod hqB)
  · exact hlarge

theorem outer_landing_has_factor_gt_two_D {p a D : Nat}
    (houter : D1OuterSlot a D) (h : ¬ ClassRough p a) :
    ∃ q, 3 ≤ q ∧ 2 * D < q ∧ (q + 1) % (4 * a) = 0 ∧
      q ∣ p + 4 * (a * a) :=
  outer_not_classRough_is_large houter h

/-- Hub-sieve range: inner slots sit in `[1, (2D+1)/4]`. -/
theorem inner_slot_le {a D : Nat} (h : D1InnerSlot a D) :
    a ≤ (2 * D + 1) / 4 :=
  (Nat.le_div_iff_mul_le (by omega : 0 < 4)).mpr (by
    rw [Nat.mul_comm]
    exact h)

/-- On an inner slot the t=1 candidate `4a−1` is hub-sized. -/
theorem inner_t1_is_hub {a D : Nat} (hinner : D1InnerSlot a D) :
    4 * a - 1 ≤ 2 * D := by
  have h' : 4 * a ≤ 2 * D + 1 := hinner
  omega

/-- Any aligned divisor at an outer slot is automatically `> 2D`. -/
theorem outer_aligned_gt_two_D {a q D : Nat}
    (houter : D1OuterSlot a D)
    (hmod : (q + 1) % (4 * a) = 0) :
    2 * D < q := by
  have houter' : 2 * D + 1 < 4 * a := houter
  have ha : 0 < a := by omega
  have : 4 * a ≤ q + 1 := aligned_mul_le_succ ha hmod
  omega

/-- `n` is `B`-smooth: every prime factor is `≤ B`. -/
def SmoothTo (n B : Nat) : Prop :=
  ∀ q, IsPrime q → q ∣ n → q ≤ B

theorem exists_prime_gt_of_not_smooth {n B : Nat}
    (h : ¬ SmoothTo n B) :
    ∃ q, IsPrime q ∧ q ∣ n ∧ B < q := by
  obtain ⟨q, hq⟩ := Classical.not_forall.mp h
  obtain ⟨hP, hq⟩ := Classical.not_imp.mp hq
  obtain ⟨hdvd, hle⟩ := Classical.not_imp.mp hq
  exact ⟨q, hP, hdvd, by omega⟩

/-- A `B`-smooth integer strictly larger than `B` is not prime. -/
theorem smooth_gt_not_prime {n B : Nat}
    (hgt : B < n) (hs : SmoothTo n B) (hP : IsPrime n) : False :=
  Nat.lt_irrefl B (Nat.lt_of_lt_of_le hgt (hs n hP (Nat.dvd_refl n)))

/-- Outer landing: a unique-in-the-box large prime hit, or a `2D`-smooth
    aligned composite (alignment need not pass to prime factors). -/
theorem outer_landing_large_prime_or_smooth {p a D q : Nat}
    (houter : D1OuterSlot a D)
    (_hq3 : 3 ≤ q) (hmod : (q + 1) % (4 * a) = 0)
    (hdvd : q ∣ p + 4 * (a * a)) :
    (∃ r, IsPrime r ∧ 2 * D < r ∧ r ∣ p + 4 * (a * a)) ∨
      (SmoothTo q (2 * D) ∧ 2 * D < q) := by
  have hqgt : 2 * D < q := outer_aligned_gt_two_D houter hmod
  rcases Classical.em (SmoothTo q (2 * D)) with hs | hns
  · exact Or.inr ⟨hs, hqgt⟩
  · obtain ⟨r, hP, hrdvd, hgt⟩ := exists_prime_gt_of_not_smooth hns
    exact Or.inl ⟨r, hP, hgt, Nat.dvd_trans hrdvd hdvd⟩

/-- A large prime factor of an outer landing hits at most one slot in `[·, D]`. -/
theorem outer_large_prime_unique_hit {r p a b D : Nat}
    (hP : IsPrime r) (hD : 0 < D) (hgt : 2 * D < r)
    (hba : b < a) (haD : a ≤ D)
    (ha : r ∣ p + 4 * (a * a)) (hb : r ∣ p + 4 * (b * b)) :
    False := by
  have hne2 : r ≠ 2 := by omega
  exact at_most_one_hit_of_q_gt_two_D hP hne2 hba haD hgt ha hb

/-- t=1 dictionary (any `a`): `4a−1 ∣ p+4a²` iff `4a−1 ∣ p+a`.
    Independent of the `4p+1` slice. -/
theorem d1_t1_divides_iff {a p : Nat} (ha : 0 < a) :
    (4 * a - 1) ∣ p + 4 * (a * a) ↔ (4 * a - 1) ∣ p + a := by
  have hqt : (4 * a - 1) + 1 = 4 * a * 1 := by
    rw [Nat.mul_one]
    exact Nat.sub_add_cancel (by omega)
  simpa using d1_aligned_divides_iff (t := 1) hqt

theorem not_classRough_of_t1 {p a : Nat} (ha : 0 < a)
    (h : (4 * a - 1) ∣ p + a) :
    ¬ ClassRough p a := by
  have hqt : (4 * a - 1) + 1 = 4 * a := Nat.sub_add_cancel (by omega)
  have hq3 : 3 ≤ 4 * a - 1 := by omega
  have hmod : ((4 * a - 1) + 1) % (4 * a) = 0 := by
    rw [hqt]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_refl (4 * a))
  exact not_classRough_of_aligned_dvd hq3 hmod ((d1_t1_divides_iff ha).mpr h)

/-- A `2D`-smooth aligned outer landing still has a hub prime factor of `p+4a²`.
    That prime cannot itself be aligned at an outer slot. -/
theorem outer_smooth_has_hub_prime {p a D q : Nat}
    (hq2 : 2 ≤ q) (hs : SmoothTo q (2 * D)) (hgt : 2 * D < q)
    (hdvd : q ∣ p + 4 * (a * a)) :
    ∃ r, IsPrime r ∧ r ≤ 2 * D ∧ r ∣ p + 4 * (a * a) ∧ r < q := by
  obtain ⟨r, hP, hrdvd⟩ := exists_prime_factor q hq2
  have hrle : r ≤ 2 * D := hs r hP hrdvd
  have hne : r ≠ q := fun heq =>
    smooth_gt_not_prime hgt hs (heq ▸ hP)
  have hlt : r < q :=
    Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hrdvd) hne
  exact ⟨r, hP, hrle, Nat.dvd_trans hrdvd hdvd, hlt⟩

/-- Outer class-roughness fails by a unique-in-the-box large prime, or by a
    hub prime (unaligned at this outer slot) dividing a smooth aligned composite. -/
theorem outer_not_classRough_large_or_hub {p a D : Nat}
    (houter : D1OuterSlot a D) (h : ¬ ClassRough p a) :
    (∃ r, IsPrime r ∧ 2 * D < r ∧ r ∣ p + 4 * (a * a)) ∨
    (∃ r, IsPrime r ∧ r ≤ 2 * D ∧ r ∣ p + 4 * (a * a) ∧
        (r + 1) % (4 * a) ≠ 0) := by
  obtain ⟨q, hq3, _, hmod, hdvd⟩ := outer_landing_has_factor_gt_two_D houter h
  rcases outer_landing_large_prime_or_smooth houter hq3 hmod hdvd with hl | ⟨hs, hgt⟩
  · exact Or.inl hl
  · obtain ⟨r, hP, hrle, hrdvd, _⟩ :=
      outer_smooth_has_hub_prime (by omega) hs hgt hdvd
    refine Or.inr ⟨r, hP, hrle, hrdvd, ?_⟩
    intro hr_al
    exact no_aligned_le_of_outer houter hr_al hrle

/-- The trivial count `M = D−1` never beats the interval length. -/
theorem trivial_bound_does_not_save {D : Nat} (hD : 0 < D) :
    ¬ (D - 1 + 1 < D) := by
  have : D - 1 + 1 = D := Nat.sub_add_cancel hD
  omega

/-- The whole growing box `[2, D(p)]` is class-rough. -/
def D1NtExceptional (Dlevel : Nat → Nat) (p : Nat) : Prop :=
  ∀ a, 2 ≤ a → a ≤ Dlevel p → ClassRough p a

/-- Any aligned divisor in range kills the NT-exceptional property. -/
theorem not_d1NtExceptional_of_aligned {Dlevel : Nat → Nat} {p a q : Nat}
    (ha2 : 2 ≤ a) (hA : a ≤ Dlevel p)
    (hq3 : 3 ≤ q) (hmod : (q + 1) % (4 * a) = 0)
    (hdvd : q ∣ p + 4 * (a * a)) :
    ¬ D1NtExceptional Dlevel p :=
  fun hex => hex a ha2 hA q hq3 hmod hdvd

/-- NT-exceptional iff every inner slot and every outer slot is class-rough. -/
theorem d1NtExceptional_iff_inner_outer (Dlevel : Nat → Nat) (p : Nat) :
    D1NtExceptional Dlevel p ↔
      (∀ a, 2 ≤ a → a ≤ Dlevel p → D1InnerSlot a (Dlevel p) → ClassRough p a) ∧
      (∀ a, 2 ≤ a → a ≤ Dlevel p → D1OuterSlot a (Dlevel p) → ClassRough p a) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha2 hA _hi
      exact h a ha2 hA
    · intro a ha2 hA _ho
      exact h a ha2 hA
  · intro ⟨hI, hO⟩ a ha2 hA
    rcases inner_or_outer a (Dlevel p) with hi | ho
    · exact hI a ha2 hA hi
    · exact hO a ha2 hA ho

theorem not_d1NtExceptional_iff (Dlevel : Nat → Nat) (p : Nat) :
    ¬ D1NtExceptional Dlevel p ↔
      ∃ a, 2 ≤ a ∧ a ≤ Dlevel p ∧ ¬ ClassRough p a := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Classical.not_forall.mp h
    obtain ⟨ha2, ha⟩ := Classical.not_imp.mp ha
    obtain ⟨hA, hnr⟩ := Classical.not_imp.mp ha
    exact ⟨a, ha2, hA, hnr⟩
  · intro ⟨a, ha2, hA, hnr⟩ hex
    exact hnr (hex a ha2 hA)

/-- The d=1 remainder is exactly: no NT-exceptional a=1-split hard primes. -/
theorem D1Remainder_iff_no_nt_exceptional
    (Dlevel : Nat → Nat) (X0 : Nat) :
    D1Remainder Dlevel X0 ↔
      ∀ p, X0 ≤ p → IsPrime p → HardClass p → ThreeModFourFree (p + 4) →
        ¬ D1NtExceptional Dlevel p := by
  constructor
  · intro h p hge hp hhard hfree hex
    obtain ⟨a, q, ha2, hA, hq3, hmod, hdvd⟩ := h p hge hp hhard hfree
    exact hex a ha2 hA q hq3 hmod hdvd
  · intro h p hge hp hhard hfree
    obtain ⟨a, ha2, hA, hnr⟩ :=
      (not_d1NtExceptional_iff Dlevel p).mp (h p hge hp hhard hfree)
    obtain ⟨q, hq3, hmod, hdvd⟩ := not_classRough_iff.mp hnr
    exact ⟨a, q, ha2, hA, hq3, hmod, hdvd⟩

/-- Failure of NT-exceptionality splits as an inner (hub) hit or an outer hit. -/
theorem not_d1NtExceptional_iff_inner_or_outer (Dlevel : Nat → Nat) (p : Nat) :
    ¬ D1NtExceptional Dlevel p ↔
      (∃ a, 2 ≤ a ∧ a ≤ Dlevel p ∧ D1InnerSlot a (Dlevel p) ∧ ¬ ClassRough p a) ∨
      (∃ a, 2 ≤ a ∧ a ≤ Dlevel p ∧ D1OuterSlot a (Dlevel p) ∧ ¬ ClassRough p a) := by
  constructor
  · intro h
    obtain ⟨a, ha2, hA, hnr⟩ := (not_d1NtExceptional_iff Dlevel p).mp h
    rcases inner_or_outer a (Dlevel p) with hi | ho
    · exact Or.inl ⟨a, ha2, hA, hi, hnr⟩
    · exact Or.inr ⟨a, ha2, hA, ho, hnr⟩
  · intro h
    rcases h with ⟨a, ha2, hA, _, hnr⟩ | ⟨a, ha2, hA, _, hnr⟩
    · exact fun hex => hnr (hex a ha2 hA)
    · exact fun hex => hnr (hex a ha2 hA)

/-- Remainder from a hub-slot landing or an outer-slot landing. -/
theorem D1Remainder_of_inner_or_outer
    (Dlevel : Nat → Nat) (X0 : Nat)
    (h : ∀ p, X0 ≤ p → IsPrime p → HardClass p → ThreeModFourFree (p + 4) →
      (∃ a, 2 ≤ a ∧ a ≤ Dlevel p ∧ D1InnerSlot a (Dlevel p) ∧ ¬ ClassRough p a) ∨
      (∃ a, 2 ≤ a ∧ a ≤ Dlevel p ∧ D1OuterSlot a (Dlevel p) ∧ ¬ ClassRough p a)) :
    D1Remainder Dlevel X0 :=
  (D1Remainder_iff_no_nt_exceptional Dlevel X0).mpr fun p hge hp hhard hfree =>
    (not_d1NtExceptional_iff_inner_or_outer Dlevel p).mpr (h p hge hp hhard hfree)

/-- QED from an inner (hub) or outer landing on a=1-split hard primes. -/
theorem erdos_straus_of_d1_inner_or_outer
    (Dlevel : Nat → Nat)
    (hD : ∀ p, 10000 ≤ p → 1 ≤ Dlevel p)
    (h : ∀ p, 10000 ≤ p → IsPrime p → HardClass p → ThreeModFourFree (p + 4) →
      (∃ a, 2 ≤ a ∧ a ≤ Dlevel p ∧ D1InnerSlot a (Dlevel p) ∧ ¬ ClassRough p a) ∨
      (∃ a, 2 ≤ a ∧ a ≤ Dlevel p ∧ D1OuterSlot a (Dlevel p) ∧ ¬ ClassRough p a)) :
    ErdosStraus :=
  erdos_straus_of_d1_remainder Dlevel hD
    (D1Remainder_of_inner_or_outer Dlevel 10000 h)

/-- **Uniform Nair–Tenenbaum interface** (QED-strength).
    `M p` is an upper bound for the number of class-rough slots in
    `[2, D(p)]`.  If `M p + 1 < Dlevel p`, that bound is strictly below
    the interval length, so the box cannot be entirely class-rough.
    Mean-value / exceptional-count bounds do not discharge this. -/
def D1UniformNtBound (Dlevel : Nat → Nat) (X0 : Nat) (M : Nat → Nat) : Prop :=
  ∀ p : Nat, X0 ≤ p → IsPrime p → HardClass p → ThreeModFourFree (p + 4) →
    M p + 1 < Dlevel p → ¬ D1NtExceptional Dlevel p

theorem D1Remainder_of_uniform_nt
    (Dlevel M : Nat → Nat) (X0 : Nat)
    (hM : ∀ p, X0 ≤ p → M p + 1 < Dlevel p)
    (h : D1UniformNtBound Dlevel X0 M) :
    D1Remainder Dlevel X0 := by
  intro p hge hp hhard hfree
  have hnr : ¬ D1NtExceptional Dlevel p := h p hge hp hhard hfree (hM p hge)
  obtain ⟨a, ha2, hA, hcr⟩ := (not_d1NtExceptional_iff Dlevel p).mp hnr
  obtain ⟨q, hq3, hmod, hdvd⟩ := not_classRough_iff.mp hcr
  exact ⟨a, q, ha2, hA, hq3, hmod, hdvd⟩

/-- QED from a uniform NT bound strictly below the growing interval length.
    The schedule `D ~ exp(c√log x)` with `M` the Henriot implicit constant
    is the intended discharge; it is not proved here. -/
theorem erdos_straus_of_d1_uniform_nt
    (Dlevel M : Nat → Nat)
    (hM : ∀ p, 10000 ≤ p → M p + 1 < Dlevel p)
    (h : D1UniformNtBound Dlevel 10000 M) :
    ErdosStraus :=
  erdos_straus_of_d1_remainder Dlevel
    (fun p hp => by have := hM p hp; omega)
    (D1Remainder_of_uniform_nt Dlevel M 10000 hM h)

end ES.Covering
