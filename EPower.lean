/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  EPower.lean — Layer A (core). See README.md and erdos-straus-E-power.md.
  Bare Lean, no imports.

  Combinatorial core of the two-stage E_power repair: hub
  factorisation, fibre 1/ℓ, independent Suen, dependent pair mass,
  Janson mass ratio, sequential Janson I counting, one-log slice,
  transfer at a genuine period, the exact two-stage count, and the
  H1×H2 combination algebra for finite product-space density.
  H1/H2 exponentials, two-log mass, and PeriodSmallEnough are named
  uninhabited hypotheses. This file does not prove the Erdős–Straus
  conjecture, does not prove S_A ≪ x^{1-δ}, and does not discharge
  AnalyticSurvivorBound.
-/

namespace ES.EPower

/-! # Covering cells -/

structure Cell where
  a : Nat
  c : Nat
  d : Nat
  ha : 0 < a
  hc : 0 < c
  hd : 0 < d

@[simp] def Cell.q (cell : Cell) : Nat := 4 * cell.a * cell.c * cell.d - 1

theorem Cell.four_acd_pos (cell : Cell) : 0 < 4 * cell.a * cell.c * cell.d :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 4) cell.ha) cell.hc) cell.hd

theorem Cell.four_acd_ge_four (cell : Cell) : 4 ≤ 4 * cell.a * cell.c * cell.d := by
  have ha : 1 ≤ cell.a := cell.ha
  have hc : 1 ≤ cell.c := cell.hc
  have hd : 1 ≤ cell.d := cell.hd
  calc
    4 = 4 * 1 * 1 * 1 := by simp
    _ ≤ 4 * cell.a * cell.c * cell.d :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 4) ha) hc) hd

theorem Cell.q_pos (cell : Cell) : 0 < cell.q := by
  have h : 4 ≤ 4 * cell.a * cell.c * cell.d := cell.four_acd_ge_four
  have : 1 < 4 * cell.a * cell.c * cell.d :=
    Nat.lt_of_succ_le (Nat.le_trans (by decide : 2 ≤ 4) h)
  exact Nat.sub_pos_of_lt this

theorem Cell.q_ge_three (cell : Cell) : 3 ≤ cell.q := by
  have h : 4 ≤ 4 * cell.a * cell.c * cell.d := cell.four_acd_ge_four
  simp [Cell.q]
  exact Nat.le_sub_of_add_le (by omega)

theorem Cell.gcd_q_c (cell : Cell) : Nat.gcd cell.q cell.c = 1 := by
  have hle : 1 ≤ 4 * cell.a * cell.c * cell.d := cell.four_acd_pos
  have g4 : Nat.gcd cell.q cell.c ∣ 4 * cell.a * cell.c * cell.d :=
    Nat.dvd_trans (Nat.gcd_dvd_right _ _) ⟨4 * cell.a * cell.d, by
      simp [Nat.mul_comm, Nat.mul_left_comm]⟩
  have gq : Nat.gcd cell.q cell.c ∣ cell.q := Nat.gcd_dvd_left _ _
  have g1 : Nat.gcd cell.q cell.c ∣ 1 := by
    have hsub : 4 * cell.a * cell.c * cell.d - cell.q = 1 :=
      Nat.sub_sub_self hle
    have := Nat.dvd_sub g4 gq
    rwa [hsub] at this
  exact Nat.dvd_one.mp g1

theorem Cell.gcd_c_q (cell : Cell) : Nat.gcd cell.c cell.q = 1 := by
  rw [Nat.gcd_comm]
  exact cell.gcd_q_c

def Cell.covers (cell : Cell) (n : Nat) : Prop :=
  (cell.c * n + cell.a) % cell.q = 0

instance (cell : Cell) (n : Nat) : Decidable (cell.covers n) := by
  unfold Cell.covers; infer_instance

def Cell.residue? (cell : Cell) : Option Nat :=
  (List.range cell.q).find? fun r => (cell.c * r + cell.a) % cell.q = 0

def Cell.residue (cell : Cell) : Nat :=
  cell.residue?.getD 0

def boxCells (A : Nat) : List Cell :=
  (List.range A).flatMap fun a' =>
    (List.range A).flatMap fun c' =>
      (List.range 5).map fun d' =>
        { a := a' + 1
          c := c' + 1
          d := d' + 1
          ha := Nat.succ_pos _
          hc := Nat.succ_pos _
          hd := Nat.succ_pos _ }

def cellEvents (A : Nat) : List (Nat × Nat) :=
  (boxCells A).filterMap fun cell =>
    cell.residue?.map fun r => (cell.q, r)

def events (A : Nat) : List (Nat × Nat) :=
  (cellEvents A).eraseDups

theorem mem_events_iff (A : Nat) (qr : Nat × Nat) :
    qr ∈ events A ↔ qr ∈ cellEvents A :=
  List.mem_eraseDups

theorem events_union_stable (A : Nat) (n : Nat) :
    (∃ qr ∈ cellEvents A, n % qr.1 = qr.2) ↔
      ∃ qr ∈ events A, n % qr.1 = qr.2 := by
  constructor
  · intro ⟨qr, hmem, hhold⟩
    exact ⟨qr, (mem_events_iff A qr).mpr hmem, hhold⟩
  · intro ⟨qr, hmem, hhold⟩
    exact ⟨qr, (mem_events_iff A qr).mp hmem, hhold⟩

theorem events_q_pos (A : Nat) : ∀ e ∈ events A, 0 < e.1 := by
  intro e he
  have he' : e ∈ cellEvents A := (mem_events_iff A e).mp he
  rcases List.mem_filterMap.mp he' with ⟨cell, _, hmap⟩
  cases hres : cell.residue? with
  | none => simp [hres] at hmap
  | some r =>
    have : e = (cell.q, r) := by
      simpa [cellEvents, hres] using hmap.symm
    rw [this]
    exact cell.q_pos

/-! # Prime-power hub split -/

def IsTRough (T ℓ : Nat) : Prop :=
  ∀ d, 2 ≤ d → d ≤ T → ¬ d ∣ ℓ

def peelPow (p n : Nat) : Nat × Nat :=
  if h : 1 < p ∧ p ∣ n ∧ 0 < n then
    have : n / p < n := Nat.div_lt_self h.2.2 h.1
    let tail := peelPow p (n / p)
    (p * tail.1, tail.2)
  else
    (1, n)
termination_by n

def smoothRough : Nat → Nat → Nat × Nat
  | 0, n => (1, n)
  | T + 1, n =>
    if T + 1 ≤ 1 then
      smoothRough T n
    else
      let prev := smoothRough T n
      let peeled := peelPow (T + 1) prev.2
      (prev.1 * peeled.1, peeled.2)

def smoothPart (T n : Nat) : Nat := (smoothRough T n).1
def largePart (T n : Nat) : Nat := (smoothRough T n).2

def hubOf (T : Nat) (qs : List Nat) : Nat :=
  qs.foldl (fun acc q => Nat.lcm acc (smoothPart T q)) 1

theorem peelPow_prod (p n : Nat) :
    (peelPow p n).1 * (peelPow p n).2 = n := by
  apply (Nat.rec (motive := fun t =>
      ∀ m, m ≤ t → (peelPow p m).1 * (peelPow p m).2 = m) · · n n
      (Nat.le_refl n))
  · intro m hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst hm0
    unfold peelPow
    simp
  · intro t ih m hm
    unfold peelPow
    split
    · next h =>
      have hlt : m / p < m := Nat.div_lt_self h.2.2 h.1
      have hle : m / p ≤ t :=
        Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hm)
      have ih' := ih (m / p) hle
      have hmul : p * (m / p) = m := Nat.mul_div_cancel' h.2.1
      calc
        (p * (peelPow p (m / p)).1) * (peelPow p (m / p)).2
            = p * ((peelPow p (m / p)).1 * (peelPow p (m / p)).2) := by
              simp [Nat.mul_assoc]
        _ = p * (m / p) := by rw [ih']
        _ = m := hmul
    · simp

theorem peelPow_not_dvd (p n : Nat) (hp : 1 < p) (hn : 0 < n) :
    ¬ p ∣ (peelPow p n).2 := by
  apply (Nat.rec (motive := fun t =>
      ∀ m, m ≤ t → 0 < m → ¬ p ∣ (peelPow p m).2) · · n n (Nat.le_refl n) hn)
  · intro m hm hmpos
    have : False := Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hmpos hm)
    exact this.elim
  · intro t ih m hm hmpos
    unfold peelPow
    split
    · next h =>
      have hlt : m / p < m := Nat.div_lt_self h.2.2 h.1
      have hle : m / p ≤ t :=
        Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hm)
      have hppos : 0 < p := Nat.zero_lt_of_lt hp
      have hple : p ≤ m := Nat.le_of_dvd hmpos h.2.1
      have hpos : 0 < m / p := Nat.div_pos hple hppos
      exact ih (m / p) hle hpos
    · next h =>
      intro hdvd
      exact h ⟨hp, hdvd, hmpos⟩

theorem smoothRough_prod (T n : Nat) :
    (smoothRough T n).1 * (smoothRough T n).2 = n := by
  induction T with
  | zero => simp [smoothRough]
  | succ T ih =>
    unfold smoothRough
    split
    · exact ih
    · have hprev := ih
      have hpeel := peelPow_prod (T + 1) (smoothRough T n).2
      calc
        ((smoothRough T n).1 * (peelPow (T + 1) (smoothRough T n).2).1)
            * (peelPow (T + 1) (smoothRough T n).2).2
            = (smoothRough T n).1
                * ((peelPow (T + 1) (smoothRough T n).2).1
                    * (peelPow (T + 1) (smoothRough T n).2).2) := by
              simp [Nat.mul_assoc]
        _ = (smoothRough T n).1 * (smoothRough T n).2 := by rw [hpeel]
        _ = n := hprev

theorem smoothPart_mul_largePart (T n : Nat) :
    smoothPart T n * largePart T n = n :=
  smoothRough_prod T n

theorem largePart_not_dvd (T n d : Nat) (hn : 0 < n) (h2 : 2 ≤ d) (hd : d ≤ T) :
    ¬ d ∣ largePart T n := by
  induction T with
  | zero => omega
  | succ T ih =>
    unfold largePart smoothRough
    split
    · next hT => omega
    · next _hT =>
      if hdT : d ≤ T then
        have hprev : ¬ d ∣ (smoothRough T n).2 := ih hdT
        intro hfin
        have hprod := peelPow_prod (T + 1) (smoothRough T n).2
        have hdiv : (peelPow (T + 1) (smoothRough T n).2).2 ∣ (smoothRough T n).2 :=
          ⟨(peelPow (T + 1) (smoothRough T n).2).1, by rw [Nat.mul_comm, hprod]⟩
        exact hprev (Nat.dvd_trans hfin hdiv)
      else
        have heq : d = T + 1 := by omega
        subst heq
        intro hfin
        have hpos : 0 < (smoothRough T n).2 := by
          have hprod := smoothRough_prod T n
          have : 0 < (smoothRough T n).1 * (smoothRough T n).2 := by
            rw [hprod]; exact hn
          exact Nat.pos_of_mul_pos_left this
        exact peelPow_not_dvd (T + 1) (smoothRough T n).2 (by omega) hpos hfin

theorem largePart_rough (T n : Nat) (hn : 0 < n) : IsTRough T (largePart T n) :=
  fun d h2 hd => largePart_not_dvd T n d hn h2 hd

theorem peelPow_fst_pow (p n : Nat) : ∃ e, (peelPow p n).1 = p ^ e := by
  apply (Nat.rec (motive := fun t =>
      ∀ m, m ≤ t → ∃ e, (peelPow p m).1 = p ^ e) · · n n (Nat.le_refl n))
  · intro m hm
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst hm0
    unfold peelPow
    exact ⟨0, by simp⟩
  · intro t ih m hm
    unfold peelPow
    split
    · next h =>
      have hlt : m / p < m := Nat.div_lt_self h.2.2 h.1
      have hle : m / p ≤ t :=
        Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hm)
      rcases ih (m / p) hle with ⟨e, he⟩
      refine ⟨e + 1, ?_⟩
      simp [he, Nat.pow_succ']
    · exact ⟨0, by simp⟩

/-- If `d > 1` divides a power of `p`, then `d` shares a factor with `p`. -/
theorem dvd_pow_gcd_gt_one {d p e : Nat} (hd : d ∣ p ^ e) (h2 : 1 < d) :
    1 < Nat.gcd d p := by
  if h : Nat.gcd d p = 1 then
    have hpow : Nat.gcd d (p ^ e) = 1 := Nat.gcd_pow_right_of_gcd_eq_one h
    have hleft : Nat.gcd d (p ^ e) = d := Nat.gcd_eq_left hd
    have : d = 1 := by rw [← hleft, hpow]
    omega
  else
    have hpos : 0 < Nat.gcd d p :=
      Nat.gcd_pos_of_pos_left p (Nat.zero_lt_of_lt h2)
    omega

/-- Every divisor `d > 1` of the `T`-smooth part has a factor in `2..T`. -/
theorem dvd_smoothPart_has_small_factor (T n d : Nat)
    (hd : d ∣ smoothPart T n) (h2 : 1 < d) :
    ∃ k, 2 ≤ k ∧ k ≤ T ∧ k ∣ d := by
  induction T with
  | zero =>
    have hs : smoothPart 0 n = 1 := by simp [smoothPart, smoothRough]
    have : d ∣ 1 := by rwa [hs] at hd
    have : d = 1 := Nat.eq_one_of_dvd_one this
    omega
  | succ T ih =>
    unfold smoothPart smoothRough at hd
    split at hd
    · rcases ih hd with ⟨k, hk2, hkT, hkd⟩
      exact ⟨k, hk2, Nat.le_succ_of_le hkT, hkd⟩
    · next hT =>
      rcases peelPow_fst_pow (T + 1) (smoothRough T n).2 with ⟨e, he⟩
      have hd' : d ∣ (smoothRough T n).1 * (T + 1) ^ e := by
        simpa [he] using hd
      let g := Nat.gcd d ((T + 1) ^ e)
      if hg : 1 < g then
        have hgdiv : g ∣ (T + 1) ^ e := Nat.gcd_dvd_right _ _
        have hgt : 1 < Nat.gcd g (T + 1) := dvd_pow_gcd_gt_one hgdiv hg
        let k := Nat.gcd g (T + 1)
        have hk2 : 2 ≤ k := Nat.succ_le_of_lt hgt
        have hkT : k ≤ T + 1 :=
          Nat.le_of_dvd (Nat.succ_pos T) (Nat.gcd_dvd_right g (T + 1))
        have hkd : k ∣ d :=
          Nat.dvd_trans (Nat.gcd_dvd_left g (T + 1)) (Nat.gcd_dvd_left d _)
        exact ⟨k, hk2, hkT, hkd⟩
      else
        have hpos : 0 < g :=
          Nat.gcd_pos_of_pos_left _ (Nat.zero_lt_of_lt h2)
        have hg1 : g = 1 := by omega
        have hdiv : d ∣ (smoothRough T n).1 :=
          Nat.Coprime.dvd_of_dvd_mul_right
            (Nat.coprime_iff_gcd_eq_one.mpr hg1) hd'
        rcases ih hdiv with ⟨k, hk2, hkT, hkd⟩
        exact ⟨k, hk2, Nat.le_succ_of_le hkT, hkd⟩

theorem smoothPart_pos (T n : Nat) (hn : 0 < n) : 0 < smoothPart T n := by
  have hprod := smoothPart_mul_largePart T n
  have : 0 < smoothPart T n * largePart T n := by
    rw [hprod]; exact hn
  exact Nat.pos_of_mul_pos_right this

/-- The prime-power split is coprime: `gcd(s, ℓ) = 1`. -/
theorem gcd_smooth_large (T n : Nat) (hn : 0 < n) :
    Nat.gcd (smoothPart T n) (largePart T n) = 1 := by
  let g := Nat.gcd (smoothPart T n) (largePart T n)
  if h : g = 1 then
    exact h
  else
    have hpos : 0 < g := Nat.gcd_pos_of_pos_left _ (smoothPart_pos T n hn)
    have hg : 1 < g := by omega
    have hs : g ∣ smoothPart T n := Nat.gcd_dvd_left _ _
    have hℓ : g ∣ largePart T n := Nat.gcd_dvd_right _ _
    rcases dvd_smoothPart_has_small_factor T n g hs hg with ⟨k, hk2, hkT, hkd⟩
    have hkℓ : k ∣ largePart T n := Nat.dvd_trans hkd hℓ
    exact False.elim (largePart_not_dvd T n k hn hk2 hkT hkℓ)

theorem dvd_foldl_lcm (init : Nat) (xs : List Nat) (g : Nat → Nat) {d : Nat}
    (hd : d ∣ init) :
    d ∣ xs.foldl (fun a x => Nat.lcm a (g x)) init := by
  induction xs generalizing init with
  | nil => simpa
  | cons x xs ih =>
    have hnext : d ∣ Nat.lcm init (g x) :=
      Nat.dvd_trans hd (Nat.dvd_lcm_left init (g x))
    simpa [List.foldl_cons] using ih (Nat.lcm init (g x)) hnext

theorem foldl_lcm_of_mem (init : Nat) (xs : List Nat) (g : Nat → Nat)
    (x : Nat) (hx : x ∈ xs) :
    g x ∣ xs.foldl (fun acc y => Nat.lcm acc (g y)) init := by
  induction xs generalizing init with
  | nil => cases hx
  | cons y ys ih =>
    simp [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl heq =>
      rw [heq]
      exact dvd_foldl_lcm (Nat.lcm init (g y)) ys g (Nat.dvd_lcm_right init (g y))
    | inr hmem =>
      exact ih (Nat.lcm init (g y)) hmem

theorem hubOf_dvd (T : Nat) (qs : List Nat) (q : Nat) (hq : q ∈ qs) :
    smoothPart T q ∣ hubOf T qs :=
  foldl_lcm_of_mem 1 qs (smoothPart T) q hq

/-! # Fibre classification -/

inductive FibreClass where
  | incompatible
  | hubForced
  | residual (ell : Nat)
deriving DecidableEq, Repr

def classify (T q r ρ : Nat) : FibreClass :=
  let s := smoothPart T q
  let ell := largePart T q
  if s = 0 then
    FibreClass.incompatible
  else if ρ % s ≠ r % s then
    FibreClass.incompatible
  else if ell ≤ 1 then
    FibreClass.hubForced
  else
    FibreClass.residual ell

def hubSurvives (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat) : Bool :=
  evs.all fun e => classify T e.1 e.2 ρ ≠ FibreClass.hubForced

def residualElls (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat) : List Nat :=
  evs.filterMap fun e =>
    match classify T e.1 e.2 ρ with
    | FibreClass.residual ell => some ell
    | _ => none

def muRho (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat) : List Nat :=
  residualElls T evs ρ

/-- Residual events as `(ℓ, r mod ℓ)`. These are the inputs to `μ_ρ`,
    `Δ_ρ`, and `δ_ρ`. Independent pairs (`gcd = 1`) are not summands of
    `Δ_ρ`. -/
def residualEvents (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat) :
    List (Nat × Nat) :=
  evs.filterMap fun e =>
    match classify T e.1 e.2 ρ with
    | FibreClass.residual ell => some (ell, e.2 % ell)
    | _ => none

def invNat (n : Nat) : Rat :=
  if n = 0 then 0 else (1 : Rat) / (n : Nat)

/-- Exact fibre mass `μ_ρ = ∑ 1/ℓ_i`. Not the unconditional `∑ 1/q`. -/
def muRhoMass (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat) : Rat :=
  ((residualEvents T evs ρ).map (fun e => invNat e.1)).sum

def pairList {α : Type _} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairList xs

def pairCompatible (ℓ₁ r₁ ℓ₂ r₂ : Nat) : Bool :=
  r₁ % Nat.gcd ℓ₁ ℓ₂ == r₂ % Nat.gcd ℓ₁ ℓ₂

/-- Congruence pair mass: `1/lcm` if residues agree mod `gcd`, else `0`. -/
def pairMass (ℓ₁ r₁ ℓ₂ r₂ : Nat) : Rat :=
  if Nat.gcd ℓ₁ ℓ₂ = 0 then 0
  else if pairCompatible ℓ₁ r₁ ℓ₂ r₂ then
    invNat (Nat.lcm ℓ₁ ℓ₂)
  else
    0

def dependent (e₁ e₂ : Nat × Nat) : Bool :=
  let g := Nat.gcd e₁.1 e₂.1
  g != 0 && g != 1

/-- Exact fibre pair mass `Δ_ρ`, summed only over dependent pairs. -/
def deltaRhoMass (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat) : Rat :=
  ((pairList (residualEvents T evs ρ)).map fun p =>
    if dependent p.1 p.2 then pairMass p.1.1 p.1.2 p.2.1 p.2.2 else 0).sum

def neighborMass (e : Nat × Nat) (evs : List (Nat × Nat)) : Rat :=
  ((evs.filter (fun e' => !(e' == e) && dependent e e')).map
    (fun e' => invNat e'.1)).sum

/-- Suen/Janson `δ_ρ = max_i ∑_{j ∼ i} P(E_j)`. -/
def deltaStar (evs : List (Nat × Nat)) : Rat :=
  (evs.map (fun e => neighborMass e evs)).max?.getD 0

def deltaRhoStar (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat) : Rat :=
  deltaStar (residualEvents T evs ρ)

def residualModulus (T : Nat) (evs : List (Nat × Nat)) : Nat :=
  evs.foldl (fun acc e => Nat.lcm acc (largePart T e.1)) 1

/-! # Fibre cardinality and the 1/ℓ repair

    After a compatible hub residue `ρ (mod s)`, the event `n ≡ r (mod sℓ)`
    meets the fibre `{n < sℓ : n ≡ ρ (mod s)}` in exactly one point.
    The conditional probability is therefore `1/ℓ`, not `1/q`.
    Hub-forced events (`ℓ = 1`) cover the whole fibre.
-/

def fibre (s ℓ ρ : Nat) : List Nat :=
  (List.range (s * ℓ)).filter (fun n => n % s == ρ)

def fibreHits (s ℓ ρ r : Nat) : List Nat :=
  (fibre s ℓ ρ).filter (fun n => n % (s * ℓ) == r % (s * ℓ))

theorem range_mul_succ (s ℓ : Nat) :
    List.range (s * (ℓ + 1))
      = List.range (s * ℓ) ++ (List.range s).map (s * ℓ + ·) := by
  rw [Nat.mul_succ, List.range_add]

theorem fibre_length (s ℓ ρ : Nat) (_hs : 0 < s) (hρ : ρ < s) :
    (fibre s ℓ ρ).length = ℓ := by
  induction ℓ with
  | zero => simp [fibre]
  | succ ℓ ih =>
    unfold fibre
    rw [range_mul_succ, List.filter_append, List.length_append]
    have hleft :
        ((List.range (s * ℓ)).filter (fun n => n % s == ρ)).length = ℓ := ih
    have hright :
        (((List.range s).map (s * ℓ + ·)).filter
          (fun n => n % s == ρ)).length = 1 := by
      rw [List.filter_map, List.length_map]
      have hcongr :
          (List.range s).filter
              ((fun n => n % s == ρ) ∘ fun x => s * ℓ + x)
            = (List.range s).filter (· == ρ) := by
        apply List.filter_congr
        intro k hk
        have hklt : k < s := List.mem_range.mp hk
        have hmod : (s * ℓ + k) % s = k := by
          rw [Nat.add_mod]
          have hz : s * ℓ % s = 0 := Nat.mul_mod_right s ℓ
          rw [hz, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hklt]
        simp [hmod]
      rw [hcongr, ← List.count_eq_length_filter, List.count_range]
      simp [hρ]
    simp [hleft, hright]

theorem mem_fibre (s ℓ ρ n : Nat) :
    n ∈ fibre s ℓ ρ ↔ n < s * ℓ ∧ n % s = ρ := by
  simp [fibre, List.mem_filter, List.mem_range, beq_iff_eq]

theorem fibre_nodup (s ℓ ρ : Nat) : (fibre s ℓ ρ).Nodup :=
  List.Pairwise.filter (fun n => n % s == ρ) List.nodup_range

theorem fibreHits_eq_eq (s ℓ ρ r : Nat) :
    fibreHits s ℓ ρ r
      = (fibre s ℓ ρ).filter (fun n => n == r % (s * ℓ)) := by
  apply List.filter_congr
  intro n hn
  have hnlt : n < s * ℓ := (mem_fibre s ℓ ρ n).mp hn |>.1
  simp [Nat.mod_eq_of_lt hnlt]

/-- Compatible fibre: exactly one hit. Incompatible: none.
    This is the kernel-checked form of \(P(E\mid\rho)=1/\ell\). -/
theorem fibre_hit_count (s ℓ ρ r : Nat)
    (hs : 0 < s) (hℓ : 0 < ℓ) (_hρ : ρ < s) :
    (fibreHits s ℓ ρ r).length = if r % s = ρ then 1 else 0 := by
  have hred : (r % (s * ℓ)) % s = r % s :=
    Nat.mod_mod_of_dvd r ⟨ℓ, rfl⟩
  have htlt : r % (s * ℓ) < s * ℓ := Nat.mod_lt r (Nat.mul_pos hs hℓ)
  have hmem :
      r % (s * ℓ) ∈ fibre s ℓ ρ ↔ r % s = ρ := by
    rw [mem_fibre, hred]
    simp [htlt]
  rw [fibreHits_eq_eq, ← List.count_eq_length_filter]
  have hcnt :=
    (List.nodup_iff_count_eq_ite.mp (fibre_nodup s ℓ ρ)) (r % (s * ℓ))
  rw [hcnt]
  simp [hmem]

theorem compatible_hit_one (s ℓ ρ r : Nat)
    (hs : 0 < s) (hℓ : 0 < ℓ) (hρ : ρ < s) (hcompat : r % s = ρ) :
    (fibreHits s ℓ ρ r).length = 1 := by
  simp [fibre_hit_count s ℓ ρ r hs hℓ hρ, hcompat]

theorem incompatible_hit_zero (s ℓ ρ r : Nat)
    (hs : 0 < s) (hℓ : 0 < ℓ) (hρ : ρ < s) (hinc : r % s ≠ ρ) :
    (fibreHits s ℓ ρ r).length = 0 := by
  simp [fibre_hit_count s ℓ ρ r hs hℓ hρ, hinc]

/-- Hub-forced (`ℓ = 1`): a compatible event covers the whole fibre. -/
theorem hub_forced_covers (s ρ r : Nat)
    (hs : 0 < s) (hρ : ρ < s) (hcompat : r % s = ρ) :
    (fibreHits s 1 ρ r).length = 1 ∧ (fibre s 1 ρ).length = 1 :=
  ⟨compatible_hit_one s 1 ρ r hs (by decide) hρ hcompat,
    fibre_length s 1 ρ hs hρ⟩

/-! # CRT uniqueness (hub / independent Suen) -/

theorem dvd_sub_of_mod_eq {a b m : Nat} (h : a % m = b % m) (_hle : b ≤ a)
    (_hm : 0 < m) : m ∣ a - b := by
  have ha : a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm
  have hb : b = m * (b / m) + b % m := (Nat.div_add_mod b m).symm
  have hsub : a - b = m * (a / m - b / m) := by
    have : a - b
        = (m * (a / m) + a % m) - (m * (b / m) + b % m) := by
      rw [← ha, ← hb]
    rw [this, h, Nat.add_sub_add_right, Nat.mul_sub_left_distrib]
  exact ⟨a / m - b / m, hsub⟩

theorem crt_unique {q P n₁ n₂ : Nat}
    (hcop : Nat.gcd q P = 1) (hq : 0 < q) (hP : 0 < P)
    (hn₁ : n₁ < q * P) (hn₂ : n₂ < q * P)
    (hqeq : n₁ % q = n₂ % q) (hPeq : n₁ % P = n₂ % P) : n₁ = n₂ := by
  cases Nat.le_total n₂ n₁ with
  | inl hle =>
    have hqdvd : q ∣ n₁ - n₂ := dvd_sub_of_mod_eq hqeq hle hq
    have hPdvd : P ∣ n₁ - n₂ := dvd_sub_of_mod_eq hPeq hle hP
    have hprod : q * P ∣ n₁ - n₂ :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.coprime_iff_gcd_eq_one.mpr hcop) hqdvd hPdvd
    have hlt : n₁ - n₂ < q * P := by omega
    rcases hprod with ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k =>
      have : q * P ≤ n₁ - n₂ := by
        rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      exact absurd this (Nat.not_le.mpr hlt)
  | inr hle =>
    have hqdvd : q ∣ n₂ - n₁ := dvd_sub_of_mod_eq hqeq.symm hle hq
    have hPdvd : P ∣ n₂ - n₁ := dvd_sub_of_mod_eq hPeq.symm hle hP
    have hprod : q * P ∣ n₂ - n₁ :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.coprime_iff_gcd_eq_one.mpr hcop) hqdvd hPdvd
    have hlt : n₂ - n₁ < q * P := by omega
    rcases hprod with ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k =>
      have : q * P ≤ n₂ - n₁ := by
        rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      exact absurd this (Nat.not_le.mpr hlt)

theorem nodup_map_of_inj {α β : Type _} {l : List α} {f : α → β}
    (hnd : l.Nodup)
    (hinj : ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd' := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, ih hnd'.2 (fun x y hx hy =>
      hinj x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy))⟩
    intro hf
    rcases List.mem_map.mp hf with ⟨b, hb, heq⟩
    have : a = b := hinj a b List.mem_cons_self (List.mem_cons_of_mem _ hb) heq.symm
    exact hnd'.1 (this ▸ hb)

theorem crt_exists (q P r s : Nat)
    (hcop : Nat.gcd q P = 1) (hq : 0 < q) (hP : 0 < P)
    (hr : r < q) (hs : s < P) :
    ∃ n, n < q * P ∧ n % q = r ∧ n % P = s := by
  let imgs := (List.range P).map (fun k => (r + k * q) % P)
  have hnlt : ∀ k, k < P → r + k * q < q * P := by
    intro k hk
    have h1 : r + k * q < q + k * q := Nat.add_lt_add_right hr _
    have h2 : q + k * q = q * (k + 1) := by
      rw [Nat.mul_comm k, Nat.mul_succ, Nat.add_comm]
    have h3 : q * (k + 1) ≤ q * P := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hk)
    omega
  have hinj : ∀ k₁ k₂, k₁ ∈ List.range P → k₂ ∈ List.range P →
      (r + k₁ * q) % P = (r + k₂ * q) % P → k₁ = k₂ := by
    intro k₁ k₂ hk₁ hk₂ heq
    have hk₁lt := List.mem_range.mp hk₁
    have hk₂lt := List.mem_range.mp hk₂
    have hn₁ := hnlt k₁ hk₁lt
    have hn₂ := hnlt k₂ hk₂lt
    have hqeq : (r + k₁ * q) % q = (r + k₂ * q) % q := by
      simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    have heq' := crt_unique hcop hq hP hn₁ hn₂ hqeq heq
    have : k₁ * q = k₂ * q := by omega
    exact Nat.eq_of_mul_eq_mul_right hq this
  have hnd : imgs.Nodup :=
    nodup_map_of_inj List.nodup_range hinj
  have hsR : s ∈ List.range P := List.mem_range.mpr hs
  if hsmem : s ∈ imgs then
    rcases List.mem_map.mp hsmem with ⟨k, hk, hkeq⟩
    refine ⟨r + k * q, hnlt k (List.mem_range.mp hk), ?_, hkeq⟩
    simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  else
    have hsub : imgs ⊆ (List.range P).erase s := by
      intro x hx
      have hxR : x ∈ List.range P := List.mem_range.mpr (by
        rcases List.mem_map.mp hx with ⟨k, _, hk⟩
        rw [← hk]; exact Nat.mod_lt _ hP)
      have hne : x ≠ s := fun heq => hsmem (heq ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr hxR
    have hle := hnd.length_le_of_subset hsub
    have hlen : imgs.length = P := by simp [imgs]
    have herase : ((List.range P).erase s).length = P - 1 := by
      simpa [List.length_range] using List.length_erase_of_mem hsR
    have hP1 : P ≤ P - 1 := by simpa [hlen, herase] using hle
    have hlt : P - 1 < P := Nat.sub_lt hP (by decide)
    exact False.elim (Nat.not_le.mpr hlt hP1)

/-! # Finite Suen: independent one-modulus case -/

/-- Avoiding one residue class modulo `q` leaves exactly `q − 1` residues.
    This is the kernel-checked independent Suen count for a single event. -/
theorem avoid_one_count (q r : Nat) (hq : 1 < q) :
    ((List.range q).filter (· != r % q)).length = q - 1 := by
  have hqpos : 0 < q := by omega
  have hr : r % q ∈ List.range q := List.mem_range.mpr (Nat.mod_lt r hqpos)
  have hnodup : (List.range q).Nodup := List.nodup_range
  rw [← hnodup.erase_eq_filter (r % q), List.length_erase_of_mem hr, List.length_range]

/-- On `0 .. q−1`, `n % q = n`, so the congruence miss set is the same. -/
theorem avoid_one_mod (q r : Nat) (hq : 1 < q) :
    ((List.range q).filter (fun n => n % q != r % q)).length = q - 1 := by
  have hqpos : 0 < q := by omega
  have hcongr :
      (List.range q).filter (fun n => n % q != r % q)
        = (List.range q).filter (· != r % q) := by
    apply List.filter_congr
    intro n hn
    have : n < q := List.mem_range.mp hn
    simp [Nat.mod_eq_of_lt this]
  rw [hcongr, avoid_one_count q r hq]

def FiniteSuen : Prop :=
  ∀ q r, 1 < q →
    ((List.range q).filter (fun n => n % q != r % q)).length = q - 1

theorem finiteSuen_holds : FiniteSuen :=
  avoid_one_mod

theorem length_filter_add_not {α : Type _} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> simp [hp] <;> omega

theorem length_filter_or_and {α : Type _} (p q : α → Bool) (l : List α) :
    (l.filter (fun x => p x || q x)).length
        + (l.filter (fun x => p x && q x)).length
      = (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq] <;> omega

theorem succ_mul_succ_sub (a b : Nat) :
    (a + 1) * (b + 1) - (b + 1 + (a + 1) - 1) = a * b := by
  have hprod : (a + 1) * (b + 1) = a * b + a + b + 1 := by
    simp [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]
  have hsum : b + 1 + (a + 1) - 1 = a + b + 1 := by
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hassoc : a * b + a + b + 1 = a * b + (a + b + 1) := by
    simp [Nat.add_assoc]
  rw [hprod, hsum, hassoc, Nat.add_sub_cancel]

theorem avoid_card_formula (q P : Nat) (hq : 1 < q) (hP : 1 < P) :
    q * P - (P + q - 1) = (q - 1) * (P - 1) := by
  let a := q - 1
  let b := P - 1
  have ha : q = a + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hq))).symm
  have hb : P = b + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hP))).symm
  rw [ha, hb]
  have ha1 : a + 1 - 1 = a := Nat.add_sub_cancel a 1
  have hb1 : b + 1 - 1 = b := Nat.add_sub_cancel b 1
  simp [ha1, hb1]
  exact succ_mul_succ_sub a b

/-- Independent two-event Suen: coprime moduli leave `(q−1)(P−1)` residues. -/
theorem avoid_two_coprime (q P r s : Nat)
    (hcop : Nat.gcd q P = 1) (hq : 1 < q) (hP : 1 < P) :
    ((List.range (q * P)).filter
      (fun n => n % q != r % q && n % P != s % P)).length
      = (q - 1) * (P - 1) := by
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hPpos : 0 < P := Nat.zero_lt_of_lt hP
  let A := fun n : Nat => n % q == r % q
  let B := fun n : Nat => n % P == s % P
  have hA :
      ((List.range (q * P)).filter A).length = P := by
    change ((List.range (q * P)).filter (fun n => n % q == r % q)).length = P
    exact fibre_length q P (r % q) hqpos (Nat.mod_lt r hqpos)
  have hB :
      ((List.range (q * P)).filter B).length = q := by
    have h := fibre_length P q (s % P) hPpos (Nat.mod_lt s hPpos)
    simpa [fibre, B, Nat.mul_comm P q] using h
  have hAB :
      ((List.range (q * P)).filter (fun n => A n && B n)).length = 1 := by
    let xs := (List.range (q * P)).filter (fun n => A n && B n)
    have ⟨n0, hnlt, hnq, hnP⟩ :=
      crt_exists q P (r % q) (s % P) hcop hqpos hPpos
        (Nat.mod_lt r hqpos) (Nat.mod_lt s hPpos)
    have hmem : n0 ∈ xs := by
      refine List.mem_filter.mpr ⟨List.mem_range.mpr hnlt, ?_⟩
      simp [A, B, hnq, hnP]
    have huniq : ∀ x ∈ xs, x = n0 := by
      intro x hx
      have hxF := List.mem_filter.mp hx
      have hxlt := List.mem_range.mp hxF.1
      have hxAB : A x = true ∧ B x = true := by
        simpa [Bool.and_eq_true] using hxF.2
      have hxq : x % q = r % q := by simpa [A, beq_iff_eq] using hxAB.1
      have hxP : x % P = s % P := by simpa [B, beq_iff_eq] using hxAB.2
      exact crt_unique hcop hqpos hPpos hxlt hnlt
        (hxq.trans hnq.symm) (hxP.trans hnP.symm)
    have hnd : xs.Nodup :=
      List.Pairwise.filter (fun n => A n && B n) List.nodup_range
    change xs.length = 1
    match xs with
    | [] => exact False.elim (by cases hmem)
    | [a] => rfl
    | a :: b :: as =>
      have ha : a = n0 := huniq a (by simp)
      have hb : b = n0 := huniq b (by simp)
      have hnd' := List.nodup_cons.mp hnd
      exact False.elim (hnd'.1 (by simp [ha, hb]))
  have hor :
      ((List.range (q * P)).filter (fun n => A n || B n)).length + 1
        = P + q := by
    have := length_filter_or_and A B (List.range (q * P))
    omega
  have hUnion :
      ((List.range (q * P)).filter (fun n => A n || B n)).length
        = P + q - 1 := by omega
  have havoid :
      ((List.range (q * P)).filter (fun n => !(A n || B n))).length
        = q * P - (P + q - 1) := by
    have hsum := length_filter_add_not (fun n => A n || B n) (List.range (q * P))
    have hlen : (List.range (q * P)).length = q * P := List.length_range
    omega
  have hpred :
      ((List.range (q * P)).filter (fun n => !(A n || B n)))
        = (List.range (q * P)).filter
            (fun n => !(n % q == r % q) && !(n % P == s % P)) := by
    apply List.filter_congr
    intro n _hn
    simp [A, B, Bool.not_or]
  have hpred' :
      ((List.range (q * P)).filter
          (fun n => !(n % q == r % q) && !(n % P == s % P)))
        = (List.range (q * P)).filter
            (fun n => n % q != r % q && n % P != s % P) := by
    apply List.filter_congr
    intro n _hn
    rfl
  rw [← hpred', ← hpred, havoid, avoid_card_formula q P hq hP]

/-- Incompatible residual pair: no common residue. Pair mass is `0`. -/
theorem pair_hit_incompatible (ℓ₁ r₁ ℓ₂ r₂ : Nat)
    (_h1 : 0 < ℓ₁) (_h2 : 0 < ℓ₂)
    (hinc : r₁ % Nat.gcd ℓ₁ ℓ₂ ≠ r₂ % Nat.gcd ℓ₁ ℓ₂) :
    ((List.range (Nat.lcm ℓ₁ ℓ₂)).filter
      (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂)).length = 0 := by
  have hnil :
      (List.range (Nat.lcm ℓ₁ ℓ₂)).filter
        (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂) = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro n _hn hf
    have h12 : Nat.gcd ℓ₁ ℓ₂ ∣ ℓ₁ := Nat.gcd_dvd_left _ _
    have h22 : Nat.gcd ℓ₁ ℓ₂ ∣ ℓ₂ := Nat.gcd_dvd_right _ _
    have hab : n % ℓ₁ = r₁ % ℓ₁ ∧ n % ℓ₂ = r₂ % ℓ₂ := by
      simpa [Bool.and_eq_true, beq_iff_eq] using hf
    have hn1 : n % Nat.gcd ℓ₁ ℓ₂ = r₁ % Nat.gcd ℓ₁ ℓ₂ :=
      calc
        n % Nat.gcd ℓ₁ ℓ₂ = (n % ℓ₁) % Nat.gcd ℓ₁ ℓ₂ :=
          (Nat.mod_mod_of_dvd n h12).symm
        _ = (r₁ % ℓ₁) % Nat.gcd ℓ₁ ℓ₂ := by rw [hab.1]
        _ = r₁ % Nat.gcd ℓ₁ ℓ₂ := Nat.mod_mod_of_dvd r₁ h12
    have hn2 : n % Nat.gcd ℓ₁ ℓ₂ = r₂ % Nat.gcd ℓ₁ ℓ₂ :=
      calc
        n % Nat.gcd ℓ₁ ℓ₂ = (n % ℓ₂) % Nat.gcd ℓ₁ ℓ₂ :=
          (Nat.mod_mod_of_dvd n h22).symm
        _ = (r₂ % ℓ₂) % Nat.gcd ℓ₁ ℓ₂ := by rw [hab.2]
        _ = r₂ % Nat.gcd ℓ₁ ℓ₂ := Nat.mod_mod_of_dvd r₂ h22
    exact hinc (hn1.symm.trans hn2)
  simp [hnil]

/-- Coprime residual pair: unique common residue. Pair mass is `1/lcm`. -/
theorem pair_hit_coprime (ℓ₁ r₁ ℓ₂ r₂ : Nat)
    (hcop : Nat.gcd ℓ₁ ℓ₂ = 1) (h1 : 0 < ℓ₁) (h2 : 0 < ℓ₂) :
    ((List.range (ℓ₁ * ℓ₂)).filter
      (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂)).length = 1 := by
  let xs := (List.range (ℓ₁ * ℓ₂)).filter
    (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂)
  have ⟨n0, hnlt, hnq, hnP⟩ :=
    crt_exists ℓ₁ ℓ₂ (r₁ % ℓ₁) (r₂ % ℓ₂) hcop h1 h2
      (Nat.mod_lt r₁ h1) (Nat.mod_lt r₂ h2)
  have hmem : n0 ∈ xs := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hnlt, ?_⟩
    simp [hnq, hnP]
  have huniq : ∀ x ∈ xs, x = n0 := by
    intro x hx
    have hxF := List.mem_filter.mp hx
    have hxlt := List.mem_range.mp hxF.1
    have hxAB : x % ℓ₁ = r₁ % ℓ₁ ∧ x % ℓ₂ = r₂ % ℓ₂ := by
      simpa [Bool.and_eq_true, beq_iff_eq] using hxF.2
    exact crt_unique hcop h1 h2 hxlt hnlt
      (hxAB.1.trans hnq.symm) (hxAB.2.trans hnP.symm)
  have hnd : xs.Nodup :=
    List.Pairwise.filter
      (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂) List.nodup_range
  change xs.length = 1
  match xs with
  | [] => exact False.elim (by cases hmem)
  | [_a] => rfl
  | a :: b :: as =>
    have ha : a = n0 := huniq a (by simp)
    have hb : b = n0 := huniq b (by simp)
    have hnd' := List.nodup_cons.mp hnd
    exact False.elim (hnd'.1 (by simp [ha, hb]))

theorem lcm_pos_of_pos {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 < Nat.lcm m n := by
  have h := Nat.gcd_mul_lcm m n
  have : 0 < Nat.gcd m n * Nat.lcm m n := by
    rw [h]; exact Nat.mul_pos hm hn
  exact Nat.pos_of_mul_pos_left this

/-- Two residues that agree modulo both `ℓ₁` and `ℓ₂` agree modulo `lcm`. -/
theorem crt_unique_lcm {ℓ₁ ℓ₂ n₁ n₂ : Nat}
    (h1 : 0 < ℓ₁) (h2 : 0 < ℓ₂)
    (hn₁ : n₁ < Nat.lcm ℓ₁ ℓ₂) (hn₂ : n₂ < Nat.lcm ℓ₁ ℓ₂)
    (heq1 : n₁ % ℓ₁ = n₂ % ℓ₁) (heq2 : n₁ % ℓ₂ = n₂ % ℓ₂) : n₁ = n₂ := by
  cases Nat.le_total n₂ n₁ with
  | inl hle =>
    have hd1 : ℓ₁ ∣ n₁ - n₂ := dvd_sub_of_mod_eq heq1 hle h1
    have hd2 : ℓ₂ ∣ n₁ - n₂ := dvd_sub_of_mod_eq heq2 hle h2
    have hL : Nat.lcm ℓ₁ ℓ₂ ∣ n₁ - n₂ := Nat.lcm_dvd hd1 hd2
    have hlt : n₁ - n₂ < Nat.lcm ℓ₁ ℓ₂ := by omega
    rcases hL with ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k =>
      have : Nat.lcm ℓ₁ ℓ₂ ≤ n₁ - n₂ := by
        rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      exact False.elim (Nat.not_le.mpr hlt this)
  | inr hle =>
    have hd1 : ℓ₁ ∣ n₂ - n₁ := dvd_sub_of_mod_eq heq1.symm hle h1
    have hd2 : ℓ₂ ∣ n₂ - n₁ := dvd_sub_of_mod_eq heq2.symm hle h2
    have hL : Nat.lcm ℓ₁ ℓ₂ ∣ n₂ - n₁ := Nat.lcm_dvd hd1 hd2
    have hlt : n₂ - n₁ < Nat.lcm ℓ₁ ℓ₂ := by omega
    rcases hL with ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k =>
      have : Nat.lcm ℓ₁ ℓ₂ ≤ n₂ - n₁ := by
        rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      exact False.elim (Nat.not_le.mpr hlt this)

theorem lcm_eq_gcd_mul_divs (ℓ₁ ℓ₂ : Nat) (hg : 0 < Nat.gcd ℓ₁ ℓ₂) :
    Nat.lcm ℓ₁ ℓ₂
      = Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂) * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) := by
  have hℓ1 : Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂) = ℓ₁ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left ℓ₁ ℓ₂)
  have hℓ2 : Nat.gcd ℓ₁ ℓ₂ * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) = ℓ₂ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right ℓ₁ ℓ₂)
  have hprod :
      (Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂))
          * (Nat.gcd ℓ₁ ℓ₂ * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂))
        = ℓ₁ * ℓ₂ := by
    rw [hℓ1, hℓ2]
  apply Nat.eq_of_mul_eq_mul_left hg
  have hmul : Nat.gcd ℓ₁ ℓ₂ * Nat.lcm ℓ₁ ℓ₂ = ℓ₁ * ℓ₂ :=
    Nat.gcd_mul_lcm ℓ₁ ℓ₂
  rw [hmul, ← hprod]
  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem scaled_mod (g a k t ρ : Nat) :
    (g * (a * k + t) + ρ) % (g * a)
      = (g * t + ρ) % (g * a) := by
  have h : g * (a * k + t) + ρ = g * a * k + (g * t + ρ) := by
    have h1 : g * (a * k + t) = g * (a * k) + g * t := Nat.mul_add g _ _
    have h2 : g * (a * k) = g * a * k := (Nat.mul_assoc g a k).symm
    rw [h1, h2, Nat.add_assoc]
  rw [h, Nat.mul_add_mod]

/-- Residue of `g * m + r % g` modulo `g * a`, for the lcm CRT lift. -/
theorem scaled_residue (g a m r : Nat)
    (hma : m % a = (r / g) % a) :
    (g * m + r % g) % (g * a) = r % (g * a) := by
  have hm : m = a * (m / a) + m % a := (Nat.div_add_mod m a).symm
  have hr : r = g * (r / g) + r % g := (Nat.div_add_mod r g).symm
  have hr' : r / g = a * ((r / g) / a) + (r / g) % a :=
    (Nat.div_add_mod (r / g) a).symm
  have hleft : (g * m + r % g) % (g * a)
      = (g * (a * (m / a) + m % a) + r % g) % (g * a) :=
    congrArg (fun x => (g * x + r % g) % (g * a)) hm
  have hsc := scaled_mod g a (m / a) (m % a) (r % g)
  have hrr : r = g * (a * ((r / g) / a) + (r / g) % a) + r % g :=
    hr.trans (congrArg (fun x => g * x + r % g) hr')
  have hright : r % (g * a)
      = (g * (a * ((r / g) / a) + (r / g) % a) + r % g) % (g * a) :=
    congrArg (fun x => x % (g * a)) hrr
  have hsc' := scaled_mod g a ((r / g) / a) ((r / g) % a) (r % g)
  rw [hleft, hsc, hma, hright, hsc']

/-- Compatible residues have a unique common class modulo `lcm`,
    including when `gcd > 1`. This is the dependent-pair mass `1/lcm`. -/
theorem crt_exists_lcm (ℓ₁ ℓ₂ r₁ r₂ : Nat)
    (h1 : 0 < ℓ₁) (h2 : 0 < ℓ₂)
    (hcompat : r₁ % Nat.gcd ℓ₁ ℓ₂ = r₂ % Nat.gcd ℓ₁ ℓ₂) :
    ∃ n, n < Nat.lcm ℓ₁ ℓ₂ ∧ n % ℓ₁ = r₁ % ℓ₁ ∧ n % ℓ₂ = r₂ % ℓ₂ := by
  have hg : 0 < Nat.gcd ℓ₁ ℓ₂ := Nat.gcd_pos_of_pos_left ℓ₂ h1
  have hga : Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂) = ℓ₁ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left ℓ₁ ℓ₂)
  have hgb : Nat.gcd ℓ₁ ℓ₂ * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) = ℓ₂ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right ℓ₁ ℓ₂)
  have ha : 0 < ℓ₁ / Nat.gcd ℓ₁ ℓ₂ :=
    Nat.div_pos (Nat.le_of_dvd h1 (Nat.gcd_dvd_left ℓ₁ ℓ₂)) hg
  have hb : 0 < ℓ₂ / Nat.gcd ℓ₁ ℓ₂ :=
    Nat.div_pos (Nat.le_of_dvd h2 (Nat.gcd_dvd_right ℓ₁ ℓ₂)) hg
  have hcop :
      Nat.gcd (ℓ₁ / Nat.gcd ℓ₁ ℓ₂) (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) = 1 :=
    (Nat.coprime_div_gcd_div_gcd hg).gcd_eq_one
  have hlcm := lcm_eq_gcd_mul_divs ℓ₁ ℓ₂ hg
  have ⟨m, hmlt, hma, hmb⟩ :=
    crt_exists (ℓ₁ / Nat.gcd ℓ₁ ℓ₂) (ℓ₂ / Nat.gcd ℓ₁ ℓ₂)
      ((r₁ / Nat.gcd ℓ₁ ℓ₂) % (ℓ₁ / Nat.gcd ℓ₁ ℓ₂))
      ((r₂ / Nat.gcd ℓ₁ ℓ₂) % (ℓ₂ / Nat.gcd ℓ₁ ℓ₂))
      hcop ha hb (Nat.mod_lt _ ha) (Nat.mod_lt _ hb)
  have hρ : r₁ % Nat.gcd ℓ₁ ℓ₂ < Nat.gcd ℓ₁ ℓ₂ := Nat.mod_lt r₁ hg
  have hnlt :
      Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂
        < Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂)
            * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) := by
    have hstep :
        Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂
          < Nat.gcd ℓ₁ ℓ₂ * m + Nat.gcd ℓ₁ ℓ₂ :=
      Nat.add_lt_add_left hρ _
    have hsucc :
        Nat.gcd ℓ₁ ℓ₂ * m + Nat.gcd ℓ₁ ℓ₂
          = Nat.gcd ℓ₁ ℓ₂ * (m + 1) := (Nat.mul_succ _ _).symm
    have hle :
        Nat.gcd ℓ₁ ℓ₂ * (m + 1)
          ≤ Nat.gcd ℓ₁ ℓ₂
              * ((ℓ₁ / Nat.gcd ℓ₁ ℓ₂) * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂)) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hmlt)
    have hassoc :
        Nat.gcd ℓ₁ ℓ₂
            * ((ℓ₁ / Nat.gcd ℓ₁ ℓ₂) * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂))
          = Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂)
              * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) :=
      (Nat.mul_assoc _ _ _).symm
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_eq hstep hsucc)
      (Nat.le_trans hle (Nat.le_of_eq hassoc))
  have hmod1 :
      (Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂) % ℓ₁ = r₁ % ℓ₁ := by
    have hsc :=
      scaled_residue (Nat.gcd ℓ₁ ℓ₂) (ℓ₁ / Nat.gcd ℓ₁ ℓ₂) m r₁ hma
    have h1 :
        (Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂)
            % (Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂))
          = (Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂) % ℓ₁ := by
      rw [hga]
    have h2 :
        r₁ % (Nat.gcd ℓ₁ ℓ₂ * (ℓ₁ / Nat.gcd ℓ₁ ℓ₂)) = r₁ % ℓ₁ := by
      rw [hga]
    rw [← h1, hsc, h2]
  have hmod2 :
      (Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂) % ℓ₂ = r₂ % ℓ₂ := by
    have hma' : m % (ℓ₂ / Nat.gcd ℓ₁ ℓ₂)
        = (r₂ / Nat.gcd ℓ₁ ℓ₂) % (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) := hmb
    have hsc :=
      scaled_residue (Nat.gcd ℓ₁ ℓ₂) (ℓ₂ / Nat.gcd ℓ₁ ℓ₂) m r₂ hma'
    have hn :
        Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂
          = Nat.gcd ℓ₁ ℓ₂ * m + r₂ % Nat.gcd ℓ₁ ℓ₂ := by
      rw [hcompat]
    have h1 :
        (Nat.gcd ℓ₁ ℓ₂ * m + r₂ % Nat.gcd ℓ₁ ℓ₂)
            % (Nat.gcd ℓ₁ ℓ₂ * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂))
          = (Nat.gcd ℓ₁ ℓ₂ * m + r₂ % Nat.gcd ℓ₁ ℓ₂) % ℓ₂ := by
      rw [hgb]
    have h2 :
        r₂ % (Nat.gcd ℓ₁ ℓ₂ * (ℓ₂ / Nat.gcd ℓ₁ ℓ₂)) = r₂ % ℓ₂ := by
      rw [hgb]
    rw [hn, ← h1, hsc, h2]
  refine ⟨Nat.gcd ℓ₁ ℓ₂ * m + r₁ % Nat.gcd ℓ₁ ℓ₂, ?_, hmod1, hmod2⟩
  rwa [hlcm]

/-- Dependent compatible pair: unique common residue modulo `lcm`.
    Pair mass is `1/lcm` when `gcd > 1` and the residues agree. -/
theorem pair_hit_compatible (ℓ₁ r₁ ℓ₂ r₂ : Nat)
    (h1 : 0 < ℓ₁) (h2 : 0 < ℓ₂)
    (hcompat : r₁ % Nat.gcd ℓ₁ ℓ₂ = r₂ % Nat.gcd ℓ₁ ℓ₂) :
    ((List.range (Nat.lcm ℓ₁ ℓ₂)).filter
      (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂)).length = 1 := by
  let xs := (List.range (Nat.lcm ℓ₁ ℓ₂)).filter
    (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂)
  have ⟨n0, hnlt, hnq, hnP⟩ := crt_exists_lcm ℓ₁ ℓ₂ r₁ r₂ h1 h2 hcompat
  have hmem : n0 ∈ xs := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hnlt, ?_⟩
    simp [hnq, hnP]
  have huniq : ∀ x ∈ xs, x = n0 := by
    intro x hx
    have hxF := List.mem_filter.mp hx
    have hxlt := List.mem_range.mp hxF.1
    have hxAB : x % ℓ₁ = r₁ % ℓ₁ ∧ x % ℓ₂ = r₂ % ℓ₂ := by
      simpa [Bool.and_eq_true, beq_iff_eq] using hxF.2
    exact crt_unique_lcm h1 h2 hxlt hnlt
      (hxAB.1.trans hnq.symm) (hxAB.2.trans hnP.symm)
  have hnd : xs.Nodup :=
    List.Pairwise.filter
      (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂) List.nodup_range
  change xs.length = 1
  match xs with
  | [] => exact False.elim (by cases hmem)
  | [_a] => rfl
  | a :: b :: as =>
    have ha : a = n0 := huniq a (by simp)
    have hb : b = n0 := huniq b (by simp)
    have hnd' := List.nodup_cons.mp hnd
    exact False.elim (hnd'.1 (by simp [ha, hb]))

/-- Pair mass on `lcm`: `1` if compatible, `0` if not. -/
theorem pair_hit_count (ℓ₁ r₁ ℓ₂ r₂ : Nat)
    (h1 : 0 < ℓ₁) (h2 : 0 < ℓ₂) :
    ((List.range (Nat.lcm ℓ₁ ℓ₂)).filter
      (fun n => n % ℓ₁ == r₁ % ℓ₁ && n % ℓ₂ == r₂ % ℓ₂)).length
      = if r₁ % Nat.gcd ℓ₁ ℓ₂ = r₂ % Nat.gcd ℓ₁ ℓ₂ then 1 else 0 := by
  if hcompat : r₁ % Nat.gcd ℓ₁ ℓ₂ = r₂ % Nat.gcd ℓ₁ ℓ₂ then
    simp [hcompat, pair_hit_compatible ℓ₁ r₁ ℓ₂ r₂ h1 h2 hcompat]
  else
    simp [hcompat, pair_hit_incompatible ℓ₁ r₁ ℓ₂ r₂ h1 h2 hcompat]

/-! # Janson form (dependent pairs only)

    `Δ` sums pair mass only over `dependent` pairs (`gcd > 1`).
    Titu gives the mass ratio `∑ p²/(p+d) ≥ μ²/(μ+2Δ)`.
    Sequential Janson I counting is `janson_hit_lower` /
    `janson_step` (after the empty-graph product). The exponential
    `P ≤ exp(-∑ p/(1+δ))` is not proved. Do not inhabit
    `FibreSuenHypothesis` with these lemmas.
-/

def hitCount (e : Nat × Nat) (M : Nat) : Nat :=
  if e.1 = 0 then 0
  else ((List.range M).filter (fun n => n % e.1 == e.2 % e.1)).length

def pairHitCount (e₁ e₂ : Nat × Nat) (M : Nat) : Nat :=
  if e₁.1 = 0 ∨ e₂.1 = 0 then 0
  else ((List.range M).filter
    (fun n => n % e₁.1 == e₁.2 % e₁.1 && n % e₂.1 == e₂.2 % e₂.1)).length

def muHit (evs : List (Nat × Nat)) (M : Nat) : Nat :=
  (evs.map (fun e => hitCount e M)).sum

/-- Janson `Δ` as a hit count: dependent pairs only. -/
def deltaHit (evs : List (Nat × Nat)) (M : Nat) : Nat :=
  ((pairList evs).map fun p =>
    if dependent p.1 p.2 then pairHitCount p.1 p.2 M else 0).sum

/-- Pair-intersection mass, including independent pairs. Used to
    justify `pairMass`; Janson `Δ` keeps only `dependent` summands. -/
def neighborPairMass (e : Nat × Nat) (evs : List (Nat × Nat)) : Rat :=
  ((evs.filter (fun e' => !(e' == e) && dependent e e')).map
    (fun e' => pairMass e.1 e.2 e'.1 e'.2)).sum

theorem pairHitCount_lcm (ℓ₁ r₁ ℓ₂ r₂ : Nat)
    (h1 : 0 < ℓ₁) (h2 : 0 < ℓ₂) :
    pairHitCount (ℓ₁, r₁) (ℓ₂, r₂) (Nat.lcm ℓ₁ ℓ₂)
      = if r₁ % Nat.gcd ℓ₁ ℓ₂ = r₂ % Nat.gcd ℓ₁ ℓ₂ then 1 else 0 := by
  have hne1 : ℓ₁ ≠ 0 := Nat.pos_iff_ne_zero.mp h1
  have hne2 : ℓ₂ ≠ 0 := Nat.pos_iff_ne_zero.mp h2
  simp [pairHitCount, hne1, hne2]
  exact pair_hit_count ℓ₁ r₁ ℓ₂ r₂ h1 h2

theorem two_mul_le_add_sq (x y : Nat) : 2 * x * y ≤ x * x + y * y := by
  induction x generalizing y with
  | zero => simp
  | succ x ih =>
    cases y with
    | zero => simp
    | succ y =>
      have h := ih y
      have hL : 2 * (x + 1) * (y + 1) = 2 * x * y + 2 * x + 2 * y + 2 := by
        simp [Nat.succ_mul, Nat.mul_succ, Nat.mul_add, Nat.add_mul,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hR :
          (x + 1) * (x + 1) + (y + 1) * (y + 1)
            = x * x + y * y + 2 * x + 2 * y + 2 := by
        simp [Nat.succ_mul, Nat.mul_succ, Nat.mul_add, Nat.add_mul,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      omega

theorem add_mul_self (x y : Nat) :
    (x + y) * (x + y) = x * x + y * y + 2 * x * y := by
  have h : (x + y) * (x + y) = x * x + x * y + y * x + y * y := by
    simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have hxy : x * y + y * x = 2 * x * y := by
    rw [Nat.mul_comm y x, Nat.mul_assoc]
    exact (Nat.two_mul (x * y)).symm
  rw [h]
  omega

/-- Titu's lemma for two terms, cleared denominators.
    `a₁²/b₁ + a₂²/b₂ ≥ (a₁+a₂)²/(b₁+b₂)`. -/
theorem titu_two (a₁ b₁ a₂ b₂ : Nat) :
    (a₁ * a₁ * b₂ + a₂ * a₂ * b₁) * (b₁ + b₂)
      ≥ (a₁ + a₂) * (a₁ + a₂) * b₁ * b₂ := by
  have hcross : 2 * a₁ * a₂ * b₁ * b₂
      ≤ a₁ * a₁ * b₂ * b₂ + a₂ * a₂ * b₁ * b₁ := by
    have := two_mul_le_add_sq (a₁ * b₂) (a₂ * b₁)
    have h' : 2 * (a₁ * b₂) * (a₂ * b₁) = 2 * a₁ * a₂ * b₁ * b₂ := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h'' :
        (a₁ * b₂) * (a₁ * b₂) + (a₂ * b₁) * (a₂ * b₁)
          = a₁ * a₁ * b₂ * b₂ + a₂ * a₂ * b₁ * b₁ := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rwa [h', h''] at this
  have hL :
      (a₁ * a₁ * b₂ + a₂ * a₂ * b₁) * (b₁ + b₂)
        = a₁ * a₁ * b₂ * b₁ + a₂ * a₂ * b₁ * b₁
            + a₁ * a₁ * b₂ * b₂ + a₂ * a₂ * b₁ * b₂ := by
    rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
    simp [Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hR :
      (a₁ + a₂) * (a₁ + a₂) * b₁ * b₂
        = a₁ * a₁ * b₁ * b₂ + a₂ * a₂ * b₁ * b₂
            + 2 * a₁ * a₂ * b₁ * b₂ := by
    rw [add_mul_self]
    have hs : (a₁ * a₁ + a₂ * a₂ + 2 * a₁ * a₂) * b₁
        = a₁ * a₁ * b₁ + a₂ * a₂ * b₁ + 2 * a₁ * a₂ * b₁ := by
      rw [Nat.add_mul, Nat.add_mul]
    rw [hs, Nat.add_mul, Nat.add_mul]
  have hcomm : a₁ * a₁ * b₂ * b₁ = a₁ * a₁ * b₁ * b₂ := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- Janson mass ratio for two events: if `d` is the dependent-pair
    hit count, then `∑ p²/(p+d) ≥ μ²/(μ+2d)`. Independent pairs take
    `d = 0` and are not in `Δ`. -/
theorem janson_mass_two (p₁ p₂ d : Nat) :
    (p₁ * p₁ * (p₂ + d) + p₂ * p₂ * (p₁ + d)) * (p₁ + p₂ + d + d)
      ≥ (p₁ + p₂) * (p₁ + p₂) * (p₁ + d) * (p₂ + d) := by
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    titu_two p₁ (p₁ + d) p₂ (p₂ + d)

theorem janson_mass_two_events (e₁ e₂ : Nat × Nat) (M : Nat) :
    let p₁ := hitCount e₁ M
    let p₂ := hitCount e₂ M
    let d := if dependent e₁ e₂ then pairHitCount e₁ e₂ M else 0
    (p₁ * p₁ * (p₂ + d) + p₂ * p₂ * (p₁ + d)) * (p₁ + p₂ + d + d)
      ≥ (p₁ + p₂) * (p₁ + p₂) * (p₁ + d) * (p₂ + d) :=
  janson_mass_two (hitCount e₁ M) (hitCount e₂ M)
    (if dependent e₁ e₂ then pairHitCount e₁ e₂ M else 0)

theorem pairMass_of_hit (ℓ₁ r₁ ℓ₂ r₂ : Nat)
    (h1 : 0 < ℓ₁) (_h2 : 0 < ℓ₂) :
    pairMass ℓ₁ r₁ ℓ₂ r₂
      = if r₁ % Nat.gcd ℓ₁ ℓ₂ = r₂ % Nat.gcd ℓ₁ ℓ₂ then
          invNat (Nat.lcm ℓ₁ ℓ₂)
        else 0 := by
  have hg : Nat.gcd ℓ₁ ℓ₂ ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.gcd_pos_of_pos_left ℓ₂ h1)
  unfold pairMass pairCompatible
  simp [hg, beq_iff_eq]

/-! # Mass growth (termwise two-log input) -/

def cellWeight (cell : Cell) : Rat :=
  (1 : Rat) / (4 * cell.a * cell.c * cell.d : Nat)

theorem Cell.q_lt_four_acd (cell : Cell) :
    cell.q < 4 * cell.a * cell.c * cell.d := by
  have h : 1 ≤ 4 * cell.a * cell.c * cell.d := cell.four_acd_pos
  simp [Cell.q]
  exact Nat.sub_lt h (by decide)

theorem one_div_nat_num_den (n : Nat) (hn : 0 < n) :
    ((1 : Rat) / (n : Nat)).num = 1 ∧ ((1 : Rat) / (n : Nat)).den = n := by
  have heq : (1 : Rat) / (n : Nat) = mkRat 1 n :=
    (Rat.mkRat_eq_div (1 : Int) n).symm
  have hnz : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hnorm : mkRat 1 n = Rat.normalize 1 n hnz := by
    unfold mkRat
    simp [hnz]
  rw [heq, hnorm, Rat.normalize_eq]
  constructor <;> simp

theorem one_div_anti {q N : Nat} (hq : 0 < q) (hN : 0 < N) (hle : q ≤ N) :
    (1 : Rat) / (N : Nat) ≤ (1 : Rat) / (q : Nat) := by
  have hq' := one_div_nat_num_den q hq
  have hN' := one_div_nat_num_den N hN
  rw [Rat.le_iff, hq'.1, hq'.2, hN'.1, hN'.2]
  simpa using Int.ofNat_le.mpr hle

/-- Termwise mass growth: `1/q ≥ 1/(4acd)`. Summing over the box
    produces the two-log harmonic comparison of the write-up. -/
theorem Cell.inv_q_ge_weight (cell : Cell) :
    cellWeight cell ≤ (1 : Rat) / (cell.q : Nat) :=
  one_div_anti cell.q_pos cell.four_acd_pos (Nat.le_of_lt cell.q_lt_four_acd)

def MassGrowth : Prop :=
  ∀ cell : Cell, cellWeight cell ≤ (1 : Rat) / (cell.q : Nat)

theorem massGrowth_holds : MassGrowth :=
  Cell.inv_q_ge_weight

theorem Rat.add_le_add {a b c d : Rat} (hac : a ≤ c) (hbd : b ≤ d) :
    a + b ≤ c + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr hac) (Rat.add_le_add_left.mpr hbd)

/-- Termwise comparison folds over any cell list. This is not yet
    `μ(A) ≥ κ(log A)²` after deduplication. -/
theorem map_weight_le_invq (cells : List Cell) :
    (cells.map cellWeight).sum
      ≤ (cells.map fun c => (1 : Rat) / (c.q : Nat)).sum := by
  induction cells with
  | nil => simp
  | cons c cells ih =>
    simp [List.sum_cons]
    exact Rat.add_le_add (Cell.inv_q_ge_weight c) ih

theorem box_weight_le_invq (A : Nat) :
    ((boxCells A).map cellWeight).sum
      ≤ ((boxCells A).map fun c => (1 : Rat) / (c.q : Nat)).sum :=
  map_weight_le_invq _

def harm (n : Nat) : Rat :=
  ((List.range n).map (fun k => (1 : Rat) / (k + 1 : Nat))).sum

def sliceCells (A : Nat) : List Cell :=
  (List.range A).map fun a' =>
    { a := a' + 1
      c := 1
      d := 1
      ha := Nat.succ_pos _
      hc := Nat.succ_pos _
      hd := Nat.succ_pos _ }

/-- The `c=d=1` slice has distinct moduli `4a−1`. After dedup this is
    a one-log family: mass at least `∑ 1/(4a)`. Two-log after full
    dedup remains an external hypothesis. -/
theorem slice_q_nodup (A : Nat) : ((sliceCells A).map Cell.q).Nodup := by
  simp [sliceCells]
  apply nodup_map_of_inj List.nodup_range
  intro a' b' _ha _hb hq
  have : 4 * (a' + 1) - 1 = 4 * (b' + 1) - 1 := by
    simpa [Cell.q] using hq
  have h4 : 4 * (a' + 1) = 4 * (b' + 1) := by omega
  have : a' + 1 = b' + 1 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h4
  omega

theorem slice_invq_ge_weight (A : Nat) :
    ((sliceCells A).map cellWeight).sum
      ≤ ((sliceCells A).map fun c => (1 : Rat) / (c.q : Nat)).sum :=
  map_weight_le_invq _

/-! # H1 / H2 assembly: two-stage count bound -/

/-- If every surviving fibre contributes at most `M` uncovered points,
    the total uncovered count is at most `#survivors · M`.
    This is the exact H1×H2 combination on finite fibres. -/
theorem sum_le_length_mul_max (xs : List Nat) (M : Nat)
    (h : ∀ x ∈ xs, x ≤ M) : xs.sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≤ M := h x (by simp)
    have ih' : xs.sum ≤ xs.length * M :=
      ih (fun y hy => h y (by simp [hy]))
    simp [List.sum_cons, List.length_cons]
    calc
      x + xs.sum ≤ M + xs.length * M := Nat.add_le_add hx ih'
      _ = xs.length * M + M := Nat.add_comm _ _
      _ = (xs.length + 1) * M := (Nat.succ_mul xs.length M).symm

def HubExponentialBound : Prop :=
  ∀ (fibreHits : List Nat) (M : Nat),
    (∀ x ∈ fibreHits, x ≤ M) →
      fibreHits.sum ≤ fibreHits.length * M

def FibreExponentialBound : Prop :=
  HubExponentialBound

theorem hubFibre_assembly : HubExponentialBound :=
  sum_le_length_mul_max

theorem fibreBound_assembly : FibreExponentialBound :=
  hubFibre_assembly

/-! # Exact product-space density and the two-stage identity -/

def avoids (evs : List (Nat × Nat)) (n : Nat) : Bool :=
  evs.all fun e => e.1 == 0 || n % e.1 != e.2 % e.1

def uncovered (evs : List (Nat × Nat)) (M : Nat) : List Nat :=
  (List.range M).filter (fun n => avoids evs n)

def fibreUncovered (evs : List (Nat × Nat)) (H L ρ : Nat) : Nat :=
  ((List.range L).filter (fun t => avoids evs (ρ + H * t))).length

theorem sum_map_add (n : Nat) (f g : Nat → Nat) :
    ((List.range n).map (fun i => f i + g i)).sum
      = ((List.range n).map f).sum + ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.map_append,
      List.sum_append, List.sum_append, List.sum_append, ih]
    simp [Nat.add_assoc, Nat.add_left_comm]

theorem sum_ite_eq_filter_length (n : Nat) (p : Nat → Bool) :
    ((List.range n).map (fun i => if p i then 1 else 0)).sum
      = ((List.range n).filter p).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.sum_append,
      List.length_append, ih]
    by_cases hp : p n <;> simp [hp]

theorem fibreUncovered_succ (evs : List (Nat × Nat)) (H L ρ : Nat) :
    fibreUncovered evs H (L + 1) ρ
      = fibreUncovered evs H L ρ
          + if avoids evs (ρ + H * L) then 1 else 0 := by
  unfold fibreUncovered
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases hp : avoids evs (ρ + H * L) <;> simp [hp]

/-- Exact two-stage count: every `n < H L` is uniquely `ρ + H t`.
    This is the finite form of
    `P(uncovered) = E[P(fibre survives | ρ)]`. -/
theorem map_const_zero_sum (n : Nat) :
    ((List.range n).map (fun _ => (0 : Nat))).sum = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp

theorem two_stage_count (evs : List (Nat × Nat)) (H L : Nat) (_hH : 0 < H) :
    (uncovered evs (H * L)).length
      = ((List.range H).map (fun ρ => fibreUncovered evs H L ρ)).sum := by
  induction L with
  | zero =>
    simp [uncovered, fibreUncovered]
    exact (map_const_zero_sum H).symm
  | succ L ih =>
    have hrange :
        List.range (H * (L + 1))
          = List.range (H * L) ++ (List.range H).map (H * L + ·) := by
      rw [Nat.mul_succ, List.range_add]
    have hsplit :
        (uncovered evs (H * (L + 1))).length
          = (uncovered evs (H * L)).length
              + (((List.range H).map (H * L + ·)).filter
                  (fun n => avoids evs n)).length := by
      unfold uncovered
      rw [hrange, List.filter_append, List.length_append]
    rw [hsplit]
    have hright :
        (((List.range H).map (H * L + ·)).filter
            (fun n => avoids evs n)).length
          = ((List.range H).filter
              (fun ρ => avoids evs (ρ + H * L))).length := by
      rw [List.filter_map, List.length_map]
      apply congrArg List.length
      apply List.filter_congr
      intro ρ _hρ
      simp [Nat.add_comm (H * L)]
    have hfib :
        ((List.range H).map (fun ρ => fibreUncovered evs H (L + 1) ρ)).sum
          = ((List.range H).map (fun ρ => fibreUncovered evs H L ρ)).sum
              + ((List.range H).map
                  (fun ρ =>
                    if avoids evs (ρ + H * L) then 1 else 0)).sum := by
      have hmap :=
        List.map_congr_left (l := List.range H)
          (fun ρ _ => fibreUncovered_succ evs H L ρ)
      rw [hmap]
      exact sum_map_add H
        (fun ρ => fibreUncovered evs H L ρ)
        (fun ρ => if avoids evs (ρ + H * L) then 1 else 0)
    have hite :=
      sum_ite_eq_filter_length H (fun ρ => avoids evs (ρ + H * L))
    rw [hright, ← hite, ih, hfib]

theorem avoids_false_of_hit (evs : List (Nat × Nat)) (e : Nat × Nat) (n : Nat)
    (hmem : e ∈ evs) (hq : 0 < e.1) (hhit : n % e.1 = e.2 % e.1) :
    avoids evs n = false := by
  unfold avoids
  cases h : evs.all (fun e => e.1 == 0 || n % e.1 != e.2 % e.1) with
  | false => rfl
  | true =>
    have hall := List.all_eq_true.mp h e hmem
    have hne : e.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hq
    simp [hhit, hne, beq_iff_eq] at hall

theorem classify_eq_hubForced_iff (T q r ρ : Nat) :
    classify T q r ρ = FibreClass.hubForced ↔
      smoothPart T q ≠ 0 ∧
        ρ % smoothPart T q = r % smoothPart T q ∧
        largePart T q ≤ 1 := by
  constructor
  · intro h
    if hs : smoothPart T q = 0 then
      simp [classify, hs] at h
    else if hinc : ρ % smoothPart T q ≠ r % smoothPart T q then
      simp [classify, hs, hinc] at h
    else if hell : largePart T q ≤ 1 then
      exact ⟨hs, by omega, hell⟩
    else
      simp [classify, hs, hinc, hell] at h
  · intro ⟨hs, hcompat, hell⟩
    simp [classify, hs, hcompat, hell]

theorem hub_forced_hits (T H q r ρ n : Nat)
    (hs : smoothPart T q ∣ H) (hρ : n % H = ρ)
    (hcls : classify T q r ρ = FibreClass.hubForced)
    (hq : 0 < q) :
    n % q = r % q := by
  have hspec := (classify_eq_hubForced_iff T q r ρ).mp hcls
  have hprod := smoothPart_mul_largePart T q
  have hspos : 0 < smoothPart T q := Nat.pos_of_ne_zero hspec.1
  have hℓpos : 0 < largePart T q := by
    have : 0 < smoothPart T q * largePart T q := by
      rw [hprod]; exact hq
    exact Nat.pos_of_mul_pos_left this
  have hell : largePart T q = 1 := by omega
  let s := smoothPart T q
  have hn : n % q = n % s := by
    have hqs : q = s * largePart T q := hprod.symm
    rw [hqs, hell, Nat.mul_one]
  have hr : r % q = r % s := by
    have hqs : q = s * largePart T q := hprod.symm
    rw [hqs, hell, Nat.mul_one]
  have hnmod : n % s = ρ % s := by
    have := Nat.mod_mod_of_dvd n hs
    rw [← this, hρ]
  rw [hn, hr, hnmod, hspec.2.1]

theorem fibre_zero_of_not_hub
    (T : Nat) (evs : List (Nat × Nat)) (H ρ t : Nat)
    (_hH : 0 < H) (hρ : ρ < H)
    (heq : H = hubOf T (evs.map (·.1)))
    (hfail : hubSurvives T evs ρ = false)
    (hpos : ∀ e ∈ evs, 0 < e.1) :
    avoids evs (ρ + H * t) = false := by
  have ⟨e, hmem, hne⟩ := List.all_eq_false.mp hfail
  have hcls : classify T e.1 e.2 ρ = FibreClass.hubForced := by
    simpa using hne
  have hqmem : e.1 ∈ evs.map (·.1) := List.mem_map.mpr ⟨e, hmem, rfl⟩
  have hsv : smoothPart T e.1 ∣ H := by
    rw [heq]; exact hubOf_dvd T (evs.map (·.1)) e.1 hqmem
  have hmod : (ρ + H * t) % H = ρ := by
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt hρ]
  have hhit :=
    hub_forced_hits T H e.1 e.2 ρ (ρ + H * t) hsv hmod hcls (hpos e hmem)
  exact avoids_false_of_hit evs e (ρ + H * t) hmem (hpos e hmem) hhit

theorem fibreUncovered_eq_zero_of_not_hub
    (T : Nat) (evs : List (Nat × Nat)) (H L ρ : Nat)
    (hH : 0 < H) (hρ : ρ < H)
    (heq : H = hubOf T (evs.map (·.1)))
    (hfail : hubSurvives T evs ρ = false)
    (hpos : ∀ e ∈ evs, 0 < e.1) :
    fibreUncovered evs H L ρ = 0 := by
  unfold fibreUncovered
  have hnil :
      (List.range L).filter (fun t => avoids evs (ρ + H * t)) = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro t _ht hf
    have := fibre_zero_of_not_hub T evs H ρ t hH hρ heq hfail hpos
    simp [this] at hf
  simp [hnil]

theorem map_sum_zero_off (l : List Nat) (p : Nat → Bool) (f : Nat → Nat)
    (h : ∀ x ∈ l, p x = false → f x = 0) :
    (l.map f).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hp : p x <;> simp [hp, h x List.mem_cons_self, ih']

/-- Surviving-fibre form of the two-stage identity:
    uncovered count = sum of fibre counts over hub survivors. -/
theorem two_stage_survivors
    (T : Nat) (evs : List (Nat × Nat)) (H L : Nat)
    (hH : 0 < H) (heq : H = hubOf T (evs.map (·.1)))
    (hpos : ∀ e ∈ evs, 0 < e.1) :
    (uncovered evs (H * L)).length
      = (((List.range H).filter (fun ρ => hubSurvives T evs ρ)).map
          (fun ρ => fibreUncovered evs H L ρ)).sum := by
  have hfull := two_stage_count evs H L hH
  have hzero :
      ∀ ρ ∈ List.range H,
        hubSurvives T evs ρ = false → fibreUncovered evs H L ρ = 0 := by
    intro ρ hρmem hfail
    exact fibreUncovered_eq_zero_of_not_hub T evs H L ρ hH
      (List.mem_range.mp hρmem) heq hfail hpos
  have hmap :=
    map_sum_zero_off (List.range H) (fun ρ => hubSurvives T evs ρ)
      (fun ρ => fibreUncovered evs H L ρ) hzero
  exact hfull.trans hmap

theorem list_sum_mul (xs : List Nat) (c : Nat) :
    (xs.map (fun x => x * c)).sum = xs.sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp [List.sum_cons, ih, Nat.add_mul]

theorem sum_mul_le_of_each (xs : List Nat) (c M : Nat)
    (h : ∀ x ∈ xs, x * c ≤ M) :
    xs.sum * c ≤ xs.length * M := by
  have hsum : xs.sum * c = (xs.map (fun x => x * c)).sum :=
    (list_sum_mul xs c).symm
  have hle : ∀ y ∈ xs.map (fun x => x * c), y ≤ M := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, heq⟩
    exact heq ▸ h x hx
  have := sum_le_length_mul_max (xs.map (fun x => x * c)) M hle
  simpa [hsum, List.length_map] using this

/-- Combination algebra for the replacement target: H1 and H2 with
    exponents `a k²` and `b k²` give density `≤ 2^{-(a+b) k²}`. -/
theorem finite_density_combine
    (uncov H L hubSurv a b k : Nat) (fibres : List Nat)
    (hId : uncov = fibres.sum) (hLen : fibres.length = hubSurv)
    (hH1 : hubSurv * 2 ^ (a * k * k) ≤ H)
    (hH2 : ∀ x ∈ fibres, x * 2 ^ (b * k * k) ≤ L) :
    uncov * 2 ^ ((a + b) * k * k) ≤ H * L := by
  have hsplit : (a + b) * k * k = a * k * k + b * k * k := by
    simp [Nat.add_mul]
  have hpow : 2 ^ ((a + b) * k * k)
      = 2 ^ (a * k * k) * 2 ^ (b * k * k) := by
    rw [hsplit, Nat.pow_add]
  have hrearr :
      fibres.sum * (2 ^ (a * k * k) * 2 ^ (b * k * k))
        = (fibres.sum * 2 ^ (b * k * k)) * 2 ^ (a * k * k) := by
    simp [Nat.mul_left_comm, Nat.mul_comm]
  rw [hId, hpow, hrearr]
  have h2 : fibres.sum * 2 ^ (b * k * k) ≤ fibres.length * L :=
    sum_mul_le_of_each fibres (2 ^ (b * k * k)) L hH2
  have hstep :
      (fibres.sum * 2 ^ (b * k * k)) * 2 ^ (a * k * k)
        ≤ (fibres.length * L) * 2 ^ (a * k * k) :=
    Nat.mul_le_mul_right _ h2
  have hassoc : fibres.length * L * 2 ^ (a * k * k)
      = fibres.length * 2 ^ (a * k * k) * L := by
    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have h1 : fibres.length * 2 ^ (a * k * k) ≤ H := by
    rw [hLen]; exact hH1
  have hfin : fibres.length * 2 ^ (a * k * k) * L ≤ H * L :=
    Nat.mul_le_mul_right L h1
  exact Nat.le_trans hstep (hassoc ▸ hfin)

/-! # Density-to-count transfer (justified AP discrepancy) -/

def countResidue (M r lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else
    (List.range (hi - lo)).filter
      (fun i => (lo + i) % M == r % M) |>.length

def countResidueLen (M r lo L : Nat) : Nat :=
  (List.range L).filter (fun i => (lo + i) % M == r % M) |>.length

theorem countResidue_eq_len (M r lo hi : Nat) :
    countResidue M r lo hi = countResidueLen M r lo (hi - lo) := by
  unfold countResidue countResidueLen
  split
  · have : hi - lo = 0 := Nat.sub_eq_zero_of_le ‹hi ≤ lo›
    simp [this]
  · rfl

/-- A single residue class meets `[lo, hi)` in at most `length` points. -/
theorem countResidue_le_length (M r lo hi : Nat) :
    countResidue M r lo hi ≤ hi - lo := by
  unfold countResidue
  split
  · simp
  · have := List.length_filter_le
      (fun i => (lo + i) % M == r % M) (List.range (hi - lo))
    simpa [List.length_range] using this

theorem distinct_cong_gap {M r a b : Nat} (hM : 0 < M)
    (ha : a % M = r % M) (hb : b % M = r % M) (hle : a ≤ b) :
    a = b ∨ M ≤ b - a := by
  have hdiv : M ∣ b - a := dvd_sub_of_mod_eq (by rw [ha, hb]) hle hM
  rcases hdiv with ⟨k, hk⟩
  cases k with
  | zero =>
    left
    omega
  | succ k =>
    right
    rw [hk]
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- At most one hit in any window of length `≤ M`. -/
theorem countResidueLen_le_one (M r lo L : Nat)
    (hM : 0 < M) (hL : L ≤ M) :
    countResidueLen M r lo L ≤ 1 := by
  let xs :=
    (List.range L).filter (fun i => (lo + i) % M == r % M)
  change xs.length ≤ 1
  have hnodup : xs.Nodup :=
    List.Pairwise.filter (fun i => (lo + i) % M == r % M) List.nodup_range
  if hle : xs.length ≤ 1 then
    exact hle
  else
  have h0 : 0 < xs.length := by omega
  have h1 : 1 < xs.length := by omega
  let i := xs[0]
  let j := xs[1]
  have hi : i ∈ xs := List.getElem_mem h0
  have hj : j ∈ xs := List.getElem_mem h1
  have hinej : i ≠ j := by
    intro heq
    have := (List.nodup_iff_eq_of_getElem_eq.mp hnodup) 0 1 h0 h1 heq
    exact (Nat.ne_of_lt (by decide : (0 : Nat) < 1)) this
  have hiL : i < L := List.mem_range.mp (List.mem_filter.mp hi).1
  have hjL : j < L := List.mem_range.mp (List.mem_filter.mp hj).1
  have hiC : (lo + i) % M = r % M := by
    simpa [beq_iff_eq] using (List.mem_filter.mp hi).2
  have hjC : (lo + j) % M = r % M := by
    simpa [beq_iff_eq] using (List.mem_filter.mp hj).2
  cases Nat.le_total i j with
  | inl hij =>
    have hne : lo + i ≠ lo + j := by omega
    have hgap0 := distinct_cong_gap hM hiC hjC (Nat.add_le_add_left hij lo)
    have hgap : M ≤ (lo + j) - (lo + i) := hgap0.resolve_left hne
    have hji : (lo + j) - (lo + i) = j - i := Nat.add_sub_add_left lo j i
    have hlt : j - i < M := by
      have : j - i ≤ j := Nat.sub_le j i
      exact Nat.lt_of_le_of_lt this (Nat.lt_of_lt_of_le hjL hL)
    exact False.elim (Nat.not_le.mpr hlt (hji ▸ hgap))
  | inr hji =>
    have hne : lo + j ≠ lo + i := by omega
    have hgap0 := distinct_cong_gap hM hjC hiC (Nat.add_le_add_left hji lo)
    have hgap : M ≤ (lo + i) - (lo + j) := hgap0.resolve_left hne
    have hij : (lo + i) - (lo + j) = i - j := Nat.add_sub_add_left lo i j
    have hlt : i - j < M := by
      have : i - j ≤ i := Nat.sub_le i j
      exact Nat.lt_of_le_of_lt this (Nat.lt_of_lt_of_le hiL hL)
    exact False.elim (Nat.not_le.mpr hlt (hij ▸ hgap))

theorem countResidueLen_add (M r lo a b : Nat) :
    countResidueLen M r lo (a + b)
      = countResidueLen M r lo a + countResidueLen M r (lo + a) b := by
  unfold countResidueLen
  rw [List.range_add, List.filter_append, List.length_append]
  congr 1
  rw [List.filter_map, List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro i _hi
  simp [Nat.add_assoc]

theorem countResidueLen_blocks (M r lo q : Nat) (hM : 0 < M) :
    countResidueLen M r lo (M * q) ≤ q := by
  induction q with
  | zero => simp [countResidueLen]
  | succ q ih =>
    rw [Nat.mul_succ, countResidueLen_add]
    have hwin : countResidueLen M r (lo + M * q) M ≤ 1 :=
      countResidueLen_le_one M r (lo + M * q) M hM (Nat.le_refl _)
    omega

/-- Justified AP discrepancy: a residue class meets an interval of
    length `L` in at most `L/M + 1` points. The withdrawn `O(H)` claim
    was this lemma at the hub alone; residual moduli need their own
    period. -/
theorem countResidueLen_le_div_add_one (M r lo L : Nat) (hM : 0 < M) :
    countResidueLen M r lo L ≤ L / M + 1 := by
  let q := L / M
  let rem := L % M
  have hL : L = M * q + rem := (Nat.div_add_mod L M).symm
  have heq : countResidueLen M r lo L
      = countResidueLen M r lo (M * q + rem) := by simp [hL]
  rw [heq, countResidueLen_add]
  have hblk : countResidueLen M r lo (M * q) ≤ q :=
    countResidueLen_blocks M r lo q hM
  have hrem : countResidueLen M r (lo + M * q) rem ≤ 1 :=
    countResidueLen_le_one M r (lo + M * q) rem hM
      (Nat.le_of_lt (Nat.mod_lt L hM))
  exact Nat.add_le_add hblk hrem

theorem countResidue_le_div_add_one (M r lo hi : Nat) (hM : 0 < M) :
    countResidue M r lo hi ≤ (hi - lo) / M + 1 := by
  rw [countResidue_eq_len]
  exact countResidueLen_le_div_add_one M r lo (hi - lo) hM

def DensityCountTransfer : Prop :=
  ∀ M r lo hi, 0 < M → countResidue M r lo hi ≤ (hi - lo) / M + 1

theorem densityCountTransfer_holds : DensityCountTransfer :=
  countResidue_le_div_add_one

/-- Transfer at a genuine period: a union of `|R|` residue classes
    meets an interval of length `L` in at most `|R| (L/M + 1)` points.
    Residual moduli are allowed — `M` must be a common period, not the
    hub alone. If `|R| ≤ M` this is `≤ L + M`. -/
def countUncovered (M : Nat) (rs : List Nat) (lo L : Nat) : Nat :=
  (rs.map (fun r => countResidueLen M r lo L)).sum

theorem transfer_at_period (M : Nat) (rs : List Nat) (lo L : Nat)
    (hM : 0 < M) :
    countUncovered M rs lo L ≤ rs.length * (L / M + 1) := by
  have h : ∀ x ∈ rs.map (fun r => countResidueLen M r lo L),
      x ≤ L / M + 1 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨r, _, hr⟩
    have := countResidueLen_le_div_add_one M r lo L hM
    simp [hr] at this
    exact this
  have hsum :=
    sum_le_length_mul_max (rs.map (fun r => countResidueLen M r lo L))
      (L / M + 1) h
  simpa [countUncovered, List.length_map] using hsum

theorem transfer_uncovered_le_length_add_period
    (M : Nat) (rs : List Nat) (lo L : Nat)
    (hM : 0 < M) (hR : rs.length ≤ M) :
    countUncovered M rs lo L ≤ L + M := by
  have h := transfer_at_period M rs lo L hM
  have hmul : rs.length * (L / M + 1) ≤ M * (L / M + 1) :=
    Nat.mul_le_mul_right _ hR
  have hsplit : M * (L / M + 1) = M * (L / M) + M := by
    rw [Nat.mul_add, Nat.mul_one]
  have hML : M * (L / M) ≤ L := Nat.mul_div_le L M
  omega

/-! # H2: residual reduction and independent fibre Suen

    Fibre Suen for a pairwise-coprime residual family (`Δ_ρ = 0`) is
    the independent product. That is not the two-log hypothesis
    `FibreSuenHypothesis`: a coprime family cannot carry two-log mass.
    Dependent fibres (`Δ_ρ > 0`) remain open.
-/

theorem residual_hit_iff (s ℓ n r : Nat)
    (hcop : Nat.gcd s ℓ = 1) (hs : 0 < s) (hℓ : 0 < ℓ)
    (hcompat : n % s = r % s) :
    n % (s * ℓ) = r % (s * ℓ) ↔ n % ℓ = r % ℓ := by
  constructor
  · intro h
    have hℓdiv : ℓ ∣ s * ℓ := ⟨s, by rw [Nat.mul_comm]⟩
    have hn : (n % (s * ℓ)) % ℓ = n % ℓ := Nat.mod_mod_of_dvd n hℓdiv
    have hr : (r % (s * ℓ)) % ℓ = r % ℓ := Nat.mod_mod_of_dvd r hℓdiv
    rw [← hn, h, hr]
  · intro h
    have hmul : 0 < s * ℓ := Nat.mul_pos hs hℓ
    have hns : (n % (s * ℓ)) % s = n % s :=
      Nat.mod_mod_of_dvd n ⟨ℓ, rfl⟩
    have hrs : (r % (s * ℓ)) % s = r % s :=
      Nat.mod_mod_of_dvd r ⟨ℓ, rfl⟩
    have hnℓ : (n % (s * ℓ)) % ℓ = n % ℓ :=
      Nat.mod_mod_of_dvd n ⟨s, by rw [Nat.mul_comm]⟩
    have hrℓ : (r % (s * ℓ)) % ℓ = r % ℓ :=
      Nat.mod_mod_of_dvd r ⟨s, by rw [Nat.mul_comm]⟩
    exact crt_unique hcop hs hℓ (Nat.mod_lt n hmul) (Nat.mod_lt r hmul)
      (hns.trans (hcompat.trans hrs.symm))
      (hnℓ.trans (h.trans hrℓ.symm))

theorem classify_eq_incompatible_iff (T q r ρ : Nat) :
    classify T q r ρ = FibreClass.incompatible ↔
      smoothPart T q = 0 ∨
        ρ % smoothPart T q ≠ r % smoothPart T q := by
  constructor
  · intro h
    if hs : smoothPart T q = 0 then
      exact Or.inl hs
    else if hinc : ρ % smoothPart T q ≠ r % smoothPart T q then
      exact Or.inr hinc
    else if hell : largePart T q ≤ 1 then
      simp [classify, hs, hinc, hell] at h
    else
      simp [classify, hs, hinc, hell] at h
  · intro h
    cases h with
    | inl hs => simp [classify, hs]
    | inr hinc =>
      if hs : smoothPart T q = 0 then
        simp [classify, hs]
      else
        simp [classify, hs, hinc]

theorem classify_eq_residual_iff (T q r ρ ell : Nat) :
    classify T q r ρ = FibreClass.residual ell ↔
      smoothPart T q ≠ 0 ∧
        ρ % smoothPart T q = r % smoothPart T q ∧
        1 < largePart T q ∧ ell = largePart T q := by
  constructor
  · intro h
    if hs : smoothPart T q = 0 then
      simp [classify, hs] at h
    else if hinc : ρ % smoothPart T q ≠ r % smoothPart T q then
      simp [classify, hs, hinc] at h
    else if hell : largePart T q ≤ 1 then
      simp [classify, hs, hinc, hell] at h
    else
      have hlt : 1 < largePart T q := Nat.not_le.mp hell
      simp [classify, hs, hinc, hell] at h
      exact ⟨hs, by omega, hlt, by omega⟩
  · intro ⟨hs, hcompat, hell, heq⟩
    have hnot : ¬ largePart T q ≤ 1 := Nat.not_le.mpr hell
    simp [classify, hs, hcompat, hnot, heq]

theorem ne_mod_of_ne_small {n r q s : Nat} (hdvd : s ∣ q)
    (hne : n % s ≠ r % s) : n % q ≠ r % q := by
  intro heq
  have hn : (n % q) % s = n % s := Nat.mod_mod_of_dvd n hdvd
  have hr : (r % q) % s = r % s := Nat.mod_mod_of_dvd r hdvd
  exact hne (hn.symm.trans (heq ▸ hr))

theorem classify_incompatible_miss (T H q r ρ n : Nat)
    (hs : smoothPart T q ∣ H) (hρ : n % H = ρ)
    (hcls : classify T q r ρ = FibreClass.incompatible)
    (hq : 0 < q) :
    n % q ≠ r % q := by
  have hinc := (classify_eq_incompatible_iff T q r ρ).mp hcls
  have hprod := smoothPart_mul_largePart T q
  have hspos : 0 < smoothPart T q := by
    have : 0 < smoothPart T q * largePart T q := by
      rw [hprod]; exact hq
    exact Nat.pos_of_mul_pos_right this
  have hne : ρ % smoothPart T q ≠ r % smoothPart T q := by
    cases hinc with
    | inl hz => exact False.elim (Nat.ne_of_gt hspos hz)
    | inr h => exact h
  have hnmod : n % smoothPart T q = ρ % smoothPart T q := by
    have := Nat.mod_mod_of_dvd n hs
    rw [← this, hρ]
  have hsmall : n % smoothPart T q ≠ r % smoothPart T q := by
    rw [hnmod]; exact hne
  exact ne_mod_of_ne_small ⟨largePart T q, hprod.symm⟩ hsmall

theorem mem_residualEvents (T : Nat) (evs : List (Nat × Nat)) (ρ : Nat)
    (e' : Nat × Nat) :
    e' ∈ residualEvents T evs ρ ↔
      ∃ e ∈ evs, classify T e.1 e.2 ρ = FibreClass.residual e'.1 ∧
        e' = (e'.1, e.2 % e'.1) := by
  constructor
  · intro h
    rcases List.mem_filterMap.mp h with ⟨e, hmem, hf⟩
    revert hf
    cases hcls : classify T e.1 e.2 ρ with
    | residual ell =>
      intro hf
      have heq : e' = (ell, e.2 % ell) := Option.some.inj hf.symm
      refine ⟨e, hmem, ?_, ?_⟩
      · rw [heq]; exact hcls
      · rw [heq]
    | incompatible =>
      intro hf
      simp at hf
    | hubForced =>
      intro hf
      simp at hf
  · intro ⟨e, hmem, hcls, heq⟩
    refine List.mem_filterMap.mpr ⟨e, hmem, ?_⟩
    change (match classify T e.1 e.2 ρ with
      | FibreClass.residual ell => some (ell, e.2 % ell)
      | _ => none) = some e'
    rw [hcls]
    exact congrArg some heq.symm

theorem avoids_eq_residual
    (T : Nat) (evs : List (Nat × Nat)) (H ρ n : Nat)
    (hsurv : hubSurvives T evs ρ = true)
    (heq : H = hubOf T (evs.map (·.1)))
    (hρ : n % H = ρ) (hpos : ∀ e ∈ evs, 0 < e.1) :
    avoids evs n = avoids (residualEvents T evs ρ) n := by
  cases hE : avoids evs n with
  | false =>
    cases hR : avoids (residualEvents T evs ρ) n with
    | false => rfl
    | true =>
      have ⟨e, hmem, hne⟩ := List.all_eq_false.mp hE
      have hq : 0 < e.1 := hpos e hmem
      have hhit : ¬ (e.1 == 0 || n % e.1 != e.2 % e.1) := by
        simpa using hne
      have heq0 : e.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hq
      have hmod : n % e.1 = e.2 % e.1 := by
        simp [heq0, beq_iff_eq] at hhit
        exact hhit
      have hqmem : e.1 ∈ evs.map (·.1) := List.mem_map.mpr ⟨e, hmem, rfl⟩
      have hsv : smoothPart T e.1 ∣ H := by
        rw [heq]; exact hubOf_dvd T _ e.1 hqmem
      if hcls : classify T e.1 e.2 ρ = FibreClass.hubForced then
        have : hubSurvives T evs ρ = false := by
          refine List.all_eq_false.mpr ⟨e, hmem, ?_⟩
          simp [hcls]
        simp [hsurv] at this
      else if hinc : classify T e.1 e.2 ρ = FibreClass.incompatible then
        exact False.elim
          (classify_incompatible_miss T H e.1 e.2 ρ n hsv hρ hinc hq hmod)
      else
        have hell : ∃ ell, classify T e.1 e.2 ρ = FibreClass.residual ell := by
          cases h : classify T e.1 e.2 ρ with
          | residual ell => exact ⟨ell, rfl⟩
          | incompatible => exact False.elim (hinc h)
          | hubForced => exact False.elim (hcls h)
        rcases hell with ⟨ell, hres⟩
        have hspec := (classify_eq_residual_iff T e.1 e.2 ρ ell).mp hres
        have he' : (ell, e.2 % ell) ∈ residualEvents T evs ρ :=
          (mem_residualEvents T evs ρ (ell, e.2 % ell)).mpr
            ⟨e, hmem, hres, rfl⟩
        have hRall := List.all_eq_true.mp hR (ell, e.2 % ell) he'
        have hℓpos : 0 < ell := by
          have : 1 < ell := by rw [hspec.2.2.2]; exact hspec.2.2.1
          exact Nat.zero_lt_of_lt this
        have hprod := smoothPart_mul_largePart T e.1
        have hspos : 0 < smoothPart T e.1 := Nat.pos_of_ne_zero hspec.1
        have hcop : Nat.gcd (smoothPart T e.1) ell = 1 := by
          rw [hspec.2.2.2]; exact gcd_smooth_large T e.1 hq
        have hcompat : n % smoothPart T e.1 = e.2 % smoothPart T e.1 := by
          have := Nat.mod_mod_of_dvd n hsv
          rw [← this, hρ, hspec.2.1]
        have hiff :=
          residual_hit_iff (smoothPart T e.1) ell n e.2 hcop hspos hℓpos
            hcompat
        let s := smoothPart T e.1
        have hqeq : e.1 = s * ell := by
          have hℓeq : ell = largePart T e.1 := hspec.2.2.2
          exact (hℓeq ▸ hprod).symm
        have hmod' : n % (s * ell) = e.2 % (s * ell) := by
          rw [← hqeq]; exact hmod
        have hℓeq : n % ell = e.2 % ell := hiff.mp hmod'
        have hne0 : ell ≠ 0 := Nat.pos_iff_ne_zero.mp hℓpos
        simp [hne0, beq_iff_eq] at hRall
        exact False.elim (hRall hℓeq)
  | true =>
    cases hR : avoids (residualEvents T evs ρ) n with
    | true => rfl
    | false =>
      have ⟨e', hmem', hne'⟩ := List.all_eq_false.mp hR
      rcases (mem_residualEvents T evs ρ e').mp hmem' with
        ⟨e, hmem, hcls, heq'⟩
      have hspec := (classify_eq_residual_iff T e.1 e.2 ρ e'.1).mp hcls
      have hq : 0 < e.1 := hpos e hmem
      have hℓpos : 0 < e'.1 := by
        have : 1 < e'.1 := by rw [hspec.2.2.2]; exact hspec.2.2.1
        exact Nat.zero_lt_of_lt this
      have hall := List.all_eq_true.mp hE e hmem
      have hqmem : e.1 ∈ evs.map (·.1) := List.mem_map.mpr ⟨e, hmem, rfl⟩
      have hsv : smoothPart T e.1 ∣ H := by
        rw [heq]; exact hubOf_dvd T _ e.1 hqmem
      have hprod := smoothPart_mul_largePart T e.1
      have hspos : 0 < smoothPart T e.1 := Nat.pos_of_ne_zero hspec.1
      have hcop : Nat.gcd (smoothPart T e.1) e'.1 = 1 := by
        rw [hspec.2.2.2]; exact gcd_smooth_large T e.1 hq
      have hcompat : n % smoothPart T e.1 = e.2 % smoothPart T e.1 := by
        have := Nat.mod_mod_of_dvd n hsv
        rw [← this, hρ, hspec.2.1]
      let s := smoothPart T e.1
      have hqeq : e.1 = s * e'.1 := by
        have hℓeq : e'.1 = largePart T e.1 := hspec.2.2.2
        exact (hℓeq ▸ hprod).symm
      have hmiss : n % e.1 ≠ e.2 % e.1 := by
        have hne0 : e.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hq
        simp [hne0, beq_iff_eq] at hall
        exact hall
      have hiff :=
        residual_hit_iff s e'.1 n e.2 hcop hspos hℓpos hcompat
      have hmissℓ : n % e'.1 ≠ e.2 % e'.1 := by
        intro heqℓ
        have : n % e.1 = e.2 % e.1 := by
          rw [hqeq]
          exact hiff.mpr heqℓ
        exact hmiss this
      have hr : e'.2 = e.2 % e'.1 := congrArg Prod.snd heq'
      have hne0 : e'.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hℓpos
      simp [hne0, hr, beq_iff_eq] at hne'
      exact False.elim (hmissℓ hne')

def evProd (evs : List (Nat × Nat)) : Nat :=
  evs.foldl (fun acc e => acc * e.1) 1

def evMissProd (evs : List (Nat × Nat)) : Nat :=
  evs.foldl (fun acc e => acc * (e.1 - 1)) 1

theorem foldl_mul_factor (init : Nat) (xs : List (Nat × Nat)) :
    xs.foldl (fun acc e => acc * e.1) init
      = init * xs.foldl (fun acc e => acc * e.1) 1 := by
  induction xs generalizing init with
  | nil => simp
  | cons e xs ih =>
    rw [List.foldl_cons, ih, List.foldl_cons, ih (1 * e.1), Nat.one_mul,
      Nat.mul_assoc]

theorem evProd_cons (e : Nat × Nat) (evs : List (Nat × Nat)) :
    evProd (e :: evs) = e.1 * evProd evs := by
  unfold evProd
  rw [List.foldl_cons, foldl_mul_factor, Nat.one_mul]

theorem foldl_miss_factor (init : Nat) (xs : List (Nat × Nat)) :
    xs.foldl (fun acc e => acc * (e.1 - 1)) init
      = init * xs.foldl (fun acc e => acc * (e.1 - 1)) 1 := by
  induction xs generalizing init with
  | nil => simp
  | cons e xs ih =>
    rw [List.foldl_cons, ih, List.foldl_cons, ih (1 * (e.1 - 1)), Nat.one_mul,
      Nat.mul_assoc]

theorem evMissProd_cons (e : Nat × Nat) (evs : List (Nat × Nat)) :
    evMissProd (e :: evs) = (e.1 - 1) * evMissProd evs := by
  unfold evMissProd
  rw [List.foldl_cons, foldl_miss_factor, Nat.one_mul]

theorem evProd_dvd_of_mem (evs : List (Nat × Nat)) (e : Nat × Nat)
    (hmem : e ∈ evs) : e.1 ∣ evProd evs := by
  induction evs with
  | nil => cases hmem
  | cons e' evs ih =>
    rw [evProd_cons]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      rw [heq]
      exact ⟨evProd evs, rfl⟩
    | inr h =>
      exact Nat.dvd_trans (ih h) ⟨e'.1, by rw [Nat.mul_comm]⟩

theorem coprime_to_evProd (q : Nat) (evs : List (Nat × Nat))
    (h : ∀ e ∈ evs, Nat.gcd q e.1 = 1) :
    Nat.gcd q (evProd evs) = 1 := by
  induction evs with
  | nil => simp [evProd]
  | cons e evs ih =>
    rw [evProd_cons]
    have he : Nat.gcd q e.1 = 1 := h e List.mem_cons_self
    have ht : Nat.gcd q (evProd evs) = 1 :=
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact (Nat.coprime_iff_gcd_eq_one.mpr he).mul_right
      (Nat.coprime_iff_gcd_eq_one.mpr ht)

theorem all_eq_of_pred {α : Type _} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.all_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem avoids_mod_of_dvd (evs : List (Nat × Nat)) (P n : Nat)
    (hdiv : ∀ e ∈ evs, e.1 ∣ P) :
    avoids evs n = avoids evs (n % P) := by
  unfold avoids
  apply all_eq_of_pred
  intro e hmem
  have hn : (n % P) % e.1 = n % e.1 := Nat.mod_mod_of_dvd n (hdiv e hmem)
  simp [hn]

theorem avoids_cons (e : Nat × Nat) (evs : List (Nat × Nat)) (n : Nat) :
    avoids (e :: evs) n
      = (avoids evs n && (e.1 == 0 || n % e.1 != e.2 % e.1)) := by
  simp [avoids, List.all_cons, Bool.and_comm]

theorem coprime_shift_inj (H L ρ t₁ t₂ : Nat)
    (hL : 0 < L) (hcop : Nat.gcd H L = 1)
    (ht₁ : t₁ < L) (ht₂ : t₂ < L)
    (heq : (ρ + H * t₁) % L = (ρ + H * t₂) % L) : t₁ = t₂ := by
  have hcop' : Nat.Coprime L H :=
    Nat.coprime_iff_gcd_eq_one.mpr (by rwa [Nat.gcd_comm])
  cases Nat.le_total t₂ t₁ with
  | inl hle =>
    have hleAdd : ρ + H * t₂ ≤ ρ + H * t₁ :=
      Nat.add_le_add_left (Nat.mul_le_mul_left H hle) _
    have hdiv : L ∣ (ρ + H * t₁) - (ρ + H * t₂) :=
      dvd_sub_of_mod_eq heq hleAdd hL
    have hsub : (ρ + H * t₁) - (ρ + H * t₂) = H * (t₁ - t₂) := by
      rw [Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    have hHd : L ∣ H * (t₁ - t₂) := by rwa [hsub] at hdiv
    have hd : L ∣ t₁ - t₂ := hcop'.dvd_of_dvd_mul_left hHd
    have hlt : t₁ - t₂ < L := Nat.lt_of_le_of_lt (Nat.sub_le t₁ t₂) ht₁
    rcases hd with ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k =>
      have : L ≤ t₁ - t₂ := by
        rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      exact False.elim (Nat.not_le.mpr hlt this)
  | inr hle =>
    have hleAdd : ρ + H * t₁ ≤ ρ + H * t₂ :=
      Nat.add_le_add_left (Nat.mul_le_mul_left H hle) _
    have hdiv : L ∣ (ρ + H * t₂) - (ρ + H * t₁) :=
      dvd_sub_of_mod_eq heq.symm hleAdd hL
    have hsub : (ρ + H * t₂) - (ρ + H * t₁) = H * (t₂ - t₁) := by
      rw [Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    have hHd : L ∣ H * (t₂ - t₁) := by rwa [hsub] at hdiv
    have hd : L ∣ t₂ - t₁ := hcop'.dvd_of_dvd_mul_left hHd
    have hlt : t₂ - t₁ < L := Nat.lt_of_le_of_lt (Nat.sub_le t₂ t₁) ht₂
    rcases hd with ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k =>
      have : L ≤ t₂ - t₁ := by
        rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      exact False.elim (Nat.not_le.mpr hlt this)

theorem fibreUncovered_periodic (evs : List (Nat × Nat)) (M K ρ : Nat)
    (hdiv : ∀ e ∈ evs, e.1 ∣ M) (hρ : ρ < M) :
    fibreUncovered evs M K ρ = if avoids evs ρ then K else 0 := by
  unfold fibreUncovered
  have hper : ∀ t, avoids evs (ρ + M * t) = avoids evs ρ := by
    intro t
    have hmod : (ρ + M * t) % M = ρ := by
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt hρ]
    have h1 := avoids_mod_of_dvd evs M (ρ + M * t) hdiv
    have h2 := avoids_mod_of_dvd evs M ρ hdiv
    have hρM : ρ % M = ρ := Nat.mod_eq_of_lt hρ
    rw [h1, hmod, h2, hρM]
  if hp : avoids evs ρ then
    have : (List.range K).filter (fun t => avoids evs (ρ + M * t))
        = List.range K := by
      apply List.filter_eq_self.mpr
      intro t _ht
      simp [hper t, hp]
    simp [this, hp]
  else
    have : (List.range K).filter (fun t => avoids evs (ρ + M * t)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t _ht hf
      simp [hper t, hp] at hf
    simp [this, hp]

theorem sum_ite_const (n K : Nat) (p : Nat → Bool) :
    ((List.range n).map (fun i => if p i then K else 0)).sum
      = ((List.range n).filter p).length * K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.filter_append,
      List.sum_append, List.length_append, ih]
    by_cases hp : p n
    · simp [hp, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    · simp [hp]

theorem uncovered_periodic_mul (evs : List (Nat × Nat)) (M K : Nat)
    (hM : 0 < M) (hdiv : ∀ e ∈ evs, e.1 ∣ M) :
    (uncovered evs (M * K)).length = (uncovered evs M).length * K := by
  have htwo := two_stage_count evs M K hM
  have hfib :
      ((List.range M).map (fun ρ => fibreUncovered evs M K ρ)).sum
        = ((List.range M).map
            (fun ρ => if avoids evs ρ then K else 0)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro ρ hρ
    exact fibreUncovered_periodic evs M K ρ hdiv (List.mem_range.mp hρ)
  have hite := sum_ite_const M K (fun ρ => avoids evs ρ)
  unfold uncovered at htwo ⊢
  rw [htwo, hfib, hite]

theorem evProd_pos (evs : List (Nat × Nat))
    (h : ∀ e ∈ evs, 0 < e.1) : 0 < evProd evs := by
  induction evs with
  | nil => simp [evProd]
  | cons e evs ih =>
    rw [evProd_cons]
    exact Nat.mul_pos (h e List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem filter_and_split {α : Type _} (p q : α → Bool) (l : List α) :
    (l.filter p).length
      = (l.filter (fun x => p x && q x)).length
          + (l.filter (fun x => p x && !q x)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq] <;> omega

/-- Independent two-event density on the product period. -/
theorem independent_two_prod (q P r s : Nat)
    (hcop : Nat.gcd q P = 1) (hq : 1 < q) (hP : 1 < P) :
    (uncovered [(q, r), (P, s)] (q * P)).length = (q - 1) * (P - 1) := by
  unfold uncovered
  have h := avoid_two_coprime q P r s hcop hq hP
  have hpred :
      ((List.range (q * P)).filter
          (fun n => n % q != r % q && n % P != s % P))
        = (List.range (q * P)).filter
            (fun n => avoids [(q, r), (P, s)] n) := by
    apply List.filter_congr
    intro n _hn
    have hqB : (q == 0) = false := by
      simp [Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hq)]
    have hPB : (P == 0) = false := by
      simp [Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hP)]
    simp [avoids, hqB, hPB]
  rw [← hpred, h]

/-- Empty-list and one-event independent Suen, used as H2 when `Δ_ρ = 0`
    has length at most 1. The n-event product is `avoid_two_coprime`
    plus the coprime-extension step still in progress. -/
theorem independent_avoid_nil :
    (uncovered [] 1).length = 1 := by
  simp [uncovered, avoids]

theorem independent_avoid_one (q r : Nat) (hq : 1 < q) :
    (uncovered [(q, r)] q).length = q - 1 := by
  unfold uncovered
  have h := avoid_one_mod q r hq
  have hpred :
      ((List.range q).filter (fun n => n % q != r % q))
        = (List.range q).filter (fun n => avoids [(q, r)] n) := by
    apply List.filter_congr
    intro n _hn
    have hqB : (q == 0) = false := by
      simp [Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hq)]
    simp [avoids, hqB]
  rw [← hpred, h]

theorem avoids_append_singleton (evs : List (Nat × Nat)) (e : Nat × Nat)
    (n : Nat) :
    avoids (evs ++ [e]) n = avoids (e :: evs) n := by
  simp [avoids, List.all_cons, Bool.and_comm]

theorem fibre_congruence_exists (P Q ρ r : Nat)
    (hP : 0 < P) (hQ : 0 < Q) (hcop : Nat.gcd P Q = 1) (hρ : ρ < P) :
    ∃ t, t < Q ∧ (ρ + P * t) % Q = r % Q := by
  have ⟨n, hnlt, hnq, hnP⟩ :=
    crt_exists Q P (r % Q) ρ (by rwa [Nat.gcd_comm]) hQ hP
      (Nat.mod_lt r hQ) hρ
  have ht : n / P < Q := (Nat.div_lt_iff_lt_mul hP).mpr hnlt
  refine ⟨n / P, ht, ?_⟩
  have hn : n = ρ + P * (n / P) :=
    calc
      n = P * (n / P) + n % P := (Nat.div_add_mod n P).symm
      _ = P * (n / P) + ρ := by rw [hnP]
      _ = ρ + P * (n / P) := Nat.add_comm _ _
  rw [← hn]
  exact hnq

theorem fibre_congruence_unique (P Q ρ t₁ t₂ : Nat)
    (hQ : 0 < Q) (hcop : Nat.gcd P Q = 1)
    (ht₁ : t₁ < Q) (ht₂ : t₂ < Q)
    (heq : (ρ + P * t₁) % Q = (ρ + P * t₂) % Q) : t₁ = t₂ :=
  coprime_shift_inj P Q ρ t₁ t₂ hQ hcop ht₁ ht₂ heq

theorem fibre_congruence_count (P Q ρ r : Nat)
    (hP : 0 < P) (hQ : 0 < Q) (hcop : Nat.gcd P Q = 1) (hρ : ρ < P) :
    ((List.range Q).filter
        (fun t => (ρ + P * t) % Q == r % Q)).length = 1 := by
  rcases fibre_congruence_exists P Q ρ r hP hQ hcop hρ with ⟨t0, ht0, hhit⟩
  let xs := (List.range Q).filter (fun t => (ρ + P * t) % Q == r % Q)
  have hmem : t0 ∈ xs := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr ht0, ?_⟩
    simp [hhit]
  have huniq : ∀ t ∈ xs, t = t0 := by
    intro t ht
    have htF := List.mem_filter.mp ht
    have heq : (ρ + P * t) % Q = r % Q := by
      simpa [beq_iff_eq] using htF.2
    exact fibre_congruence_unique P Q ρ t t0 hQ hcop
      (List.mem_range.mp htF.1) ht0 (heq.trans hhit.symm)
  have hnd : xs.Nodup :=
    List.Pairwise.filter (fun t => (ρ + P * t) % Q == r % Q) List.nodup_range
  change xs.length = 1
  match xs with
  | [] => exact False.elim (by cases hmem)
  | [a] => rfl
  | a :: b :: as =>
    have ha : a = t0 := huniq a (by simp)
    have hb : b = t0 := huniq b (by simp)
    have hnd' := List.nodup_cons.mp hnd
    exact False.elim (hnd'.1 (by simp [ha, hb]))

theorem fibre_congruence_miss (P Q ρ r : Nat)
    (hP : 0 < P) (hQ : 0 < Q) (hcop : Nat.gcd P Q = 1) (hρ : ρ < P) :
    ((List.range Q).filter
        (fun t => (ρ + P * t) % Q != r % Q)).length = Q - 1 := by
  have hsum :=
    length_filter_add_not (fun t => (ρ + P * t) % Q == r % Q) (List.range Q)
  have hhit := fibre_congruence_count P Q ρ r hP hQ hcop hρ
  have hlen : (List.range Q).length = Q := List.length_range
  have hmiss :
      ((List.range Q).filter (fun t => !((ρ + P * t) % Q == r % Q))).length
        = Q - 1 := by omega
  have hpred :
      (List.range Q).filter (fun t => !((ρ + P * t) % Q == r % Q))
        = (List.range Q).filter (fun t => (ρ + P * t) % Q != r % Q) := by
    apply List.filter_congr
    intro t _ht
    rfl
  rwa [← hpred]

/-- Adding a coprime modulus multiplies the avoid count by `Q − 1`.
    This is the empty-graph Suen step (`Δ = 0`). -/
theorem avoid_coprime_extension (evs : List (Nat × Nat)) (P Q r : Nat)
    (hP : 0 < P) (hQ : 1 < Q) (hcop : Nat.gcd P Q = 1)
    (hdiv : ∀ e ∈ evs, e.1 ∣ P) :
    (uncovered (evs ++ [(Q, r)]) (P * Q)).length
      = (uncovered evs P).length * (Q - 1) := by
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQ
  have htwo := two_stage_count (evs ++ [(Q, r)]) P Q hP
  have hfib : ∀ ρ ∈ List.range P,
      fibreUncovered (evs ++ [(Q, r)]) P Q ρ
        = if avoids evs ρ then Q - 1 else 0 := by
    intro ρ hρR
    have hρ : ρ < P := List.mem_range.mp hρR
    have hper : ∀ t, avoids evs (ρ + P * t) = avoids evs ρ := by
      intro t
      have hmod : (ρ + P * t) % P = ρ := by
        rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt hρ]
      have h1 := avoids_mod_of_dvd evs P (ρ + P * t) hdiv
      have h2 := avoids_mod_of_dvd evs P ρ hdiv
      have hρP : ρ % P = ρ := Nat.mod_eq_of_lt hρ
      rw [h1, hmod, h2, hρP]
    have hQB : (Q == 0) = false := by
      simp [Nat.pos_iff_ne_zero.mp hQpos]
    unfold fibreUncovered
    have hpred : ∀ t,
        avoids (evs ++ [(Q, r)]) (ρ + P * t)
          = (avoids evs ρ && ((ρ + P * t) % Q != r % Q)) := by
      intro t
      have happ := avoids_append_singleton evs (Q, r) (ρ + P * t)
      rw [happ, avoids_cons, hper t]
      simp [hQB]
    if hp : avoids evs ρ then
      have : (List.range Q).filter
          (fun t => avoids (evs ++ [(Q, r)]) (ρ + P * t))
          = (List.range Q).filter
              (fun t => (ρ + P * t) % Q != r % Q) := by
        apply List.filter_congr
        intro t _ht
        simp [hpred t, hp]
      rw [this, fibre_congruence_miss P Q ρ r hP hQpos hcop hρ]
      simp [hp]
    else
      have : (List.range Q).filter
          (fun t => avoids (evs ++ [(Q, r)]) (ρ + P * t)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro t _ht hf
        simp [hpred t, hp] at hf
      simp [this, hp]
  have hmap :
      ((List.range P).map
          (fun ρ => fibreUncovered (evs ++ [(Q, r)]) P Q ρ)).sum
        = ((List.range P).map
            (fun ρ => if avoids evs ρ then Q - 1 else 0)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    exact hfib
  have hite := sum_ite_const P (Q - 1) (fun ρ => avoids evs ρ)
  unfold uncovered at htwo ⊢
  rw [htwo, hmap, hite]

/-- Independent n-event Suen: pairwise-coprime moduli leave
    `∏ (q_i − 1)` residues on the product period. Empty-graph case
    (`Δ = 0`). Coprime packing cannot carry two-log mass, so this
    does not inhabit `FibreSuenHypothesis`. -/
theorem independent_avoid_prod (evs : List (Nat × Nat))
    (hpos : ∀ e ∈ evs, 1 < e.1)
    (hpair : evs.Pairwise (fun e₁ e₂ => Nat.gcd e₁.1 e₂.1 = 1)) :
    (uncovered evs (evProd evs)).length = evMissProd evs := by
  induction evs with
  | nil =>
    simp [uncovered, evProd, evMissProd, avoids]
  | cons e evs ih =>
    have hpos' : ∀ x ∈ evs, 1 < x.1 :=
      fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hpair' := (List.pairwise_cons.mp hpair).2
    have ih' := ih hpos' hpair'
    have he : 1 < e.1 := hpos e List.mem_cons_self
    have hlist : ∀ x ∈ evs, Nat.gcd e.1 x.1 = 1 :=
      (List.pairwise_cons.mp hpair).1
    have hP : 0 < evProd evs :=
      evProd_pos evs (fun x hx => Nat.zero_lt_of_lt (hpos' x hx))
    have hcop : Nat.gcd (evProd evs) e.1 = 1 := by
      rw [Nat.gcd_comm]
      exact coprime_to_evProd e.1 evs hlist
    have hdiv : ∀ x ∈ evs, x.1 ∣ evProd evs :=
      fun x hx => evProd_dvd_of_mem evs x hx
    have hext :=
      avoid_coprime_extension evs (evProd evs) e.1 e.2 hP he hcop hdiv
    have hpred :
        uncovered (e :: evs) (evProd (e :: evs))
          = uncovered (evs ++ [e]) (evProd evs * e.1) := by
      unfold uncovered
      rw [evProd_cons, Nat.mul_comm]
      apply List.filter_congr
      intro n _hn
      exact (avoids_append_singleton evs e n).symm
    rw [hpred, hext, ih', evMissProd_cons, Nat.mul_comm]

theorem residualEvents_q_gt_one (T : Nat) (evs : List (Nat × Nat))
    (ρ : Nat) (e' : Nat × Nat)
    (hmem : e' ∈ residualEvents T evs ρ) : 1 < e'.1 := by
  rcases (mem_residualEvents T evs ρ e').mp hmem with ⟨e, _hmem, hcls, _heq⟩
  have hspec := (classify_eq_residual_iff T e.1 e.2 ρ e'.1).mp hcls
  rw [hspec.2.2.2]
  exact hspec.2.2.1

/-- Empty-graph H2 on a surviving fibre: residual events pairwise
    coprime and coprime to the hub ⇒ fibre count equals `evMissProd`.
    Exact Suen when `Δ_ρ = 0`. -/
theorem fibre_independent_count
    (T : Nat) (evs : List (Nat × Nat)) (H L ρ : Nat)
    (hsurv : hubSurvives T evs ρ = true)
    (heq : H = hubOf T (evs.map (·.1)))
    (hL : L = evProd (residualEvents T evs ρ))
    (hρ : ρ < H) (hH : 0 < H)
    (hpos : ∀ e ∈ evs, 0 < e.1)
    (hpair : (residualEvents T evs ρ).Pairwise
        (fun e₁ e₂ => Nat.gcd e₁.1 e₂.1 = 1))
    (hcop : Nat.gcd H L = 1) :
    fibreUncovered evs H L ρ
      = evMissProd (residualEvents T evs ρ) := by
  have hrespos : ∀ e ∈ residualEvents T evs ρ, 1 < e.1 :=
    fun e hx => residualEvents_q_gt_one T evs ρ e hx
  have hLpos : 0 < L := by
    rw [hL]
    exact evProd_pos _ (fun e hx => Nat.zero_lt_of_lt (hrespos e hx))
  have hdiv : ∀ e ∈ residualEvents T evs ρ, e.1 ∣ L := by
    intro e hx
    rw [hL]
    exact evProd_dvd_of_mem _ e hx
  have hprod :=
    independent_avoid_prod (residualEvents T evs ρ) hrespos hpair
  have hred : ∀ t,
      avoids evs (ρ + H * t)
        = avoids (residualEvents T evs ρ) (ρ + H * t) := by
    intro t
    have hmod : (ρ + H * t) % H = ρ := by
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod,
        Nat.mod_eq_of_lt hρ]
    exact avoids_eq_residual T evs H ρ (ρ + H * t) hsurv heq hmod hpos
  have hmodL : ∀ t,
      avoids (residualEvents T evs ρ) (ρ + H * t)
        = avoids (residualEvents T evs ρ) ((ρ + H * t) % L) :=
    fun t => avoids_mod_of_dvd _ L (ρ + H * t) hdiv
  let f := fun t : Nat => (ρ + H * t) % L
  let xs := (List.range L).filter (fun t => avoids evs (ρ + H * t))
  let ys := (List.range L).filter
      (fun n => avoids (residualEvents T evs ρ) n)
  let zs := xs.map f
  have hxs_pred : xs = (List.range L).filter
      (fun t => avoids (residualEvents T evs ρ) (f t)) := by
    apply List.filter_congr
    intro t _ht
    rw [hred t, hmodL t]
  have hzsys : zs ⊆ ys := by
    intro n hn
    rcases List.mem_map.mp hn with ⟨t, ht, heqf⟩
    have ht' : t ∈ (List.range L).filter
        (fun t => avoids (residualEvents T evs ρ) (f t)) := by
      rw [← hxs_pred]; exact ht
    have htF := List.mem_filter.mp ht'
    have hnL : n < L := by
      rw [← heqf]; exact Nat.mod_lt (ρ + H * t) hLpos
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hnL, ?_⟩
    have : avoids (residualEvents T evs ρ) (f t) = true := htF.2
    simpa [f, heqf] using this
  have hndzs : zs.Nodup := by
    have hndxs : xs.Nodup :=
      List.Pairwise.filter (fun t => avoids evs (ρ + H * t)) List.nodup_range
    refine nodup_map_of_inj hndxs ?_
    intro t₁ t₂ ht₁ ht₂ heq'
    have ht₁L : t₁ < L := List.mem_range.mp (List.mem_filter.mp ht₁).1
    have ht₂L : t₂ < L := List.mem_range.mp (List.mem_filter.mp ht₂).1
    exact fibre_congruence_unique H L ρ t₁ t₂ hLpos hcop ht₁L ht₂L heq'
  have hysub : ys ⊆ zs := by
    intro n hn
    have hnF := List.mem_filter.mp hn
    have hnL : n < L := List.mem_range.mp hnF.1
    rcases fibre_congruence_exists H L ρ n hH hLpos hcop hρ with
      ⟨t, ht, htf⟩
    have htn : f t = n := by
      simp [f, htf, Nat.mod_eq_of_lt hnL]
    have htxs : t ∈ xs := by
      refine List.mem_filter.mpr ⟨List.mem_range.mpr ht, ?_⟩
      have : avoids (residualEvents T evs ρ) (f t) = true := by
        simpa [htn] using hnF.2
      rw [hred t, hmodL t]
      exact this
    exact List.mem_map.mpr ⟨t, htxs, htn⟩
  have hlenzs : zs.length ≤ ys.length :=
    hndzs.length_le_of_subset hzsys
  have hndys : ys.Nodup :=
    List.Pairwise.filter (fun n => avoids (residualEvents T evs ρ) n)
      List.nodup_range
  have hlenys : ys.length ≤ zs.length :=
    hndys.length_le_of_subset hysub
  have hlen : xs.length = ys.length := by
    have : zs.length = xs.length := List.length_map (as := xs) f
    omega
  unfold fibreUncovered
  change xs.length = evMissProd (residualEvents T evs ρ)
  have hys : ys.length = evMissProd (residualEvents T evs ρ) := by
    unfold uncovered at hprod
    rw [← hL] at hprod
    exact hprod
  exact hlen.trans hys

/-! # Sequential Janson I counting

    Independent of the non-neighbor algebra, the hit rate on a set
    is exactly `1/q`. Union bound on neighbors then gives the
    integer form of Janson I:

      `hitAmong * M + Δ_nbr * M ≥ hitCount * |U|`

    i.e. `γ ≥ p − Δ_nbr / |U|`, not `γ ≥ p/(1+δ)`. Combined with
    the sequential split this is `janson_step`. Neither statement
    is `P ≤ exp(-∑ p/(1+δ))`, and neither inhabits
    `FibreSuenHypothesis`.
-/

def evLcm (evs : List (Nat × Nat)) : Nat :=
  evs.foldl (fun acc e => Nat.lcm acc e.1) 1

def hitAmong (e : Nat × Nat) (ns : List Nat) : Nat :=
  if e.1 = 0 then 0
  else (ns.filter (fun n => n % e.1 == e.2 % e.1)).length

def neighbors (e : Nat × Nat) (evs : List (Nat × Nat)) : List (Nat × Nat) :=
  evs.filter (fun e' => dependent e e')

def nonNeighbors (e : Nat × Nat) (evs : List (Nat × Nat)) : List (Nat × Nat) :=
  evs.filter (fun e' => !dependent e e')

def neighborDeltaHit (e : Nat × Nat) (evs : List (Nat × Nat)) (M : Nat) : Nat :=
  ((neighbors e evs).map (fun e' => pairHitCount e e' M)).sum

theorem foldl_lcm_factor (init : Nat) (xs : List (Nat × Nat)) :
    xs.foldl (fun acc e => Nat.lcm acc e.1) init
      = Nat.lcm init (xs.foldl (fun acc e => Nat.lcm acc e.1) 1) := by
  induction xs generalizing init with
  | nil => simp [Nat.lcm_one_right]
  | cons e xs ih =>
    rw [List.foldl_cons, ih, List.foldl_cons, ih (Nat.lcm 1 e.1),
      Nat.lcm_one_left]
    exact Nat.lcm_assoc init e.1 _

theorem evLcm_cons (e : Nat × Nat) (evs : List (Nat × Nat)) :
    evLcm (e :: evs) = Nat.lcm e.1 (evLcm evs) := by
  unfold evLcm
  rw [List.foldl_cons, foldl_lcm_factor, Nat.lcm_one_left]

theorem evLcm_of_mem (evs : List (Nat × Nat)) (e : Nat × Nat)
    (hmem : e ∈ evs) : e.1 ∣ evLcm evs := by
  induction evs with
  | nil => cases hmem
  | cons e' evs ih =>
    rw [evLcm_cons]
    cases List.mem_cons.mp hmem with
    | inl heq =>
      rw [heq]
      exact Nat.dvd_lcm_left _ _
    | inr h =>
      exact Nat.dvd_trans (ih h) (Nat.dvd_lcm_right e'.1 (evLcm evs))

theorem evLcm_dvd (evs : List (Nat × Nat)) (M : Nat)
    (h : ∀ e ∈ evs, e.1 ∣ M) : evLcm evs ∣ M := by
  induction evs with
  | nil =>
    simp [evLcm]
  | cons e evs ih =>
    rw [evLcm_cons]
    exact Nat.lcm_dvd (h e List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem coprime_gcd_lcm (q a b : Nat)
    (ha : Nat.gcd q a = 1) (hb : Nat.gcd q b = 1) :
    Nat.gcd q (Nat.lcm a b) = 1 := by
  have hdvd : Nat.lcm a b ∣ a * b :=
    ⟨Nat.gcd a b, (Nat.lcm_mul_gcd a b).symm⟩
  have hcop : Nat.Coprime q (a * b) :=
    (Nat.coprime_iff_gcd_eq_one.mpr ha).mul_right
      (Nat.coprime_iff_gcd_eq_one.mpr hb)
  exact hcop.coprime_dvd_right hdvd

theorem coprime_to_evLcm (q : Nat) (evs : List (Nat × Nat))
    (h : ∀ e ∈ evs, Nat.gcd q e.1 = 1) :
    Nat.gcd q (evLcm evs) = 1 := by
  induction evs with
  | nil => simp [evLcm]
  | cons e evs ih =>
    rw [evLcm_cons]
    exact coprime_gcd_lcm q e.1 (evLcm evs)
      (h e List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem not_bne_eq_beq (x y : Nat) : (!(x != y)) = (x == y) := by
  simp [bne, Bool.not_not]

theorem all_filter_and {α : Type _} (p q : α → Bool) (l : List α) :
    l.all q
      = ((l.filter p).all q && (l.filter (fun x => !p x)).all q) := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    by_cases hp : p a
    · simp [hp, List.all_cons, ih, Bool.and_assoc]
    · simp [hp, List.all_cons, ih, Bool.and_left_comm, Bool.and_assoc,
        Bool.and_comm]

theorem avoids_partition (e : Nat × Nat) (evs : List (Nat × Nat)) (n : Nat) :
    avoids evs n
      = (avoids (neighbors e evs) n && avoids (nonNeighbors e evs) n) := by
  unfold avoids neighbors nonNeighbors
  exact all_filter_and (fun e' => dependent e e')
    (fun e' => e'.1 == 0 || n % e'.1 != e'.2 % e'.1) evs

theorem filter_imp_length {α : Type _} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    have ht : ∀ x ∈ xs, p x = true → q x = true :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ih' := ih ht
    by_cases hp : p a
    · have hq : q a = true := h a List.mem_cons_self hp
      simp [hp, hq]
      exact ih'
    · by_cases hq : q a
      · simp [hp, hq]
        exact Nat.le_trans ih' (Nat.le_succ _)
      · simp [hp, hq]
        exact ih'

theorem length_filter_or_le {α : Type _} (p q : α → Bool) (l : List α) :
    (l.filter (fun x => p x || q x)).length
      ≤ (l.filter p).length + (l.filter q).length := by
  have h := length_filter_or_and p q l
  omega

theorem filter_or_cover {α : Type _} (p q r : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true ∨ r x = true) :
    (l.filter p).length ≤ (l.filter q).length + (l.filter r).length := by
  have himp : ∀ x ∈ l, p x = true → (q x || r x) = true := by
    intro x hx hp
    cases h x hx hp with
    | inl hq => simp [hq]
    | inr hr => simp [hr]
  exact Nat.le_trans (filter_imp_length p (fun x => q x || r x) l himp)
    (length_filter_or_le q r l)

theorem uncovered_cons_eq_append (e : Nat × Nat) (evs : List (Nat × Nat))
    (M : Nat) :
    uncovered (e :: evs) M = uncovered (evs ++ [e]) M := by
  unfold uncovered
  apply List.filter_congr
  intro n _hn
  exact (avoids_append_singleton evs e n).symm

theorem hitAmong_uncovered (e : Nat × Nat) (evs : List (Nat × Nat)) (M : Nat)
    (hq : 0 < e.1) :
    hitAmong e (uncovered evs M)
      = ((List.range M).filter
          (fun n => n % e.1 == e.2 % e.1 && avoids evs n)).length := by
  have hne : e.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  simp [hitAmong, uncovered, hne, List.filter_filter]

theorem uncovered_cons_split (e : Nat × Nat) (evs : List (Nat × Nat)) (M : Nat)
    (hq : 0 < e.1) :
    (uncovered (e :: evs) M).length + hitAmong e (uncovered evs M)
      = (uncovered evs M).length := by
  have hne : e.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  have hqB : (e.1 == 0) = false := by simp [hne]
  have hsplit :=
    filter_and_split (fun n => avoids evs n)
      (fun n => n % e.1 != e.2 % e.1) (List.range M)
  have hnew :
      uncovered (e :: evs) M
        = (List.range M).filter
            (fun n => avoids evs n && (n % e.1 != e.2 % e.1)) := by
    unfold uncovered
    apply List.filter_congr
    intro n _hn
    rw [avoids_cons]
    simp [hqB]
  have hhit := hitAmong_uncovered e evs M hq
  have hnot :
      ((List.range M).filter
          (fun n => avoids evs n && !(n % e.1 != e.2 % e.1))).length
        = ((List.range M).filter
            (fun n => avoids evs n && (n % e.1 == e.2 % e.1))).length := by
    apply congrArg List.length
    apply List.filter_congr
    intro n _hn
    simp [not_bne_eq_beq]
  have hcomm :
      ((List.range M).filter
          (fun n => avoids evs n && (n % e.1 == e.2 % e.1))).length
        = ((List.range M).filter
            (fun n => n % e.1 == e.2 % e.1 && avoids evs n)).length := by
    apply congrArg List.length
    apply List.filter_congr
    intro n _hn
    simp [Bool.and_comm]
  rw [hnew, hhit]
  unfold uncovered
  omega

theorem hitCount_of_dvd (e : Nat × Nat) (M : Nat)
    (hq : 0 < e.1) (hdvd : e.1 ∣ M) :
    hitCount e M = M / e.1 := by
  have hne : e.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  have hρ : e.2 % e.1 < e.1 := Nat.mod_lt e.2 hq
  rcases hdvd with ⟨k, hk⟩
  have hlen := fibre_length e.1 k (e.2 % e.1) hq hρ
  unfold hitCount
  simp [hne]
  rw [hk, Nat.mul_div_cancel_left k hq]
  simpa [fibre] using hlen

theorem mul_sub_pred_mul (x q K : Nat) (hq : 0 < q) :
    x * q * K - x * (q - 1) * K = x * K := by
  cases q with
  | zero => cases hq
  | succ a =>
    have ha : a + 1 - 1 = a := Nat.add_sub_cancel a 1
    rw [ha]
    have hdist : x * (a + 1) * K = x * a * K + x * K := by
      rw [Nat.mul_add x a 1, Nat.mul_one, Nat.add_mul]
    rw [hdist, Nat.add_sub_cancel_left]

theorem fibre_congruence_count_mul (P Q ρ r K : Nat)
    (hP : 0 < P) (hQ : 0 < Q) (hcop : Nat.gcd P Q = 1) (hρ : ρ < P) :
    ((List.range (Q * K)).filter
        (fun t => (ρ + P * t) % Q == r % Q)).length = K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hrange :
        List.range (Q * (K + 1))
          = List.range (Q * K) ++ (List.range Q).map (Q * K + ·) := by
      rw [Nat.mul_succ, List.range_add]
    rw [hrange, List.filter_append, List.length_append, ih]
    have hright :
        (((List.range Q).map (Q * K + ·)).filter
            (fun t => (ρ + P * t) % Q == r % Q)).length = 1 := by
      rw [List.filter_map, List.length_map]
      have hcongr :
          (List.range Q).filter
              ((fun t => (ρ + P * t) % Q == r % Q) ∘ fun u => Q * K + u)
            = (List.range Q).filter
                (fun u => (ρ + P * u) % Q == r % Q) := by
        apply List.filter_congr
        intro u _hu
        have hdecomp : ρ + P * (Q * K + u) = (ρ + P * u) + P * Q * K := by
          simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
        have hz : (P * Q * K) % Q = 0 := by
          have : P * Q * K = Q * (P * K) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          rw [this, Nat.mul_mod_right]
        have hmod : (ρ + P * (Q * K + u)) % Q = (ρ + P * u) % Q := by
          rw [hdecomp, Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]
        simp [hmod]
      rw [hcongr, fibre_congruence_count P Q ρ r hP hQ hcop hρ]
    omega

/-- If `gcd(q, evLcm evs) = 1` then `E` is independent of the
    non-neighbor algebra: the hit rate on `uncovered evs` is `1/q`. -/
theorem hit_among_independent (e : Nat × Nat) (evs : List (Nat × Nat))
    (M : Nat) (hq : 0 < e.1) (hM : 0 < M) (hdvd : e.1 ∣ M)
    (hdiv : ∀ e' ∈ evs, e'.1 ∣ M)
    (hcop : Nat.gcd e.1 (evLcm evs) = 1) :
    hitAmong e (uncovered evs M) * e.1 = (uncovered evs M).length := by
  if hq1 : e.1 = 1 then
    unfold hitAmong uncovered
    simp [hq1, Nat.mod_one]
  else
    have hqt : 1 < e.1 := Nat.lt_of_le_of_ne hq (Ne.symm hq1)
    have hLdiv : evLcm evs ∣ M := evLcm_dvd evs M hdiv
    have hLpos : 0 < evLcm evs :=
      Nat.pos_of_ne_zero (fun h0 => by
        rw [h0] at hLdiv
        have : M = 0 := Nat.eq_zero_of_zero_dvd hLdiv
        exact Nat.ne_of_gt hM this)
    have hLq : evLcm evs * e.1 ∣ M := by
      rw [Nat.mul_comm]
      exact (Nat.coprime_iff_gcd_eq_one.mpr hcop).mul_dvd_of_dvd_of_dvd
        hdvd hLdiv
    rcases hLq with ⟨K, hK⟩
    have hdivL : ∀ e' ∈ evs, e'.1 ∣ evLcm evs :=
      fun e' hx => evLcm_of_mem evs e' hx
    have hold :
        (uncovered evs M).length
          = (uncovered evs (evLcm evs)).length * e.1 * K := by
      have hper :=
        uncovered_periodic_mul evs (evLcm evs) (e.1 * K) hLpos hdivL
      have hMK : M = evLcm evs * (e.1 * K) := by
        rw [hK, Nat.mul_assoc]
      rw [← hMK] at hper
      rw [hper, Nat.mul_assoc]
    have hcop' : Nat.gcd (evLcm evs) e.1 = 1 := by
      rwa [Nat.gcd_comm]
    have hext :=
      avoid_coprime_extension evs (evLcm evs) e.1 e.2 hLpos hqt hcop' hdivL
    have hnewP :
        (uncovered (e :: evs) (evLcm evs * e.1)).length
          = (uncovered evs (evLcm evs)).length * (e.1 - 1) := by
      rw [uncovered_cons_eq_append, hext]
    have hdivN : ∀ e' ∈ e :: evs, e'.1 ∣ evLcm evs * e.1 := by
      intro e' hx
      cases List.mem_cons.mp hx with
      | inl heq =>
        rw [heq]
        exact ⟨evLcm evs, Nat.mul_comm _ _⟩
      | inr hmem =>
        exact Nat.dvd_trans (hdivL e' hmem) ⟨e.1, rfl⟩
    have hPpos : 0 < evLcm evs * e.1 := Nat.mul_pos hLpos hq
    have hnew :
        (uncovered (e :: evs) M).length
          = (uncovered evs (evLcm evs)).length * (e.1 - 1) * K := by
      have hper :=
        uncovered_periodic_mul (e :: evs) (evLcm evs * e.1) K hPpos hdivN
      have hMK : M = evLcm evs * e.1 * K := hK
      rw [← hMK] at hper
      rw [hper, hnewP]
    have hsplit := uncovered_cons_split e evs M hq
    have hsub :=
      mul_sub_pred_mul (uncovered evs (evLcm evs)).length e.1 K hq
    have hhit :
        hitAmong e (uncovered evs M)
          = (uncovered evs (evLcm evs)).length * K := by
      omega
    rw [hhit, hold]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem coprime_nonNeighbors (e : Nat × Nat) (evs : List (Nat × Nat))
    (hq : 0 < e.1) (_hpos : ∀ e' ∈ evs, 0 < e'.1) :
    ∀ e' ∈ nonNeighbors e evs, Nat.gcd e.1 e'.1 = 1 := by
  intro e' hx
  have hfil : (!dependent e e') = true := (List.mem_filter.mp hx).2
  have hnd : dependent e e' = false := by
    cases hdep : dependent e e'
    · rfl
    · simp [hdep] at hfil
  have hgpos : 0 < Nat.gcd e.1 e'.1 :=
    Nat.gcd_pos_of_pos_left e'.1 hq
  have hne0 : (Nat.gcd e.1 e'.1 != 0) = true := by
    simp [bne_iff_ne, Nat.pos_iff_ne_zero.mp hgpos]
  change ((Nat.gcd e.1 e'.1 != 0) && (Nat.gcd e.1 e'.1 != 1)) = false at hnd
  simp [hne0] at hnd
  exact hnd

theorem pairHitCount_eq (e e' : Nat × Nat) (M : Nat) (hq : 0 < e.1) :
    pairHitCount e e' M
      = if e'.1 = 0 then 0
        else ((List.range M).filter
          (fun n => n % e.1 == e.2 % e.1
            && n % e'.1 == e'.2 % e'.1)).length := by
  have hne : e.1 ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  unfold pairHitCount
  by_cases hz : e'.1 = 0
  · simp [hne, hz]
  · simp [hne, hz]

theorem hit_among_not_avoids_le (e : Nat × Nat) (evs : List (Nat × Nat))
    (M : Nat) (hq : 0 < e.1) :
    ((List.range M).filter
        (fun n => n % e.1 == e.2 % e.1 && !avoids evs n)).length
      ≤ ((evs.map (fun e' => pairHitCount e e' M)).sum) := by
  induction evs with
  | nil =>
    simp [avoids]
  | cons e' evs ih =>
    have hcover :
        ∀ n ∈ List.range M,
          (n % e.1 == e.2 % e.1 && !avoids (e' :: evs) n) = true →
            (n % e.1 == e.2 % e.1 && !avoids evs n) = true
              ∨ (n % e.1 == e.2 % e.1
                  && !(e'.1 == 0 || n % e'.1 != e'.2 % e'.1)) = true := by
      intro n _hn hp
      have hpair := Bool.and_eq_true_iff.mp hp
      have hav := avoids_cons e' evs n
      have hnot : (!avoids (e' :: evs) n) = true := hpair.2
      have hor : (!avoids evs n ||
          !(e'.1 == 0 || n % e'.1 != e'.2 % e'.1)) = true := by
        rw [hav] at hnot
        simpa [Bool.not_and] using hnot
      cases Bool.or_eq_true_iff.mp hor with
      | inl hL => exact Or.inl (Bool.and_eq_true_iff.mpr ⟨hpair.1, hL⟩)
      | inr hR => exact Or.inr (Bool.and_eq_true_iff.mpr ⟨hpair.1, hR⟩)
    have hle :=
      filter_or_cover
        (fun n => n % e.1 == e.2 % e.1 && !avoids (e' :: evs) n)
        (fun n => n % e.1 == e.2 % e.1 && !avoids evs n)
        (fun n => n % e.1 == e.2 % e.1
          && !(e'.1 == 0 || n % e'.1 != e'.2 % e'.1))
        (List.range M) hcover
    have hpair : ((List.range M).filter
          (fun n => n % e.1 == e.2 % e.1
            && !(e'.1 == 0 || n % e'.1 != e'.2 % e'.1))).length
        ≤ pairHitCount e e' M := by
      rw [pairHitCount_eq e e' M hq]
      by_cases hz : e'.1 = 0
      · have hqB : (e'.1 == 0) = true := by simp [hz]
        have :
            (List.range M).filter
                (fun n => n % e.1 == e.2 % e.1
                  && !(e'.1 == 0 || n % e'.1 != e'.2 % e'.1))
              = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro n _hn hf
          simp [hqB] at hf
        rw [this]
        simp [hz]
      · have hqB : (e'.1 == 0) = false := by simp [hz]
        have hpred :
            (List.range M).filter
                (fun n => n % e.1 == e.2 % e.1
                  && !(e'.1 == 0 || n % e'.1 != e'.2 % e'.1))
              = (List.range M).filter
                  (fun n => n % e.1 == e.2 % e.1
                    && n % e'.1 == e'.2 % e'.1) := by
          apply List.filter_congr
          intro n _hn
          simp only [hqB, Bool.false_or, not_bne_eq_beq]
        rw [hpred]
        simp [hz]
    simp [List.map_cons, List.sum_cons]
    omega

theorem neighborDeltaHit_eq (e : Nat × Nat) (evs : List (Nat × Nat))
    (M : Nat) :
    neighborDeltaHit e evs M
      = ((neighbors e evs).map (fun e' => pairHitCount e e' M)).sum :=
  rfl

/-- Janson I counting: the hit rate on the current uncovered set
    is at least `p − Δ_nbr / |U|`. Independent of Harris/FKG. -/
theorem janson_hit_lower (e : Nat × Nat) (evs : List (Nat × Nat)) (M : Nat)
    (hq : 0 < e.1) (hM : 0 < M) (hdvd : e.1 ∣ M)
    (hpos : ∀ e' ∈ evs, 0 < e'.1)
    (hdiv : ∀ e' ∈ evs, e'.1 ∣ M) :
    hitAmong e (uncovered evs M) * M + neighborDeltaHit e evs M * M
      ≥ hitCount e M * (uncovered evs M).length := by
  have hCdiv : ∀ e' ∈ nonNeighbors e evs, e'.1 ∣ M :=
    fun e' hx => hdiv e' (List.mem_filter.mp hx).1
  have hcop : Nat.gcd e.1 (evLcm (nonNeighbors e evs)) = 1 :=
    coprime_to_evLcm e.1 (nonNeighbors e evs)
      (coprime_nonNeighbors e evs hq hpos)
  have hind :=
    hit_among_independent e (nonNeighbors e evs) M hq hM hdvd hCdiv hcop
  have hUC := hitAmong_uncovered e (nonNeighbors e evs) M hq
  have hU := hitAmong_uncovered e evs M hq
  have hcover :
      ∀ n ∈ List.range M,
        (n % e.1 == e.2 % e.1 && avoids (nonNeighbors e evs) n) = true →
          (n % e.1 == e.2 % e.1 && avoids evs n) = true
            ∨ (n % e.1 == e.2 % e.1 && !avoids (neighbors e evs) n)
                = true := by
    intro n _hn hp
    have hpair := Bool.and_eq_true_iff.mp hp
    have hpart := avoids_partition e evs n
    have havC : avoids (nonNeighbors e evs) n = true := hpair.2
    by_cases havN : avoids (neighbors e evs) n
    · have hav : avoids evs n = true := by
        simp [hpart, havN, havC]
      exact Or.inl (Bool.and_eq_true_iff.mpr ⟨hpair.1, hav⟩)
    · have hnot : (!avoids (neighbors e evs) n) = true := by
        simp [havN]
      exact Or.inr (Bool.and_eq_true_iff.mpr ⟨hpair.1, hnot⟩)
  have hle :=
    filter_or_cover
      (fun n => n % e.1 == e.2 % e.1 && avoids (nonNeighbors e evs) n)
      (fun n => n % e.1 == e.2 % e.1 && avoids evs n)
      (fun n => n % e.1 == e.2 % e.1 && !avoids (neighbors e evs) n)
      (List.range M) hcover
  have hdle :=
    hit_among_not_avoids_le e (neighbors e evs) M hq
  have hΔ : neighborDeltaHit e evs M
      = ((neighbors e evs).map (fun e' => pairHitCount e e' M)).sum :=
    rfl
  have hUCle :
      hitAmong e (uncovered (nonNeighbors e evs) M)
        ≤ hitAmong e (uncovered evs M) + neighborDeltaHit e evs M := by
    rw [hUC, hU, hΔ]
    omega
  have hp := hitCount_of_dvd e M hq hdvd
  have hdivq : e.1 * (M / e.1) = M := Nat.mul_div_cancel' hdvd
  have hUCleM :
      hitAmong e (uncovered (nonNeighbors e evs) M) * M
        ≤ hitAmong e (uncovered evs M) * M
            + neighborDeltaHit e evs M * M := by
    have := Nat.mul_le_mul_right M hUCle
    rw [Nat.add_mul] at this
    exact this
  have hindM :
      hitAmong e (uncovered (nonNeighbors e evs) M) * M
        = (uncovered (nonNeighbors e evs) M).length * hitCount e M := by
    have hmulM :
        hitAmong e (uncovered (nonNeighbors e evs) M) * M
          = hitAmong e (uncovered (nonNeighbors e evs) M)
              * (e.1 * (M / e.1)) :=
      congrArg (fun x =>
        hitAmong e (uncovered (nonNeighbors e evs) M) * x) hdivq.symm
    have hassoc :
        hitAmong e (uncovered (nonNeighbors e evs) M) * (e.1 * (M / e.1))
          = (hitAmong e (uncovered (nonNeighbors e evs) M) * e.1)
              * (M / e.1) := by
      simp [Nat.mul_assoc]
    have hlen :
        (hitAmong e (uncovered (nonNeighbors e evs) M) * e.1) * (M / e.1)
          = (uncovered (nonNeighbors e evs) M).length * (M / e.1) := by
      rw [hind]
    have hpc :
        (uncovered (nonNeighbors e evs) M).length * (M / e.1)
          = (uncovered (nonNeighbors e evs) M).length * hitCount e M := by
      rw [hp]
    exact hmulM.trans (hassoc.trans (hlen.trans hpc))
  have hmono : ∀ n, avoids evs n = true →
      avoids (nonNeighbors e evs) n = true := by
    intro n hav
    have hpart := avoids_partition e evs n
    simp [hpart] at hav
    exact hav.2
  have hUle :
      (uncovered evs M).length
        ≤ (uncovered (nonNeighbors e evs) M).length := by
    unfold uncovered
    apply filter_imp_length
    intro n _hn hav
    exact hmono n hav
  have hpμ :
      hitCount e M * (uncovered evs M).length
        ≤ hitCount e M * (uncovered (nonNeighbors e evs) M).length :=
    Nat.mul_le_mul_left _ hUle
  calc
    hitCount e M * (uncovered evs M).length
      ≤ hitCount e M * (uncovered (nonNeighbors e evs) M).length := hpμ
    _ = (uncovered (nonNeighbors e evs) M).length * hitCount e M :=
      Nat.mul_comm _ _
    _ = hitAmong e (uncovered (nonNeighbors e evs) M) * M := hindM.symm
    _ ≤ hitAmong e (uncovered evs M) * M + neighborDeltaHit e evs M * M :=
      hUCleM

/-- Sequential Janson I step: adding `e` multiplies the uncovered
    count by at most `(M − p)/M`, plus a neighbor-error `Δ_nbr`. -/
theorem janson_step (e : Nat × Nat) (evs : List (Nat × Nat)) (M : Nat)
    (hq : 0 < e.1) (hM : 0 < M) (hdvd : e.1 ∣ M)
    (hpos : ∀ e' ∈ evs, 0 < e'.1)
    (hdiv : ∀ e' ∈ evs, e'.1 ∣ M) :
    (uncovered (e :: evs) M).length * M
        + (uncovered evs M).length * hitCount e M
      ≤ (uncovered evs M).length * M + neighborDeltaHit e evs M * M := by
  have hsplit := uncovered_cons_split e evs M hq
  have hlow := janson_hit_lower e evs M hq hM hdvd hpos hdiv
  have hmul :
      (uncovered (e :: evs) M).length * M
          + hitAmong e (uncovered evs M) * M
        = (uncovered evs M).length * M := by
    rw [← Nat.add_mul, hsplit]
  rw [Nat.mul_comm ((uncovered evs M).length) (hitCount e M)]
  calc
    (uncovered (e :: evs) M).length * M
        + hitCount e M * (uncovered evs M).length
      ≤ (uncovered (e :: evs) M).length * M
          + (hitAmong e (uncovered evs M) * M
              + neighborDeltaHit e evs M * M) :=
        Nat.add_le_add_left hlow _
    _ = ((uncovered (e :: evs) M).length * M
            + hitAmong e (uncovered evs M) * M)
          + neighborDeltaHit e evs M * M := by
        simp [Nat.add_assoc]
    _ = (uncovered evs M).length * M + neighborDeltaHit e evs M * M := by
        rw [hmul]

/-! # Open analytic hypotheses

    These are the remaining programme statements. They are *not*
    inhabited. `e_power_core_holds` does not imply them.
    `finite_product_density_of` is the replacement-target assembly:
    H1 and H2 imply the finite product-space density bound.
-/

/-- H1 on the dyadic schedule `A = 2^k`: hub-survival density
    `≤ 2^{-γ k²}`. Not inhabited. -/
def HubExponentialHypothesis : Prop :=
  ∃ γ : Nat, 0 < γ ∧
    ∀ k T, 0 < k →
      ((List.range (hubOf T ((events (2 ^ k)).map (·.1)))).filter
          (fun ρ => hubSurvives T (events (2 ^ k)) ρ)).length
          * 2 ^ (γ * k * k)
        ≤ max (hubOf T ((events (2 ^ k)).map (·.1))) 1

/-- H2: every surviving fibre has uncovered density `≤ 2^{-γ k²}`.
    Residual reduction, empty-graph Suen, dependent pair mass
    (`pair_hit_compatible`), the Janson mass ratio (`janson_mass_two`),
    and sequential Janson I counting (`janson_hit_lower`, `janson_step`)
    are proved. The exponential `P ≤ 2^{-γ k²}` is not. Not inhabited. -/
def FibreSuenHypothesis : Prop :=
  ∃ γ : Nat, 0 < γ ∧
    ∀ k T ρ, 0 < k →
      hubSurvives T (events (2 ^ k)) ρ = true →
        fibreUncovered (events (2 ^ k))
            (hubOf T ((events (2 ^ k)).map (·.1)))
            (residualModulus T (events (2 ^ k))) ρ
          * 2 ^ (γ * k * k)
        ≤ max (residualModulus T (events (2 ^ k))) 1

/-- Integer form of `u(A) ≤ 2^{-γ (log₂ A)²}` on the product space
    `ℤ/H × ℤ/L`. This is the replacement target. Not inhabited. -/
def FiniteProductDensityBound : Prop :=
  ∃ γ : Nat, 0 < γ ∧
    ∀ k T, 0 < k →
      (uncovered (events (2 ^ k))
          (hubOf T ((events (2 ^ k)).map (·.1))
            * residualModulus T (events (2 ^ k)))).length
          * 2 ^ (γ * k * k)
        ≤ max (hubOf T ((events (2 ^ k)).map (·.1))) 1
            * max (residualModulus T (events (2 ^ k))) 1

/-- Deduplicated harmonic mass `∑ 1/q`. The old event-count form
    `κ k² ≤ |events|` is vacuous (`|events| ∼ A²`). The `c=d=1`
    slice is one-log (`slice_q_nodup`). Not inhabited. -/
def eventMass (evs : List (Nat × Nat)) : Rat :=
  (evs.map (fun e => invNat e.1)).sum

def DedupTwoLogMass : Prop :=
  ∃ (κ k0 : Nat), 1 < κ ∧
    ∀ k, k0 ≤ k →
      ((k * k : Nat) : Rat) / (κ : Nat) ≤ eventMass (events (2 ^ k))

/-- Transfer at residual moduli: some period `M` of the uncovered set
    satisfies `M ≤ x / 2^{δ k}` on the schedule `A = 2^k`. -/
def PeriodSmallEnough : Prop :=
  ∃ δ : Nat, 0 < δ ∧
    ∀ k x, 0 < x →
      ∃ M, 0 < M ∧ M * 2 ^ (δ * k) ≤ x

/-- H1 and H2 imply the finite product-space density bound. Transfer
    is not used. This is the replacement-target combination. -/
theorem finite_product_density_of
    (hHub : HubExponentialHypothesis)
    (hFibre : FibreSuenHypothesis) :
    FiniteProductDensityBound := by
  rcases hHub with ⟨γH, hγH, hH1⟩
  rcases hFibre with ⟨γL, hγL, hH2⟩
  refine ⟨γH + γL, Nat.add_pos_left hγH γL, ?_⟩
  intro k T hk
  if h0 : hubOf T ((events (2 ^ k)).map (·.1)) = 0
      ∨ residualModulus T (events (2 ^ k)) = 0 then
    have hHL :
        hubOf T ((events (2 ^ k)).map (·.1))
          * residualModulus T (events (2 ^ k)) = 0 := by
      cases h0 with
      | inl hH => simp [hH]
      | inr hL => simp [hL]
    simp [uncovered, hHL]
  else
    have hHpos : 0 < hubOf T ((events (2 ^ k)).map (·.1)) := by omega
    have hLpos : 0 < residualModulus T (events (2 ^ k)) := by omega
    have hmaxH :
        max (hubOf T ((events (2 ^ k)).map (·.1))) 1
          = hubOf T ((events (2 ^ k)).map (·.1)) :=
      Nat.max_eq_left (Nat.succ_le_of_lt hHpos)
    have hmaxL :
        max (residualModulus T (events (2 ^ k))) 1
          = residualModulus T (events (2 ^ k)) :=
      Nat.max_eq_left (Nat.succ_le_of_lt hLpos)
    have hpos : ∀ e ∈ events (2 ^ k), 0 < e.1 := events_q_pos (2 ^ k)
    have hid :=
      two_stage_survivors T (events (2 ^ k))
        (hubOf T ((events (2 ^ k)).map (·.1)))
        (residualModulus T (events (2 ^ k))) hHpos rfl hpos
    have h1 := hH1 k T hk
    have h2 :
        ∀ x ∈ ((List.range (hubOf T ((events (2 ^ k)).map (·.1)))).filter
            (fun ρ => hubSurvives T (events (2 ^ k)) ρ)).map
            (fun ρ =>
              fibreUncovered (events (2 ^ k))
                (hubOf T ((events (2 ^ k)).map (·.1)))
                (residualModulus T (events (2 ^ k))) ρ),
          x * 2 ^ (γL * k * k)
            ≤ residualModulus T (events (2 ^ k)) := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨ρ, hρ, hxe⟩
      have hsurv : hubSurvives T (events (2 ^ k)) ρ = true :=
        (List.mem_filter.mp hρ).2
      have := hH2 k T ρ hk hsurv
      rw [hmaxL] at this
      exact hxe ▸ this
    have hcomb :=
      finite_density_combine
        (uncovered (events (2 ^ k))
          (hubOf T ((events (2 ^ k)).map (·.1))
            * residualModulus T (events (2 ^ k)))).length
        (hubOf T ((events (2 ^ k)).map (·.1)))
        (residualModulus T (events (2 ^ k)))
        ((List.range (hubOf T ((events (2 ^ k)).map (·.1)))).filter
          (fun ρ => hubSurvives T (events (2 ^ k)) ρ)).length
        γH γL k
        (((List.range (hubOf T ((events (2 ^ k)).map (·.1)))).filter
            (fun ρ => hubSurvives T (events (2 ^ k)) ρ)).map
          (fun ρ =>
            fibreUncovered (events (2 ^ k))
              (hubOf T ((events (2 ^ k)).map (·.1)))
              (residualModulus T (events (2 ^ k))) ρ))
        hid (by simp) (by rwa [hmaxH] at h1) h2
    rwa [hmaxH, hmaxL]

def ExceptionalCountBound : Prop :=
  HubExponentialHypothesis ∧ FibreSuenHypothesis ∧ DedupTwoLogMass
    ∧ PeriodSmallEnough ∧ FiniteProductDensityBound

/-- Finite density needs only H1 and H2; transfer is separate.
    The combinatorial core does not discharge the hypotheses. -/
theorem exceptional_count_of
    (hHub : HubExponentialHypothesis)
    (hFibre : FibreSuenHypothesis)
    (hMass : DedupTwoLogMass)
    (hPer : PeriodSmallEnough) :
    ExceptionalCountBound :=
  ⟨hHub, hFibre, hMass, hPer, finite_product_density_of hHub hFibre⟩

/-! # Assembly of the kernel-checked core

    `ExceptionalPowerSaving` is the combinatorial core below, not
    \(S_A\ll x^{1-\delta}\) and not \(u(A)\le 2^{-\gamma k^2}\).
    H1/H2, two-log mass, and residual-modulus transfer remain open.
    The replacement target is `FiniteProductDensityBound`, assembled
    from H1 and H2 by `finite_product_density_of`.
-/

def ExceptionalPowerSaving : Prop :=
  MassGrowth ∧ FiniteSuen ∧ HubExponentialBound ∧ FibreExponentialBound
    ∧ DensityCountTransfer

theorem e_power_of
    (hMass : MassGrowth)
    (hSuen : FiniteSuen)
    (hHub : HubExponentialBound)
    (hFibre : FibreExponentialBound)
    (hTransfer : DensityCountTransfer) :
    ExceptionalPowerSaving :=
  ⟨hMass, hSuen, hHub, hFibre, hTransfer⟩

theorem e_power_core_holds : ExceptionalPowerSaving :=
  e_power_of massGrowth_holds finiteSuen_holds
    hubFibre_assembly fibreBound_assembly densityCountTransfer_holds

end ES.EPower
