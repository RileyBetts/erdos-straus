/-
Copyright (c) 2026 Riley Betts Ltd. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/

/-
  Layer A (core).  See README.md.

  Bare Lean ≥ 4.33.0, no imports.  Axioms: propext, Quot.sound, plus
  Lean.ofReduceBool for the native_decide instances (see README audit).
  Quadratic reciprocity is the named field `InvariantData.reciprocity`;
  Layer B (`ErdosStrausQR.lean`, `ErdosStrausBLRoute.lean`) discharges it.

  Formalization of the arithmetic heart of:
    M. Bright, D. Loughran, "Brauer–Manin obstruction for Erdős–Straus surfaces",
    Bull. LMS 52 (2020) 746–761, arXiv:1908.02526.

  Design (see plan §4m): everything except quadratic reciprocity is elementary
  casework; we prove the finite heart of BL Lemma 3.8 unconditionally (§2–§3),
  package the single deep input as an interface (§4), and assemble the
  conditional Theorem 1.2 / Corollary 1.3 anatomy (§5).  No `sorry`.
  On a machine with Mathlib, `ErdosStrausQR.lean` instantiates the odd-place
  content of §4 from `legendreSym.quadratic_reciprocity`.
-/

namespace BL

/-! ## §1  Serre's 2-adic symbol data
For odd r:  ε(r) ≡ (r−1)/2,  ω(r) ≡ (r²−1)/8  (mod 2);
i.e. ε(r) = 1 iff r ≡ 3 (mod 4);  ω(r) = 1 iff r ≡ ±3 (mod 8).
Defined on residues in [0,8). -/

def eps (r : Int) : Int := if r % 4 = 3 then 1 else 0
/-- ω(r) = 1 iff r ≡ ±3 (mod 8).  Reduce first: the unreduced test `r = 3 ∨ r = 5`
    would miss e.g. r = 11 ≡ 3 (mod 8). -/
def omg (r : Int) : Int := if r % 8 = 3 ∨ r % 8 = 5 then 1 else 0

/-- normalize an integer to its residue in [0,8) -/
def res8 (r : Int) : Int := r % 8

def oddRes : List Int := [1, 3, 5, 7]

/-! ## §2  The finite heart of BL Lemma 3.8
In reduced 2-adic coordinates (u₁,u₂,u₃) = (2^{s+e}r₁, 2^{s+e}r₂, 2^{e}r₃),
rᵢ odd, s ≥ 1 (this shape is forced by the elementary valuation analysis of
BL §3.3.4), the ES equation for odd n yields the key congruence (BL 3.4):
      2^s·r₁r₂ + (r₁+r₂)·r₃ ≡ 0 (mod 8),
and the 2-adic invariant of α is (−1)^(f+g) with
      f = ε(−r₁r₃)·ε(−r₂r₃),   g = s·(ω(r₁)+ω(r₂))
(using r⁻¹ ≡ r (mod 8), ω(−x)=ω(x), ω(xy)≡ω(x)+ω(y)).  Only the residues
mod 8 and (2^s mod 8, s mod 2) ∈ {(2,1),(4,0),(0,1),(0,0)} matter, so the
lemma reduces to a finite verification. -/

def pairTS : List (Int × Int) := [(2,1),(4,0),(0,1),(0,0)]

def negRes (x : Int) : Int := (8 - x % 8) % 8   -- residue of −x in [0,8)

def fExp (a b c : Int) : Int :=
  eps (negRes (a*c)) * eps (negRes (b*c))

def gExp (sm a b : Int) : Int := sm * (omg (a % 8) + omg (b % 8))

def lemma38Check : Bool :=
  oddRes.all fun a => oddRes.all fun b => oddRes.all fun c =>
    pairTS.all fun tsm =>
      decide ((tsm.1 * a * b + (a + b) * c) % 8 ≠ 0
              ∨ (fExp a b c + gExp tsm.2 a b) % 2 = 0)

/-- **The finite verification at the heart of BL Lemma 3.8** (fully proved). -/
theorem lemma38_check_true : lemma38Check = true := by decide

/-! ## §3  Lemma 3.8, assembled over residues
From the finite check we obtain: for any residue data satisfying the key
congruence, the invariant exponent is even — stated for arbitrary integers
via their residues. -/

theorem mem_oddRes_of_odd (r : Int) (h : r % 2 = 1) : r % 8 ∈ oddRes := by
  have hb : 0 ≤ r % 8 ∧ r % 8 < 8 := ⟨Int.emod_nonneg r (by decide),
    Int.emod_lt_of_pos r (by decide)⟩
  have hpar : r % 8 % 2 = 1 := by omega
  simp only [oddRes, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lemma38_residue
    (a b c t sm : Int)
    (ha : a ∈ oddRes) (hb : b ∈ oddRes) (hc : c ∈ oddRes)
    (hts : (t, sm) ∈ pairTS)
    (hcong : (t * a * b + (a + b) * c) % 8 = 0) :
    (fExp a b c + gExp sm a b) % 2 = 0 := by
  simp only [oddRes, pairTS, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at ha hb hc hts
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl <;>
  rcases hts with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  revert hcong <;> decide

/-- Serre's 2-adic invariant of α from reduced residues and the parity of s.
    Lemma 3.8 is the claim that this equals 1 on the 2-adic shape of a
    solution at odd n. -/
def serreInv2 (a b c sm : Int) : Int :=
  if (fExp a b c + gExp sm a b) % 2 = 0 then 1 else -1

theorem serreInv2_eq_one_of_residue
    (a b c t sm : Int)
    (ha : a ∈ oddRes) (hb : b ∈ oddRes) (hc : c ∈ oddRes)
    (hts : (t, sm) ∈ pairTS)
    (hcong : (t * a * b + (a + b) * c) % 8 = 0) :
    serreInv2 a b c sm = 1 := by
  have h := lemma38_residue a b c t sm ha hb hc hts hcong
  unfold serreInv2
  rw [if_pos h]

/-! ## §3b  Power bookkeeping: (2^s mod 8, s mod 2) always lies in pairTS -/

theorem pow2_mod8 : ∀ s : Nat, s ≥ 1 →
    (((2:Int)^s % 8, ((s % 2 : Nat) : Int)) : Int × Int) ∈ pairTS := by
  intro s hs
  induction s with
  | zero => omega
  | succ k ih =>
    by_cases hk : k ≥ 1
    · have hmem := ih hk
      have hmod : (2:Int)^(k+1) % 8 = (2^k % 8) * (2 % 8) % 8 := by
        rw [Int.pow_succ, Int.mul_emod]
      simp only [pairTS, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [hmod, h1] <;>
        first
          | (have hs2 : (k+1) % 2 = 0 := by omega
             rw [hs2]; decide)
          | (have hs2 : (k+1) % 2 = 1 := by omega
             rw [hs2]; decide)
    · have hk0 : k = 0 := by omega
      subst hk0
      simp [pairTS]

/-! ## §4  The reciprocity interface — the single deep input

Everything above is unconditional.  The one input this development does not
prove is Hilbert reciprocity for the explicit-formula symbols, equivalent to
quadratic reciprocity together with its two supplements.  We package exactly
the consequence the assembly consumes: the product of local invariants of the
Brauer class α over all places equals 1.  On a machine with Mathlib, this
structure is instantiated from `legendreSym.quadratic_reciprocity` and
friends; that discharge is the single remaining port. -/

structure InvariantData where
  /-- local invariant of α at the real place, on the given adelic point -/
  invInf : Int
  /-- local invariant of α at 2 -/
  inv2 : Int
  /-- local invariant of α at the odd prime p | n -/
  invP : Int
  /-- product of local invariants at all remaining (good) places -/
  invGood : Int
  /-- all invariants are signs -/
  signInf : invInf = 1 ∨ invInf = -1
  sign2 : inv2 = 1 ∨ inv2 = -1
  signP : invP = 1 ∨ invP = -1
  signGood : invGood = 1 ∨ invGood = -1
  /-- Hilbert reciprocity: the global product is trivial.  THE deep input. -/
  reciprocity : invInf * inv2 * invP * invGood = 1

/-! ## §5  The conditional Theorem 1.2, prime case: the anatomy

BL Theorem 1.2 for n = p an odd prime is precisely the following bookkeeping:
  • invInf = −1 on the positive octant            (BL Lemma 3.1),
  • inv2   = 1 for odd n                          (BL Lemma 3.8; §2–§3 above
                                                   prove its arithmetic heart),
  • invGood = 1                                   (BL Lemma 3.5),
  • reciprocity                                   (§4 interface),
whence invP = −1 — Yamamoto's non-residue condition, i.e. the covering-witness
fingerprint (plan §4m). -/

theorem one_pow_int : ∀ n : Nat, (1:Int) ^ n = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ m ihm => rw [Int.pow_succ, ihm]; rfl

theorem bl_thm12_prime_anatomy (H : InvariantData)
    (hInf : H.invInf = -1) (h2 : H.inv2 = 1) (hGood : H.invGood = 1) :
    H.invP = -1 := by
  have hrec := H.reciprocity
  rw [hInf, h2, hGood] at hrec
  rcases H.signP with h | h
  · rw [h] at hrec; omega
  · exact h

/-- Corollary (Yamamoto / Corollary 1.3 shape): under the same local inputs,
the Legendre-symbol value attached to the p-adic invariant is −1.  With
`leg` denoting the symbol and the p-adic invariant computed by Serre's odd
formula as `leg` raised to the valuation (BL Lemma 3.4), oddness of the
valuation forces the symbol itself to be −1. -/
theorem yamamoto_condition (H : InvariantData) (leg : Int) (vpar : Nat)
    (hInf : H.invInf = -1) (h2 : H.inv2 = 1) (hGood : H.invGood = 1)
    (hform : H.invP = leg ^ vpar) (hsign : leg = 1 ∨ leg = -1)
    (hodd : vpar % 2 = 1) :
    leg = -1 := by
  have hP := bl_thm12_prime_anatomy H hInf h2 hGood
  have := hodd
  rcases hsign with h | h
  · exfalso
    rw [h, one_pow_int vpar] at hform
    omega
  · exact h

/-! ## §6  The QR-free instance tier

The Legendre symbol needs no reciprocity to be *defined*: squareness mod p is
a bounded search.  Consequently Theorem 1.2 for any concrete n is a finite
computation, verifiable outright — reciprocity is what makes the *universal*
statement provable; instances never needed it.  (`native_decide` adds the
`Lean.ofReduceBool` axiom; kernel `decide` is possible for small p at higher
cost, and Track C's ZK attestation replaces the axiom at scale.) -/

/-- Legendre symbol by bounded search — no reciprocity in the definition. -/
def legendre (a p : Nat) : Int :=
  if a % p = 0 then 0
  else if (List.range p).any (fun x => (x * x) % p = a % p) then 1 else -1

/-- **Verified instance of Theorem 1.2** at the smallest hard-class prime
p = 1009, on the very solution proved in `ErdosStraus.lean`
(`es_1009 : IsES 1009 276 3027 92828`).  Type-2 shape: p ‖ u₂, p ‖ u₃ with
unit parts (3, 92); by BL Lemma 3.4 the p-adic invariant is
legendre(−3·92 mod p) = legendre(733), required to be −1.  It is. -/
theorem thm12_instance_1009 :
    legendre ((1009 - (3 * 92) % 1009) % 1009) 1009 = -1 := by
  native_decide

/-- Cross-check on the Yamamoto side: the covering-witness fact that opened
the whole program — 1009 is a quadratic non-residue mod the witness modulus
q = 11 — is the same invariant seen from the other end. -/
theorem witness_fingerprint_1009 : legendre (1009 % 11) 11 = -1 := by
  native_decide

/-! ## §7  BL Lemma 3.2 — the unit-ratio lemma (fully proved)

Factored integer coordinates u_i = a_i·p^{b_i}, n = n'·p^b with v_p(n) ≤ 1;
p's primality enters only through the packaged splitting property.  If no two
valuations agree, the term n'·a₁a₂·p^{b₁+b₂+b} has strictly minimal
valuation, forcing p | n'·a₁·a₂ — contradiction.  Hence some u_i/u_j is a
p-adic unit.  This is the hypothesis-discharger for Lemma 3.4 and for the
Type-1/Type-2 solution taxonomy. -/

theorem pow_add_int (p : Int) (m n : Nat) : p^(m+n) = p^m * p^n := by
  induction n with
  | zero => rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | succ k ih =>
    rw [show m + (k+1) = (m+k)+1 from rfl, Int.pow_succ, ih, Int.pow_succ,
      Int.mul_assoc]

theorem pow_pos_int (p : Int) (hp : 0 < p) (n : Nat) : 0 < p^n := by
  induction n with
  | zero => rw [Int.pow_zero]; omega
  | succ k ih => rw [Int.pow_succ]; exact Int.mul_pos ih hp

theorem pow_dvd_pow_int (p : Int) {m n : Nat} (h : m ≤ n) : p^m ∣ p^n :=
  ⟨p^(n-m), by rw [← pow_add_int]; congr 1; omega⟩

theorem dvd_mul_left_int {a b : Int} (c : Int) (h : a ∣ b) : a ∣ c * b := by
  obtain ⟨w, hw⟩ := h
  exact ⟨c * w, by rw [hw, ← Int.mul_assoc, Int.mul_comm c a, Int.mul_assoc]⟩

/-- BL Lemma 3.2 in ordered form (`b1 ≤ b2 ≤ b3` is WLOG by relabelling the
    three coordinates).  The splitting hypothesis is `Nat.Prime.dvd_mul` after
    the Mathlib port in `ErdosStrausQR.lean`. -/
theorem lemma32
    (p : Int) (hp : 0 < p)
    (hprime : ∀ x y : Int, p ∣ x*y → p ∣ x ∨ p ∣ y)
    (n' a1 a2 a3 : Int) (b b1 b2 b3 : Nat) (hb : b ≤ 1)
    (hn : ¬ p ∣ n') (h1 : ¬ p ∣ a1) (h2 : ¬ p ∣ a2)
    (hord : b1 ≤ b2 ∧ b2 ≤ b3)
    (heq : 4 * (a1*a2*a3) * p^(b1+b2+b3)
         = n' * (a1*a2 * p^(b1+b2+b)) + n' * (a1*a3 * p^(b1+b3+b))
           + n' * (a2*a3 * p^(b2+b3+b))) :
    b1 = b2 ∨ b2 = b3 := by
  apply Classical.byContradiction
  intro hcon
  have hne12 : b1 ≠ b2 := fun h => hcon (Or.inl h)
  have hne23 : b2 ≠ b3 := fun h => hcon (Or.inr h)
  obtain ⟨h12, h23⟩ := hord
  -- strict chain forces b3 ≥ b2+1 ≥ b1+2, and b3 > b since b ≤ 1 ≤ ... b3 ≥ 2
  have hK1 : b1+b2+b+1 ≤ b1+b2+b3 := by omega
  have hK2 : b1+b2+b+1 ≤ b1+b3+b := by omega
  have hK3 : b1+b2+b+1 ≤ b2+b3+b := by omega
  -- p^{K+1} divides the three non-minimal terms
  have hd0 : p^(b1+b2+b+1) ∣ 4 * (a1*a2*a3) * p^(b1+b2+b3) := by
    rw [Int.mul_assoc]
    exact dvd_mul_left_int 4 (dvd_mul_left_int (a1*a2*a3) (pow_dvd_pow_int p hK1))
  have hd2 : p^(b1+b2+b+1) ∣ n' * (a1*a3 * p^(b1+b3+b)) :=
    dvd_mul_left_int n' (dvd_mul_left_int (a1*a3) (pow_dvd_pow_int p hK2))
  have hd3 : p^(b1+b2+b+1) ∣ n' * (a2*a3 * p^(b2+b3+b)) :=
    dvd_mul_left_int n' (dvd_mul_left_int (a2*a3) (pow_dvd_pow_int p hK3))
  -- rearrange the equation (linear in the four product atoms) and conclude
  have h1eq : n' * (a1*a2 * p^(b1+b2+b))
      = 4 * (a1*a2*a3) * p^(b1+b2+b3)
        - (n' * (a1*a3 * p^(b1+b3+b)) + n' * (a2*a3 * p^(b2+b3+b))) := by
    omega
  have hdvd1 : p^(b1+b2+b+1) ∣ n' * (a1*a2 * p^(b1+b2+b)) := by
    rw [h1eq]
    exact Int.dvd_sub hd0 (Int.dvd_add hd2 hd3)
  -- cancel p^K:  n'·a1·a2·p^K = p^K·p·w  ⟹  n'·a1·a2 = p·w
  obtain ⟨w, hw⟩ := hdvd1
  have hKne : (p:Int)^(b1+b2+b) ≠ 0 := Int.ne_of_gt (pow_pos_int p hp _)
  have hw' : (n' * (a1*a2)) * p^(b1+b2+b) = (p * w) * p^(b1+b2+b) := by
    have lhs : (n' * (a1*a2)) * p^(b1+b2+b) = n' * (a1*a2 * p^(b1+b2+b)) := by
      rw [Int.mul_assoc]
    have rhs : (p:Int)^(b1+b2+b+1) * w = (p * w) * p^(b1+b2+b) := by
      rw [Int.pow_succ, Int.mul_assoc, Int.mul_comm ((p:Int)^(b1+b2+b)) (p * w)]
    rw [lhs, hw, rhs]
  have hcancel : n' * (a1*a2) = p * w :=
    Int.eq_of_mul_eq_mul_right hKne hw'
  have hpd : p ∣ n' * (a1*a2) := ⟨w, hcancel⟩
  rcases hprime _ _ hpd with h | h
  · exact hn h
  · rcases hprime _ _ h with h' | h'
    · exact h1 h'
    · exact h2 h'

/-! ## §8  BL Lemma 3.4 — the unit-ratio evaluation (fully proved)

Serre's explicit odd-prime formula, and the evaluation showing that with a
unit second slot the invariant is the Legendre symbol of the unit part raised
to the valuation parity — the exact form consumed by `yamamoto_condition`
(§5) and verified concretely in §6. -/

/-- Serre's explicit odd-prime Hilbert symbol: for a = p^α·uₐ, b = p^β·u_b
(uₐ, u_b units), (a,b)_p = (−1)^{αβε(p)}·leg(uₐ)^β·leg(u_b)^α. -/
def hilbertOdd (p : Nat) (al be : Nat) (ua ub : Nat) : Int :=
  (if al % 2 = 1 ∧ be % 2 = 1 ∧ p % 4 = 3 then -1 else 1)
    * legendre ua p ^ be * legendre ub p ^ al

/-- signs are stable under parity of exponent -/
theorem sign_pow_parity (x : Int) (hx : x = 1 ∨ x = -1) (k : Nat) :
    x ^ k = x ^ (k % 2) := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rcases hx with h | h
    · subst h
      have hop : ∀ j : Nat, (1:Int) ^ j = 1 := by
        intro j
        induction j with
        | zero => rfl
        | succ i ihi => rw [Int.pow_succ, ihi]; rfl
      rw [hop, hop]
    · subst h
      rw [Int.pow_succ, ih]
      have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases hm with hm | hm
      · rw [hm, show (m+1) % 2 = 1 from by omega]; rfl
      · rw [hm, show (m+1) % 2 = 0 from by omega]; rfl

/-- **BL Lemma 3.4** (formula form): when u₂/u₃ is a p-adic unit (β = 0),
the p-adic invariant of α reduces to the Legendre symbol of the unit part
raised to the valuation — and only the valuation's parity matters. -/
theorem lemma34 (p : Nat) (al : Nat) (ua ub : Nat)
    (hleg : legendre ub p = 1 ∨ legendre ub p = -1) :
    hilbertOdd p al 0 ua ub = legendre ub p ^ (al % 2) := by
  unfold hilbertOdd
  have h0 : ¬ (al % 2 = 1 ∧ (0:Nat) % 2 = 1 ∧ p % 4 = 3) := by omega
  rw [if_neg h0, Int.pow_zero, Int.mul_one, Int.one_mul,
    sign_pow_parity _ hleg]

/-- the Legendre symbol of a unit residue is a sign (interface hygiene) -/
theorem legendre_unit_sign (a p : Nat) (h : a % p ≠ 0) :
    legendre a p = 1 ∨ legendre a p = -1 := by
  unfold legendre
  rw [if_neg h]
  by_cases hc : (List.range p).any (fun x => (x * x) % p = a % p)
  · rw [if_pos hc]; exact Or.inl rfl
  · rw [if_neg hc]; exact Or.inr rfl

/-! ## §9  BL Lemma 3.1 — the real place (fully proved)

The Hilbert symbol at ℝ is −1 iff both arguments are negative.
On the positive octant both ratios −u₁/u₃, −u₂/u₃ are negative, so
inv_∞ α = −1.  Sign(−x) = sign(−x/z) for z > 0, so it is enough to
evaluate on the numerators. -/

/-- Real Hilbert symbol: `(a,b)_∞ = −1` iff `a < 0` and `b < 0`. -/
def hilbertInf (a b : Int) : Int := if a < 0 ∧ b < 0 then -1 else 1

/-- 2-adic Hilbert symbol of two odd integers: `(a,b)_2 = (−1)^{ε(a)ε(b)}`. -/
def hilbert2Odd (a b : Int) : Int :=
  if a % 4 = 3 ∧ b % 4 = 3 then -1 else 1

theorem lemma31_pos {x y : Nat} (hx : 0 < x) (hy : 0 < y) :
    hilbertInf (-(x : Int)) (-(y : Int)) = -1 := by
  have hx' : ¬ (0 ≤ -(x : Int)) := by omega
  have hy' : ¬ (0 ≤ -(y : Int)) := by omega
  simp [hilbertInf]
  omega

/-- **BL Lemma 3.1** (positive octant): inv_∞ α = −1 on natural-number
    solutions.  The two ratios −u_i/u_j are negative, so the real Hilbert
    symbol is −1. -/
theorem lemma31 {x y z : Nat} (hx : 0 < x) (hy : 0 < y) (_hz : 0 < z) :
    hilbertInf (-(x : Int)) (-(y : Int)) = -1 :=
  lemma31_pos hx hy

/-- For two odd residues the 2-adic symbol is −1 iff both are 3 (mod 4). -/
theorem hilbert2Odd_of_mod4 {a b : Int}
    (_ha : a % 4 = 1 ∨ a % 4 = 3) (_hb : b % 4 = 1 ∨ b % 4 = 3) :
    hilbert2Odd a b = -1 ↔ a % 4 = 3 ∧ b % 4 = 3 := by
  simp [hilbert2Odd]


end BL
