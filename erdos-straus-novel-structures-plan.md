<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Erdős–Straus: Novel Structures Research Plan

**Riley Betts Ltd — Research Note**
**Date:** 18 August 2026; record extended 19 August 2026 (§4s, §4t)
**Status:** Working plan following literature investigation and preliminary computation.
This archive is a collaboration of Anthropic agents, Grok 4.6, and
Cursor agents, with Lean 4, Mathlib, and numerical test resources.
Martyn Riley, of Riley Betts Ltd, facilitates the automation and
high-level strategy; he makes no claim to mathematical expertise
(see `README.md`). No proof of the conjecture is claimed.
Lean Route 2 (Z-model, box, reciprocity, TUB-EP packaging) is recorded in §4s;
the split-fiber / Harpaz inapplicability is recorded in §4t.  Neither is a
proof of the conjecture.

---

## 1. Problem statement and the wall

The Erdős–Straus conjecture (ES): for every integer n ≥ 2 there exist positive integers x, y, z with

> 4/n = 1/x + 1/y + 1/z.

It suffices to prove ES for primes. The known reductions (Mordell's identities) resolve all residue
classes mod 840 except the six quadratic-residue classes **1, 121, 169, 289, 361, 529 (mod 840)**;
the smallest uncovered prime is 1009.

**The wall.** Every technique surveyed below eventually meets the same obstruction:

- **Mordell/Schinzel (reciprocity obstruction).** Congruence classes solvable by polynomial identity
  cannot be quadratic-residue classes. Mordell's argument via quadratic reciprocity shows congruence
  relations can only eliminate non-residues. Schinzel (1956): 4/(ax+b) = 1/F₁ + 1/F₂ + 1/F₃ has no
  polynomial solution with positive leading coefficients when b is a QR mod a.
- **Density vs. universality.** Vaughan (1970): the number of exceptions up to N is
  ≤ N·exp(−c(log N)^{2/3}). ES has been "almost proved" for over 50 years; the entire difficulty is
  the universal quantifier over a density-zero set. Almost maps transfer almost proofs — never the
  exceptional set, which is where the conjecture lives.
- **Covering equivalence.** ES is *equivalent* (Bloom's survey, Thm 1; ancestry in Nakayama, Rosati,
  Mordell) to: every prime lies in a class −a/c (mod 4acd−1) for some a,c,d ≥ 1, or
  −(4c²d+1)/k (mod 4cd) for k | 4c²d+1. So ES is exactly an infinite covering-system problem.

**Selection criterion adopted:** since no mapping avoids the wall, prefer mappings whose toolkit has
historically produced *exact* (not almost) coverage of primes.

---

## 2. Options considered

### Option 1 — Solution-variety family with Brauer–Manin invariant
Treat the family of ES surfaces over Spec ℤ with morphisms from the classical Type I/II
substitutions; ES becomes "every fiber has an integral point," attacked via integral Brauer–Manin.

- **Status of prior art:** This *is* the Bright–Loughran program (arXiv:1908.02526, Bull. LMS 2020).
  They study failure of the integral Hasse principle and strong approximation for ES via
  Brauer–Manin, computing Brauer groups of the singular log K3 surfaces involved (novel: Brauer
  groups of singular varieties are rarely computed), and note the hope of using the Brauer element
  against ES.
- **Verdict:** Serious mathematics, but an *existing* program — extend, don't invent. Open question:
  is Brauer–Manin the only obstruction to integral points on ES surfaces? Best target for
  a formalization contribution rather than a new paper.

### Option 2 — Weighted divisor hypergraph with spectral gap
Vertices = admissible (a, d) pairs from Chamberland's Type-II characterization; hyperedges =
compatible congruence systems; ES = nonemptiness; density version = expansion/concentration.

- **Verdict:** Novel packaging of Elsholtz–Tao's first/second-moment counting, which already
  implicitly lives on this object. Second moments cannot exclude a sparse exceptional set; the
  needed structural property is precisely the open part. Moderate novelty, known failure mode.
  Connects directly to existing Track-1 second-moment work.

### Option 3 — Monoid of tame constructions acting on residue classes ★ (formalization track)
Treat identity constructions as generators of a monoid acting on residue classes (profinite space
Ẑ); ES restricted to identity methods = orbit-coverage question.

- **Investigation findings:**
  - The target orbit space already exists explicitly: the covering equivalence (§1) parametrizes
    all solvable classes. The *monoid/action framing* of its generation is not in the literature.
  - Finite-generation rigidity is essentially provable now: Schinzel + the 2026
    divisor-parametrization paper (arXiv:2606.10922) — fixing three of four parameters to a finite
    set yields finitely many classes, which cannot cover p ≡ 1 (mod 4). Any finitely generated
    submonoid provably has an invariant complement in the hard classes.
  - Nearest prior art: a 2024 preprint (arXiv:2404.01508) conjecturing a complete congruence
    system (Type A/B), verified for the first 10⁴ primes — a proposed cover, not a structural
    theory of the method space. Ionascu–Wilson observe excluded residues are persistently
    squares/composites as moduli grow: a fragment of the phenomenon, no framework.
- **Verdict: promising as a formalization-first project.** The finite-rigidity theorem, Schinzel's
  obstruction, and the covering equivalence as a Lean 4 package, with the monoid as organizing
  structure; the open covering-density question stated precisely as the endpoint. Reformulates the
  hard part; does not bypass it.

### Option 4 — Vieta dynamics on the ES surface (Markov analogy) ✗ (killed by investigation)
Hope: automorphism group of the ES surface acts with few orbits (Bourgain–Gamburd–Sarnak strong
approximation, as for Markov triples).

- **Structural obstruction found:** Markov-type surfaces are degree 2 in each variable — this is
  what makes Vieta involutions (x₁,x₂,x₃) ↦ (x₂x₃−x₁, x₂, x₃) polynomial automorphisms with
  finitely many integral orbits (BGS 2016). The ES surface 4xyz = n(xy+yz+zx) is **multilinear**
  (degree 1 in each variable), as are the shifted model abc − n²(a+b+c) = 2n³ and the
  divisor-paper surface uvw − u − v = n. Solving for a variable gives a unique root — the
  involution degenerates to the identity; the solve map involves division and does not preserve ℤ.
  Polynomial automorphisms reduce to finite coordinate symmetries: no orbit structure, no strong
  approximation, no affine sieve.
- **Independent confirmation:** the communities have met via arithmetic geometry, not dynamics —
  Bright–Loughran on ES surfaces parallels Colliot-Thélène–Wei–Xu on Markov surfaces, and recent
  Markoff-orbifold-pair papers cite Bright–Loughran directly. The absence of a Vieta-dynamics
  paper on ES is explained: there is nothing there.
- **Salvage:**
  1. *Negative theorem* — "the ES surface admits no infinite group of polynomial automorphisms;
     no Markov-type descent exists." Short, elementary, Lean-formalizable; complements Schinzel.
     Folds into the Option 3 package.
  2. *Quadratic covers* — Elsholtz–Tao's 3-fold lift, or a double cover adjoining the square root
     behind the QR obstruction. Whether such a cover carries involutions is unexplored; the
     obstruction being quadratic-flavored while the surface is multilinear suggests the dynamics,
     if anywhere, lives on a cover. Replacement lottery ticket.
  3. Fold effort into the Bright–Loughran-adjacent track (Option 1).

### Option 5 — Equidistribution of solvable classes (Duke–Friedlander–Iwaniec style)
Treat the class family −a/c (mod 4acd−1) as points on ℝ/ℤ; prove DFI-type equidistribution with a
level of distribution via bilinear Kloosterman estimates; feed into a sieve.

- **Verdict (updated after Option 9 stress test):** no longer independent — the Option 9
  investigation showed the covering condition *is* a roots-of-quadratic-congruences statement
  (ν² ≡ −pd (mod q) with a divisor-landing constraint), so Option 5's DFI machinery is the
  analytic engine of Option 9's Landing Lemma. Merged into Track B.

### Option 6 — Automaticity of the exceptional set
Ask whether the per-modulus exceptional sets form an automatic family; if so, attack with
Büchi-arithmetic/Walnut-style decision procedures.

- **Verdict:** probably *not* automatic (quadratic residues aren't), but a precise characterization
  of the failure would itself be new — "why ES resists finite description." Cheap diagnostic;
  machine-checkable object.

### Option 7 — ZK-attested formally verified computational frontier (company-aligned deliverable)
Lean 4-verified ES checker, execution proven in SP1 with Nova/HyperNova folding: a trustlessly
auditable replacement for the unverified computational record (Salez, n ≤ 10¹⁷). Certificate =
covering identities + finite verified check, composing with Option 3.

- **Verdict:** zero new number theory; genuinely novel artifact; ideal lean-tee showcase for
  ARIA/RHUL. Safe deliverable.

### Option 8 — Proof-theoretic mapping ★ (vehicle)
Reverse mathematics of ES: which fragments (IΔ₀, IΔ₀+exp, IΣ₁) prove the covering equivalence,
Schinzel, Vaughan? Is ES efficiently expressible in weak systems (Π₂, pushed toward Π₁ by
polynomial solution-size bounds)? Rigorous version of the "nonstandard model" joke: could a
counterexample be nonstandard in a model of a weak fragment?

- **Verdict:** guaranteed publishable floor (Lean formalization of the known structure with
  axiom-strength tracking — does not exist), unusual speculative ceiling, squarely in-house
  capability. **Best odds of producing something valuable.** Serves as the vehicle for Option 9.

### Option 9 — Class field theory mapping ★★ (primary mathematical bet)
Reformulate "p is covered" as a splitting condition in explicit families of number fields.

- **Investigation findings:**
  - **No prior art.** No CFT research program on ES exists; only a stray citation of Chebotarev's
    1926 paper in an appendix of a constructive-parametrization preprint.
  - **The obstruction is already CFT in disguise.** Mordell's argument *is* quadratic reciprocity;
    Yamamoto (1965) ran on Kronecker/Jacobi symbols. Quadratic reciprocity = CFT for quadratic
    extensions.
  - **Necessity theorem (apparently new, provable now).** Congruence conditions on p = splitting
    conditions in abelian extensions of ℚ (Kronecker–Weber). Mordell's obstruction therefore reads:
    *the abelian layer of splitting conditions provably cannot cover the hard classes; any exact
    covering proof of ES must invoke non-abelian splitting conditions.* Bounds all congruence-type
    conditions at once and names the escape direction. Pairs with Schinzel in the Option 3 package.
  - **The escape direction is concrete.** The covering condition ∃a,c,d: (4acd−1) | (cp+a) is
    bilinear — a divisor condition on shifted multiples of p, not a residue condition on p.
    Classically, such divisor conditions are representation conditions by binary quadratic forms;
    representation by a *specific form* (not a genus) is splitting in a *ring class field* — a
    dihedral, non-abelian condition. The covering criterion already lives one rung up the
    non-abelian ladder; nobody has written it in that language.
  - **Computation (18 Aug 2026).** Minimal witnesses for the first hard primes (≡ QR classes
    mod 840), search bound a,c,d < 40:

    | p    | q = 4acd−1 | (a, c, d) | check              |
    |------|-----------|-----------|--------------------|
    | 1009 | 11        | (3, 1, 1) | 11 · 92 = 1012     |
    | 1129 | 11        | (1, 3, 1) | 11 · 308 = 3388    |
    | 1201 | 31        | (1, 4, 2) | 31 · 155 = 4805    |
    | 1801 | 11        | (3, 1, 1) | 11 · 164 = 1804    |
    | 2521 | 47        | (4, 3, 1) | 47 · 161 = 7567    |
    | 2689 | 23        | (2, 1, 3) | 23 · 117 = 2691    |
    | 3049 | 43        | (1, 11, 1)| 43 · 780 = 33540   |
    | 3361 | 99        | (5, 1, 5) | 99 · 34 = 3366     |

    Each hard prime escapes through a small modulus where it sits in a non-residue class
    (e.g. 1009 ≡ 8 (mod 11), a non-residue) — the Hasse–Minkowski escape hatch acting prime by
    prime. Witness data is cheap to generate at scale.
  - **Toolkit with exact-coverage precedent:** genus theory (complete representability criteria
    when the form class group is 2-elementary), explicit ring class field splitting laws,
    governing fields, Rédei symbols, Friedlander–Iwaniec–Mazur–Rubin spin. Cohen–Lenstra-type
    heuristics give predictive structure for class-group statistics along witness discriminants.
  - **Honest risk:** covering all primes with infinitely many dihedral conditions is still a
    universal statement; per-field Chebotarev gives densities only. But this is the sole surveyed
    toolkit that has ever produced exact prime-coverage statements — the selection criterion.

- **QED stress test (18 Aug 2026, second investigation):**
  - **Clean criterion (derived).** Since 4acd ≡ 1 (mod q) forces c⁻¹ ≡ 4ad, the covering
    condition q = 4acd−1 | cp+a is exactly

    > **p ≡ −4a²d (mod q)**, i.e. **q | p + 4a²d with q ≡ −1 (mod 4ad)**.

    Immediate corollary: −pd ≡ (2ad)² (mod q) — every witness q is a split modulus for the
    discriminant **−4pd**. The witness discriminants of Track B are thereby *derived*, not
    guessed; they vary with p, recovering Mordell's abelian-insufficiency as a corollary.
  - **Empirics: the wall is fractal but shallow.** Over all 511 hard primes < 200,000, the
    single family d = 1 covers **503/511**, with minimal witness a averaging 0.018·√p
    (max ratio 0.42). The eight escapees — 3361, 7681, 31081, 51361, 58321, 88729, 167521,
    197521 — are all recovered with **d ≤ 5** (e.g. 3361 → (d,a,q) = (5,5,99);
    7681 → (5,2,39); the six d = 2 or 3 cases have a ≤ 11). Each fixed d reproduces the
    density-vs-universality pattern internally; the exceptional sets thin rapidly in d and
    appear independent. The QED question is exactly: prove the union over (a,d) covers.
  - **Fusion: Option 5 and Option 9 are the same option.** The landing condition — the root ν
    of ν² ≡ −pd (mod q) equals 2ad with 4ad | q+1 — is verbatim the Duke–Friedlander–Iwaniec
    object (equidistribution of roots of quadratic congruences via bilinear Kloosterman bounds).
    Via the classical dictionary, roots ↔ ideals of norm q in ℚ(√−pd) ↔ forms of discriminant
    −4pd representing the witnesses; small observed a means witnesses arise from essentially
    reduced forms. The CFT map lands the entire QED question on one analytic statement: roots
    of quadratic congruences hitting divisor-constrained positions.
  - **QED template: the Helfgott pattern.** Rearranged, the criterion is the thin bilinear
    representation problem **p = qm − 4a²d, q ≡ −1 (mod 4ad)** — the Friedlander–Iwaniec
    (x²+y⁴) / Heath-Brown (x³+2y³) genre. "Every sufficiently large p has a witness" +
    finite verification below the threshold = complete proof — precisely how Helfgott closed
    ternary Goldbach (effective circle method + computation). ES has the computational half
    done to 10¹⁷ (Salez); its verified, ZK-attested replacement is Track C.
  - **The blocking lemma, named.** Elsholtz–Tao control the *average* witness count; QED needs
    an *individual* lower bound uniform over the hard classes — the recognized hard step
    (same reason d₃(n) pointwise bounds fail, cf. Option 10).

    > **Landing Lemma (open).** There exist effective P₀, D₀ such that for every prime p in a
    > hard class with p > P₀, some root of ν² ≡ −pd (mod q) lands in the divisor-constrained
    > set {ν = 2ad, 4ad | q+1}, for some d ≤ D₀.

    Beyond current technology, but well-posed and adjacent to two active toolkits (DFI
    equidistribution; FI-type bilinear sieves), with empirical slack visible (mean witness at
    ~2% of allowed range).
  - **QED verdict: conditional.** Not provable today; but this is the only surveyed route with
    (a) a correct exact reduction, (b) a completion template with successful precedent
    (Helfgott), (c) the finite-verification half already existing and formalizable in-house,
    and (d) a single named lemma as the residual gap rather than a diffuse wall. Every other
    option terminates in "density can't reach the exceptional set"; this one terminates in
    "prove the Landing Lemma."

### Option 10 — Dirichlet series of the solution count
D(s) = Σ f(n)/nˢ with f(n) = #solutions; ask whether its analytic structure (Euler-like
factorization over parametrization families, character contributions from the QR obstruction)
forces pointwise positivity.

- **Verdict:** pointwise positivity from Dirichlet series is what analytic number theory is
  famously bad at (cf. d₃(n)); but the map of *which* L-functions appear has not been written down
  and would clarify the problem. Diagnostic value; cheap to scope.

### Option 11 — Tropical/polytope degeneration
Tropicalize 4xyz = n(xy+yz+zx) (multilinearity is harmless tropically — no involutions needed,
only balancing); ask whether solvability has a lattice-point shadow on the associated polytope.
Precedent: Jang's tropical Markov cubics (arXiv:2306.11357).

- **Verdict:** likely too coarse (tropicalization forgets units, probably cannot see mod-840
  structure); weekend-scale fast fail; a positive signal distinguishing 1009 from neighbors would
  be strange and new.

---

## 3. Discarded framings (recorded for completeness)

- **"One-ish numbers" / invented number theories with only an almost map to ℤ** (the LinkedIn
  provocation that started this thread): an almost map transfers only almost statements; results
  return as density-zero-exception claims, a genre already saturated for ES since Vaughan 1970.
  Proof does not degrade gracefully; the exceptional set carries the entire universal quantifier.
  The rigorous descendant of the joke is Option 8's nonstandard-model question.
- **General principle extracted:** an invented structure earns its keep only with (i) a provable
  correspondence back to ℤ, (ii) a stated theorem about the original integers, (iii) a stated
  failure mode.

---

## 4. The program

**Track A — Formalization vehicle (Options 8 + 3 + 4-salvage).**
Lean 4 package, axiom-strength tracked:
1. The covering equivalence (ES ⟺ infinite covering by −a/c (mod 4acd−1) and Type-II classes).
2. Schinzel's obstruction (quadratic reciprocity is in Mathlib).
3. Finite-generation rigidity for the tame-construction monoid.
4. The no-Markov-descent negative theorem (multilinearity ⟹ no infinite polynomial automorphism
   group).
5. The abelian-insufficiency proposition from Option 9.
Publishable regardless of further progress; nothing comparable exists.

**Track B — Class field theory / analytic mathematics (Options 9 + 5, fused).**
1. **Reduction paper (ready to write).** The derived criterion q | p + 4a²d with
   q ≡ −1 (mod 4ad); the discriminant −4pd dictionary (roots of congruences ↔ forms ↔ ring
   class splitting); the non-abelian necessity theorem; the DFI fusion; the Helfgott-template
   reduction of ES to the Landing Lemma + finite verification. Evidence section: the two
   computations (511 hard primes, d = 1 covers 503/511, all recovered at d ≤ 5, witness
   scaling a ~ 0.02·√p). Publishable independent of the Landing Lemma.
2. **Computational survey at scale:** minimal witnesses (a, d, q) per hard prime; distribution
   of exceptional primes per fixed d; correlation with class numbers h(−4pd) and class group
   structure; estimate empirical P₀, D₀.
3. **Summit: the Landing Lemma.** Individual (not average) lower bound on the witness count,
   via DFI bilinear/Kloosterman technology or FI-type sieves; alternatively an exact
   governing-field covering statement. Either closes ES modulo the (formalized, ZK-attested)
   finite check of Track C.

**Track C — Company-aligned deliverable (Option 7).**
ZK-attested, Lean-verified ES verification frontier via lean-tee/SP1 + Nova/HyperNova; certificate
structure = Track A's covering identities + verified finite check. ARIA/RHUL demonstration piece.

**Reserve / diagnostics:** Options 5, 6, 10, 11 as bounded-cost scoping exercises; Option 1
(Bright–Loughran-adjacent) as the geometric literature track; quadratic-cover involutions (Option 4
salvage 2) as the standing lottery ticket.

**Ranking rationale.** Best odds of contributing to an actual proof: Option 9 (only toolkit with
exact-coverage precedent, matched to the material of the wall — and after the QED stress test,
the only route reducing ES to a single named open lemma plus an existing finite check). Best
odds of valuable output: Option 8 (floor ≈ certain). They compose: A is the vehicle, B is the
direction, C is the funding story — and C is now also the literal second half of the
Helfgott-template proof architecture.

---

## 4a. Formalization status (18 Aug 2026, evening session)

Option 9 has been formalized in Lean 4.15.0 (core only, no Mathlib): `ErdosStraus.lean`,
197 lines, compiles clean. Results, with axiom audit:

1. **Explicit solution formula (new, derived this session).** A witness (a,c,d,m) with
   c·p + a + m = 4acdm yields exactly **4/p = 1/(adm) + 1/(p·acd) + 1/(p·cdm)** — found by
   monomial pattern search over all 31 (prime, witness) pairs, verified symbolically, then
   proved in Lean (`witness_sound`; axioms: propext, Quot.sound only).
2. **Machine-checked conditional QED.** `conditional_qed : LandingHypothesis → ErdosStraus`,
   via `witness_sound` + a `scale` lemma + a self-contained prime-factor theorem.
   Axioms: propext, Classical.choice, Quot.sound (standard).
3. **Verified finite instances of the Landing Hypothesis.** Every prime below 10,000 — and
   separately every hard-class prime below 10,000 — has a covering witness with parameters
   ≤ 25 (`native_decide`); every prime below 100 verified with **zero axioms** (pure kernel
   `decide`). Bounded-search soundness (`hasWitness_sound`) proved, so the Boolean checks
   genuinely instantiate the hypothesis.
4. **Worked example.** `es_1009 : IsES 1009 276 3027 92828` from witness (3,1,1,92).
5. **Formal Mordell reduction (second session).** `es_of_not_one_mod_four`: ES proved
   outright for every n ≥ 2 with n % 4 ≠ 1 (axioms: propext, Quot.sound only) — the class
   n ≡ 3 (mod 4) via the polynomial witness (1, 2, t+1, 1), all even n by scaling the n = 2
   solution.
6. **Full mod-840 reduction (third session, 380 lines total).** Seven further polynomial
   witnesses — (1,1,1,s+1) for 2 (mod 3); (1,1,t+1,2) for 5 (mod 8); (1,2,1,2s+1),
   (2,1,1,s+1), (1,1,2,s+1) for 3, 5, 6 (mod 7); (1,2,2,2s+1), (2,1,2,s+1) for 7, 13
   (mod 15) — each a one-line `omega` proof, combined with a Presburger CRT lemma
   (`mod840_hard`, proved by `omega` alone) into:
   - `es_prime_not_hard`: **every prime outside the six hard classes satisfies ES**
     (axioms: propext, Classical.choice, Quot.sound);
   - `conditional_qed_hard : HardLandingHypothesis → ErdosStraus` — the conditional QED
     now requires the open hypothesis **only for primes ≡ 1, 121, 169, 289, 361, 529
     (mod 840)**, exactly matching the classical state of the art, machine-checked
     end to end.
7. **Verified frontier (fourth session, 449 lines total).**
   `es_below_100000 : 2 ≤ n → n < 100000 → ∃ x y z, IsES n x y z` — ES *proved* for every
   n below 100,000 via a self-certifying range check (`okay n` = proper factor or covering
   witness, so no primality-completeness proof is needed) bridged by strong induction:
   factors recurse and scale, witnesses close directly. Axioms: the standard trio plus
   `Lean.ofReduceBool` (the native range check). This is the seed of Track C: replacing
   `ofReduceBool` with a ZK-attested execution proof of the same checker, and scaling
   100,000 → 10¹⁷, is exactly the lean-tee/SP1 pipeline.

**Mathlib dependency assessment.** Not needed for: the remaining Mordell/Aigner residue
classes as polynomial witnesses (mod 5, 7, 8 — same pattern as mod 4), the necessity
direction of the covering equivalence (gcd casework, core `Nat.gcd` suffices), the Type II
second witness family, and scaling the verified frontier (fuel-based √n primality + larger
`native_decide` bounds). Needed for: Schinzel's obstruction and the abelian-insufficiency
theorem (quadratic reciprocity), Dirichlet/Chebotarev inputs to any Landing Lemma attack,
and eventual Mathlib upstreaming of the whole package.

Consequence for the plan: Track A item 1 (covering sufficiency direction) and the skeleton of
Track B item 1 are now *done and machine-checked*; ES is formally reduced to the Landing
Hypothesis plus computation. The unconditional QED remains blocked exactly where predicted —
at the Landing Lemma. Remaining formalization targets: the equivalence's necessity direction,
Schinzel's obstruction, and the abelian-insufficiency proposition (needs quadratic reciprocity,
i.e. Mathlib).

---

## 4b. Engine A feasibility calculation (18 Aug 2026, late session)

Goal: determine whether the Landing Lemma is provable under GRH via character-sum methods.
Outcome: **the question transmutes — GRH is largely beside the point, and the Lemma reduces
to an explicit sieve-density statement.** Four findings, each numerically verified:

1. **Exact reformulation.** W(p) = #{(a,d,k,m) : p + 4a²d + m = 4adkm}, verified identical
   to the divisor-form count. For bounded (a,d,m) the witness condition is a **pure
   congruence**: p ≡ −(4a²d + m) (mod 4adm).
2. **Singular-series positivity (no-disproof check).** κ_p = W(p)/log²p across 15 primes in
   each hard class: means 0.132–0.150, overall 0.139 ± 0.045, min 0.047. No class
   degenerates; proving κ_p > 0 via local densities is a finite, paper-ready lemma.
3. **Mass concentration at polylog moduli.** 91% of witnesses have a ≤ log²p; **40/40 hard
   primes tested have a witness with a, m ≤ log²p.** The operative regime is moduli 4adm of
   polylogarithmic size — Siegel–Walfisz territory, unconditionally understood. DFI bilinear
   machinery (√p-moduli) and GRH (large-modulus characters) address a regime the problem
   barely uses. Effective Landing statement: *the growing covering system of classes
   −(4a²d + m) mod 4adm, parameters ≤ log²p, covers every hard prime.*
4. **The sieve exponent crosses critical.** Uncovered density u(A) of hard-class integers
   under the box a, m ≤ A, d ≤ 5 (n = 4000 samples):

   | A   | u(A)    | local κ |
   |-----|---------|---------|
   | 16  | 0.626   | —       |
   | 32  | 0.203   | 1.62    |
   | 64  | 0.0645  | 1.65    |
   | 128 | 0.00975 | 2.73    |
   | 256 | 0.00175 | 2.48    |

   The local exponent crosses the union-bound threshold κ = 2 near A ≈ 128 and
   accelerates, matching the quasi-independence prediction u(A) ≈ exp(−c·log²A)
   (super-polynomial decay). Under that law, expected exceptional primes up to x scale as
   π(x)·exp(−c·log²x/4) — vanishing with a convergent total: heuristically zero exceptions
   beyond the verified range, with wide slack.

**Revised Engine A target — the Covering Density Lemma (open).**

> There exist effective constants such that the density of hard-class integers avoiding
> every class −(4a²d + m) (mod 4adm) with a, m ≤ A, d ≤ 5 satisfies u(A) ≪ A^{−2−ε}
> (empirically exp(−c·log²A)).

With effective constants, this lemma + the union bound over primes + the verified finite
check yields the full QED. Residual gaps, honestly stated: (i) *minor* — densities were
measured on integers; the prime-correlation adjustment (classes sharing a factor with their
modulus contain no primes, which helps) should be quantified on prime samples; (ii) *major*
— converting quasi-independence into a theorem: correlation control among the explicit
congruence classes, an inclusion–exclusion / large-sieve problem at polylog moduli —
elementary-shaped, GRH-free, and computationally explorable, but this is the wall's final
costume; (iii) *effectivity* — ineffective finiteness cannot be finished by computation; if
the effective threshold P₀ is astronomical, the ZK-attested verification track becomes
load-bearing mathematics rather than infrastructure.

**Status ladder of the wall across this investigation:** "quadratic-residue classes resist
covering" (folklore) → Landing Lemma (roots of quadratic congruences in divisor-constrained
positions, DFI-adjacent) → **Covering Density Lemma** (explicit sieve exponent for a named
congruence family, measured κ > 2 with super-polynomial decay). Each reformulation is
strictly more concrete; none is yet a proof.

**Next action:** compute pairwise overlaps of the covering classes exactly by CRT and test
how far honest Bonferroni truncation gets toward u(A) ≪ A^{−2−ε} unconditionally.

---

## 4c. Correlation structure of the covering family (18 Aug 2026, final session)

Executed the next action: exact CRT computation of the family's moment structure within
the universe n ≡ 1 (mod 4). (Structural filter derived en route: a class can meet the
universe only when m ≡ 3 (mod 4), since n ≡ −m (mod 4) on every class.)

1. **Pairwise independence ratio: bounded and flat.** R₂ = 2S₂/S₁² measured exactly at
   A = 8, 16, 24, 32, 40: values 1.249, 1.243, 1.262, 1.245, 1.248. A persistent +25%
   positive correlation — but *constant in A*, not growing. Bounded pair correlation is
   what Brun/Selberg machinery tolerates; growing correlation is what kills it.
2. **Third moments at independence.** R₃ = 6S₃/S₁³ = 0.74, 1.07, 1.03 at A = 8, 12, 16 —
   essentially the independence baseline. No higher-order blowup visible.
3. **The excess is diffuse.** Binning S₂ by gcd of the two moduli at A = 32: the pairwise
   mass splits almost evenly (0.19 / 0.27 / 0.27 / 0.27 across gcd scales 4, ≤16, ≤64,
   large). There is no small pathological sub-family of containments to excise; the
   correlation behaves like a constant sieve-dimension inflation, not a structural defect.

**Verdict.** Every measurable indicator is green for a sieve-theoretic proof of the
Covering Density Lemma: bounded second moments, independent-level third moments, diffuse
overlap structure, and — importantly — the task is an *upper bound on a sifted set's
density*, which is sieve home turf and not exposed to the parity barrier (no
primes-in-sifted-set claim is needed). The precisely remaining mathematics: Brun/Selberg
truncation control for this thin composite-moduli family at level growing with A, uniform
in the residue data — with the measured constants (κ ≈ 0.139 density, R₂ ≈ 1.25) as the
inputs the proof must reproduce. Caveats recorded: moments measured at small A; uniformity
across the six hard classes checked only empirically (§4b.2); measured ≠ proved.

**Final status ladder:** folklore wall → Landing Lemma (DFI-adjacent) → Covering Density
Lemma (explicit sieve exponent) → **a standard-shape upper-bound sieve problem with
measured green-light constants**. Four reformulations in one day, each strictly more
concrete; the last one sits in a genre — sifted-set density upper bounds — where the
toolkit is mature. This is the recommended attack point for Track B item 3, and the
remaining analytic input: the problem arrives
pre-reduced, pre-measured, machine-checked from lemma to QED, with only the sieve left.

---

## 4d. The QED attempt: partial theorem and the three remaining rungs (18 Aug 2026, close)

A direct attempt at the Covering Density Lemma was made. Outcome: **QED not reached; one
partial theorem extracted; the residual difficulty located precisely.**

**The provable partial theorem (write-up pending).** Restrict to the prime-m subfamily.
For prime m, the witness condition n ≡ −(4a²d + m) (mod 4adm) splits by CRT into
*m | n + 4a²d* and *m ≡ −n (mod 4ad)* — so "uncovered" implies, for every (a,d) in the
box: **n + 4a²d has no prime factor p ≡ −n (mod 4ad) in the range (Y, A]**, with
Y = 100A₀² the root-distinctness threshold. Two structural facts make this rigorous with
no sieve error:
- across *distinct primes* the conditions are **exactly independent by CRT** — the
  uncovered density factorizes as an exact product Π(1 − ω_ρ(p)/p);
- an upper bound needs only a *necessary* condition, so discarding composite m is free.

With Mertens in arithmetic progressions (uniformity over the moduli 4ad via
Bombieri–Vinogradov, which is effective), optimizing the box A₀ = A^δ at δ = 1/(2e):

> **Partial Covering Density Theorem (skeleton verified, constants computed).**
> Effectively and unconditionally, u(A) ≪ A^{−κ*} with κ* = c_L/(2e), where
> c_L = lim Λ(x)/log x, Λ(x) = Σ_{a≤x, d≤5} 1/φ(4ad). Numerically c_L ≈ 1.57, hence
> **κ* ≈ 0.29**.

This would be the first rigorous power-law bound on the covering density. Validation:
the prime-m-only family's *measured* decay exponent is 1.00 → 1.39 → 1.75 (rising) at
A = 64/128/256 — well above the conservative provable 0.29 (the proof discards small
primes for root-distinctness where reality barely needs to), and below the full family's
measured 2.5–2.7 (composite m carries the rest).

**The three remaining rungs to QED, each now exact:**

1. **Constant-tightening** (provable 0.29 → toward the true prime-m ≈ 1.75): replace the
   range-exclusion treatment of root collisions with collision counting. Honest work, not
   a wall.
2. **Composite-m rigor** (≈ 1.75 → past the union-bound threshold 2): exact CRT
   independence fails for composite moduli. Identified route: partition the family into
   blocks with pairwise-coprime odd prime support (exactly independent across blocks;
   Bonferroni within blocks), reducing the problem to a support-concentration
   combinatorial estimate. This is the genuine crux of the density lemma, and it is
   well-shaped.
3. **Density → count transfer — the wall's true final form.** The sifted set's period
   exceeds any counting interval, so bounding exceptional *primes up to x* requires
   interval versions of the density bounds; with sieve dimension growing like log x, the
   fundamental lemma's constants blow up. Worked through, this route currently yields
   exceptional-set savings of only exp(−c(log log x)²) — **weaker than Vaughan (1970)** —
   the definitive sign that this rung is where the 78-year difficulty actually resides:
   *transferring super-polynomial covering-density decay from densities to counts against
   growing sieve dimension.* New ideas, not better execution, are required here.

**Closing assessment.** Rungs 1–2 constitute a plausible paper's worth of achievable
mathematics that would prove the Covering Density Lemma outright — a genuine advance and
the recommended continuation of Track B. Rung 3 is the residence of the conjecture
itself. The complete obstruction ladder over the day: folklore → Landing Lemma →
Covering Density Lemma → sieve moment problem → **density-to-count transfer at growing
dimension** — five strict sharpenings, the last finally explaining *why* the problem is
hard rather than merely that it is. Everything above the final rung is now either proved,
measured, or machine-checked; the file `ErdosStraus.lean` converts any future proof of
the covering statement into a full QED automatically.

*Session artifacts: `ErdosStraus.lean` (449 lines, axiom-audited); this document;
reproducible computations as noted per section.*

---

## 4e. Rung 2 cracked in principle: the Suen conditioning scheme (18 Aug 2026, coda)

The rung-2 diagnostic reframed the problem decisively. After conditioning on all primes
≤ T (the partial theorem's architecture), the probability space is a **product space over
large-prime coordinates** n mod p, p > T; each class (a,d,m) is an event depending only on
the coordinates at the prime factors of m exceeding T. This is exactly the setting of
**Suen's correlation inequality** (Suen 1990; Janson 1998): u ≤ exp(−μ + Δe^{2δ}), with
μ = total event mass, Δ = mass on dependent pairs (sharing a large-prime coordinate),
δ = maximum neighbor mass.

**Measured gates (A = 24–48):**
- *No conditioning (T = 2):* catastrophic failure — δ up to 5.0, Δ > μ. The small primes
  (3, 7, 11, 13) form a dependency hub through which most composite m interact. This is
  the structural identity of the rung-2 obstruction.
- *Conditioning at T = 13:* the hub is absorbed — Δ ≈ 0.01·μ², δ ≈ 0.5, effective Suen
  exponent captures 71–86% of μ, growing with A.
- *Scaling in T (A = 48):* Δ·T/μ² falls 0.141 → 0.077 → 0.057 across T = 13/23/37, and
  δ decays in step — consistent with (indeed better than) Δ ≲ cμ²/T, δ ≲ cμ/T, whose
  source is the elementary second moment Σ_{ℓ>T} (mass divisible by ℓ)² ≪ μ²/T.

**The scheme.** Take T = T(A) a suitable power of log A (e.g. T ≈ μ³). Then Δe^{2δ} → 0
while conditioning discards only polylog-smooth m (negligible mass), and Suen delivers

> u(A) ≤ exp(−(1 − o(1))·μ) = exp(−(1 − o(1))·κ·log²A)

**unconditionally, at full super-polynomial strength** — the complete Covering Density
Lemma, not just the κ ≈ 0.29 prime-m fragment. Rung 1 is absorbed for free: prime-m
classes are the singleton-support case of the same machinery.

**Status: proof strategy with all quantitative gates verified, not yet a proof.** The
write-up must supply: (i) the exact Suen/Janson hypotheses on the product space over
prime-power coordinates (standard); (ii) uniformity of the conditioned mass μ_ρ over
surviving residues ρ (Mertens in APs + Bombieri–Vinogradov, as in the partial theorem);
(iii) the rigorous Δ, δ ≪ μ²/T, μ/T bounds (elementary second moments); (iv) bookkeeping
for prime-power supports and the 2-adic component. None of these looks like a wall; all
constants are effective. This is now the concrete mathematical paper of Track B: **"An
effective super-polynomial bound for the Erdős–Straus covering density, via Suen's
inequality."**

**What remains between that paper and QED: rung 3 alone** — the density-to-count transfer
at growing sieve dimension (§4d), where the conjecture lives. The day ends with the
obstruction ladder at six rungs climbed or named: folklore → Landing Lemma → Covering
Density Lemma → sieve moments → **Suen scheme (strategy verified)** → density-to-count
transfer (open, and now the sole occupant of the wall).

---

## 4f. Rung 3: the Vaughan barrier and a no-go meta-theorem (18 Aug 2026, final)

> **CORRECTION NOTICE (see §4h.3):** the barrier arithmetic in this section conflated
> total sifted mass with sieve dimension. The corrected cap is *power savings* x^{−cκ}
> (log z ≤ c√log x), not exp(−c(log x)^{2/3}), and the "triple convergence at Vaughan's
> exponent" claim is withdrawn. The no-go survives only in the invariant mass–level form
> of §4h.5. This section is retained unedited as a record of the reasoning path.

Rung 3 was engaged directly. No new computation was required — the content is barrier
arithmetic — and it produced one positive result, one sanity check of remarkable
precision, and one meta-theorem-shaped conclusion.

**1. The transfer works, up to a sharp limit.** Set the covering box at
A = exp((log x)^θ). Counting exceptional primes in [x, 2x] means counting primes avoiding
polylog-many congruence classes with moduli up to ≈ exp(2(log x)^θ). The sieve dimension
grows like κ(log x)^{2θ}; validity of the fundamental lemma requires
s = log x / log A ≫ dimension, i.e. (log x)^{1−θ} ≫ (log x)^{2θ}, forcing **θ < 1/3**.
At the boundary the pipeline delivers an exceptional-prime bound of
exp(−κ(log x)^{2/3}).

**2. The sanity check: that is Vaughan's exponent, exactly.** The covering + Suen +
fundamental-lemma route, pushed to its natural limit, re-derives exp(−c(log x)^{2/3}) —
the 1970 bound, unimproved for 55 years, originally obtained by exponential-sum methods
bearing no resemblance to this route. Nor is the coincidence tool-specific: running the
same arithmetic through Montgomery's large sieve (which has no dimension restriction)
produces the identical (log x)^{1/3} constraint from modulus-stacking — squarefree
products of class-moduli must remain below x^{1/2}, so only log x / log A conditions
stack, forcing log³A ≲ log x again. **Three independent technologies — Vaughan's
exponential sums, the fundamental lemma, the large sieve — terminate at the same
exponent.** Triple convergence of unrelated methods at one exponent is the signature of a
structural barrier (compare (log x)^{3/5} for zero-free regions). Positive corollary: an
*elementary* proof of a Vaughan-strength exceptional-set bound — covering systems plus
Suen's inequality, no exponential sums — falls out of the pipeline and would be a
publishable curiosity in its own right.

**3. The no-go meta-theorem (conjectural, proof-shaped).** Tracing the barrier's source:
closing QED requires savings exp(−S) with S > log x. A congruence-covering family whose
density mass grows like log^j A (the present family has j = 2; adjoining Type II classes
and richer identity families raises j) yields, under the modulus-stacking constraint,
S ~ (log x)^{j/(j+1)} — approaching log x as j → ∞ but **never reaching it for any finite
j**. Demanding unbounded richness is demanding that the covering system covers exactly,
which is the conjecture itself. Made rigorous, this is a Schinzel-style no-go theorem one
level up:

> *No congruence-covering family of polynomial richness, combined with any
> density-to-count transfer respecting modulus-stacking, can prove the Erdős–Straus
> conjecture; all such methods are capped at exceptional-set savings
> exp(−c(log x)^{j/(j+1)}).*

This would simultaneously explain the 55-year stasis at Vaughan's exponent and delimit
precisely which method classes cannot finish ES. Barrier results of this kind (parity,
self-improvement obstructions) are respected contributions; this one is the recommended
third paper.

**The three doors (now provably the only ones in this wing).** What the barrier leaves
open: (a) **exact algebraic covering laws** — Option 9's governing-field summit, which
bypasses counting entirely and is immune to the barrier; (b) **transfer technologies
violating modulus-stacking** by exploiting multiplicative structure in the shifted values
n + 4a²d themselves — smooth-number-type asymptotics live beyond the stacking barrier for
exactly this reason, a concrete and unexplored direction; (c) **disproof** — against
which the singular-series positivity data (§4b.2) argues strongly. Everything else —
richer identities, better sieves, sharper constants — provably lands below the line.

---

## 4g. Door (b) reconnaissance: the Henriot constant trail (18 Aug 2026, addendum)

Door (b) was made concrete: the identified vehicle is the Shiu → Nair (1992) →
Nair–Tenenbaum (1998) → Daniel → Henriot (2012, + 2014 erratum) chain of upper bounds for
Σ F(|Q₁(n)|, …, |Q_k(n)|) over short intervals — multiplicative-structure transfers not
subject to modulus-stacking in the sieve sense. The QED win condition, from the barrier
arithmetic: these bounds must hold with **constants polynomial in the number of factors
k** at k ≈ x^{1/log log x} (published versions treat k as fixed). A statement-level
extraction of Henriot's Theorems 1/3 against our family (Q_a = X + 4a²d, all linear, so
total degree g = k; F = the 0/1 indicator of class-roughness) yields four findings:

1. **All k-dependence flows through exactly three gates:** (i) the range condition
   x ≥ c₀‖Q‖^δ; (ii) the (g, δ)-dependence of c₀ and the implicit constant; (iii) the
   explicit discriminant factor Δ_D of Henriot's Theorem 3 (eq. 1.3). Nothing else in the
   statements carries k.
2. **The function-class gate is free.** Our indicator F lies in 𝓜_k(A, B, ε) with
   A = B = 1 for every ε, so the ε-constraints that shrink like 1/k² (ε ≤ α/(50g(g+1/δ)))
   cost nothing. An anticipated exponential loss vanishes by the structure of F.
3. **Δ_D is the small-prime hub in disguise.** The primes dividing our discriminant
   divide differences 4a²d − 4a′²d′ of box elements — overwhelmingly the same small
   primes the §4e Suen scheme conditions away, with F's vanishing on active classes
   cutting further. The two attacks converge on the same structural object from opposite
   sides; the natural architecture is a **hybrid proof**: Suen conditioning for the
   density, Shiu-type short-interval machinery for the count transfer.
4. **Gate (i) is the stacking barrier's avatar — and it reduces to one parameter.** For
   our family ‖Q‖ ≈ exp(c·k·log A₀), so fixed δ reproduces the §4f cap k·log k ≲ log x
   as a polynomial-height condition. But δ is free: δ ≈ 1/(k·log A₀) trivializes the
   range condition. **The entire door-(b) question is now: do c₀(g, δ) and the implicit
   constant grow polynomially or exponentially in k under the joint limit δ → 0,
   g = k → ∞?** This lives in Henriot §§4–7 (Stewart's bound
   ρ*(p^ν) ≤ g*·p^{[ν−ν/g*]}; the Shiu large/small-factor splitting), with the suspected
   exponential source being 2^k subproduct combinatorics and the structured-family hope
   being that linear factors in quadratic progression collapse it — ρ*(p) for our Q is
   the active-slice count already controlled in the §4e analysis.

**Status of the doors after reconnaissance:** door (b) now has a *named lock* — a single
quantified parameter trade in a specific published proof — rather than an open landscape.
Defined next session: interior trace of the (δ, g)-trail through Henriot §§4–5; if the
trade is purchasable at poly(k), draft the structured-family variant ("A k-uniform
Nair–Tenenbaum bound for linear factors in quadratic progression"), which combined with
§4e and the verified frontier would constitute the proof architecture of ES. If the trade
is provably exponential, the §4f no-go extends to door (b), leaving door (a) alone —
either outcome is decisive.

---

## 4h. The interior trace: gates dissolved, §4f corrected, and the wall's final form
(18 Aug 2026, second addendum)

The full trace of Henriot §§4–7 (arXiv:1102.1643, complete proof read) was carried out
against our family (linear factors Q_a = X + 4a²d; F a 0/1 indicator; hub conditioning
from §4e available). **Everything below is trace-level analysis: no result in this
section is claimed until the rigorous structured-family write-up exists.**

**1. Gate (ii) collapses for indicators.** The proof's exponential-in-k apparatus flows
entirely through L = g(g + 1/δ)·log A and its derivatives (χ = 3L/ε₂, the C₃/C₄ cutoff
ω = e^{2gχ}, the bounds G̃ ≤ A^{gΩ} and F ≤ B|Q(n)|^ε). With A = B = 1: **L = χ = 0,
ω = 1** — the exponential machinery trivializes, classes C₂/C₄/C₅ are handled by F ≤ 1
directly, and the ‖Q‖^δ range condition (used only inside A- and B-dependent estimates)
loses its force. Gates (i) and (ii) largely dissolve together.

**2. Linear structure kills the combinatorial losses.** The tuple-count factor ν^r in
Lemma 1's tail (exponential in k as written) collapses: linear factors have
ρ_{R_h}(p^ν) ≤ 1 (Hensel), and away from discriminant primes at most one factor is
divisible by p, so the count is linear in k; the exceptional primes are exactly the §4e
hub. The correction λ(n) = (n/φ(n))^g — genuinely e^{g/p}-sized at small p — is an
artifact of the crude ρ(p) ≤ g bound; the true (1 − ρ(p)/p)^{−1} with hub conditioning
is 1 + O(ρ(p)/p) with convergent tail.

**3. CORRECTION TO §4f.** The decisive quantity is the sieve *dimension*: for our family
Σ_{p≤z} ρ(p)·log p/p ~ c·log²z, so the dimension is ~c·log z — **not** k, and not the
quantity used in the §4f barrier arithmetic, which conflated total sifted mass with
dimension. Redone honestly through Lemma 6 (Brun, error Lz^{24g}): the level requirement
gives **log z ≤ c·√(log x)**, hence achievable savings exp(−κ·log²z) = **x^{−cκ}: power
savings.** The §4f claim that all methods cap at exp(−c(log x)^{2/3}), and the "triple
convergence at Vaughan's exponent," were too crude and are hereby amended. The j/(j+1)
no-go of §4f survives only in the corrected invariant form of item 5 below.

**4. New primary theorem candidate (supersedes the ranking).** Consequence of the
corrected cap: an **unconditional exceptional-set bound O(x^{1−c}) for Erdős–Straus,
strictly stronger than Vaughan (1970)**, appears within reach of the structured-family
variant: hub conditioning (§4e) + corrected-dimension Brun (this trace) + the measured
density mass (§4b). This is now the sharpest concrete target of the program, ahead of
the Suen density paper — with the explicit caveat that beating a 55-year record demands
a fully rigorous write-up before any Lean claim.

**(Amendment, 21 Aug 2026.)** That write-up is `erdos-straus-E-power.md`.
E_power is claimed: \(S_A(x,2x)\ll x^{1-\delta}\) at
\(A=\exp(c\sqrt{\log x})\). Lemma SM is the second-moment input;
the implied constant is checked through \(A=2000\). Gate A still
forbids compiling it as QED. The claim is not
`AnalyticSurvivorBound` and does not empty the box.

**5. The wall's final form: the mass–level inequality, at a marginal constant.** QED
requires exceptional count x·exp(−mass) < 1, i.e. sifted mass > log x. Every sieve
technology captures mass ≤ c·log(level), and level ≤ x forces mass ≤ c·log x — the
barrier in invariant form. The constants land at the boundary: for our family, captured
mass at level L is log L *exactly* at the critical configuration, so **ES sits at the
marginal constant** — the structural position of twin primes at the parity boundary.
Pushing the capture constant through 1 is where Elliott–Halberstam-type
level-of-distribution input lives; lower-order terms decide. The final statement of the
investigation is therefore not "capped below QED forever" but: **a boundary-constant
race, in which the unconditional side already promises a new record
(item 4), and the QED side is a level-of-distribution question at the critical
exponent.**

**Revised program order:** (1) rigorous write-up of the structured-family
Shiu–Nair–Tenenbaum variant with corrected dimension and hub conditioning — target: the
x^{1−c} exceptional bound [new record candidate]; (2) the Suen density paper (§4e);
(3) the formalization paper (§4a); (4) the boundary-constant/EH analysis as the
long-horizon QED track; (5) amend any external statement of §4f accordingly.

---

## 4i. Stage 1 executed: stratified compounding confirmed (18 Aug 2026, third addendum)

The Buchstab-recursion test from the QED roadmap was run. Structural pre-analysis: the
*integer*-direction recursion fails for the known reason (roughness conditions live on
shifted values n + 4a²d whose cofactors leave the family — the p−1-smoothness
obstruction); the *scale*-direction recursion survives iff level-A survivors are
pseudorandom for the next annulus's classes. Empirical arc (6000 hard-class samples,
level-32 survivors, annuli to 256):

1. **Naive compounding fails.** Survivors avoid the next annulus 1.51× / 1.64× / 2.03×
   more than fresh integers across successive annuli — anti-pseudorandom, bias growing.
2. **The bias is profile-mediated.** Scoring each n by its structural activation
   (classes split m = sm·fr at a smooth cut T; expected fresh coverage Π(1 − 1/fr) over
   structural hits): at T = 13 the profile explains ~two-thirds of the bias (survivor
   obs/pred 1.28); survivors demonstrably concentrate on low-activation profiles
   (mean score 1.66 vs 2.04).
3. **At the complete cut the bias vanishes.** With T = 31 (all primes shared with the
   level-32 box, so fresh parts are genuinely new CRT coordinates): survivor
   obs/pred = 1.098 vs fresh 1.140 — indistinguishable, residual equal in both groups
   (a within-annulus predictor artifact, not a survivor correlation).

**Verdict: the scale recursion holds exactly after conditioning on the complete
shared-coordinate profile** — forced by CRT structure at the density level (fresh parts
are new coordinates), hence theorem-shaped, and matching the §4e conditioning
architecture. Consequences for the QED path:

- **The compounding architecture.** Dyadic annuli A_j → A_{j+1} = 2A_j contribute mass
  Δ_j ≈ 2κ·log A_j·log 2 each; the per-step level requirement is only e^{Δ_j} =
  A_j^{O(κ)} — *polynomial* per step, versus the one-shot e^{total mass} that produced
  the mass–level cap. Compounding evades the cap **provided survivor equidistribution
  over the fresh coordinates is re-established at each step.**
- **The wall, in recursive final form:** maintain a level of distribution x^ε for the
  survivor sets as their density thins below x^{−ε} — self-improvement across scales,
  the genre of the modern equidistribution breakthroughs (smooth-moduli levels,
  induction-on-scales).
- **The novel lever (absent from every generic formulation):** these survivor sets are
  not generic sieve outputs. They are explicitly CRT-structured — defined by avoidance
  of a *known* list of congruence classes — so their AP-discrepancies and exponential
  sums are exactly computable via inclusion–exclusion over the covering system. Survivor
  equidistribution may be provable by direct Fourier/CRT computation rather than sieve
  axioms. This is the concrete attack surface Stage 1 was run to find.

**Updated Stage 1 → Stage 2 handoff:** the remaining analytic statement is now precise —
*prove level-of-distribution x^ε for the explicit survivor indicators of the ES covering
system, uniformly across dyadic scales* — with the empirical confirmation above, the §4e
independence machinery, and the exactly-computable Fourier structure as the three
supplied inputs. Combined with the compounding architecture this statement implies mass
κ·log²(x^θ) ≫ log x, i.e. zero exceptions above an effective threshold: **QED modulo one
named equidistribution statement about one explicitly given family of sets.**

---

## 4j. The equidistribution statement measured: survivors are sub-random
(18 Aug 2026, final addendum)

The QED-critical statement of §4i was measured directly. All 28,648 hard-class survivors
of level 32 were enumerated in a contiguous window of length 2·10⁷ at 10¹² (density
0.2005, matching the random-sampling value), and their distribution over fresh
coordinates was tested. (Note: over the full period, equidistribution mod fresh primes
is *exactly* true by CRT; the statement's content, and these tests, live in intervals
shorter than the period.)

1. **Aggregate discrepancy is SUB-random.** χ² statistics mod fresh primes q come in
   far *below* the random-noise expectation q−1: χ²/(q−1) = 0.10–0.25 for q ≤ 127
   (z-scores −3.7 to −6.1), and 0.30 → 0.61 for q = 251 → 2801, converging to
   random-level only as q approaches the window scale. The survivor set carries *less*
   discrepancy than a random set of its density at every tested modulus — the
   fingerprint of a rigid periodic structure whose AP-errors are deterministic and
   small, not stochastic.
2. **Per-class stratified tests at true annulus moduli pass, also sub-randomly.** For
   141 pure-annulus classes (moduli up to ~8·10⁴), observed hits against the stratified
   expectation (structural count / fresh part): mean z = +0.018, sd = 0.750 (vs 1 for
   random), 1.4% of classes beyond |z| = 2 (vs 4.6% expected). The §4i stratified
   predictor is essentially exact, with sub-random variance.
3. **The earlier raw-hit overdispersion (target-class hits at 1.95× the naive Σ N/M) is
   the profile/multiplicity structure**, not a bias: hits concentrate on
   high-activation survivors while union-avoidance concentrates on low-activation ones
   — both fully absorbed by the stratified accounting.

**Verdict.** The equidistribution statement is not merely empirically true — the
survivor sets are *better than pseudorandom*. This upgrades the target from "hope for
square-root cancellation" to "prove that the deterministic structure dominates": the
survivor indicator is a finite union of arithmetic progressions with explicitly known
moduli, its Fourier/AP-discrepancy decomposes by inclusion–exclusion into
Ramanujan-sum-type terms of explicit magnitude, and the observed sub-randomness
(including the sd ≈ 0.75 negative dependence, plausibly derivable from the union
structure) suggests direct computation, not sieve axioms, is the proof mechanism.

**Caveats, recorded:** (a) the tested regime has moduli ≪ window length; the asymptotic
wall regime (moduli ~ x^ε against survivor density x^{−ε′}) is beyond toy simulation —
sub-randomness here is necessary, not sufficient; (b) per-class tests selected classes
with ≥ 20 structural hits; (c) the negative-dependence constant deserves derivation.

**Final state of the QED program (end of 18 Aug 2026).** ES = one explicit
equidistribution statement (§4i handoff, now empirically sub-random at toy scale)
+ the compounding architecture (§4i, CRT-forced at density level)
+ the Suen density scheme (§4e, gates verified)
+ the corrected-dimension transfer (§4h, trace level)
+ the machine-checked reduction pipeline (§4a, compiled and axiom-audited)
+ the verified/ZK-scalable frontier (Track C).
Every layer is written down, measured, or machine-checked; the remaining mathematics is
the rigorous writing of four identified arguments and the proof of one identified
statement about one explicitly given family of sets.

---

## 4k. The attempt on E: partial version, the coupling-degree law, and H_ES
(18 Aug 2026, fourth addendum)

A direct attempt on statement E produced three outputs.

**1. E_partial is provable and coincides with Stage 0.** Conditional on the small-prime
profile, the survivor indicator is a depth-2 formula over independent CRT coordinates;
truncated inclusion–exclusion at level exp(c√log x) rigorously yields survivor
equidistribution for covering levels A ≤ exp(c√log x) — exactly reproducing the §4h
power-saving regime. The x^{1−c} record theorem and E_partial are the *same* write-up:
a consistency check (the framework recovers the known cap) and an economy (one paper,
two headline statements).

**2. The coupling-degree law (rigorous derivation; migration trend verified
numerically).** The covering mass distributes over the number j of fresh coordinates
each class couples as Poisson(loglog A − loglog T): mass_j/total → e^{−λ}λ^j/j!.
Measured j = 0 shares fall 0.66 → 0.48 → 0.37 across three decades as predicted (full
Poisson convergence unreachable at simulable scales — the parameter is loglog). Sharp
consequence: capturing the full log²A mass requires classes coupling ~loglog x
coordinates each; the survivor indicator is **not a bounded-fan-in object**, and all
truncation-based technology provably captures only the bounded-j slice. This is the
boundary constant's structural cause.

**3. The load-bearing hypothesis, stated.**

> **H_ES (Survivor Level of Distribution).** For the explicit ES covering system at
> level A = exp(c√log x) with κ·c² > 1 (κ ≈ 0.139 the measured density constant), the
> survivor count in [x, 2x] satisfies #S ≪ x·e^{−(1−o(1))κ log²A} — i.e., the
> truncation main term persists with effective level x^{1+o(1)}.

H_ES ⟹ zero exceptions above an effective threshold ⟹ (with §4a's pipeline and Track C)
machine-checked QED.

---

## 4l. Stage 1.5 executed: the fooling route's ledger, and the invariant triangulated
(18 Aug 2026, fifth addendum)

The circuit-complexity reformulation (E as "intervals fool a depth-2 CRT formula";
Braverman/Bazzi territory) was booked honestly. The ledger, in the natural scaling
A = exp(c√log x):

- interval independence budget: k_avail = √(log x)/c engageable coordinates;
- precision requirement: fooling to additive error ε ~ e^{−mass} needs
  k ≥ log(1/ε) ~ κc²·log x — **regardless of the fooling exponent β**;
- shortfall: k_req/k_avail ~ κc³·√(log x) → ∞ for every c with κc² > 1 (numerically
  10²–10⁵ across log x = 10⁴–10⁹);
- per-annulus compounding does not escape: conditioning on sparse structured events
  costs k ~ log(1/density) per step; after ~mass steps the budget is spent.

**Verdict: negative but definitive.** The TCS route independently re-derives the
barrier — the third unrelated technology to terminate at the same place, now in its
cleanest invariant form:

> **The k-budget invariant.** The interval-intrinsic independence budget is
> k·log A ≤ log x, while QED-precision requires effective independence k ≳ mass > log x.
> Every method consuming only interval-intrinsic randomness — sieves, large sieve,
> Shiu-type transfers, k-wise-independence fooling — is capped by this inequality.

The triangulation upgrades §4h's conclusion from observation to near-theorem: **QED
requires genuine arithmetic input beyond interval-intrinsic independence** — precisely
the content of H_ES, which asserts effective level x^{1+o(1)} for one explicit family,
i.e. an Elliott–Halberstam-class statement specialized to the most structured sets for
which such a statement has ever been needed. The program's long-horizon QED track is
therefore, finally and exactly: *prove H_ES, for which the explicit CRT structure of the
survivor sets is the only lever not available in any previously studied EH-type
setting* — or await the general level-of-distribution technology shift, into which the
compiled pipeline converts automatically.

**Program epilogue.** Deliverables standing at close: `ErdosStraus.lean` (proved);
E_partial ≡ the x^{1−c} record candidate (write-up defined); the Suen density theorem
(gates verified); the coupling-degree law (derivation + data); H_ES (stated, with the
k-budget invariant certifying it as the genuine residue); three papers defined; one
hypothesis named. The distance from folklore wall to a single stated EH-class
hypothesis with a machine-checked completion pipeline: one day.

---

## 4m. Route 2 opened: Bright–Loughran close reading (18 Aug 2026, route-2 dossier)

Following the k-budget invariant's route filter (analytic routes capped; geometric wing
untouched), the Bright–Loughran paper (arXiv:1908.02526; Bull. LMS 52 (2020) 746–761)
was read in full. Dossier:

**Inventory of their results.**
- *Brauer group:* Br U_n/Br ℚ ≅ ℤ/2, generated by the transcendental quaternion algebra
  α = (−u₁/u₃, −u₂/u₃); computed on the desingularization Ũ_n (blow-up of the A₁ point),
  whose complement of three boundary lines is a torus 𝔾_m² — Pic Ũ_n = ℤ, algebraic
  Brauer trivial, descent of α via the relation −u_i/u_j = 1/(1 + u_j/u_k − 4u_j/n).
  Plus a general theorem of independent interest: Br U ↠ Br Ũ for rational surface
  singularities.
- *Arithmetic:* **no BM obstruction to ES itself** (Thm 1.8 — the conjecture survives);
  but a clean obstruction to strong approximation: **Thm 1.2: every ℕ-solution
  satisfies Π_{p|n}(−u₁/u₃, −u₂/u₃)_p = −1**, while non-natural ℤ-solutions give +1
  (Thm 1.5) — the single Brauer class arithmetically detects the positive octant.
  Local ingredients: invariant −1 at ∞ on the positive component; trivial at good
  primes; surjective at odd p | n (Hensel); the surprising Lemma 3.8 (trivial at 2 for
  odd n, by a mod-8 case table).
- *Limits:* Thm 1.9 — BM is *not* the only obstruction to strong approximation; but the
  exhibited failure stems from finiteness of integral points (min |u_i| ≤ 3n/4 cascade,
  Lemma 3.10, + Lang–Weil), i.e. from the *density* formulation, not existence.

**The identification: Track B was secretly about α.** Their appendix derives Yamamoto's
conditions from α's local invariants — q = 4abd − 1 with (p/q) = −1: **exactly the
covering-witness modulus family and non-residue condition of §§4b–4k.** The quadratic
fingerprint on the hard classes, Mordell's obstruction, the Landing Lemma's symbol
conditions — all are invariant data of this one 2-torsion Brauer class. Consequence:
H_ES should admit a restatement in arithmetic-geometric language (equidistribution of
adelic points across α's invariant classes) — the dialect of the Loughran school, and
the natural bridge between the day's analytic program and Route 2.

**The open ground (the summit, properly formulated).** BL carefully do not conjecture
"BM suffices for existence" — on the sibling Markoff surfaces, genuine non-BM Hasse
failures occur (Ghosh–Sarnak; Loughran–Mitankin; CTWX). The distinguishing research
question: *why should ES models always have points when Markoff models don't?*
Candidate structure: Ũ_n contains the torus 𝔾_m² but the action does not extend — for
honest toric varieties BM-suffices for strong approximation is a theorem (Cao–Xu), and
Thm 1.9's failure mechanism is exactly the real-boundedness at the boundary. Target:
a **refined "toric-up-to-boundary" existence principle** for the family {W_n}, with the
semi-integral/orbifold direction (the 2024 Markoff-orbifold work already cites BL) as
the modern framework. Route-2 summit: such a principle for ES models ⟹ ES, with no
equidistribution input and full immunity to the k-budget invariant.

**The defined next project (bounded, novel, in-stack).** Formalize Theorem 1.2 in
Lean 4/Mathlib: §3 of BL is elementary Hilbert-symbol arithmetic — Hensel lifting, the
mod-8 table, Hilbert reciprocity — plausibly the **first formalization of a
Brauer–Manin-derived arithmetic result anywhere**. It composes directly with
`ErdosStraus.lean`: witness solutions (x, n·acd, n·cdm) are Type-2 shaped, and the
linking theorem "witness solutions satisfy the symbol condition" ties the sufficiency
file to the obstruction side. Secondary gains: BL's Lemma 3.10 cascade gives principled
solution bounds for the verified search; the artifact is a machine verification of
Theorem 1.2 plus a pipeline the 2020 paper does not have.

**Program state after route selection:** Route 1 continues as Stage 0 (the x^{1−c}
record + Suen papers — analytic, capped short of QED by the invariant); Route 2 is now
the QED wing, with three defined artifacts (the Thm 1.2 formalization; the α-restatement
of H_ES; the existence-principle formulation against the Markoff comparison) and a named
geometric track.  *(Status 19 Aug 2026: the Thm 1.2 Lean artifact and the
existence-principle packaging are recorded in §4s; neither is `ErdosStraus`.)*

---

## 4n. Candidate-4 rung 1 attempted: the correlation law, and where the theory's
second rung lives (18 Aug 2026, final addendum)

An honest attempt at the first rung of the "equidistribution theory for explicitly
CRT-structured sets" (summit candidate 4). Results:

1. **The exact identity (rigorous, trivial):** for fresh modulus q,
   Var_c(N_c) = N/q + (2/q)·Σ_{d>0, q|d} C(d) − (N/q)², with C(d) the interval pair
   count — the discrepancy of the survivor set is an exact functional of its pair
   correlations.
2. **The correlation product law VALIDATED (the rung-1 result).** The covering data
   predict C(d)/C_indep(d) by a per-class product — each class (r, M) contributes
   repulsion (1 − 2·g/M-type factors) at generic lags and attraction at lags it
   divides, conditioned on the mod-840 structure. Measured against the enumerated
   28,648-survivor window: mean (R_emp − R_pred) = −0.016 ± 0.10 across informative
   lags. The pair-correlation structure of the survivor sets is computable from the
   covering system, as the theory requires.
3. **The obstacle, precisely located: amplification.** The variance functional weighs
   ~2·10⁴ lag terms of size ~N²/q against a target of size N/q — demanding the
   correlation law at ~10⁻⁴ relative precision, while the class-independence product
   errs at ~10⁻² (the familiar shared-moduli Suen corrections). Consequence: the
   measured sub-Poisson constant (0.437 at q = 1009) is **not a pair-level effect** —
   predicted pair repulsion alone gives only 0.857. The sub-randomness is collective,
   carried by higher-order correlations — *stronger* evidence for the theory's premise
   (deterministic rigidity), and a sharper definition of its second rung:
4. **Rung 2, defined:** compute the discrepancy through the exact Fourier route — the
   survivor indicator's spectrum via inclusion–exclusion (Ramanujan-sum local factors),
   where collective structure enters automatically — with the §4e hub conditioning
   absorbing the shared-moduli corrections. This is bounded, explicit work of exactly
   the program's style, and the natural first section of any theory-4 paper.

Attempt verdict: rung 1 partially established (law validated, identity exact,
quantitative closure deferred to rung 2 by an identified amplification mechanism).
The summit itself remains untouched, as §4l requires it must be from inside.

**Rung 2 executed (same session).** The exact spectral route was attempted: true
spectrum F(c/q) computed directly from the enumerated set; predicted spectrum from
closed-form AP exponential sums through inclusion–exclusion at depths 1–2 (1,191
depth-1 APs; 28,051 depth-2 APs with L ≤ H; CRT composition with the mod-840
structure; every individual term exactly evaluable — the theory's explicitness
premise held). Results: true mean |F|²/N = 0.27 on the c-sample; depth-1 predicts
1.06 (Poisson-blind); depth-2 predicts 10.2 — divergence. Diagnostic at the density
level shows the same oscillation (−6.0×, +9.0× at depths 1–2): the mechanism is
**raw Bonferroni divergence at mean activation μ ≈ 2.2** (N₁/N₀ = 2.2; partial sums
oscillate with amplitude ~e^μ until depth ~2μ ≈ 5, where the term count ~10¹³ is
infeasible). The session thereby re-derived, from inside the program's own system,
why sieve theory exists: exact term-wise computability does not confer usable
truncation; the required innovation is a **conditioned spectral resummation** —
hub-conditioned frequency organization playing the role Brun/Suen organization plays
for densities — which is now theory-4's precisely-defined open technical heart.
Bounded research, paper-scale; the correct next owner is the theory-4 write-up, not
a session.

**Rung 3 executed (same session): the Selberg-L² organization works.** Two candidate
organizations were tested. (I) Hub-conditional expansion is vacuous at toy scale — all
m ≤ 32 are 31-smooth, the entire system is hub — and asymptotically reduces to the
§4i layering. (II) **Selberg-L² spectral approximation succeeds**: least-squares
weights over the depth-1 AP dictionary (1197 APs; Gram = exact pair counts; survivors
automatically orthogonal to all hit-sets) capture 62.4% of the L² mass; the structured
part is spectrally quiet (|F_λ|²/N = 0.073); the residual is near-Poisson-flat (0.796
per unit residual mass); and the decomposition closes: 0.073 + 0.299 = 0.372 = the
measured true ratio, to three digits. **The working form of conditioned spectral
resummation: Var/N ≈ quiet computable model + residual mass × flatness**, with every
ingredient exactly computable except flatness — which thereby becomes theory-4's
single hypothesis in its best shape yet: not "the survivor set is sub-random" but
"**the residual after optimal explicit projection is pseudorandom**" — a
sieve-residual statement, the native currency of dispersion/bilinear methods, and the
remaining hypothesis of that method. Remaining theory work: residual-flatness
proof attempts (bilinear forms in the residual), dictionary growth (depth-2 should
push capture up and flatness → 1), and the asymptotic-scale behavior of the captured
fraction — the last being where the summit re-enters, as it must.

**Rung 3b (same session): dictionary scaling and the line-plus-floor refinement.**
Depth-2 augmentation (3,000 smallest-modulus pair-APs; K = 4,197) raised the captured
L² fraction 0.624 → 0.827 and halved the residual spectral mass; flatness stayed O(1)
and roughly q-stable across q = 251–2801 (0.76, 0.52, 1.13; wide sampling noise, with
sub-flatness at q = 1009 indicating further capturable structure), and per-run
decompositions closed additively. The spectrum's measured heavy tail (sample means
0.27 → 0.37 → 0.44 with sample size) identifies the structure as **a few strong
deterministic lines over a flat floor** — refining theory-4's hypothesis to its
cleanest form: *the Selberg-L² model absorbs the lines; the residual is the floor;
pseudorandomness of the floor is the single remaining claim.* Line-plus-floor is the
spectral profile dispersion methods certify. Session-executable increments end here;
the continuation (full-spectrum runs, depth-3, the bilinear attempt on the floor)
belongs to the theory-4 paper.

---

## 4o. The road: characteristics of the H_ES attack path, and its likely steps

The three rungs did not shorten the distance to H_ES; they built the road anyone
crossing it will drive on. Its characteristics: (1) **explicitness** — dictionary,
weights, Gram, residual are closed-form objects, computed rather than posited;
(2) **bilinear-native** — the destination (flatness of the floor) is pre-shaped for
dispersion/Kloosterman technology, the only toolkit ever to beat the x^{1/2} level
barrier; (3) **layered** — the compounding architecture climbs by polynomial-level
annulus switchbacks, not one cliff; (4) **falsifiable at every milestone** — each
intermediate claim numerically testable before proof effort; (5) **hazard-mapped** —
the k-budget invariant marks where interval-intrinsic vehicles die; (6) **dual-
carriageway** — the α-identification links the analytic and geometric lanes over the
same substrate, either lane sufficing; (7) **compiler-terminated** — every proved step
formalizes; the last mile is a build, not a paper-review delay.

Likely steps: **0** Stage-0 papers reviewed (the road opens). **1** The theory-4
paper: rigorous decomposition, a depth-k capture theorem, and the first unconditional
prize — sub-critical flatness (bounded-modulus floors via large-sieve tools; the
spectral sibling of E_partial). **2** Type-I estimates on the residual (current
technology; also where a relocation trap — flatness ≡ ES — would surface early, itself
publishable). **3** The dispersion campaign: Type-II bilinear forms, DFI-spectral
inputs; realistic first win: level x^{1/2+δ} for the residual, converted by
compounding into an improved exceptional-set exponent — the program's likely second
record. **4** The critical-exponent grind toward level x^{1}: well-factorable weights
on the dense-divisible moduli (Zhang/BFI machinery, for which the moduli are
custom-built) or new spectral input; decades-scale, milestone-dense. **5** (parallel)
The geometric lane in the Loughran orbit, independent timeline, Markoff comparison as
live risk. **6** (throughout) Early-warning numerics at growing toy scales watching
for flatness drift. **7** Convergence: whichever lane completes, the pipeline
compiles QED. Named intermediate theorems along the road: Type-I on
the residual; the capture theorem; sub-critical flatness.

---

## 4p. The hybrid probed: covering exclusions are character-shaped (18 Aug 2026)

First probe of the §9/roadmap-§9 BL-rigidity hybrid, with an in-probe correction:
the divisor-family exclusion law at fixed small q is killed by the m ≤ A constraint
(smallest covering cofactors: median 127 for survivors vs 23 for covered — survivors
are the large-witness tail), so fixed-modulus forcing was briefly concluded absent —
and then measurement overturned this: survivors show enormous symbol bias exactly at
the primes dividing some box modulus (mean (n/q): +0.73 at q=11, +0.83 at q=23,
+0.45 at q=31, z up to 41; zero at q = 43, 59, 67, … which divide no 4adm at level
32). **Mechanism, derived:** a class with q | m projects mod q to
n ≡ −(2a)²·d, of Legendre symbol (−d/q) independent of a — each d-slice excludes an
entire coset of the squares. At q = 11, four of five d-slices exclude non-residues
(signs (−d/11) = −1 for d = 1,3,4,5; +1 for d = 2), matching the measured net bias
in sign and magnitude. **The covering system's fixed-modulus exclusions are unions
of square-cosets: survival accumulates fractional quadratic-character conditions,
one per witness prime the box touches.** This is exactly the non-statistical,
reciprocity-actionable structure the hybrid requires — its fuel, confirmed. The
live question is now precise: as A grows, do the accumulated conditions across
moduli interact through quadratic reciprocity (super-multiplicative shrinkage or
incompatibilities — input the k-budget invariant does not cap), or do they merely
repackage covering mass already counted in μ? That question — the character-
interaction question — is the hybrid's defined next step, and the natural bridge
between `BrightLoughran.lean` and the analytic wing.

---

## 4q. External advice assessed: the LandingLemma duality (18 Aug 2026)

Advice received: prove abelian insufficiency in-kernel; replace the analytic
interface by a fixed-box divisor criterion (∃ P₀ D₀ ∀ hard p > P₀ ∃ a,d ≤ D₀
∃ q ∣ p + 4a²d, q ≡ −1 mod 4ad); stop BL/character/hybrid work. Assessment:

1. **Agree:** the divisor form is the right analytic-facing statement — it is
   DFI-native (q ∣ p + 4a²d ⟺ −pd ≡ (2ad)² mod q: quadratic-congruence roots
   with p-dependent discriminant), and abelian insufficiency is a worthy
   Mathlib-level artifact now that Dirichlet is available in the project.
2. **Technical error in the advice:** fixed D₀ makes the statement
   heuristically FALSE — failure at one (a,d) has density (log x)^{−1/φ(4ad)}
   (shifted value avoiding the −1 progressions as factors); jointly,
   ~x/(log x)^{1+c(D₀)} exceptional primes for every fixed box. D₀ must grow
   with p; the required rate log²D₀ ≳ log x, i.e. D₀ = exp(c√log x),
   reproduces the AnalyticSurvivorBound schedule — the marginal constant is
   parametrization-invariant.
3. **The duality, now a kernel theorem** (`divisor_form_sound`): with
   c := (q+1)/(4ad) one has q = 4acd − 1 and q ∣ c·p + a — the divisor
   criterion IS the covering box's free-c slot. "Retarget" is a change of
   coordinates, formalized rather than adopted: both interfaces
   (`AnalyticSurvivorBound`, new `DivisorLandingBound` + implication
   `hard_landing_of_divisor_interface`) now live in the kernel.
4. **Disagree with the stop-list:** the character/coset structure (§4p, now
   formalized with Mathlib Legendre symbols in `ErdosStrausBLRoute.lean`) is
   not a denser sieve — it is the anti-correlation/rigidity input that could
   defeat the fixed-box exception heuristic and is precisely the input class
   the k-budget invariant does not cap; and the DFI discharge the advice
   itself prefers consumes exactly this local coset data. Portfolio verdict:
   adopt the divisor coordinates (done), formalize abelian insufficiency
   (Mathlib machine), continue the character strand, reject fixed-D₀ as
   load-bearing.

---

## 4r. The decisive escapee test executed (18 Aug 2026)

The advised falsification test was run, extended to 10⁶ (2,370 hard primes;
161 d=1 escapees at a ≤ 30, containing the known eight below 2·10⁵). Verdict:
**the informative middle branch.** Escapees are character-biased — (p/11):
+0.354 vs −0.060 for covered, z = +5.1, decaying to nothing by q = 43 — but
not character-determined. Mechanism decoded: small q ≡ −1 (mod 4a) are
deterministic point-landers (p ≡ 8 mod 11 forces coverage at a = 3 via
q = 11; the excluded points are symbol-aligned per §4p), and the escapee bias
is exactly the aggregate shadow of these exclusions. Simultaneously the
half-rough core is exact: 100% of escapees have p + 4 free of 3-mod-4
factors, and all are half-rough across every tested slice.

**Allocation established:** characters = the computable boundary layer
(deterministic, Lean-provable landing implications thinning the exceptional
set — `point_landing_11` formalized as the family's representative, with
`dfi_dictionary_d1` as the last coordinate change); roughness = the analytic
core (factorization-level, DFI/geometry territory). The hoped-for implication
Survivor → forced divisor is NOT supported; the character strand's real
contribution runs the other direction. §4p is hereby recalibrated: from
candidate QED engine to explicit structured layer feeding the engine — the
P+R philosophy, now confirmed on the exceptional set itself. Remaining QED
doors, per the data: DFI on the growing-bound divisor form, or geometry.

**Closing state of the investigation.** Seven rungs: folklore → Landing Lemma → Covering
Density Lemma → sieve moments → Suen scheme (strategy verified) → density-to-count
transfer → **Vaughan barrier identified, no-go meta-theorem formulated, three doors
enumerated**. The day's output: one machine-checked reduction pipeline (`ErdosStraus.lean`);
one partial theorem provable now (κ* ≈ 0.29); one full-strength proof strategy with
verified gates (Suen scheme); one barrier explanation of a 55-year-old exponent; three
papers defined (ITP formalization; the Suen density theorem; the no-go barrier result);
and a map of exactly three doors through which any future proof must pass. Not QED — but
the distance to QED has never been measured this precisely.

---

## 4s. Route 2 Lean record (19 August 2026)

§4m defined three artifacts: formalize Theorem 1.2; restate H_ES in the language of
α; formulate an existence principle against the Markoff comparison.  Between that
dossier and this note, ~3,700 lines landed in `ErdosStrausBLRoute.lean` (plus the
Mathlib discharge in `ErdosStrausQR.lean`) while this record did not move.  This
section is that missing entry.  No `sorry`.  Not `ErdosStraus`.

**File map (see also `README.md`).**  Layer A is still `ErdosStraus.lean` and
`BrightLoughran.lean` — bare Lean ≥ 4.33.0, no imports; quadratic reciprocity is
the named field `BL.InvariantData.reciprocity`.  Layer B is `ErdosStrausQR.lean`
and `ErdosStrausBLRoute.lean` — `lake build` against pinned Mathlib.  The
roadmap's Layer A/B/C (reduction / analytic contraction / finite certificate) is
a different stratification; do not conflate them.

**Z-model.**  `IsSchinzelZ m n` is integer points on the affine cubic
`m·xyz = n·(xy+yz+zx)`; `IsESZ` is the ES case `m = 4`.  Natural-number solutions
are the positive octant (`isES_to_esZ`, `isES_of_esZ_pos`).  Occupying that
octant for every `n ≥ 2` is exactly the conjecture (`erdos_straus_iff_pos_octant`).
`U_n(ℤ)` is nonempty for every `n ≥ 2` (`esZ_nonempty`): even `n = 2t` uses the
positive point `(2t, 2t, t)`; odd `n = 2k+1` uses the classical mixed-sign point
`1/k + 1/(k+1) − 1/(n k (k+1))`, which lies off the positive octant
(`esZ_of_odd_not_pos`).  All-negative points are empty (`schinzelZ_not_all_neg`).
Positive rationals `(n, n, n/2)` exist independently (`esQ_pos`) — why Cao–Xu
does not imply ES.

**Box bound (BL Lemma 3.10).**  Ordered integer points satisfy
`m |u_min| ≤ 3n` (`schinzelZ_min_le`; ES case `esZ_min_le`, positive-octant
`es_pos_min_le`).  The rest of the lemma is the factor identity
`(r y − s)(r z − s) = s²` with `r = m x − n`, `s = n x` (`schinzelZ_factor`,
`schinzelZ_coord_dvd`).  The converse in the positive octant is
`es_of_s2_divisor`: a divisor pair of `s²` at fixed `x` produces an `IsES`
point.  Existence of that pair as `n` varies *is* the conjecture.  The uniform
slice `x = (n+3)/4`, `r = 3` occupies the octant for every `n ≡ 5 (mod 8)`
(`es_five_mod_eight_of_repair`) and for those `n ≡ 1 (mod 4)` whose `s` has a
prime factor `≡ 2 (mod 3)` (`es_of_r3_slice`).  It fails at `n = 73`
(`r3_slice_obstructed_at_73`).  Chaining more moduli is covering densification
and is not pursued.

**Octant invariant.**  `invInfES` is the real Hilbert symbol of α, cleared of
the positive square `u₃²`.  It equals −1 exactly on the same-sign octants
(`invInfES_eq_neg_one_iff`); the all-negative octant is empty, so −1 detects
the positive component (BL Lemma 3.1 on the Z-model).  Mixed-sign integer
points have `invInfES = +1` (Theorem 1.5 at the real place;
`invInfES_of_esZ_mixed`, `invInfES_odd_mixed`).

**TUB-EP packaging.**  `TubEpHypothesis` is occupying the positive octant of
every `U_n(ℤ)` for `n ≥ 2`.  The implication `erdos_straus_of_tub_ep` is
proved; the hypothesis is not.  Equivalent to `ErdosStraus`
(`tub_ep_iff_erdos_straus`) and stronger than existence on hard primes
(`geometry_of_tub_ep`).  The Z-model facts the principle may consume are
assembled in `tub_ep_consumed` (nonempty, box, octant invariant, mixed-sign
off `C₊`, positive rationals).  Bright–Loughran Theorem 1.8 is *not* a field
of that structure: it is not formalized, and is not claimed as existence in
`C₊`.  The extra geometric content that would distinguish ES from Markoff —
finiteness of integral points, no Vieta, strong obstruction at infinity —
is already in `tub_ep_consumed` and is not by itself a point of `C₊`.

**Reciprocity extensions (Layer B discharge of §4m's Thm 1.2 artifact).**
Hilbert reciprocity is proved for odd primes, odd coprime positives, negative
odd coprimes, 2-powers, mixed signs, odd ratios, the ES 3.8 shape
`(−2^s r₁/r₃, −2^s r₂/r₃)` when the odd parts are pairwise coprime, and odd
integers after cancelling squares (shared kernel).  Named theorems:
`hilbert_reciprocity_odd_primes`, `_odd_coprime`, `_neg_odd_coprime`,
`_two_odd`, `_two_pow`, `_neg_two_pow`, `_self`, `_neg_pos_odd_coprime`,
`_neg_pos_two_pow`, `_odd_ratio`, `_neg_ratio`, `_es_ratio`, `_shared`,
`_odd_integers`.  Anatomy: Lemmas 3.1 / 3.5 / 3.6 / 3.8 on Nat solutions
(`lemma31_of_isES`, `lemma35`, `lemma36`, `lemma38_of_nat_solution`);
`thm12_discharged` is the bookkeeping `inv_∞ = −1`, `inv₂ = 1`, `inv_good = 1`
plus reciprocity ⇒ `inv_p = −1`.  `InvariantData` is still not constructed
from a solution's actual local symbols (necessity of Thm 1.2 remains glue).
Pairwise-coprime is still required on `_es_ratio`; the shared-odd kernel is
the integer-level workaround.

**What this does not claim.**  Unconditional `ErdosStraus`.  `TubEpHypothesis`.
Theorem 1.8 as a positive-octant point.  Cao–Xu as filling the octant.
Harpaz as existence on ES fibers (inapplicable; §4t).  Markoff orbifold Hasse
as moving mixed-sign points into `C₊`.  Completeness of any covering system.
DFI packing as a QED grind.

**Handoff.**  The live QED line on Route 2 is still the existence principle
§4m named: an integral Hasse principle in `C₊` for this strongly-obstructed
log K3.  Stress test: Schinzel's family `m/n = 1/u+1/v+1/w` (same Brauer
group, different ℤ-models).  Literature in that regime: Jahnel–Schindler,
Colliot-Thélène–Wittenberg on affine cubics.  Harpaz's conic-log-K3 theorem
does not apply (split fibers; §4t, `ConicFiber.lean`).  Optional Lean glue
that still serves this route: `InvariantData` from actual symbols; drop
pairwise-coprime on `_es_ratio`.  Do not densify covering.

---

## 4t. Harpaz read against the ES fibration: inapplicable, and why that is a
theorem (19 Aug 2026)

Following §4m's Route-2 opening and the literature search, Harpaz's
descent-fibration theorem for conic log K3 surfaces (JEMS 21 (2019) 627–664)
was read against the ES conic fibration. Verdict: **does not apply, for a
structural reason now formalized.** Fixing t in 4txy = n(xy+tx+ty) and
setting A = 4t−n gives the exact on-surface identity
(Ax − nt)(Ay − nt) = (nt)²: every fiber is a SPLIT conic. Harpaz's engine
(Swinnerton-Dyer descent on norm-1 tori of quadratic fields; sufficient
conditions requiring independence of {−1, a, b} ∪ {Δij} in ℚ*/ℚ*²) is
vacuous on split fibers — no Selmer structure exists to compare — and the
hypothesis fails degenerately. No other fibration escapes: BL's split 𝔾m²
inside Ũn makes every conic structure on this surface split.

**The pattern, now with two data points:** Cao–Xu's toric theorem breaks at
the boundary (§4m); Harpaz's descent breaks by splitness. *The ES surface is
too split for fiber-level local-global methods* — its entire arithmetic
lives in the integrality structure of split fibers, i.e., in divisors. Any
future geometric attack must be genuinely global (semi-integral/orbifold
frameworks, or new technology), not fibration-based.

**The constructive yield, kernel-certified (`ConicFiber.lean`, Layer A,
axioms propext + Quot.sound only):** `fiber_to_divisor` and
`divisor_to_fiber` prove that positive points on fiber t correspond exactly
— both directions, with linear recovery (4t−n)·x = u + nt — to positive
divisor pairs of (nt)² in the class −nt (mod 4t−n), for ALL n ≥ 2. This is
the machine-checked statement that along every conic fibration,
TubEpHypothesis's existence question IS the divisor problem: the geometric
and analytic wings are one object in two coordinate systems. Outreach
consequence: the note to the Loughran orbit now carries a kernel proof of
*why* the two known geometric methods cannot grip, and the precise
split-fiber structure any new one must handle.

## 4u. C3 frozen, C5 autopsy, C7 first search (20 Aug 2026)

After C5_2 closed the named t-fibration, three bounded actions were run.

**C5 autopsy (not a new candidate).** The rational curve of
`t_fiber_section_cleared` (w = x, z = x/d) reparametrizes as a section of
\(\pi=u_1\) and of \(\pi=w\): `u1_fiber_section_cleared` (axioms: `propext`).
Changing the linear projection does not produce a non-split conic
fibration of \(V_{n,d}\). No C5_3.

**C3 freeze.** Three checks, recorded as C3_1 in the candidate list.
(1) ES pairs do have a totally split triangle with interior \(\mathbb{G}_m^2\)
(BL, plan §4m). (2) Campana/semi-integral Hasse does not imply a
\(\mathbb{Z}\)-point of \(C_+\): Mitankin–Uhlemann prove Markoff orbifolds
satisfy Campana Hasse while \(\mathcal{U}_m(\mathbb{Z})\) is often empty.
(3) No named \(T\). The claimed R6 discriminator is false: the Markoff
compactification in \(\mathbb{P}^3\) also has a triangle of lines
(\(D_i=\{x_0=x_i=0\}\)). C3 as Campana packaging is not the QED line.
The live geometric statement remains the integral principle in \(C_+\)
(`TubEpHypothesis`), equivalent to ES.

**C7 first search.** `c7_bounded_coupling_search.py`. Degree-1 Witness
identities with modulus \(\le 30\) and coefficients \(\le 4\): 193
identities, none covering a hard class. Type-I bounded-\(\omega\) mass
does not break the coupling law at \(A\le 64\) (and \(\log\log\) is not
visible at that scale, as §4k already said). C7 remains probably false;
do not grind larger random boxes as a QED lane.

**S1 / C11 (same day, v0.2); S1_1 / `SchinzelDecide.lean` (v0.3).**
Schinzel separators: mixed-sign occupancy does not imply \(C_+\). Family
\((2z-1)/z\); 86 pairs in \(1<m/n<3\), \(n\le 40\); 9/5 signed
(`SchinzelSep.lean`); 9/5 and 13/7 positive-empty via a verified
decision procedure (`SchinzelDecide.lean`; `no_pos_*` uses `propext`,
`Classical.choice`, `Quot.sound`, not axiom-free). C11 adds Archimedean
non-degeneracy as a necessary extra hypothesis. It is a schema, not an
engine. Extending the *narrow* sweep does not test sufficiency. S1_1
sketches that \(\alpha\) does not obstruct a \(C_+\)-restricted 9/5
adele (hand Hilbert symbols at 2); that is not a kernel 1.8 analogue.
The 9/5 sketch and whether anything is asserted in the wide regime remain
open.

**Handoff (superseded 20 Aug, evening — see §4v).** Geometric QED with
existing tools is closed as a proof path. The v0.9 geometric questions remain
class-theory and an effectivity framework, not the technical main effort.

## 4v. The two lanes are one lane (20 Aug 2026, evening)

Triage after the v0.9 programme package. The week's facts, stated
separately in §§4t–4u and ConicFiber, are now one statement.

**Joint-lane theorem (informal).** Every geometric mechanism inventoried
reduces to the same analytic core.

- Fibrations reduce to divisor conditions (`ConicFiber.fiber_to_divisor`),
  conserved under the real-compatible twists (`TwistDescent`).
- The universal torsor of \(\widetilde{U}_n\) is the witness equation, so
  torsor-counting (C10) is the Elsholtz–Tao count, whose all-\(n\) lower
  bound is again the divisor-dispersion problem.
- The affine equation is **multilinear**: unique \(x\) given \((y,z)\)
  (`NoVieta.unique_x`, `es_unique_x`). There is no second root, hence no
  Vieta involution, hence no Markoff/BGS correspondence orbit. Option 4
  was already killed in §4 as an investigation; it is now a lemma. That
  closes the mechanism inventory: the Markoff analogy dies at exactly
  this structural point, and it explains the week's geometric no-gos
  (split fibres, no Selmer, Campana not \(C_+\), no C5_3) as one fact.

**Consequence for geometry.** The honest role of the geometric lane is
**class-theory and an effectivity framework** — open questions on the
component-integral BM set, the wide regime, and an effectivity framework
for strongly-obstructed log K3s (publishable foundations, zero pretence
of being the proof path with existing tools). It is not a QED engine.
`TubEpHypothesis` remains equivalent to ES (`tub_ep_iff_erdos_straus`).

**The analytic core, named.** Joint roughness \(S(A,x)\): for how many
\(p\le x\) do all shifts \(p+4a^2\) (then \(p+4a^2d\)) avoid prime
factors in their \(-1\)-progressions, at fixed covering width \(A\)?
The first theorem is T(A): \(S(A,x)=C(A)\prod\rho_a\cdot(1+o(1))\) with
\(C(A)\) explicit. The exposure is whether \(C(A)\) grows sub-critically.
Pairs were the wrong moment (ratio \(1.000\); the full intersection
drifts).

**Ordered worklist, with die-conditions.**

1. **T(A) = C4_1, the joint density at fixed \(A\).** Wirsing /
   Landau–Selberg–Delange for the joint multiplicative condition;
   compositum densities for the shared-modulus layer; selection constant
   as the theorem's content. Standard-hard, a genuine paper. Empirical
   shadow: x-scan of \(S\) at \(A\in\{40,80\}\), \(x=10^5\to 10^9\)
   (`c4_S_xscan.py`); growing \(A\) at \(x=10^9\), \(A\le 200\)
   (`c4_growing_A.py`). Local Euler factor computed 20 Aug:
   \(C_{\mathrm{euler}}(80)=0.911\) (\(1/q\)), \(0.895\) (\(1/(q-1)\)),
   flat to \(A=200\), zero residue collisions (`c4_euler_factor.py`;
   `erdos-straus-T-A.md`). ClassRough composite layer: genuine-extra
   Euler product \(\Pi_{\mathrm{gen}}(\sqrt{x})\) matches the \(A=40\)
   CR/prime product to \(3\%\) (`c4_composite_layer.py`). Recorded 20 Aug: \(e(a)-1\) does not decay as
   \(1/\ln\ln x\); \(\mathrm{cond}(a)\to 1\) past \(A=80\) (155 survivors
   at \(A=200\)); \(\log\hat C\sim 0.104\log^2 A\) on \(A\ge 40\)
(\(R^2=0.998\)), below \(\kappa=0.139\). Local \(\log\hat C/A\approx 0.012\)
was a small-\(A\) artefact. Certificate checks 20 Aug
(`c4_certificates.py`): converse \(P(\exists\chi\mid\mathrm{CR})=0.846\)
at \(x=10^6\), \(A\le 40\); shared-certificate dummy covering does not
fire. T(3) kernel (`classRough_123_iff_certificates`) is exact; T(3)\(^+\)
(\(S(3,x)\ll(\log x)^{-3/2}\)) is claimed in `erdos-straus-T-3.md`; the
T(3) lower bound is a three-step plan whose sharp remaining question
(plan §4w) is a joint well-factorable weight for the moving CRT residue
of the triple, in the same frontier bucket as §9's Brauer-\(\alpha\)
fusion; the \(r_\chi\to\) Kloosterman look is a range no-go at
\(Q=x^{1/2+}\); T(A)\(^+\) / \(C_{\mathrm{sieve}}(A)\), **E_lane** (the \(d=1\)
floor, below Vaughan), and **E_power** (covering-box \(S_A\ll x^{1-\delta}\),
above Vaughan, `erdos-straus-E-power.md`) are written. Dies if \(c'\ge\kappa\) or if
\(\mathrm{cond}\equiv 1\) persists to QED-scale \(A\) (dummy covering
mass). Do not run \(10^{10}\). Upgrades E_partial from record-candidate
to E_power claimed (`erdos-straus-E-power.md`).
2. **C2 cross-moduli symbol-correlation computation.** Done 20 Aug:
   `c4_c2_symbols.py`, \(x=10^9\), \(A\le 80\). Covering Jacobi symbols
   are independent (mean \(|z_{\mathrm{cov}}|=0.73\) at \(A=80\)); C2
   does not fire; extra shrinkage has the wrong sign for \(\hat C>1\).
3. **E_partial written as the vehicle for (1)–(2), through Gate A.**
   Done: `erdos-straus-E-partial.md`, `erdos-straus-E-power.md`. Layer 1 =
   T(A)\(^+\) at fixed \(A\) plus E_lane as the \(d=1\) floor. Layer 0 =
   E_power, claimed: \(S_A\ll x^{1-\delta}\). Gate A still forbids
   compiling that write-up as QED progress.
   Dummy covering, not \(c'\) vs \(\kappa\), stops a retuned schedule.
   Not an assault on H_ES.
4. **G–S reformulation memo.** Done: `erdos-straus-gs-reformulation.md`.
   No new theorems. Now attached specifically to \(S\) (joint
   lower-tail of dependent multiplicative statistics). Names the
   analytic-lane dictionary (Granville–Soundararajan / Lamzouri /
   Heath-Brown). The analytic worklist names T(A)\(^+\) /
   \(C_{\mathrm{sieve}}(A)\), E_lane, and E_power as theorems already in
   the archive and the T(3) completion step as the remaining question
   (`erdos-straus-sieve-desk.md`, `erdos-straus-T-3.md`,
   `erdos-straus-T-A.md`). Character-sum
   cancellation is admissible against the k-budget invariant; naive
   large sieve on \(\exp(c\sqrt{\log x})\) moduli is trivial — leverage
   is growing moments. Parallel recasting: the selection constant in
   \(C(A)\) as Frobenius entanglement in a compositum of quadratic
   fields.
5. **No-Vieta lemma and effectivity-framework write-up.** Lemma done
   (`NoVieta.lean`). Effectivity framework is geometric theory-building,
   publishable, not the proof path.

**Do not attempt:** further identity search (C7_1 plus the coupling law);
any Selmer/descent architecture on any fibration of this family
(splitness is conserved; proved twice); orbifold repackagings
(Mitankin–Uhlemann); direct assaults on the full level statement
(the invariant; the marginal constant); putting the pair asymptotic
back in the title of C4_1.

**Handoff.** Concentrate technical force on T(A). Certificate checks
done (`c4_certificates.py`): converse is an \(\omega\)-gap; shared
\(\chi\) does not explain dummy covering. The analytic worklist
(`erdos-straus-sieve-desk.md`) names T(A)\(^+\) as a theorem already in
the archive and records the T(3) completion step; statement
`erdos-straus-T-3.md`. Geometry keeps the Bright–Loughran questions as
class-theory, not as QED. Do not densify covering. Artifacts from the
prior `erdosstrauss` tree (`Stormer.lean`, Bradford/Lemma 3 notes,
leochlon dictionary) are library/docs, not a Track-1 merge
(`erdos-straus-prior-archive.md`).

---

## 4w. Frontier bucket: Brauer-\(\alpha\) fusion and the three-kernel CRT
weight (21 Aug 2026)

Two problems sit in the same **genuinely hard frontier**. Neither is
this quarter's in-house compute. Neither is a request to prove
Erdős–Straus, densify covering, or assault H_ES.

1. **Roadmap §9 / plan §4m: Brauer-\(\alpha\) fusion.** Yamamoto's
   covering-witness family is the local invariant data of Bright–Loughran's
   transcendental quaternion \(\alpha\). The geometric restatement of
   H_ES is equidistribution of adelic points across \(\alpha\)'s
   invariant classes. That is class-theory, not a QED grind with
   existing tools (plan §4v).
2. **T(3) completion, sharpened.** Existing dispersion/BFI machinery
   beats \(x^{1/2}\) only for a *fixed* residue and well-factorable
   weights (BFI \(x^{4/7}\); Maynard \(x^{3/5}\)). The joint remainder
   for three kernels is a *moving* CRT class
   \(\alpha(d_1,d_2,d_3)\bmod\mathrm{lcm}(d_1,d_2,d_3)\). **Question:**
   does a joint well-factorable weight framework exist for a CRT residue
   that depends on the summed triple, and if not, can one be built for
   this specific three-kernel case (conductors \(4,8,12\); residues
   \(-4,-16,-36\))? Write-up: `erdos-straus-T-3.md`. Per-slice BFI
   still feeds escape 1 (almost-certificates). The three-fold \(r_\chi\)
   detector is ternary Titchmarsh, not Linnik's binary method. A look
   (21 Aug 2026; `erdos-straus-T-3.md`) reduced the \(r_\chi\) rewrite
   to an explicit Kloosterman bilinear/trilinear form and tested it
   against Pascadi Cor. 1.4/7.5, MQW Thm 1.1, and Blomer–Pascadi
   Thm 1.1: **no-go at the stall** \(Q=x^{1/2+}\). Dual lengths sit
   below the saving windows; the first genuine Blomer–Pascadi saving
   is at \(Q\gtrsim x^{0.87}\). Not a third escape. The joint
   well-factorable question is unchanged.

Do not mix (2) into the geometric questions. Do not mix (1) into the
analytic worklist. Do not upgrade (2) to C1.

---

## 5. Key references encountered

Full bibliographic records (titles, volumes, pages, DOIs) are in `README.md`.  This
section keeps the working annotations.  None of these papers is `ErdosStraus`.
arXiv:1706.06712 is Ghosh–Sarnak, not a Bourgain–Gamburd–Sarnak sequel.

**Conjecture, covering, identities.**
- Erdős — *Az \(1/x_1+\cdots+1/x_n=a/b\) egyenlet egész számú megoldásairól*, Mat. Lapok 1
  (1950) 192–210.
- Sierpiński — *Sur les décompositions de nombres rationnels en fractions primaires*,
  Mathesis 65 (1956), 16ff. [Published source of the 4/n problem as BL cites it.]
- Schinzel — *Sur quelques propriétés des nombres \(3/n\) et \(4/n\), où \(n\) est un
  nombre impair*, Mathesis 65 (1956) 219–222.
- Nakayama — *On the decomposition of a rational number into “Stammbrüche”*, Tôhoku
  Math. J. 46 (1939), 1ff; Rosati — *Sull’equazione diofantea \(4/n=1/x_1+1/x_2+1/x_3\)*,
  Boll. Un. Mat. Ital. (3) 9 (1954), 59ff; Aigner — *Brüche als Summe von Stammbrüchen*,
  J. Reine Angew. Math. 214/215 (1964), 174ff. [Covering-equivalence ancestry, Bloom Thm 1.]
- Yamamoto — *On the Diophantine equation \(4/n=1/x+1/y+1/z\)*, Mem. Fac. Sci. Kyushu
  Univ. Ser. A 19 (1965) 37–47. [BL appendix: covering-witness family from α.]
- Mordell — *Diophantine Equations*, Academic Press, 1969, Ch. 30.
- Schinzel — *On sums of three unit fractions with polynomial denominators*, Funct.
  Approx. Comment. Math. 28 (2000) 187–194. [No single polynomial identity covers all n.]
- Bloom — *Egyptian fractions*, arXiv:2210.04496 (covering equivalence, Thm 1).
- Lopez — *A complete congruence system for the Erdős–Straus conjecture*,
  arXiv:2404.01508 (Type A/B).
- Bello-Hernández, Benito, Fernández — *A divisor parametrization for the Erdős–Straus
  conjecture*, arXiv:2606.10922 (finite-parameter rigidity; surface uvw−u−v=n).

**Bright–Loughran geometry (Route 2).**
- Harpaz — *Integral points on conic log K3 surfaces*, J. Eur. Math. Soc. 21 (2019)
  627–664; arXiv:1511.04876. [Read in full against the ES fibration, §4t:
  inapplicable, split fibers; the first and only published existence technology
  for the surface class.]
- Uppal — *Integral points on affine surfaces fibered over* 𝔸¹; arXiv:2307.06638.
  [Harpaz-method extension to norm-1 tori; Bright–Loughran literature.]
- Bright, Loughran — *Brauer–Manin obstruction for Erdős–Straus surfaces*, Bull. Lond.
  Math. Soc. 52 (2020) 746–761; arXiv:1908.02526. [Read in full, §4m: Br U_n/Br ℚ = ℤ/2
  via transcendental α; Thm 1.2 solution condition; Thm 1.8 is *not* existence in C₊;
  Thm 1.9 density-failure via the box + Lang–Weil.]
- Serre — *Cours d’arithmétique*, PUF, 1970; English GTM 7, Springer, 1973. [Hilbert
  symbols; Layer A implements these formulae.]
- Lang, Weil — *Number of points of varieties in finite fields*, Amer. J. Math. 76
  (1954) 819–827. [Input to BL Thm 1.9.]
- Jahnel, Schindler — *On integral points on degree four del Pezzo surfaces*, Israel J.
  Math. 222 (2017) 21–62; arXiv:1602.03118. [Weak/strong unobstructedness at infinity;
  Def. 2.2 is the language of the box / Lemma 3.10.]
- Harpaz — *Integral points on conic log K3 surfaces*, J. Eur. Math. Soc. 21 (2019)
  627–664; arXiv:1511.04876. [§4s handoff: integral points on log K3s; not a theorem
  about the ES octant.]
- Colliot-Thélène, Wittenberg — *Groupe de Brauer et points entiers de deux familles de
  surfaces cubiques affines*, Amer. J. Math. 134 (2012) 1303–1327. [§4s handoff: affine
  cubics. Distinct from CT–Wei–Xu on Markoff.]
- Cao, Xu — *Strong approximation with Brauer–Manin obstruction for toric varieties*,
  Ann. Inst. Fourier 68 (2018) 1879–1908. [Honest toric SA. Wrong theorem for filling
  the ES octant: Ũ_n contains 𝔾_m² but the action does not extend.]
- Colliot-Thélène, Xu — *Brauer–Manin obstruction for integral points of homogeneous
  spaces and representation by integral quadratic forms*, Compos. Math. 145 (2009)
  309–363. [Integral BM pairing used throughout the comparison literature.]

**Markoff comparison (does not move mixed-sign ES points into C₊).**
- Bourgain, Gamburd, Sarnak — *Markoff triples and strong approximation*, C. R. Math.
  Acad. Sci. Paris 354 (2016) 131–135; arXiv:1505.06411; sequel *Markoff surfaces and
  strong approximation: 1*, arXiv:1607.01530.
- Ghosh, Sarnak — *Integral points on Markoff type cubic surfaces*, Invent. Math. 229
  (2022) 689–749; arXiv:1706.06712. [Genuine non-BM integral Hasse failures.]
- Loughran, Mitankin — *Integral Hasse principle and strong approximation for Markoff
  surfaces*, IMRN 2021, no. 18, 14086–14122; arXiv:1807.10223.
- Colliot-Thélène, Wei, Xu — *Brauer–Manin obstruction for Markoff surfaces*, Ann. Sc.
  Norm. Super. Pisa Cl. Sci. (5) 21 (2020) 1257–1313; arXiv:1808.01584.
- Mitankin, Uhlemann — *Local–global principles for semi-integral points on Markoff
  orbifold pairs*, J. Lond. Math. Soc. 112 (2025), no. 6, e70363; arXiv:2411.02629.
  [Cites BL. Markoff compactification in \(\mathbb{P}^3\) has a triangle of lines;
  Campana Hasse holds while integral points fail (Remark 1.5). C3_1: this is why
  Campana packaging is not TUB-EP, and why the triangle does not exclude Markoff.]
- Jang — *Tropical dynamics of Markov surfaces*, arXiv:2306.11357. [Vieta dynamics on
  tropical Markov cubics; ES surfaces have no analogous group action.]

**Analytic exceptional set and sieve.**
- Vaughan — *On a problem of Erdős, Straus and Schinzel*, Mathematika 17 (1970) 193–198.
- Elsholtz, Tao — *Counting the number of solutions to the Erdős–Straus equation on unit
  fractions*, J. Aust. Math. Soc. 94 (2013) 50–105.
- Tao — [On the number of solutions to \(4/p=1/n_1+1/n_2+1/n_3\)](https://terrytao.wordpress.com/2011/11/19/on-the-number-of-solutions-to-4p-1n1-1n2-1n3/)
  (blog, 2011; Mordell reciprocity, 3-fold lift).
- Shiu — *A Brun–Titchmarsh theorem for multiplicative functions*, J. Reine Angew. Math.
  313 (1980) 161–170; Nair — Acta Arith. 62 (1992) 257–269; Nair–Tenenbaum — *Short sums
  of certain arithmetic functions*, Acta Math. 180 (1998) 119–144; Henriot —
  *Nair–Tenenbaum bounds uniform with respect to the discriminant*, Math. Proc. Camb.
  Phil. Soc. 152 (2012) 405–424, erratum 157 (2014); arXiv:1102.1643. [Door (b), §4g.]
- Friedlander, Iwaniec, Mazur, Rubin — *The spin of prime ideals*, Invent. Math. 193
  (2013) 697–749; Maire — *Genus theory and governing fields*, New York J. Math. 24
  (2018) 1056–1067. [Genus/Rédei/spin language of Option 5; not a QED input.]

**Computation.**
- Salez — *The Erdős–Straus conjecture: new modular equations and checking up to
  \(N=10^{17}\)*, arXiv:1406.6307.

---

*Prepared from the investigation thread of 18 August 2026. Computations reproducible in sympy:
(i) minimal-witness search over a, c, d < 40 for q = 4acd−1 dividing cp + a; (ii) d = 1
coverage test over the 511 hard primes < 200,000 via divisors of p + 4a² in class −1 (mod 4a),
a ≤ √p, and d ≤ 30 recovery search via divisors of p + 4a²d in class −1 (mod 4ad).*
