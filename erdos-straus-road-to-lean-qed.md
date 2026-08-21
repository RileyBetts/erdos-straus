<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# From the Current Erdős–Straus Development to a Lean-Checked QED
## Execution roadmap (amended edition, 18 Aug 2026)

*Amendments over the draft: (i) a Known Barrier section stating the k-budget
invariant and its consequences for expectation-setting; (ii) the Renewal Lemma
reframed from "substantially easier" to "sharpest known target, difficulty
concentrated in the error terms"; (iii) the computational-certificate lane made
consistent; (iv) compilation gates restored. Companion documents:
`erdos-straus-novel-structures-plan.md` (the research record, §§4a–4t),
`erdos-straus-conjecture-spec.md` (acceptance requirements R1–R8),
`erdos-straus-candidate-conjectures.md` (ten candidate statements for C),
`README.md` (Layer A/B file map), `ErdosStraus.lean`, `BrightLoughran.lean`,
`ConicFiber.lean`, `ErdosStrausBLRoute.lean`.*

---

## Executive summary

The project should be treated as a layered proof programme rather than as a
direct attack on the full conjecture. The existing Lean development provides
the trusted lower layer:

    HardLandingHypothesis  ⟹  ErdosStraus.

The objective is to isolate one mathematically sharp bridge theorem above this
infrastructure, prove it, and let the existing reduction complete the argument:

1. Freeze and tidy the existing Lean kernel layer.
2. Define the explicit covering system and survivor sets in Lean.
3. Prove: failure to survive ⟹ existence of an ES witness (`covering_sound`).
4. Replace the broad `HardLandingHypothesis` by a theorem: sufficiently large
   hard primes cannot survive the covering system.
5. Prove a finite theorem for the remaining range.
6. Combine in Lean: `theorem erdos_straus : ErdosStraus`.

The central mathematical recommendation is to weaken the broad equidistribution
hypothesis into a specialised **ES Renewal/Contraction Lemma** governing only
the interaction between the current survivor set and the next shell of ES
covering congruences — with the honest caveat of §5 below.

---

## 1. Preserve the existing Lean foundation

Freeze: `Witness`, `witness_sound`, solution scaling, prime-factor existence,
the Mordell-style witness identities, `HardClass`, the reduction to the six
hard residue classes, `es_prime_not_hard`, `conditional_qed_hard`, the finite
certificate mechanism. The load-bearing implication is
HardLandingHypothesis ⟹ ErdosStraus. Modify this layer only where a change
makes later analytic formalisation substantially easier. Migrate elementary
results toward Mathlib where useful, since the analytic layer will depend on
Mathlib (quadratic reciprocity at minimum; see `BrightLoughran.lean` §4).

## 2. Replace the broad landing hypothesis with an explicit covering problem

Current form:

```lean
def HardLandingHypothesis : Prop :=
  ∀ p : Nat, IsPrime p → HardClass p → ∃ x y z, IsES p x y z
```

Introduce the covering system: let C_A be the ES covering congruences at
level A, and S_A = { n : n avoids every congruence in C_A }. Prove in Lean:

    p ∉ S_A  ⟹  ∃ a c d m, Witness p a c d m.

This separates the **elementary/formal question** (covered ⟹ witness — fully
Lean-provable now) from the **deep question** (can a large hard prime remain
in S_A?). The conjecture becomes: *every sufficiently large hard prime lies
outside S_A.*

## 3. Formalise the cardinality-to-QED bridge immediately

Before the analytic theorem, formalise its logical consequences:

```lean
theorem no_survivors_of_card_lt_one (…) :
    survivorCount A x (2*x) < 1 →
    ∀ n, x ≤ n → n < 2*x → ¬ Survivor A n := …

theorem hardLanding_of_survivor_bound (Hanalytic : …) :
    HardLandingHypothesis := …
```

The entire conjecture is then conditional on one explicit analytic estimate,
and the formal development exposes exactly what the mathematics still owes.

## 4. The analytic mechanism

Covering level A = exp(c·√(log x)); target survivor estimate

    #S_A(x, 2x)  ≪  x · exp(−(1−o(1))·κ·log²A)  =  x^{1 − κc² + o(1)}.

If κc² > 1 then eventually #S_A(x,2x) < 1, hence = 0 (integrality), and
finite verification covers the bounded range. This is the mechanism that
converts a sufficiently strong analytic estimate into QED.

## 5. KNOWN BARRIER — read before setting expectations

**(Amendment.)** The research record (plan §§4h, 4k, 4l) establishes, by three
independent derivations, the **k-budget invariant**: every method consuming
only interval-intrinsic randomness — sieves, large sieve, Shiu-type transfers,
k-wise-independence fooling, and the raw error-accounting of any multi-scale
renewal — captures sifted mass ≤ c·log(level) ≤ c·log x, while the mechanism
of §4 requires mass > log x. ES sits at the marginal constant (the structural
position of twin primes at the parity boundary). Consequences for this
roadmap: (a) the Renewal Lemma of §7 is the *sharpest known formulation* of
the target, not a route around the difficulty — its error terms ε_j are where
the open problem lives; (b) any claim that a reformulation makes the problem
"substantially easier" is unsupported unless it injects input from outside the
capped class — the two known candidates being spectral/bilinear arithmetic
input (dispersion, Kloosterman, DFI) and the algebraic rigidity of §9; (c) the
mechanism's constant κ ≈ 0.139 and the coupling-degree law (mass Poisson over
coupling degree, mean loglog) are measured at toy scale only; the asymptotic
regime is untested and untestable by simulation. Plan §4o gives the road map
through this barrier; nothing in the present document supersedes it.

## 6. First prove a genuine power-saving theorem

Before the QED estimate, complete the partial result rigorously:

    #S_A(x, 2x)  ≪  x^{1−δ}   for explicit δ > 0,

via Suen/Janson inequalities, organised truncated inclusion–exclusion
(raw truncation diverges at \(\mu\approx 2.2\) — plan §4n), dependency graphs, CRT
structure, and the fresh-mass estimates. **Claimed:** `erdos-straus-E-power.md`
(21 Aug 2026). This does not prove ES, but it
(i) validates the covering mechanism at power-saving strength, (ii) benchmarks stronger methods, and
(iii) is independently publishable — an improvement on Vaughan
(1970), the programme's first record. **Review gate A: this
written theorem passes external sieve-theoretic review before any formalisation of
the analytic layer begins.** Do not compile it as `AnalyticSurvivorBound`.

## 7. The ES Renewal Lemma — the sharpest known target

**(Reframed.)** Choose scales A_0 < A_1 < … < A_k, S_j = S_{A_j}, and seek

    #(S_{j+1} ∩ [x,2x])  ≤  exp(−ΔM_j + ε_j) · #(S_j ∩ [x,2x]),

where ΔM_j is the fresh covering mass of shell j and ε_j collects correlation
and distribution errors. Iterating: it suffices that Σ ΔM_j − Σ ε_j > log x,
whence #S_k < 1 and S_k = ∅. The genuine advantages: each step confronts only
*one highly structured shell* against the previous survivors; per-step level
demands are polynomial, not exponential; the fresh-CRT-coordinate phenomenon
(plan §4i, empirically exact after complete profile conditioning) is the
mechanism to be converted into a theorem. The honest statement of difficulty:
**Σ ε_j-control over ~log x scales is where the k-budget invariant bites** —
per-step conditioning spends independence budget at the rate the contraction
saves it. The lemma concentrates the open problem; it does not dilute it.

## 8. The spectral decomposition of the survivor set

Write 1_{S_A} = P_A + R_A: P_A the structured component (explicit AP modes;
Selberg-L² weights over the AP dictionary — plan §4n rungs 3/3b: depth-2
capture 0.827 at toy scale, residual near-Poisson-flat, decomposition closing
to three digits), R_A the residual. For the next shell C:

    ⟨1_{S_A}, 1_C⟩ = ⟨P_A, 1_C⟩ + ⟨R_A, 1_C⟩,

with the structured term exactly (or nearly exactly) computable by CRT and
finite arithmetic. The analytic task reduces to the residual term, target:

    |⟨R_A, C_{A,A'}⟩|  ≤  ε · ‖R_A‖₂ · ‖C_{A,A'}‖₂

— a statement about the residual against the *particular next-scale covering
operator*, not arbitrary progressions. This is the correct precise reading of
the observed pseudorandomness ("the floor is flat", plan §4n), and it is a
sieve-residual/bilinear statement — the native currency of dispersion methods.
Subject to §5: at asymptotic scale the required ε is the frontier.

## 9. The Bright–Loughran strand: from parallel to quantitative

Continue the Brauer–Manin work (`BrightLoughran.lean`) as a strand feeding the
covering argument, with the specific target of proving implications

    p ∈ S_A  ⟹  χ_{q₁}(p) = ε₁, …, χ_{q_k}(p) = ε_k

for quadratic characters attached to witness moduli (survival = simultaneous
non-residue conditions — the α-invariant identification, plan §4m). Then ask
whether reciprocity, a Hilbert product relation, or the Brauer class α forces
incompatibility (ideal, deterministic outcome: survival ⟹ 1 = −1), or — the
realistic quantitative version — confines survivors to a collection of
Frobenius/quadratic-residue classes shrinking fast enough to feed the §7
contraction as *non-statistical* input, which is precisely the input class the
§5 barrier does not cap. Bright–Loughran rigidity + multi-scale covering may
be stronger than either route alone; this hybrid is the roadmap's most
promising evasion of the invariant.

## 10. Theorem hierarchy

```text
Witness algebra → covering congruence sound → ¬Survivor A p → Witness p a c d m
   → IsES p x y z → hard prime lands → { finite range | analytic large range }
   → HardLandingHypothesis → Erdős–Straus
```

Analytic branch: shell arithmetic → fresh mass → correlation/residual estimate
→ ES Renewal Lemma → multi-scale contraction → survivor count < 1 → no large
survivors. Every node except the correlation/renewal input should become
comparatively routine; that input is the frontier (§5).

## 11. Target Lean architecture and the certificate lane

```lean
theorem covering_sound : ¬ Survivor A p → ∃ a c d m, Witness p a c d m := …
theorem analytic_survivor_bound :
    ∃ X₀, ∀ x ≥ X₀, survivorCount (A x) x (2*x) = 0 := …
theorem large_hard_primes_land : … := …
theorem small_hard_primes_land : ∀ p < X₀, … := <finite certificate>
theorem hard_landing : HardLandingHypothesis := …
theorem erdos_straus : ErdosStraus := conditional_qed_hard hard_landing
```

**(Certificate lane, made consistent.)** The end state contains no `sorry`
and no conjectural axiom. For the finite range, choose one lane explicitly:
(i) kernel `decide` — axiom-free, expensive; (ii) `native_decide` — fast,
adds `Lean.ofReduceBool`, acceptable if declared in the axiom audit; (iii)
Track C — ZK-attested verified computation replacing the trusted-compilation
axiom at scale (the designed lane for X₀ beyond kernel reach). The final
theorem's axiom audit is published alongside it, whichever lane is used.

## 12. Immediate programme of work

- **Step 1** — Formal covering definitions: congruence, level, `Covered`,
  `Survivor`, interval counts; prove `covering_sound`. (Now; elementary.)
- **Step 2** — *Statement-first discipline:* write the weakest Lean theorem
  whose conclusion eliminates all large survivors — **before proving it** —
  so the analysis cannot drift toward unnecessarily general results.
- **Step 3** — Complete the power-saving theorem (§6). **Done as E_power**
  (`erdos-straus-E-power.md`, 21 Aug 2026). Write-up also:
  `erdos-straus-E-partial.md`.
  Gate A **does not pass** E_power into Lean: it is a power-saving
  count, not `AnalyticSurvivorBound`. Dummy covering
  (\(\mathrm{cond}\equiv 1\)) stops a retuned QED schedule. Do not
  compile Layer 0 as progress toward `erdos_straus_of_interface`.
  External sieve-theoretic review of the write-up is the remaining
  Gate A action.
- **Step 4** — State the ES Renewal Lemma precisely, quantified only over the
  actual ES shells, with §5 cited in its documentation.
- **Step 5** — Develop the spectral projection analytically: define P_A, R_A;
  evaluate the structured contribution explicitly; identify the weakest
  residual norm estimate sufficient for contraction.
- **Step 6** — Bright–Loughran rigidity into the survivor analysis (§9):
  forced character conditions; reciprocity incompatibilities; Frobenius-class
  confinement; deterministic obstructions. Analytic sibling, same frontier
  bucket (plan §4w): a joint well-factorable weight for the moving CRT
  residue of the three T(3) kernels (`erdos-straus-T-3.md`). The
  \(r_\chi\to\) Kloosterman bilinear look is a range no-go at
  \(Q=x^{1/2+}\). Not in-house next; not C1.
- **Step 7** — Incremental formalisation, gated: formalise *stabilised
  statements and elementary lemmas* as soon as they stabilise (exposing
  hidden hypotheses, endpoints, integrality, uniformity early); the deep
  analytic *proofs* are formalised only after they exist as papers, not as
  QED (**Gate B**).
- **Step 8** — Close the finite range last, once the analytic X₀ is explicit;
  computation fills the bounded gap, it does not set strategy.

## 13. The central research question

> Can the survivors of the ES covering system be shown to contract under
> successive shells of algebraically structured covering congruences strongly
> enough that their cardinality falls below one?

Strongest current refinement:

> After removing the explicitly structured spectral component of the survivor
> indicator, can the residual be proved sufficiently uncorrelated with the
> next ES covering shell to force this contraction?

This is *potentially* weaker than a general Elliott–Halberstam theorem — the
qualifier carries §5's full weight: it is weaker only insofar as the shells'
algebraic structure (§9) or spectral/bilinear input supplies what interval
randomness cannot. It aligns directly with the observed computational
phenomena, which is what makes it the correct target.

## 14. Intended end state

**Layer A** — formal algebra and reduction: fully Lean-checked, elementary;
reduces ES to the absence of large hard-prime survivors. *(Exists.)*
**Layer B** — the deep theorem: renewal/contraction + spectral residual
cancellation + reciprocity rigidity, in some combination; proves large
survivors do not exist. *(The frontier; §5.)*
**Layer C** — finite closure below the analytic threshold, certificate lane
per §11. *(Mechanism exists; scale pending X₀.)*

    analytic theorem + finite theorem ⟹ HardLandingHypothesis ⟹ ErdősStraus.

The strategic core: turn the observed multi-scale and spectral structure into
the weakest possible ES-specific contraction theorem, make that theorem the
single load-bearing target — and never let its packaging obscure that its
error terms are a 78-year-old open problem, precisely located.

---

## 15. Geometric packaging landed (19 Aug 2026)

This document's Layer A/B/C (§14) is the *covering* architecture: reduction,
analytic contraction, finite certificate.  It is not the file map in
`README.md` (bare Lean vs Mathlib).  Both are in force.

Route 2 did not wait for the analytic Layer B.  Record: plan §4s.
Load-bearing Lean, all proved, none of it `ErdosStraus`:

- `TubEpHypothesis` and `erdos_straus_of_tub_ep` — occupying the positive
  octant implies ES; the hypothesis is not discharged.
- `IsESZ` / `esZ_nonempty` — the affine ℤ-model is nonempty for every
  `n ≥ 2` (mixed signs allowed).
- `schinzelZ_min_le` / `esZ_min_le` / `es_pos_min_le` — Jahnel–Schindler /
  BL Lemma 3.10 box.
- `hilbert_reciprocity_*` — Layer B discharge of the odd, 2-power, mixed-sign,
  and ES-ratio content of `InvariantData.reciprocity`; anatomy
  `thm12_discharged`.
- `ConicFiber.lean` — split-fiber identity and divisor correspondence
  (`fiber_to_divisor` / `divisor_to_fiber`); Harpaz inapplicable (plan §4t).

The covering Steps 1–8 above remain the analytic lane, and after plan §4v
they are the **only** technical QED lane with existing tools.  Geometry
is class-theory and an effectivity framework: `TubEpHypothesis` is equivalent to ES
(`tub_ep_iff_erdos_straus`), which is a translation, not a target.
The first theorem is T(A), the joint density at fixed covering width
(candidates C4_1). Pairs were the wrong moment. Growing \(A\) at
\(x=10^9\) gave \(\log\hat C\sim 0.104\log^2 A\) (below \(\kappa=0.139\))
and \(\mathrm{cond}\to 1\); T(A) is constant-tracking of that sequence,
not a pair lemma.
Do not read `erdos_straus_of_tub_ep` as closing this roadmap.
