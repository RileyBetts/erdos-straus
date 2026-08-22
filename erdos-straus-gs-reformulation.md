<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# Granville–Soundararajan reformulation of the analytic core

**Riley Betts Erdős–Straus programme, 20 August 2026.**
Companion to `erdos-straus-candidate-conjectures.md` (C1, C2, C4, C4_1, C6),
plan §§4e–4r and §4v, `erdos-straus-conjecture-spec.md` (R3).

This note contains **no new theorem**. It restates the survivor-density and
flatness targets in the language whose published estimates apply, names
the analytic-lane dictionary, and records two caveats that decide whether a
naive large-sieve attempt is wasted motion.

---

## The target, in the original coordinates

The covering condition at a pair \((a,d)\) is that \(p+4a^2d\) has a prime
factor \(q\equiv -1\pmod{4ad}\). Survival is *joint roughness*: for how
many hard primes \(p\le x\) do **all** shifts \(p+4a^2d\), over a growing
\((a,d)\)-box, avoid those \(-1\)-progressions?

The level schedule \(A=\exp(c\sqrt{\log x})\) with \(\kappa c^2>1\) assumes
that the slice-failure events are quasi-independent up to Suen/Janson
corrections (plan §4e). The object to test is the joint density
\(S(A,x)=\mathbb{P}(\text{all }a\le A\text{ class-rough})\), not pair
ratios. Pair ratios stay \(1.000\); \(S/\prod\rho_a\) does not. The
first theorem is T(A) (candidates C4_1). This memo is the dictionary
for the joint lower-tail that \(S\) is.

**Attachment, 20 Aug.** The Granville–Soundararajan recommendation
attaches specifically to \(S\): “all slices land rough” is a joint
lower-tail event for a vector of dependent multiplicative statistics,
which is exactly the object that moment/large-deviation machinery
computes. The x-scan (`c4_S_xscan.py`) did **not** return Mertens
drift: mean\((e-1)\) for \(a\ge 10\) rises through \(x=10^9\)
(0.0094 → 0.0168). Growing \(A\) at the same \(x\) (`c4_growing_A.py`,
\(A\le 200\)) splits that: \(\mathrm{cond}(a)\to 1\) past \(a=80\), so
extra \(d=1\) slices are mostly dummy covering mass, and
\(\log\hat C\sim 0.104\log^2 A\) sits below \(\kappa=0.139\). If cond
sticks at 1, further statistics are of a *conditioned* vector (a
selected pretentious tail), not “many weakly dependent characters.”
T(A) lives or dies on whether \(c'\) stays below \(\kappa\) uniformly
in \(A\). The 2.7–3.0 totient mismatch is the composite-divisor layer
of `ClassRough`; a prime-only control matches \(\sum 1/\varphi(4a)\) to
~17%.

**Named object, same day.** After `classRough_of_certifies`, the
indicators are character-kernel multiplicative functions: all coprime
prime factors of \(p+4a^2\) lie in \(\ker\chi\) for some real odd
\(\chi\) mod \(4a\). That is the single most classical target in this
toolkit. Shared-certificate dummy covering does not fire
(`c4_certificates.py`): inherited \(\chi\) covers \(\sim 65\)–\(73\%\) of
prefix survivors, not the \(95\)–\(98\%\) ClassRough rate.
\(\mathrm{cond}\to 1\) is large-modulus rarity. If dummy covering
sticks, it is still a *conditioned* tail of those indicators, not
\(\sim\log^2 A\) free characters.

---

## Every condition is a real-character condition

Plan §4p: survival forces the prime into explicit square-cosets. Quadratic
reciprocity turns those into values of real characters \(\chi_D(p)=\pm 1\).
The survivor-density question is therefore a question about the **joint
distribution of many quadratic-character values at primes**.

That is not a new analytic subject. It is the Granville–Soundararajan
theory of pretentious characters and large deviations of character sums,
and Lamzouri’s large-deviation theorems for character sums. The programme’s
regime — the probability that \(\sim\log^2 A\) independent-looking real
character conditions all land one way — is exactly the large-deviation
range that machinery was built for.

**Restated target (survivor density).** Let \(\mathcal{F}_A\) be the
family of real characters (equivalently, fundamental discriminants)
attached to the active covering identities at level \(A\). Write
\[
\Sigma_A(p) \;=\; \sum_{\chi\in\mathcal{F}_A} \chi(p)
\]
for the pretentious sum over that family. The event that \(p\) survives
is, up to the explicit coset-main-term bookkeeping of §4p, the event that
every relevant \(\chi(p)\) takes the forbidden value — a large-deviation
tail of \(\Sigma_A\) (or of the associated Euler product / pretentious
distance) at primes \(p\sim x\).

**Restated target (flatness / C6).** The Selberg-\(L^2\) residual of the
survivor indicator against the next covering shell is the second-moment
(or growing-moment) discrepancy of \(\Sigma_A\) after the captured
character-coset main terms are removed. Sub-critical flatness is a
statement that those moments match the quasi-independent model.

---

## The second-moment engine

The one large-sieve variant with genuine extra strength for **real**
characters is Heath-Brown’s quadratic large sieve. It is the natural
second-moment engine under \(\Sigma_A\). It is not, by itself, the QED
estimate: see the caveats.

---

## Two caveats (do not skip)

1. **The moduli count is small.** The covering moduli run up to
   \(A=\exp(c\sqrt{\log x})\), which is tiny against \(x\). A naive
   large-sieve application in this range is typically **trivial** — the
   large-sieve inequality is not the obstruction, and proving a trivial
   bound does not move H_ES. The leverage is in **moments of growing
   order** of \(\Sigma_A\), which is exactly where pretentiousness /
   Granville–Soundararajan technology does the work and a raw sieve does
   not.

2. **Admissible against the k-budget invariant.** Character-sum
   cancellation is not interval-intrinsic randomness. R3 therefore does
   **not** pre-refute the attempt. That is rarer among the options on the
   candidate list than it sounds. The invariant still caps any argument
   that only uses interval independence; it does not cap an argument that
   uses cancellation in the character sums themselves.

---

## Parallel recasting: field entanglement

Equivalently, and worth doing in parallel with the G–S dictionary: the
joint conditions are Chebotarev conditions in a compositum of quadratic
fields. The entanglement group of that compositum **is** the dependency
structure that Suen’s \(\Delta\) estimates from the other side. Recasting
the Suen conditioning as field entanglement computes the correction
factors from Galois groups rather than from pair-correlation graphs, and
connects the programme to the simultaneous-splitting literature, where
partial results already exist.

This is the Option 9 / C8 language with the geometric pretence stripped:
not “prove ES by Chebotarev,” but “name the correction factors of T(A)
as Frobenius entanglement.” The shared-modulus layer’s compositum
density is now computed for the **prime-aligned** indicator:
\(C_{\mathrm{euler}}(80)=0.911\) in the \(1/q\) normalisation, flat to
\(A=200\), zero residue collisions (`c4_euler_factor.py`;
`erdos-straus-T-A.md`). That factor is not \(C(A)\). The ClassRough
composite layer is the genuine-extra Euler product
\(\Pi_{\mathrm{gen}}(\sqrt{x})\), matching the \(A=40\) CR/prime product
to \(3\%\) (`c4_composite_layer.py`); it sits in the marginals \(\rho_a\),
not in \(\hat C\). If \(\mathrm{cond}(a)\) sticks at 1, remaining
entanglement is the law of a *conditioned* subset: extra covering
characters are dummy, and further moment/large-deviation statistics
are of a selected pretentious tail, not of \(\sim\log^2 A\) weakly
dependent free characters.

---

## Analytic-lane dictionary

Not the Bright–Loughran literature (that note is class-theory and effectivity,
plan §4v; not a proof path with existing geometric tools).

The G–S restatement names the analytic dialect:

- **Granville–Soundararajan / pretentiousness / large deviations of
  character sums** — the growing-moment / tail machinery.
- **Lamzouri** — large-deviation theorems for character sums, the
  closest off-the-shelf tail statements.
- **Heath-Brown** — quadratic large sieve as second-moment engine.
- **Sieve / LSD / shifted-convolution literature** (Wirsing,
  Landau–Selberg–Delange; Fouvry–Iwaniec, Friedlander–Iwaniec
  lineage) — for T(A) itself, the joint density at fixed \(A\),
  which is the first paper and does not wait on G–S.

T(A) working note: `erdos-straus-T-A.md` (certificates, converse
\(\omega\)-gap, shared-\(\chi\) dummy test). The analytic worklist
(`erdos-straus-sieve-desk.md`) is a written question list, not the next
compute step. C2’s
cross-moduli measurement is a **null** (covering symbols independent;
wrong sign for \(\hat C>1\)); this memo is a dictionary of the joint
lower-tail that \(S\) is, not a request to extract extra independent
characters. Do not mix the geometric questions into either.

---

## What this memo does not do

- It does not prove H_ES, E_partial, or a large-deviation tail.
  E_partial as a Gate A write-up is `erdos-straus-E-partial.md`
  (Layer 1 = T(A) on paper; Layer 0 is E_power, a recorded
  negative, `erdos-straus-E-power.md`, not `AnalyticSurvivorBound`).
- It does not license a direct assault on the full level statement
  (k-budget invariant; the marginal constant \(\kappa c^2>1\)).
- It does not replace T(A). If \(C(A)\) is super-critical in \(\log^2 A\)
  (\(c'\ge\kappa\)) or if \(\mathrm{cond}\equiv 1\) makes extra covering
  fictitious out to QED-scale \(A\), this dictionary is a dictionary of
  a dead or dummy schedule, and that death is the valuable result.
  Growing \(A\) to 200 at \(x=10^9\) gave \(c'=0.104<\kappa=0.139\) and
  \(\mathrm{cond}\approx 1\); pattern (iii) saturation of the joint
  exponent has not been seen.

## Bibliography (working)

- A. Granville, K. Soundararajan, *Large character sums*, J. Amer. Math.
  Soc. **14** (2001), 365–397.
- A. Granville, K. Soundararajan, *Pretentious multiplicative functions
  and an inequality for the zeta-function*, 2007; and subsequent
  pretentiousness papers.
- Y. Lamzouri, large-deviation theorems for character sums (see his
  papers on the distribution of \(\psi(x,\chi)\)).
- D. R. Heath-Brown, *A mean value estimate for real character sums*,
  Acta Arith. **72** (1995), 235–275 (quadratic large sieve).
- W.-C. S. Suen, *A correlation inequality and a Poisson limit theorem
  for nonoverlapping balanced subgraphs of a random graph*, Random
  Structures Algorithms **1** (1990), 231–242; S. Janson, *Poisson
  approximation for large deviations*, Random Structures Algorithms
  **1** (1990), 221–229 — the correlation inequality used in plan §4e.
