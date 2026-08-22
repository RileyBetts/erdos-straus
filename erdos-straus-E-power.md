<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# E_power — two-stage covering density (repaired programme)

**Riley Betts Erdős–Straus programme, 22 August 2026.**
Roadmap §6; plan §§4e, 4h, 4k. Companion to `erdos-straus-E-partial.md`
(Gate A), `EPower.lean`, `e_power_fibre_moments.py`. This file
**does not prove** the Erdős–Straus conjecture, does not empty the box,
and does not discharge `AnalyticSurvivorBound`.

> **Status (22 Aug 2026).** The 21 August one-stage write-up is
> **withdrawn as a theorem**. The 22 August replacement target —
> inhabit H1/H2 at the prime-power hub and obtain
> `FiniteProductDensityBound` — is **withdrawn as the next Lean
> object** (`erdos-straus-E-power-decision.md`). Growing \(T\) does
> not make \(-\log P/k^2\) and Titu\(/k^2\) both two-log. The
> combinatorial core in `EPower.lean` stands. Immediate work is a
> different split on paper, or a recorded negative, not inhabiting
> H1/H2.

E_lane (`erdos-straus-T-A.md`) is the \(d=1\) ClassRough floor, below
Vaughan. This note is the **full covering box**: integers in \([x,2x]\)
that avoid every cell of the Lean covering system at width
\(A=\exp(c\sqrt{\log x})\). That is a larger set than the exceptional
set of Erdős–Straus, so an upper bound here is an upper bound there.
Dummy covering (\(\mathrm{cond}\equiv 1\)) is a ClassRough nesting
phenomenon and does not apply to this object.

---

## Object

Lean `ES.Covering` / `ES.EPower.Covering`: a cell \((a,c,d)\) covers \(n\)
when \(q=4acd-1\) divides \(cn+a\). Always \(\gcd(c,q)=1\), so this is
a single residue class \(n\equiv r\pmod q\). The level-\(A\) system
takes \(1\le a,c\le A\) and \(1\le d\le 5\). `Survivor A n` means no
such cell covers \(n\). `covering_sound` converts a hit into a witness,
so every \(n\) for which \(4/n\) is not a sum of three unit fractions
is a survivor of every covering box. Write
\[
S_A(x,2x)
\;=\;
\#\{n:x\le n<2x,\;\mathrm{Survivor}(A,n)\}.
\]
The exceptional set of Erdős–Straus in the same interval is
\(\subseteq S_A(x,2x)\).

Raw cell mass (duplicates included):
\[
\mu_{\mathrm{raw}}(A)
\;=\;
\sum_{\substack{1\le a,c\le A\\1\le d\le 5}}\frac1{4acd-1}
\;\sim\;
\frac{H_5}{4}(\log A)^2,
\qquad
H_5=\frac{137}{60}.
\]
Distinct cells can define the same congruence event. All later
quantities use the **deduplicated** family of pairs \((q,r)\). Write
\(\mu(A)\) for the mass of that family. The events remain dependent
(small-prime hub). Raw Bonferroni on the cell indicators diverges in
practice at mean activation \(\mu\approx 2.2\) (plan §4n).

---

## Why the 21 August argument is not correct as stated

Lemma CDL claimed that after conditioning on all primes \(p\le T\), the
remaining events live on the product space of coordinates \(n\bmod p\)
for \(p>T\), and that Suen applies with the **unconditional** mass
\(\sum 1/q\) and the surrogate pair mass \(\sum_{\ell>T}\mu_\ell^2\).
Lemma Transfer then took the hub to be the primorial
\(M_T=\prod_{p\le T}p\) and the interval discrepancy to be \(O(M_T)\).

Three errors.

**1. Conditional mass is not \(\sum 1/q\).** Split each modulus as
\(q_i=s_i\ell_i\) with \(s_i\) the complete \(T\)-smooth prime-power
part and \(\ell_i\) supported on primes \(>T\). After conditioning on
a compatible hub residue \(\rho\bmod H\),
\[
P(E_i\mid\rho)
\;=\;
\frac1{\ell_i}
\]
if the event survives, and \(0\) if it is incompatible. Hub-forced
events (\(\ell_i=1\)) cover the whole fibre. The unconditional sum
\(\sum 1/q_i\) is the wrong input to Suen on the fibre.

**2. The hub is not the primorial.** Covering moduli may contain
\(p^2,p^3,\ldots\). The exact finite modulus that absorbs every
small-prime condition is
\[
H
\;=\;
\operatorname{lcm}_i(s_i),
\]
not \(\prod_{p\le T}p\).

**3. Periodicity modulo \(H\) does not give discrepancy \(O(H)\).**
Residual events still impose congruences modulo the large parts
\(\ell_i\). The passage from product-space density to
\(\#\{n\in[x,2x]\}\) is a separate analytic theorem. It must not be
hidden inside the probabilistic bound.

Lemma SM below remains a written estimate for the **surrogate**
\(\sum_{\ell>T}\mu_\ell^2\) on the raw cell family. It is not Suen's
\(\Delta\), and it does not repair (1)–(3).

The numerical tables in the withdrawn write-up, and the scripts
`e_power_suen_moments.py` / `e_power_suen_moments_large.py`, are
kept as measurements of that surrogate. They are not evidence that
one-stage CDL holds.

---

## Two-stage identity

Deduplicate first: replace the cell family by the `Finset` of distinct
pairs \((q,r)\). The union of covered integers is unchanged
(`ES.EPower.Covering.covered_iff_mem_events`).

Work fibre by fibre modulo \(H\). For each \(\rho\bmod H\), every event
is exactly one of:

| Class | Condition | Conditional probability |
| --- | --- | --- |
| Incompatible | small-prime condition disagrees with \(\rho\) | \(0\) |
| Hub-forced | compatible and \(\ell_i=1\) | the fibre is covered |
| Residual | compatible and \(\ell_i>1\) | \(1/\ell_i\) |

Write “hub survives” for the fibres with no hub-forced event. On a
surviving fibre \(\rho\), let \(I_\rho\) be the residual family and
\[
\mu_\rho
\;=\;
\sum_{i\in I_\rho}\frac1{\ell_i},
\qquad
\Delta_\rho
\;=\;
\sum_{\substack{i<j\\ i\sim j}} P_\rho(E_i\cap E_j),
\qquad
\delta_\rho
\;=\;
\max_i\sum_{j\sim i}P_\rho(E_j).
\]
For congruence events, \(P_\rho(E_i\cap E_j)=1/\operatorname{lcm}(\ell_i,\ell_j)\)
if the residual residues agree modulo \(\gcd(\ell_i,\ell_j)\), and \(0\)
otherwise. The dependency graph \(i\sim j\) joins events that share a
large-prime coordinate. Independent pairs
(\(\gcd(\ell_i,\ell_j)=1\)) are not summands of \(\Delta_\rho\).

The finite product-space identity is
\[
P(\text{uncovered})
\;=\;
P(\text{hub survives})
\cdot
\mathbb{E}\bigl[
P(\text{large-prime events survive}\mid\rho)
\bigm|
\rho\text{ survives the hub}
\bigr].
\]
Two exponential gains, then a product.

### H1 — Hub exponential bound

For some absolute \(\gamma_H>0\),
\[
P(\text{hub survives})
\;\le\;
e^{-\gamma_H\mu(A)}.
\]
The coefficient need not be close to \(1\). Any fixed positive value
is potentially enough.

### H2 — Residual fibre bound

For all surviving fibres, or all except an exponentially negligible
collection of bad fibres,
\[
-\mu_\rho+\Delta_\rho\, e^{2\delta_\rho}
\;\le\;
-\gamma_L\mu(A)
\]
for some absolute \(\gamma_L>0\). A finite Suen (or a specialised
correlation inequality for these congruence cylinders) then gives
\[
P_\rho(\text{large-prime survivor})
\;\le\;
e^{-\gamma_L\mu(A)}.
\]

Combining H1 and H2:
\[
P(\text{uncovered})
\;\le\;
e^{-(\gamma_H+\gamma_L)\mu(A)}.
\]
There is no need to prove \(\gamma_H+\gamma_L=1-o(1)\). A fixed
positive coefficient is enough for a power saving.

---

## Immediate Lean target: finite density

The first kernel-checked target is **not** \(S_A(x,2x)\ll x^{1-\delta}\).
It is a finite product-space theorem
\[
u(A)
\;\le\;
\exp\bigl(-\gamma(\log A)^2\bigr)
\]
for some explicit \(\gamma>0\), independently of interval transfer.
If that compiles, the probabilistic core is secure and the remaining
gap is a sharply defined analytic bridge.

Covering-mass growth is a separate theorem: after deduplication,
\[
\mu(A)
\;\ge\;
\kappa(\log A)^2
\]
for some fixed \(\kappa>0\) and all sufficiently large \(A\). The
constant \(\kappa\) must be recomputed from distinct events, not from
the raw cell count.

Once \(u(A)\le e^{-\gamma\mu(A)}\) and \(\mu(A)\ge\kappa(\log A)^2\)
are proved, the algebra is elementary. Set
\(A=\exp(c\sqrt{\log x})\). Then \((\log A)^2=c^2\log x\), so
\[
u(A)
\;\le\;
x^{-\gamma\kappa c^2}.
\]
Write \(\delta=\gamma\kappa c^2>0\). The density contribution is
\(x\,u(A)\le x^{1-\delta}\). That algebra lives in
`EPower/Asymptotics/DensityBound.lean`. It does not contain the
transfer.

---

## Density-to-count transfer (separate)

The remaining major issue is the passage from product-space covering
density to the number of actual integers in \([x,2x]\).

```lean
structure DensityCountTransfer : Prop where
  transfer : ...
```

The withdrawn claim that the discrepancy is \(O(H)\) must not be used
unless it is independently proved. Residual moduli beyond the hub
mean that periodicity modulo \(H\) alone does not give that bound.
This is the principal analytic-number-theory bridge after the finite
probability theorem.

`EPower.lean` now inhabits named interfaces with the **combinatorial
cores** listed below, not with the analytic H1/H2/transfer theorems.
`e_power_core_holds` is that core. It is not \(S_A\ll x^{1-\delta}\).

---

## Kernel-checked core (22 August 2026)

Layer A, `lean EPower.lean`, no `sorry`. What compiles:

| Interface | What is proved | What is not proved |
| --- | --- | --- |
| Dedup | `events = eraseDups cellEvents`; union of covered integers is unchanged | — |
| Hub split | `smoothPart * largePart = q`; large part is \(T\)-rough; **`gcd(s,ℓ)=1`** (`gcd_smooth_large`); `smoothPart q ∣ H` (`hubOf_dvd`) | — |
| Fibre law | On a compatible fibre, the event hits exactly one of \(\ell\) residues (`fibre_hit_count`). Hub-forced (\(\ell=1\)) covers the whole fibre | — |
| Fibre quantities | Exact `μ_ρ`, `Δ_ρ`, `δ_ρ`. Pair mass is `1/lcm` or `0` for every pair (`pair_hit_count`, `pair_hit_compatible`), including `gcd>1`. Janson `Δ` is `deltaHit` (dependent pairs only). Two-event Titu: `janson_mass_two`. Sequential Janson I: `hit_among_independent`, `janson_hit_lower`, `janson_step` | Exponential \(P\le\exp(-\sum p/(1+\delta))\) and Harris/FKG. `FibreSuenHypothesis` |
| Residual reduction | On a hub-surviving fibre, `avoids` equals residual-event `avoids` (`avoids_eq_residual`). Periodic fibres: `fibreUncovered_periodic`, `uncovered_periodic_mul`. Unique residual class on a coprime fibre (`fibre_congruence_count`) | — |
| Finite Suen / H2 | One-modulus avoid; CRT; empty-graph product `∏(q_i−1)` (`independent_avoid_prod`, `avoid_coprime_extension`). Surviving fibre with pairwise-coprime residuals: `fibreUncovered = evMissProd` (`fibre_independent_count`). Dependent sequential step: `γ ≥ p − Δ_{\mathrm{nbr}}/\|U\|` (`janson_hit_lower`), not `γ ≥ p/(1+δ)` | `P_ρ ≤ 2^{-γ k²}` (`FibreSuenHypothesis`). Coprime packing cannot supply two-log mass |
| Mass growth | Termwise \(1/q\ge 1/(4acd)\); `c=d=1` slice has distinct moduli (`slice_q_nodup`). `eventMass` is harmonic \(\sum 1/q\) | Deduplicated \(\mu(A)\ge k^2/\kappa\) (`DedupTwoLogMass`, harmonic, not event count). Raw \(H_5/4\,H_A^2\) factorisation |
| Two-stage identity | Exact product-space count: uncovered on \(\mathbb{Z}/HL\) equals the sum of fibre counts (`two_stage_count`). Hub-forced fibres contribute \(0\) (`two_stage_survivors`) | — |
| Finite density assembly | H1\(\times\)H2 combination: `finite_density_combine` and `finite_product_density_of`. Integer form of \(u(A)\le 2^{-\gamma k^2}\) on \(\mathbb{Z}/H\times\mathbb{Z}/L\) | `HubExponentialHypothesis`, `FibreSuenHypothesis`, `FiniteProductDensityBound` themselves |
| Transfer | Residue class: \(\le L/M+1\). Union of \(\lvert R\rvert\) classes: \(\le \lvert R\rvert(L/M+1)\). If \(\lvert R\rvert\le M\), \(\le L+M\) (`transfer_at_period`) | `PeriodSmallEnough`: a period \(M=o(x^{1-\delta})\). Transfer is **after** finite density |

`e_power_core_holds` is the combinatorial core. The replacement target is `FiniteProductDensityBound`: it follows from H1 and H2 by `finite_product_density_of`, and is **not** inhabited. Transfer is not an input. Finite density \(u(A)\le\exp(-\gamma(\log A)^2)\) and \(S_A\ll x^{1-\delta}\) remain open. Do not read `ExceptionalPowerSaving` as those statements.

---

## Lean layout

```
EPower/Covering/{Cell,Event,Dedup}.lean
EPower/Hub/{SmoothPart,PrimePowerHub,Fibre,ConditionalEvent}.lean
EPower/Probability/{DependencyGraph,PairMass,FiniteSuen,FibreSuen}.lean
EPower/Asymptotics/{CoveringMass,HubBound,FibreBound,DensityBound,Transfer}.lean
EPower.lean
```

`EPower.lean` now holds the Layer A cores above. The split below is
the intended later layout, not the present file. Conceptually:

```lean
theorem e_power_of
    (hMass     : MassGrowth)
    (hHub      : HubExponentialBound)
    (hFibre    : FibreExponentialBound)
    (hTransfer : DensityCountTransfer) :
    ExceptionalPowerSaving := ...
```

Do not start by formalising the most general Suen inequality. Prove a
finite version on these product spaces, or a specialised correlation
inequality for congruence cylinders. Do not assume Suen is the
shortest formal route.

---

## Computation as conjecture generation

`e_power_fibre_moments.py` computes, for increasing \((A,T)\):

- the deduplicated family;
- the prime-power hub \(H=\operatorname{lcm}_i(s_i)\);
- a Monte Carlo (or exact, when \(H\) is small) estimate of
  \(P(\text{hub survives})\);
- the distributions of \(\mu_\rho\), \(\Delta_\rho\), \(\delta_\rho\),
  and \(-\mu_\rho+\Delta_\rho e^{2\delta_\rho}\);
- the worst fibres, not only means.

The purpose is to identify plausible uniform inequalities such as
\[
P(\text{hub survives})
\;\le\;
e^{-\gamma_H\mu(A)},
\qquad
\Delta_\rho\, e^{2\delta_\rho}
\;\le\;
(1-\theta)\mu_\rho
\]
with explicit constants. Those become candidate lemmas. They are not
proofs.

The older scripts `e_power_suen_moments.py` and
`e_power_suen_moments_large.py` remain the surrogate-mass check for
Lemma SM. They do not compute fibre quantities.

**First fibre scan** (`e_power_fibre_moments.py`, 200 product-space
samples; `e_power_fibre_moments_A8.json`). Deduplication is visible
already at these widths (180 cells → 170 events at \(A=6\); 320 → 300
at \(A=8\)). Estimated hub-survival coefficients
\(\hat\gamma_H=-\log P(\mathrm{hub})/\mu\) sit near \(0.10\)–\(0.19\).
The fibre Suen exponent \(-\mu_\rho+\Delta_\rho e^{2\delta_\rho}\) has
negative mean at \(T=5\), but a positive tail (and a positive mean at
\(A=8\), \(T=3\)). That is consistent with H1/H2 as a split, and with
the need for a large enough hub; it is not a uniform H2 check.

| \(A\) | \(T\) | events | \(\mu\) | \(P(\mathrm{hub})\) | \(\hat\gamma_H\) | mean Suen exp. |
|------:|------:|-------:|--------:|--------------------:|-----------------:|---------------:|
| 6 | 3 | 170 | 3.38 | 0.68 | 0.11 | \(-0.43\) |
| 6 | 5 | 170 | 3.38 | 0.54 | 0.19 | \(-1.85\) |
| 8 | 3 | 300 | 4.04 | 0.67 | 0.10 | \(+2.19\) |
| 8 | 5 | 300 | 4.04 | 0.53 | 0.16 | \(-1.47\) |

---

## Lemma SM (surrogate second moments; proved on paper)

Let \(Q(A)\) be the moduli \(q=4acd-1\) of the Lean cells
\(1\le a,c\le A\), \(1\le d\le 5\). Write \(\mu_{\mathrm{raw}}(A)=\sum 1/q\) and
\(\mu_\ell(A)=\sum_{\ell\mid q}1/q\). Let
\(\Delta_{\mathrm{surr}}(A,T)=\sum_{\ell>T}\mu_\ell^2\) (an upper bound
candidate for a *different* pair-mass) and
\(\delta_{\mathrm{ub}}(A,T)=\max_q\sum_{\ell\mid q,\,\ell>T}\mu_\ell\).
There is an absolute effective \(C\) such that for all \(A\ge 3\) and
\(3\le T\le 20A^2\),
\[
\Delta_{\mathrm{surr}}(A,T)
\;\le\;
C\Bigl(\frac{\mu_{\mathrm{raw}}(A)^2}{T}+\frac{(\log 2A)^2}{\sqrt T}+\log\log(2A^2+3)-\log\log T+1\Bigr),
\]
\[
\delta_{\mathrm{ub}}(A,T)
\;\le\;
C\mu_{\mathrm{raw}}(A)\Bigl(\frac{\log 2A}{T\log T}+\frac{1}{\sqrt T\log 2A}\Bigr).
\]
On the schedule \(T=\mu_{\mathrm{raw}}/\eta\) with fixed
\(\eta\in(0,1/4]\) one has \(\mu_{\mathrm{raw}}\asymp(\log A)^2\),
hence \(T\asymp(\log A)^2\), and both remainders are
\(o(\mu_{\mathrm{raw}}^2/T)\) and \(O(\mu_{\mathrm{raw}}/T)\).

**This does not imply Suen's inequality on the fibres.** It may be a
useful comparison bound if a separate argument relates
\(\Delta_{\mathrm{surr}}\) to \(\Delta_\rho\).

**Proof.** (i) *Divisors in an arithmetic progression.* For \(x\ge 1\),
\(q\ge 1\), \(a\in\mathbb{Z}\),
\[
\sum_{\substack{n\le x\\ n\equiv a\pmod q}} d(n)
\;\ll\;
\frac{x}{q}\log(2x)+\sqrt{x}.
\]
Write \(d(n)=\sum_{uv=n}1\) and take \(u\le\sqrt n\le\sqrt x\). For each
such \(u\), the cofactor \(v\) lies in a single residue class modulo
\(q/\gcd(u,q)\le q\), so there are \(\le x/(uq)+1\) values. Summing
\(\sum_{u\le\sqrt x}(x/(uq)+1)\) gives the bound. (The symmetric range
\(v\le\sqrt x\) is identical.)

(ii) *Weighted harmonic.* For a prime \(\ell\) and \(M\ge 1\),
\[
\sum_{j\le M}\frac{d(j\ell+1)}{j}
\;\ll\;
\bigl(\log(2M\ell)\bigr)^2+\sqrt{\ell}.
\]
Dyadic \(J\le j<2J\). Then \(1/j\le 1/J\) and (i) with \(x=2J\ell\),
modulus \(\ell\), residue \(1\), yields
\(\sum_{j\sim J}d(j\ell+1)\ll J\log(2J\ell)+\sqrt{J\ell}\). The dyadic
piece is \(\ll\log(2J\ell)+\sqrt{\ell/J}\). Summing \(O(\log M)\)
dyadic intervals gives the claim (the geometric series
\(\sum 2^{-k/2}\) absorbs the square-root terms).

(iii) *Pointwise bound on \(\mu_\ell\).* If \(\ell\mid 4acd-1\) then
\(4acd-1=j\ell\) for some \(1\le j\le 20A^2/\ell\). For each \(j\) the
number of cells is \(\le 5\,d(j\ell+1)\). Hence
\[
\mu_\ell
\;\le\;
\frac{5}{\ell}\sum_{j\le 20A^2/\ell}\frac{d(j\ell+1)}{j}
\;\ll\;
\frac{(\log 2A)^2}{\ell}+\ell^{-1/2},
\]
by (ii).

(iv) *Second moment.* Square (iii) and sum over primes \(T<\ell\le 20A^2\):
\[
\sum_{\ell>T}\mu_\ell^2
\;\ll\;
(\log 2A)^4\sum_{p>T}\frac1{p^2}
+(\log 2A)^2\sum_{p>T}\frac1{p^{3/2}}
+\sum_{p>T}\frac1p.
\]
The first sum is \(\ll 1/T\), the second \(\ll T^{-1/2}\), and the third
is \(\ll\log\log(2A^2)-\log\log T+1\) by Mertens. Since
\(\mu_{\mathrm{raw}}(A)\asymp(\log A)^2\), the leading term is
\(\ll\mu_{\mathrm{raw}}^2/T\).

(v) *Neighbour mass.* For a fixed cell of modulus \(q\le 20A^2\),
\[
\sum_{\substack{\ell\mid q\\\ell>T}}\mu_\ell
\;\ll\;
(\log 2A)^2\sum_{\substack{\ell\mid q\\\ell>T}}\frac1\ell
+\sum_{\substack{\ell\mid q\\\ell>T}}\ell^{-1/2}.
\]
The first inner sum is \(\le\omega_{>T}(q)/T\le(\log q)/(T\log T)\). The
second is \(\le\omega(q)\,T^{-1/2}\le(\log q)\,T^{-1/2}/\log 2\).
Multiplying by \((\log 2A)^2\asymp\mu_{\mathrm{raw}}\) gives the stated
bound on \(\delta_{\mathrm{ub}}\).

On \(T=\mu_{\mathrm{raw}}/\eta\asymp(\log A)^2\) the remainders of (iv)
are \(o(\mu_{\mathrm{raw}}^2/T)\) and
\(\delta_{\mathrm{ub}}=O(\mu_{\mathrm{raw}}/T)\). \(\square\)

**Surrogate check (\(A=24\to 2000\)).** The tables of the withdrawn
note are unchanged as measurements of \(\Delta_{\mathrm{surr}}\)
(`e_power_suen_moments.py`, `e_power_suen_moments_large.py`). Along
\(T/\mu_{\mathrm{raw}}\approx 5\), the ratio
\(R_\Delta=T\Delta_{\mathrm{surr}}/\mu_{\mathrm{raw}}^2\) settles near
\(0.13\) and the *surrogate* loss stays \(<0.15\,\mu_{\mathrm{raw}}\).
That is not a fibre Suen check.

---

## Withdrawn claim (21 August)

The statement
\[
S_A(x,2x)\ll x^{1-\delta}
\qquad\text{via one-stage hub-conditioned Suen plus }O(M_T)
\]
is **not a theorem of this note**. It remains a target of the
two-stage programme plus transfer. Vaughan, Mathematika **17** (1970),
193–198, is still the published comparison point
(\(\ll x\exp(-c(\log x)^{2/3})\)). A compiled power of \(x\) would sit
strictly above that bound and still below the k-budget. It is not
available today.

**Gate A.** Roadmap §6 is a paper in the sieve literature if and when
the finite density theorem and the transfer are proved. Gate A does
**not** pass `AnalyticSurvivorBound` into Lean. Formalising a
power-saving count under that name would encode a result that does
not empty the box.

---

## Current reading of the evidence

The original written proof is not correct as stated, particularly in
its treatment of conditioning.

Unconditional deduplicated mass still looks two-log: \(\mu(A)/(\log A)^2\)
falls toward \(H_5/4\) through \(A=256\), and about 95% of cells survive
`eraseDups`. `DedupTwoLogMass` is now the harmonic statement
\(\mu(2^k)\ge k^2/\kappa\), still uninhabited. The old event-count form
was vacuous (\(\lvert\mathrm{events}\rvert\sim A^2\gg k^2\)).

On surviving fibres the usable Janson mass is not two-log. At \(T=3\),
the worst-fibre Titu ratio \(\mu_\rho^2/(\mu_\rho+2\Delta_\rho)\) tracks
\(1.17\ln A\) from \(A=16\) to \(A=32\), while \(k^2=(\log_2 A)^2\) is
already larger at \(A=8\) and pulling away. Pair tax \(\Delta_\rho/\mu_\rho\)
is rising. Hub survival at \(T=3\) is exactly \(2/3\) on every enumerated
\(H=3^k\), so H1 as \(P\le 2^{-\gamma k^2}\) fails for fixed \(T\).

A \(T\in\{3,5,7,11\}\) grid at \(A=8,16,32\) does not repair the split.
Unconditionally, the first primes above \(T\) each divide \(8\)–\(15\%\)
of \(T\)-rough parts (stable in \(A\)). On surviving fibres those primes
own \(\Delta_\rho\). Raising \(T\) deletes one column and hands the tax
to the next prime, or (at \(T=11\)) kills \(\Delta\) and residual \(\mu\)
together. Worst-fibre Titu at \(A=32\) is \(4.0\)–\(4.2\) for every \(T\),
against \(k^2=25\). Even \(T=11\) only reaches \(-\log P/k^2\approx 0.07\)
on 30 samples. Growing \(T\) is not a two-log schedule for this hub.
These are finite-\(A\) measurements, not a proof that the Titu mass is
\(o((\log A)^2)\), but they are why Harris/FKG is the wrong next Lean
step: it upgrades \(\gamma\), not the mass.

The exponent, if it exists, is split between hub elimination and
large-prime coverage inside surviving fibres. A coefficient
substantially below \(1\) would still suffice for
\(E(x)\ll x^{1-\delta}\). No asymptotic conclusion should be drawn
from the surrogate tables.

---

## Priority

1. Deduplicate the covering-event family (Lean: done as definitions
   and the union-invariance theorem).
2. Implement the exact prime-power hub decomposition (definitions;
   `q=s\ell` still computational).
3. Formalise hub fibres and conditional events (Lean: fibre card
   \(\ell\) and \(P=1/\ell\) on a compatible fibre).
4. Define exact \(\mu_\rho,\Delta_\rho,\delta_\rho\) (Python; not Lean).
5. Extend the numerical experiments to search for uniform fibre
   inequalities (`e_power_fibre_moments.py`).
6. Prove a finite specialised Suen (or a cylinder correlation
   inequality) in Lean. Independent one-modulus count is done;
   fibre \(\Delta_\rho\) is not.
7. Prove the finite two-stage density theorem.
8. Prove explicit covering-mass growth after deduplication
   (termwise \(1/q\ge 1/(4acd)\) is done; two-log \(\kappa\) is not).
9. Density-to-count transfer: AP seed \(L/M+1\) is done; residual
   moduli are not.
10. Assemble `e_power_of` only after every dependency is
    kernel-checked or an explicit external hypothesis. The current
    `e_power_core_holds` is the combinatorial core, not the
    exceptional-set theorem.

**Immediate milestone:** recorded negative. Revival attempt 1
(largest-prime residual) failed both revival numbers through
\(A=32\). See `erdos-straus-E-power-decision.md`. Not inhabiting
H1/H2. Not the exceptional-set count.

## What this is not

- It is not QED, H_ES, or a retuned schedule that empties the box.
- It is not a resolution of dummy covering.
- It is not E_lane, T(A)\(^+\), or the T(3) lower bound.
- It is not a compiled improvement on Vaughan.
- Lemma SM is not Suen on the fibres.

**Dies if** H1 or H2 fail uniformly, or if after deduplication
\(\mu(A)=o((\log A)^2)\), or if the transfer cannot be proved at any
positive \(\delta\). Also dies if no specialised correlation
inequality applies and a general Suen cannot be formalised with the
exact fibre quantities.

**Next.** Revival attempt 1 (largest-prime residual) failed both
numbers through \(A=32\). Stop. See `erdos-straus-E-power-decision.md`.
Do not inhabit H1/H2. Do not formalise Harris/FKG. Do not start a
second split without a written reason both numbers would pass. Do not
restore the one-stage CDL. Do not treat \(O(H)\) as a discrepancy
bound. Do not densify covering. Do not run \(x=10^{10}\). Do not
discharge `AnalyticSurvivorBound`.
