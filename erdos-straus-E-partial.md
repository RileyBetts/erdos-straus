<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# E_partial — Gate A write-up

**Riley Betts Erdős–Straus programme, 21 August 2026.**
Vehicle for T(A) = C4_1 and the C2 null, through Gate A
(`erdos-straus-road-to-lean-qed.md` Step 3). Companion to
`erdos-straus-T-A.md`, `erdos-straus-E-power.md`, plan §4k / §4v,
`ErdosStraus.lean` (`AnalyticSurvivorBound`).

This file **does not prove** the Erdős–Straus conjecture, does not
discharge `AnalyticSurvivorBound`, and does not claim H_ES. It records
what may be written as a theorem, what Gate A forbids, and why the
scans stop a retune of the QED schedule.

---

## What E_partial is

Plan §4k named two things as the same write-up: a truncated
inclusion–exclusion at covering width \(A\le\exp(c\sqrt{\log x})\), and
the classical \(x^{1-c}\) exceptional-set bound (the known cap). That
identification is a **consistency check**, not a QED path. Truncation
captures only the bounded-coupling slice (the Poisson-\(j\) law of
§4k); the k-budget invariant of §4l already says interval-intrinsic
randomness cannot buy the remaining mass.

After T(A), E_partial has a sharper job. It is the **vehicle that
carries a uniform-\(A\) Selberg upper bound up to Gate A**, and then
stops. Two layers:

**Layer 1 (T(A)\(^+\), uniform Selberg; E_lane the floor).** For each
fixed covering width \(A\),
\[
S(A,x)\;\ll\; C_{\mathrm{sieve}}(A)\,(\log x)^{-\beta(A)},
\]
unconditionally (`erdos-straus-T-A.md`, `c4_sieve_constant.py`).
\(\beta(A)=\sum_{a\le A}1/\varphi(4a)\sim c_\varphi\log A\).
\(C_{\mathrm{sieve}}(A)=\Gamma(\beta+1)\exp(\gamma\beta-B(A))\) with
the \(\Gamma\)-factor \(\exp(o(\log^2 A))\) as a theorem. Selberg does
not re-create the covering law; if \(c'(\infty)\to\kappa\) the
saturation lives in the marginals. Dummy covering remains the live
kill.

**E_lane (claimed; the \(d=1\) floor).** Uniform T(A)\(^+\) at
\(A=\exp(c\sqrt{\log x})\) gives
\[
E_{\mathrm{lane}}(x)
\;\ll\;
x\exp\bigl(-c'\sqrt{\log x}\,\log\log x\bigr),
\]
effective constants, one FL lemma. Sits below Vaughan
\(\exp(-c(\log x)^{2/3})\) because the \(d=1\) lane carries \(\log A\)
mass against the full box's \(\log^2 A\). E_power is that full-box
bound, claimed in `erdos-straus-E-power.md`. This paragraph is the
\(d=1\) floor, not that theorem.

**Layer 0 (E_power, repaired programme).** The 21 August claim
\(S_A(x,2x)\ll x^{1-\delta}\) via one-stage hub-conditioned Suen plus
an \(O(M_T)\) transfer is **withdrawn**
(`erdos-straus-E-power.md`, 22 Aug 2026). The surviving programme is a
two-stage finite covering-density theorem and a separate
density-to-count transfer. Lemma SM remains a surrogate-mass estimate,
checked through \(A=2000\) (`e_power_suen_moments_large.py`); it is
not Suen's fibre \(\Delta\). This layer still sits below the k-budget
ceiling. It does not empty the box and is not
`AnalyticSurvivorBound`. Dummy covering does not apply to this object
(covering cells on integers still cut).

Passage from Layer 1 to a *growing* \(A\) on the QED schedule
\(A=\exp(c\sqrt{\log x})\) with \(\kappa c^2>1\) is **not included**.
That passage is exactly the two live risks: \(c'\ge\kappa\), and
\(\mathrm{cond}\equiv 1\) making extra slices dummy covering mass.

---

## Euler pieces (accounted; not the theorem)

Divided out of \(C(A)\) before selection is tracked. None of these is
T(A); none retunes \(\kappa\).

| Piece | Measurement | Role |
|---|---|---|
| Pair ratios \(\rho_{ab}/(\rho_a\rho_b)\) | mean \(1.000\) to \(A=120\) | lemma |
| Prime-aligned Euler factor \(C_{\mathrm{euler}}(A)\) | \(0.91\), flat \(A=40\to 200\); zero residue collisions | quadratic Euler term in the covering product |
| ClassRough composites \(\Pi_{\mathrm{gen}}(a,\sqrt{x})\) | matches \(\rho_{\mathrm{CR}}/\rho_{\mathrm{prime}}\) at \(A=40\) to \(3\%\) | lives in the marginals \(\rho_a\), not in \(\hat C\) |
| C2 covering-symbol correlations | mean \(\lvert z\rvert=0.73\) covering vs \(0.89\) inert at \(A=80\); flagship \((p/11)(p/19)\) has \(z=-0.23\) | **does not fire**; extra shrinkage has the wrong sign for \(\hat C>1\) |

The leftover after these factors is the selection sequence \(\hat C(A)
=S/\prod\rho_a=\prod e(a)\). At \(x=10^9\): \(\hat C(80)=2.69\),
\(\hat C(200)=6.92\), \(\log\hat C\sim 0.104\log^2 A\) on \(A\ge 40\)
(\(R^2=0.998\)), against \(\kappa=0.139\).

Do not put a character-layer main term back into T(A). C2 as
reciprocity super-multiplicativity is a measured null, like C7.

---

## Gate A

Roadmap Step 3: E_power is written (`erdos-straus-E-power.md`). Gate A
forbids compiling that theorem as QED; it is a paper, not Lean.
The analytic interface in Lean is

```lean
def AnalyticSurvivorBound (Alevel : Nat → Nat) (X0 : Nat) : Prop :=
  ∀ p, X0 ≤ p → IsPrime p → HardClass p → Covered (Alevel p) p
```

This is the single load-bearing unproven target. Gate A is the
decision of what may be formalised *toward* that interface.

**Gate A admits.**

- Elementary Layer A, already compiled: covering soundness, divisor-form
  equivalence, `hard_landing_of_interface`, the finite-certificate
  schema. No change.
- A paper of Layer 1: T(A) as constant-tracking of \(C(A)\), with the
  Euler table above in the introduction and the two die conditions in
  the abstract. Opening case: T(3)\(^+\) claimed
  (\(S(3,x)\ll(\log x)^{-3/2}\); `erdos-straus-T-3.md`); matching lower
  bound open at completion of \(q>x^{1/2}\). **True vehicle: T(A)\(^+\)**,
  claimed in `erdos-straus-T-A.md` (`c4_sieve_constant.py`):
  \(S(A,x)\ll C_{\mathrm{sieve}}(A)\,(\log x)^{-\beta(A)}\) with
  \(\Gamma(\beta+1)e^{\gamma\beta}=\exp(o(\log^2 A))\) a theorem and
  expected \(B(A)=O(\log A)\). **E_lane** is the \(d=1\) floor
  \(x\exp(-c'\sqrt{\log x}\,\log\log x)\), below Vaughan. **E_power**
  is the covering-box count \(S_A\ll x^{1-\delta}\)
  (`erdos-straus-E-power.md`), below the k-budget, above Vaughan. Dummy
  covering remains the live kill of a retuned QED schedule.
- Layer 0 as that E_power paper, explicitly not QED, explicitly not
  `AnalyticSurvivorBound`. Gate A is now a written theorem against the
  sieve literature; it still forbids compiling it as QED progress.
- The C2 null and the G–S dictionary
  (`erdos-straus-gs-reformulation.md`) as a dictionary, not as extra
  independent characters.

**Gate A forbids.**

- Discharging `AnalyticSurvivorBound` in Lean, or any lemma whose
  conclusion is zero large hard survivors.
- Treating E_partial as H_ES, or assaulting H_ES.
- Retuning \(\kappa\) from \(C_{\mathrm{euler}}\approx 0.91\) or from
  the x-scan slope ratio \(0.868\). Those are Euler / Mertens pieces of
  the marginals.
- Densifying covering, or growing \(A\) on the QED schedule, while
  \(\mathrm{cond}\equiv 1\). Extra slices that do not cut are not mass.
- Formalising a Wirsing theorem that \(C(A)\) exists at each fixed \(A\)
  as if that saved the schedule.
- Running \(x=10^{10}\).

**Gate A does not pass E_power into Lean.** The power-saving theorem
does not empty the box. Formalising it under `AnalyticSurvivorBound`
would encode a result that is not the QED interface. Write it on paper
(`erdos-straus-E-power.md`); keep it out of Lean as progress toward
`erdos_straus_of_interface`.

---

## Why the schedule cannot be retuned

Covering law (prime-aligned Mertens, \(\kappa=0.139\)):
\[
\prod_{a\le A}\rho_a \;\sim\; \exp\bigl(-\kappa\log^2 A\bigr).
\]
Selection, as measured at \(x=10^9\), \(A\le 200\):
\[
\hat C(A)\;\sim\;\exp\bigl(c'\log^2 A\bigr),\qquad c'=0.104.
\]
Net if both persist:
\[
S \;\sim\; \exp\bigl(-(\kappa-c')\log^2 A\bigr)
=\exp\bigl(-0.035\log^2 A\bigr).
\]
QED needs sifted mass \(\gtrsim\log x\), i.e.
\(A=\exp(c\sqrt{\log x})\) with \(c>1/\sqrt{\kappa_{\mathrm{eff}}}\).

| Schedule | \(\kappa_{\mathrm{eff}}\) | \(c_{\min}\) | \(A\) at \(x=10^9\) |
|---|---|---|---|
| Naive covering (\(\hat C=1\)) | \(0.139\) | \(2.68\) | \(\sim 2\cdot 10^5\) |
| Retuned by \(c'=0.104\) | \(0.035\) | \(5.35\) | \(\sim 4\cdot 10^{10}\) |

The retune is not a slightly larger box. It is a qualitatively larger
level, and it assumes extra slices still cut.

They do not, already at this \(x\). \(\mathrm{cond}(a)\to 1\) past
\(a=80\) (mean \(0.993\) on \(a=161..200\)). Retention \(80\to 200\) is
\(0.275\) against \(\prod_{81}^{200}\rho_a=0.107\). If
\(\mathrm{cond}\equiv 1\) persists, then \(S(A,x)=S(A_0,x)\) for all
\(A\ge A_0\), and growing the box buys nothing.

At this \(x\): \(1{,}587{,}581\) hard primes; \(S(200)\approx 9.8\times
10^{-5}\) (\(155\) alive). Emptying the box wants \(S\lesssim 6\times
10^{-7}\). Dummy covering leaves those \(155\) in place at every larger
\(A\).

Sub-criticality \(c'<\kappa\) is therefore **not** a green light. The
live kill is dummy covering. Layer 0 (power saving at slowly growing
\(A\)) is compatible with a still-nonempty exceptional set; that is
why it is the known cap, not QED. E_power uses covering cells on
*integers*, a different object, and is compatible with a still-nonempty
ClassRough exceptional set.

---

## What a paper of E_partial may claim

**May claim (on paper, T(A)\(^+\) and E_lane).** Uniform Selberg at
fixed \(A\); E_lane
\(x\exp(-c'\sqrt{\log x}\,\log\log x)\) as the \(d=1\) floor, below
Vaughan, effective constants. T(3)\(^+\) is the \(A=3\) case.

**May claim (on paper, E_power).** \(S_A(x,2x)\ll x^{1-\delta}\) at
\(A=\exp(c\sqrt{\log x})\), effective constants
(`erdos-straus-E-power.md`). This is §4k item 1 / roadmap §6, and is
not `AnalyticSurvivorBound`. It beats Vaughan; it does not empty the
box.

**May not claim.** Zero large hard survivors; a retuned schedule that
empties the box; extra independent characters from reciprocity; that
Wirsing at fixed \(A\) is the theorem.

The G–S dictionary attaches to a *conditioned* pretentious tail if cond
sticks, not to “many weakly dependent free characters.” That dictionary
goes with the C2 null. It does not extract bits.

---

## Status of the worklist

1. T(A) empirical shadow — done (`c4_S_xscan.py`, `c4_growing_A.py`;
   Euler and \(\Pi_{\mathrm{gen}}\) accounted).
2. C2 — done, does not fire (`c4_c2_symbols.py`).
3. **This note** — Gate A write-up of E_partial as the vehicle for
   (1)–(2). Not an assault on H_ES.
4. G–S memo — already written.
5. No-Vieta — already compiled.

**Remaining mathematics**, not this quarter's in-house compute, in the
same **genuinely hard frontier** bucket as roadmap §9's Brauer-\(\alpha\)
fusion: the T(3) lower bound's sharp question (`erdos-straus-T-3.md`) —
does a joint well-factorable weight framework exist for the moving CRT
residue \(\alpha(d_1,d_2,d_3)\), and if not, can one be built for the
three-kernel case? The \(r_\chi\to\) Kloosterman look is a range no-go
at the stall (Pascadi / MQW / Blomer–Pascadi; `erdos-straus-T-3.md`).
Zheng two-modulus (arXiv:2512.22798) is a range no-go on
\(d_1\approx d_2\approx\sqrt{x}\) (`erdos-straus-T-2.md`), not T(3)
progress. Escape 1 (weaker \(c_-\) / almost-certificates) remains the paper's
outlook if that framework does not exist. The three-step plan and both
escapes stay in that note.
T(A)\(^+\) is written: Selberg upper half survives; E_lane is the
\(d=1\) floor, below Vaughan; E_power is the covering-box count, above
Vaughan. \(\mathrm{cond}\equiv 1\) remains the live kill of a QED
ClassRough schedule. Shared-certificate
inheritance does not explain that tail (`c4_certificates.py`). Do not
simulate a third decade of \(x\). Do not densify covering.

---

## What this note does not do

- It does not prove T(A) as a two-sided bracket, E_partial as a
  zero-survivor theorem, or H_ES. E_lane is the \(d=1\) floor. E_power
  is a Vaughan-beating exceptional set and is not a QED.
- It does not change Lean. Gate A forbids compiling Layer 0 as
  progress toward `erdos_straus_of_interface`.
- It does not reopen geometry as a proof path (plan §4v).
- It does not license C7, Selmer/Harpaz/Campana, or \(x=10^{10}\).
