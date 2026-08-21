<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# E_power — the \(x^{1-\delta}\) covering-box bound (claimed)

**Riley Betts Erdős–Straus programme, 21 August 2026.**
Roadmap §6; plan §§4e, 4h, 4k. Companion to `erdos-straus-E-partial.md`
(Gate A), `ErdosStraus.lean` (`Covering`, `covering_sound`). This file
**does not prove** the Erdős–Straus conjecture, does not empty the box,
and does not discharge `AnalyticSurvivorBound`.

E_lane (`erdos-straus-T-A.md`) is the \(d=1\) ClassRough floor, below
Vaughan. This note is the **full covering box**: integers in \([x,2x]\)
that avoid every cell of the Lean covering system at width
\(A=\exp(c\sqrt{\log x})\). That is a larger set than the exceptional
set of Erdős–Straus, so an upper bound here is an upper bound there.
Dummy covering (\(\mathrm{cond}\equiv 1\)) is a ClassRough nesting
phenomenon and does not apply to this object.

---

## Object

Lean `ES.Covering`: a cell \((a,c,d)\) covers \(n\) when
\(q=4acd-1\) divides \(cn+a\). The level-\(A\) system takes
\(1\le a,c\le A\) and \(1\le d\le 5\). `Survivor A n` means no such
cell covers \(n\). `covering_sound` converts a hit into a witness, so
every \(n\) for which \(4/n\) is not a sum of three unit fractions
is a survivor of every covering box. Write
\[
S_A(x,2x)
\;=\;
\#\{n:x\le n<2x,\;\mathrm{Survivor}(A,n)\}.
\]
The exceptional set of Erdős–Straus in the same interval is
\(\subseteq S_A(x,2x)\).

Naive cell mass:
\[
\mu(A)
\;=\;
\sum_{\substack{1\le a,c\le A\\1\le d\le 5}}\frac1{4acd-1}
\;\sim\;
\frac{H_5}{4}(\log A)^2,
\qquad
H_5=\frac{137}{60}.
\]
The events are dependent (small-prime hub). Raw Bonferroni on the cell
indicators diverges in practice at mean activation \(\mu\approx 2.2\)
(plan §4n, the same oscillation that kills spectral truncation). The
organization that replaces it is hub conditioning plus Suen/Janson.

---

## Why this sits below the k-budget

QED wants sifted mass \(>\log x\). Interval-intrinsic methods capture
mass \(\le C\log(\mathrm{level})\le C\log x\) (plan §4l). Power saving
wants mass \(\delta\log x\) with an explicit \(\delta<C\), so it does
not touch the ceiling and does not need dispersion, DFI, or H_ES.
That is why roadmap §6 is the first genuine theorem of the covering
count, and why Gate A records *this* paper against the Halberstam–Richert /
*Opera de Cribro* lineage before any analytic Lean.

The §4h correction is the dimension count: \(\sum_{p\le z}\rho(p)\log p/p
\sim c\log^2 z\), hence sieve dimension \(\asymp\log z\), not the number
of cells. Brun/FL at distribution level \(x^{1/2}\) forces
\(\log z\lesssim\sqrt{\log x}\). At that cap, captured mass is
\(\asymp\log x\) with a small implicit constant — a power of \(x\), not
Vaughan's \(\exp(-c(\log x)^{2/3})\).

---

## Lemma CDL (hub + Suen; claimed)

Suen, Random Structures Algorithms **1** (1990); Janson, ibid. (1990).
After conditioning on all primes \(p\le T\), the remaining covering
events live on the product space of coordinates \(n\bmod p\) for
\(p>T\). On that space
\[
u
\;\le\;
\exp\bigl(-\mu+\Delta e^{2\delta}\bigr),
\]
with \(\mu\) the total remaining mass, \(\Delta\) the mass on dependent
pairs (events sharing a large-prime coordinate), and \(\delta\) the
maximum neighbour mass.

### Lemma SM (second moments; proved)

Let \(Q(A)\) be the moduli \(q=4acd-1\) of the Lean cells
\(1\le a,c\le A\), \(1\le d\le 5\). Write \(\mu(A)=\sum 1/q\) and
\(\mu_\ell(A)=\sum_{\ell\mid q}1/q\). Let
\(\Delta(A,T)=\sum_{\ell>T}\mu_\ell^2\) (an upper bound for Suen's
pair-mass) and
\(\delta_{\mathrm{ub}}(A,T)=\max_q\sum_{\ell\mid q,\,\ell>T}\mu_\ell\)
(an upper bound for Suen's neighbour mass). There is an absolute
effective \(C\) such that for all \(A\ge 3\) and \(3\le T\le 20A^2\),
\[
\Delta(A,T)
\;\le\;
C\Bigl(\frac{\mu(A)^2}{T}+\frac{(\log 2A)^2}{\sqrt T}+\log\log(2A^2+3)-\log\log T+1\Bigr),
\]
\[
\delta_{\mathrm{ub}}(A,T)
\;\le\;
C\mu(A)\Bigl(\frac{\log 2A}{T\log T}+\frac{1}{\sqrt T\log 2A}\Bigr).
\]
On the E_power schedule \(T=\mu/\eta\) with fixed \(\eta\in(0,1/4]\)
one has \(\mu\asymp(\log A)^2\), hence \(T\asymp(\log A)^2\), and both
remainders are \(o(\mu^2/T)\) and \(O(\mu/T)\) respectively. In
particular \(\Delta e^{2\delta_{\mathrm{ub}}}=O(\eta\mu)\), which is
the input CDL needs.

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
\(\mu(A)\asymp(\log A)^2\) (double harmonic of \(1/(ac)\), \(d\le 5\)),
the leading term is \(\ll\mu^2/T\).

(v) *Neighbour mass.* For a fixed cell of modulus \(q\le 20A^2\),
\[
\sum_{\substack{\ell\mid q\\\ell>T}}\mu_\ell
\;\ll\;
(\log 2A)^2\sum_{\substack{\ell\mid q\\\ell>T}}\frac1\ell
+\sum_{\substack{\ell\mid q\\\ell>T}}\ell^{-1/2}.
\]
The first inner sum is \(\le\omega_{>T}(q)/T\le(\log q)/(T\log T)\). The
second is \(\le\omega(q)\,T^{-1/2}\le(\log q)\,T^{-1/2}/\log 2\).
Multiplying by \((\log 2A)^2\asymp\mu\) gives the stated bound on
\(\delta_{\mathrm{ub}}\).

On \(T=\mu/\eta\asymp(\log A)^2\) the remainders of (iv) are
\(o(\mu^2/T)\) and \(\delta_{\mathrm{ub}}=O(\mu/T)\), so
\(\Delta e^{2\delta_{\mathrm{ub}}}=O(\eta\mu)\). \(\square\)

Lemma SM is the written estimate that §4e treated as a measurement.
CDL now takes it as input: \(T=\mu/\eta\) with a fixed small
\(\eta\in(0,1/4]\), hence \(\Delta e^{2\delta}=O(\eta\mu)\), and the
conditioned uncovered density satisfies
\[
u(A)
\;\le\;
\exp\bigl(-(1-O(\eta))\,\mu(A)\bigr)
\;=\;
\exp\bigl(-(1-O(\eta))\,\kappa_{\mathrm{cov}}\log^2 A\bigr).
\]
Fixed \(A\) is the density theorem of plan §4e. Growing \(A\) uses the
same inequality with the \(T\)-schedule of the next lemma. Prime-\(m\)
cells (plan §4d, \(\kappa^*\approx 0.29\)) are the singleton-support
case and are included; composite cells are what the hub is for.

This is the organization that raw truncation does not supply. Bonferroni
at \(\mu\approx 2.2\) oscillates; Suen does not.

**Second-moment check (\(A=24\to 240\); `e_power_suen_moments.py`).**
The §4e gates were at \(A=24\)–\(48\). The Lean covering cells
(\(q=4acd-1\), E_power's object) were run at
\(A\in\{24,48,80,120,160,200,240\}\) and \(T\in\{13,23,37,53,97\}\).
Write \(R_\Delta=T\sum_{\ell>T}\mu_\ell^2/\mu^2\) and
\(R_\delta=T\,\delta_{\mathrm{ub}}/\mu\).

Lean family, \(R_\Delta\) at fixed \(T\):

| \(A\) | \(T=13\) | \(T=23\) | \(T=37\) | \(T=53\) | \(T=97\) |
|------:|---------:|---------:|---------:|---------:|---------:|
| 24 | 0.244 | 0.225 | 0.238 | 0.198 | 0.149 |
| 48 | 0.229 | 0.204 | 0.213 | 0.188 | 0.160 |
| 80 | 0.222 | 0.197 | 0.205 | 0.177 | 0.156 |
| 120 | 0.219 | 0.195 | 0.203 | 0.177 | 0.156 |
| 200 | 0.216 | 0.192 | 0.199 | 0.174 | 0.153 |
| 240 | 0.215 | 0.190 | 0.198 | 0.173 | 0.153 |

OLS of \(R_\Delta\) against \(\log A\) has slope \(-0.012\) to
\(-0.016\) at \(T\le 53\), and \(+0.00004\) (flat) at \(T=97\). The
shape \(\Delta\ll\mu^2/T\) **persists and does not grow with \(A\)**
on this range. Implied constant \(R_\Delta\approx 0.15\)–\(0.25\).

At **fixed** \(T=13\), the neighbour ratio \(R_\delta\) climbs
\(1.56\to 2.54\) and the Suen loss \(\Delta e^{2\delta}/\mu\) explodes
(\(1.2\to 1400\)). That is why Lemma Transfer takes \(T=\mu/\eta\), not
a fixed hub. Along the schedule \(T/\mu\approx 4.5\)–\(5\):

| \(A\) | \(T\) | \(T/\mu\) | \(R_\Delta\) | \(R_\delta\) | \(\Delta/\mu\) | loss/\(\mu\) |
|------:|------:|----------:|-------------:|-------------:|---------------:|-------------:|
| 24 | 37 | 4.40 | 0.238 | 1.80 | 0.054 | 0.122 |
| 48 | 53 | 4.56 | 0.188 | 2.23 | 0.041 | 0.110 |
| 80 | 53 | 3.69 | 0.177 | 2.09 | 0.048 | 0.149 |
| 200 | 97 | 4.85 | 0.153 | 1.97 | 0.031 | 0.071 |
| 240 | 97 | 4.57 | 0.153 | 1.94 | 0.034 | 0.078 |

On that slice \(R_\delta\) is flat, the Suen loss stays \(<0.15\,\mu\),
and \(R_\Delta\) has already fallen to \(0.15\). This is the small-\(c\)
window of E_power. The \(A=48\) extrapolation does not fail at the
first decade of growth.

The plan-\((a,d,m)\) family (large primes of \(m\)) has much smaller
\(R_\Delta\) and does not reproduce the cited \(0.141\to 0.057\)
\(T\)-scaling under this \(\Delta=\sum\mu_\ell^2\) normalisation; E_power
uses the Lean cells, where \(R_\Delta\sim 0.22\) at \(A=48\), \(T=13\)
is the same order as that citation.

**Extended check (\(A=400\to 2000\); `e_power_suen_moments_large.py`).**
Lemma SM is the bound for every \(A\); the scan is the implied
constant, not existence. Lean cells only, two-pass, same mass \(1/q\).
\(A\in\{400,800,1200,1600,2000\}\), \(T\in\{13,37,97,199,409\}\).

Lean family, \(R_\Delta\) at fixed \(T\):

| \(A\) | \(\mu\) | \(T=13\) | \(T=37\) | \(T=97\) | \(T=199\) | \(T=409\) |
|------:|--------:|---------:|---------:|---------:|----------:|----------:|
| 400 | 24.92 | 0.212 | 0.196 | 0.153 | 0.131 | 0.121 |
| 800 | 30.39 | 0.211 | 0.195 | 0.154 | 0.130 | 0.119 |
| 1200 | 33.84 | 0.210 | 0.195 | 0.155 | 0.130 | 0.119 |
| 1600 | 36.41 | 0.209 | 0.195 | 0.156 | 0.130 | 0.119 |
| 2000 | 38.46 | 0.209 | 0.195 | 0.157 | 0.131 | 0.119 |

At \(T=13\) and \(T=199,409\), \(R_\Delta\) is flat or still falling.
At \(T=97\) it drifts \(0.153\to 0.157\) because that hub is leaving
the schedule (\(T/\mu: 3.89\to 2.52\)). Implied constant
\(R_\Delta\approx 0.12\)–\(0.21\), the same range as \(A\le 240\).

Along \(T/\mu\approx 5\):

| \(A\) | \(T\) | \(T/\mu\) | \(R_\Delta\) | \(R_\delta\) | \(\Delta/\mu\) | loss/\(\mu\) |
|------:|------:|----------:|-------------:|-------------:|---------------:|-------------:|
| 400 | 97 | 3.89 | 0.153 | 2.44 | 0.039 | 0.138 |
| 800 | 199 | 6.55 | 0.130 | 2.53 | 0.020 | 0.043 |
| 1200 | 199 | 5.88 | 0.130 | 3.29 | 0.022 | 0.068 |
| 1600 | 199 | 5.47 | 0.130 | 3.21 | 0.024 | 0.077 |
| 2000 | 199 | 5.17 | 0.131 | 3.16 | 0.025 | 0.086 |

On that slice \(R_\Delta\) has settled at \(0.13\), \(R_\delta\) is
\(O(1)\) (\(2.4\)–\(3.3\)), and the Suen loss stays \(<0.15\,\mu\).
Fixed \(T=13\) remains the trap (loss \(6\cdot 10^3\to 1.5\cdot 10^7\)).
The shape of Lemma SM holds through \(A=2000\). It is not a check at
\(A=10^4\); past this range the lemma, not the table, is the bound.

---

## Lemma Transfer (count at small \(c\); claimed)

Take \(A=\exp(c\sqrt{\log x})\) and \(\alpha=\kappa_{\mathrm{cov}}c^2\),
so \(\mu(A)\sim\alpha\log x\). Hub modulus
\(M_T=\prod_{p\le T}p=\exp(\theta(T))\) with \(T=\mu/\eta\) has
\[
M_T
\;=\;
x^{\alpha/\eta+o(1)}.
\]
Choose \(\eta=1/4\) and \(c>0\) small enough that \(\alpha/\eta<1/2\)
and the Suen loss \(O(\eta)\) leaves a positive net exponent. Then:

- the main term, summed over residues \(\rho\bmod M_T\), is
  \(\ll x\cdot\exp(-(1-O(\eta))\mu)=x^{1-(1-O(\eta))\alpha}\);
- the discrepancy is \(O(M_T)=O(x^{\alpha/\eta})\), strictly smaller
  than the main term.

The same small-\(c\) constraint is the §4h fundamental-lemma cap
\((\log z)^2\lesssim\log x\) with \(z\) the largest covering modulus
retained (\(z\asymp A^2\), \(\log z\asymp 2c\sqrt{\log x}\)). Both
constraints are satisfied for an effective interval of \(c\).

---

## Theorem E_power (claimed)

There exist effective constants \(c,\delta,X_0>0\) such that for all
\(x\ge X_0\) and \(A=\exp(c\sqrt{\log x})\),
\[
S_A(x,2x)
\;\ll\;
x^{1-\delta}.
\]
The implied constant is effective. Consequently the number of
\(n\in[x,2x]\) for which \(4/n\) is not a sum of three unit fractions
is \(\ll x^{1-\delta}\).

Proof: Lemma CDL at this \(A(x)\) with the \(T\)-schedule of Lemma
Transfer; exceptions \(\subseteq\) survivors. Explicitly,
\(\delta=(1-O(\eta))\kappa_{\mathrm{cov}}c^2\) for the admissible
\((c,\eta)\) above. A numerical \(\delta\) is not the content; positivity
and effectivity are.

**Honest comparison.** Vaughan, Mathematika **17** (1970), 193–198:
exceptions among all \(n\le x\) are \(\ll x\exp(-c(\log x)^{2/3})\).
E_power is a power of \(x\), strictly stronger. The objects match
(all \(n\), not only hard primes). E_lane remains the \(d=1\)
ClassRough floor, weaker than Vaughan, because that lane carries only
\(\log A\) mass. This theorem is the full-box record; that one is the
aligned-prime floor. Both are claimed; they are not the same bound.

**Gate A.** Roadmap §6: this theorem is a paper in the sieve literature;
it is not Lean. The write-up is this note. Gate A does **not** pass
`AnalyticSurvivorBound` into Lean:
that interface asks for zero large hard survivors, i.e. mass
\(>\log x\), which is the k-budget ceiling. Formalising a power-saving
count under that name would encode a result that does not empty the
box. Write it on paper; do not compile it as QED progress.

---

## What this is not

- It is not QED, H_ES, or a retuned schedule that empties the box.
- It is not a resolution of dummy covering. Dummy covering remains the
  live kill of a QED-scale ClassRough box; extra ClassRough slices that
  do not cut are not mass. Covering *cells* on integers still cut
  residue classes, which is why this count survives that kill.
- It is not E_lane, T(A)\(^+\), or the T(3) lower bound.
- It does not use spectral Selberg-\(L^2\) organization (plan §4n rungs
  3/3b). That is the H_ES road. This theorem uses Suen on the cells.
- It is not Lean.

**Dies if** Lemma SM fails (it is proved) or if the implied ratios
\(R_\Delta\), \(R_\delta\) grow with \(A\) on the schedule \(T\asymp\mu\)
badly enough that \(\Delta e^{2\delta}\) is no longer \(O(\eta\mu)\).
They do not, on \(A=24\to 2000\)
(`e_power_suen_moments.py`, `e_power_suen_moments_large.py`):
\(R_\Delta\) settles at \(0.13\) along \(T/\mu\approx 5\), and the
Suen loss stays \(<0.15\,\mu\). Also dies if no positive \((c,\eta)\)
makes the discrepancy smaller than the Suen main term — the same
small-\(c\) constraint already in Lemma Transfer.

**Next.** Record this note with `erdos-straus-E-partial.md` and plan
§§4e, 4h against the Halberstam–Richert / *Opera de Cribro*
lineage. Do not densify covering. Do not run \(x=10^{10}\). Do not
assault H_ES. Do not discharge `AnalyticSurvivorBound`.
