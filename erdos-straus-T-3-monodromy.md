<!-- Copyright (c) 2026 Riley Betts Ltd. SPDX-License-Identifier: MIT -->
# T(3) — does joint monodromy independence give traction?

**Riley Betts Erdős–Straus programme, 21 August 2026.**
Companion to `erdos-straus-T-3.md` (Phase 4, the joint well-factorable
question), `erdos-straus-T-3-delta.md` (δ-symbol look, closed). Lead
reference: É. Fouvry, E. Kowalski, Ph. Michel, W. Sawin, *Bilinear forms
with trace functions*, arXiv:2511.09459 (v3, 11 Aug 2026). Background:
N. M. Katz, *Gauss sums, Kloosterman sums, and monodromy groups*, Ann. of
Math. Studies **116** (1988); É. Fouvry, E. Kowalski, Ph. Michel, Duke
Math. J. **163** (2014); *idem*, Geom. Funct. Anal. **25** (2015);
E. Kowalski, Ph. Michel, W. Sawin, Ann. of Math. **186** (2017).

This file **does not prove** the Erdős–Straus conjecture and does not
claim T(3) progress. It does not reopen Zheng, leg-sacrifice, or the
Farey–\(k\) incompatibility. Not Lean. Do not densify covering. Do not
discharge `AnalyticSurvivorBound`.

**Dies if.** The remaining T(3) kernel
\(\chi_2(d_2)\chi_3(d_3)\,K(\,\cdot\,;D)\) is not the trace function of
a gallant \(\ell\)-adic sheaf on a product variety over a fixed
\(\mathbf{F}_q\). Goursat–Kolchin–Ribet in arXiv:2511.09459 does not
apply. After switching, a prime modulus cannot exceed \(\sqrt{x}\).
Composite \(D\) has reducible monodromy (two prime factors: \(\mathbf{SO}_4\),
which FKMS carves out as not gallant). Range check:
`t3_monodromy_ranges.py`.

---

## Where this sits

Three routes to completing T(3) — Maynard-type uniform residues, Zheng,
and a joint δ-symbol — terminate at a phase depending jointly on two or
three quadratic-character moduli. Concretely, after the reductions
already on paper, one wants square-root cancellation in a correlation
\[
\sum_{d_2,d_3}\chi_2(d_2)\chi_3(d_3)\,K(\,\cdot\,;D),\qquad
D=\mathrm{lcm}(d_2,d_3)\asymp d_2 d_3,
\]
uniformly as \(d_2,d_3\) both run up to (and, before switching, past)
\(\sqrt{x}\). The characters are the odd real characters mod \(8\) and
\(12\); \(K\) is the Kloosterman-type kernel that appears once Type II
is opened (Phase 1: \(S(am,n;D)\) or \(e(a\overline{m}/D)\)).

The question is whether that product is the trace function of a single
\(\ell\)-adic sheaf on a product in \((d_1,d_2,d_3)\) (or the subset
after eliminating \(p\)), and whether its geometric monodromy is large
enough, via Goursat–Kolchin–Ribet, to beat per-modulus Weil.

---

## What arXiv:2511.09459 actually bounds

FKMS work with a constructible \(\ell\)-adic sheaf \(\mathcal{F}\) on
\(\mathbf{A}^1_{\mathbf{F}_q}\) for a **prime** \(q\), mixed of weights
\(\le 0\), pure of weight \(0\) on a dense open. The geometric monodromy
group \(G\subset\mathrm{GL}_r\) is **gallant** if it acts irreducibly and
either \(G^0\) is a simple algebraic group, or \(G\) is finite and
contains a quasisimple normal subgroup acting irreducibly (Definition
1.2). Kloosterman \(\mathrm{Kl}_2\) on \(\mathbf{F}_q\) is the model
example: \(G=G^0=\mathbf{SL}_2\) (Katz, GKM; FKMS §9.6).

Theorem 1.3 (Type I/II) and Theorem 1.1 bound
\(\sum_{m,n}\alpha_m\beta_n K(m^b n^c)\) for \(1\le M,N\le q/2\), with a
saving when \(M\ge q^\delta\) and \(MN\ge q^{3/4+\delta}\). Theorem 1.4
(proved in §7, “Bounds for trilinear sums with monomial arguments”)
bounds
\[
\sum_{j,m,n}\alpha_j\beta_m\gamma_n K(j^a m^b n^c)
\]
for \(J\le 4q\), \(MN\le 4q\), and is nontrivial for \(J\ge q^\delta\)
and \(MN\ge q^{1/2+\delta}\). Section 7 first regroups the monomial into
a bilinear form \(K(uv)\) on \(\mathbf{F}_q^\times\times\mathbf{F}_q^\times\).
The third variable is an extra *argument*, not an extra modulus.

Family tree: Kowalski–Michel–Sawin, Ann. of Math. **186** (2017) did
Kloosterman and hypergeometric sheaves; FKMS replace that case-by-case
list by the gallant condition. That 2017 paper is already adjacent to
Blomer–Pascadi in `erdos-straus-T-3.md` Phase 3. Fouvry–Kowalski–Michel,
Duke **163** (2014), wrap \(\sum_p K(p)\) for a trace function *modulo a
fixed \(q\)*: the prime is the argument, not the modulus.

\(\mathbf{SO}_4\) and \(\mathbf{O}_4\) are **not gallant** (FKMS §1.3):
\(\mathbf{SO}_4\cong(\mathbf{SL}_2\times\mathbf{SL}_2)/\{\pm 1\}\). They
treat a rank-\(4\) sheaf on one \(\mathbf{F}_q\) with that monodromy as
sulfatic / oxozonic, and prove a restricted substitute (Theorem 1.6),
still over a prime field.

---

## Four structural failures

**1. Wrong category.** An \(\ell\)-adic sheaf on \(\mathbf{A}^1_{\mathbf{F}_q}\)
(or on a product variety over \(\mathbf{F}_q\)) has a *fixed* finite
field. The T(3) kernel \(K(\,\cdot\,;D)\) has \(D=\mathrm{lcm}(d_2,d_3)\)
depending on the summation point. That is not a trace function on a
product variety over a fixed \(\mathbf{F}_q\). GKR in FKMS §3 compares
several sheaves on the *same* \(\mathbf{A}^1_k\), not Kloosterman sheaves
over \(\mathbf{F}_{d_2}\) and \(\mathbf{F}_{d_3}\) for varying \(d_2,d_3\).

**2. The characters are not gallant.** \(\chi_2,\chi_3\) have conductor
\(8\) and \(12\). As sheaves they are rank-\(1\) Kummer sheaves with
finite abelian monodromy. Abelian groups are not quasisimple; rank \(1\)
is not the simple-\(G^0\) case (\(r\ge 2\)). They can be absorbed as
FKMS coefficients \(\alpha,\beta\) only when \(q\) is fixed and
\(d_2,d_3\) are arguments of \(K(\,\cdot\,;q)\). Here they vary the
modulus.

**3. Prime moduli cannot leave the BV range.** After switching,
\(d_a\le\sqrt{x}\). A prime \(D\) divides some \(d_a\), hence
\(D\le\sqrt{x}\). FKMS theorems are stated for prime \(q\). The only
prime-\(q\) cell in the switched expansion is the BV wall \(Q_D=1/2\).
(`t3_monodromy_ranges.py`, `lemma_prime_modulus_after_switch`.)

**4. Composite \(D\) is not gallant.** Twisted multiplicativity
\[
S(a,b;mn)=S(a\overline{n},b\overline{n};m)\,S(a\overline{m},b\overline{m};n)
\quad((m,n)=1)
\]
presents \(K(\,\cdot\,;d_2 d_3)\) as a tensor of two Kloosterman sheaves.
Geometric monodromy is of type \(\mathbf{SL}_2\times\mathbf{SL}_2\to\mathbf{SO}_4\),
the group FKMS explicitly exclude from “gallant.” Their oxozonic
substitute is a rank-\(4\) sheaf on one prime field, not \(S(\,\cdot\,;pq)\).
Three prime factors (the symmetric cell) are \(\mathbf{SL}_2^3\), further
from simple.

---

## Optimistic lengths, even if (1)–(4) are ignored

Identify \(q=D=x^{Q_D}\), balanced Type II \(MN=x\), \(M=N=\sqrt{x}\).
Kloosterman \(S(am,n;q)=-\sqrt{q}\,K(amn)\) is monomial of type \(K(mn)\).

| Cell | \(Q_D\) | Prime after switch? | Thm 1.3 | Thm 1.4 MN-window |
|---|---|---|---|---|
| BV wall | \(1/2\) | yes | no (\(x\not\le 4\sqrt{x}\)) | no |
| \((0,1/2,1/2)\) | \(1\) | no (semiprime) | would hold if prime | would hold if prime |
| \((1/2)^3\) | \(3/2\) | no | no (\(x<q^{3/4}=x^{9/8}\)) | yes, if prime |

The one cell where Theorem 1.3’s inequalities hold is the uneven cell,
which cannot have prime \(D\) after switching. The one cell that can have
prime \(D\) has Type II lengths too *long* for Theorems 1.3–1.4
(\(MN\le 4q\) fails). Theorem 1.4 at \(Q_D=3/2\) would be in its MN-window
(\(x=q^{2/3}\ge q^{1/2}\)), still for a prime field that does not occur.

No range of \(D\) past \(x^{1/2}\) is obtained. \(D\sim x^{3/2}\) is not
cleared. Not a partial increment.

---

## What is not claimed

- T(3) progress, or that a different GKR lemma on a sheaf over
  \(\mathrm{Spec}\,\mathbf{Z}\) would fail for independent reasons.
- That \(\mathrm{Kl}_2\) over a prime is not gallant (it is).
- A re-derivation of A2.3 or of the Farey–\(k\) lemma.

**Next.** The joint well-factorable CRT residue (Phase 4 / plan §4w)
remains the object. FKMS is the right tool for bilinear forms in a
*fixed* prime modulus; it is not a third escape at the stall. The same
cut holds for the family tree behind FKMS
(`erdos-straus-varying-modulus-gap.md`). Do not densify covering.
