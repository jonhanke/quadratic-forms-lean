import Mathlib
import QuadFormsKB.Citation

/-!
# Berkovich–Hanke–Jagy, S-genus identities: the explicit local density formulas

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary
quadratic forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §4, Lemmas 4.1 and 4.2, pp. 4–5.

For an odd prime $p$ and an integer $m \ne 0$ write $\operatorname{ord}_p(m) = 2k$ or $2k + 1$, and
let $\chi = \left(\frac{-m/p^{2k}}{p}\right)$ (Legendre symbol). With
$G_k = 1 + \frac1p + \dots + \frac1{p^{k-1}}$ (`geomSum p k`, $G_0 = 0$):

* Lemma 4.1 (the form $x^2 + y^2 + z^2$):
  $\beta_{3,p}(m) = (1 - \frac1{p^2}) G_k + \frac1{p^k}(1 + \frac{\chi}{p})$ if
  $\operatorname{ord}_p(m) = 2k$, and $(1 - \frac1{p^2}) G_{k+1}$ if $\operatorname{ord}_p(m) = 2k+1$
  (`beta3`).
* Lemma 4.2 (a genus $G \sim_{\mathbb{Z}_p} \alpha x^2 + \alpha p y^2 + p z^2$ with
  $\varepsilon = \left(\frac{-\alpha}{p}\right)$):
  $\beta_{G,p}(m) = (1 - \frac1p)(1 + \varepsilon) G_k + \frac1{p^k}(1 + \varepsilon \chi)$ if
  $\operatorname{ord}_p(m) = 2k$, and $(1 - \frac1p)(1 + \varepsilon) G_k +
  \frac1{p^k}(1 - \frac{\varepsilon}{p})$ if $\operatorname{ord}_p(m) = 2k+1$ (`betaG`).

These are the right-hand sides of Lemmas 4.1 and 4.2 as functions of $(p, \varepsilon, m)$; that
they equal the local densities of the forms is proved (or recorded as open) separately.

Both formulas were checked numerically against direct counts of solutions modulo $p^6$ ($p = 3$)
and $p^4$ ($p = 5$) during formalization (helper script, not part of the build).
-/

namespace QuadFormsKB.Berkovich2012

/-- $G_k = 1 + \frac1p + \dots + \frac1{p^{k-1}} = \sum_{j < k} p^{-j}$ (so $G_0 = 0$). -/
def geomSum (p : ℕ) (k : ℕ) : ℚ := ∑ j ∈ Finset.range k, (1 / (p : ℚ)) ^ j

/-- The $p$-free part of $m$ after removing the even power: $m / p^{2k}$ with
$k = \lfloor \operatorname{ord}_p(m) / 2 \rfloor$. -/
def sqFree (p : ℕ) (m : ℤ) : ℤ := m / (p : ℤ) ^ (2 * (padicValInt p m / 2))

/-- The Legendre symbol $\chi = \left(\frac{-m/p^{2k}}{p}\right)$ attached to $m$ with
$\operatorname{ord}_p(m) = 2k$ (only used when the order is even). -/
def chiOf (p : ℕ) [Fact p.Prime] (m : ℤ) : ℤ := legendreSym p (-(sqFree p m))

/-- **Lemma 4.1, right-hand side:** the formula for $\beta_{x^2+y^2+z^2,\,p}(m)$ at an odd prime
$p$ and $m \ne 0$. -/
@[kb "berkovich2012" "§4, Lemma 4.1, p. 4"]
def beta3 (p : ℕ) [Fact p.Prime] (m : ℤ) : ℚ :=
  let v := padicValInt p m
  let k := v / 2
  if v % 2 = 0 then
    (1 - 1 / (p : ℚ) ^ 2) * geomSum p k + 1 / (p : ℚ) ^ k * (1 + chiOf p m / p)
  else
    (1 - 1 / (p : ℚ) ^ 2) * geomSum p (k + 1)

/-- $\beta_{3,p}(m / p^2)$ when $p^2 \mid m$, and $0$ otherwise (the density of a non-integer is
$0$). -/
def beta3Div (p : ℕ) [Fact p.Prime] (m : ℤ) : ℚ :=
  if (p : ℤ) ^ 2 ∣ m then beta3 p (m / (p : ℤ) ^ 2) else 0

/-- **Lemma 4.2, right-hand side:** the formula for $\beta_{G,p}(m)$ at an odd prime $p \mid S$,
for a genus $G \sim_{\mathbb{Z}_p} \alpha x^2 + \alpha p y^2 + p z^2$ with sign
$\varepsilon = \varepsilon_p(G) = \left(\frac{-\alpha}{p}\right) \in \{\pm 1\}$, and $m \ne 0$. -/
@[kb "berkovich2012" "§4, Lemma 4.2, p. 4"]
def betaG (p : ℕ) [Fact p.Prime] (ε : ℤ) (m : ℤ) : ℚ :=
  let v := padicValInt p m
  let k := v / 2
  if v % 2 = 0 then
    (1 - 1 / (p : ℚ)) * (1 + ε) * geomSum p k + 1 / (p : ℚ) ^ k * (1 + ε * chiOf p m)
  else
    (1 - 1 / (p : ℚ)) * (1 + ε) * geomSum p k + 1 / (p : ℚ) ^ k * (1 - ε / p)

end QuadFormsKB.Berkovich2012
