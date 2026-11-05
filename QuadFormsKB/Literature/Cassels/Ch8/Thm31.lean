/-
# Cassels, Chapter 8, Theorem 3.1: canonical forms for $\mathbb Z_p$-equivalence, $p \ne 2$

**Setting** (as in `Ch8/Bases.lean`): $p \ne 2$; a non-singular form $f(\vec x) = \vec x^{t}F\vec x$,
$F \in M_n(\mathbb Q_p)$ symmetric with $\det F \ne 0$; $\mathbb Z_p$-equivalence $G = T^{t}FT$ with
$T \in \mathrm{GL}_n(\mathbb Z_p)$ (`ZpEquiv`); a fixed quadratic non-residue $r$ of $p$; the canonical forms
(3.10)–(3.14) as in `Ch8/Canonical.lean`.

**Proves** `exists_unique_canonical` (**Theorem 3.1**, pp. 115–117): every non-singular $f$ is $\mathbb Z_p$-equivalent
to exactly one canonical form (existence: `exists_canonical`; uniqueness: `canonical_unique`).
-/
import QuadFormsKB.Literature.Cassels.Ch8.CanonicalExists
import QuadFormsKB.Literature.Cassels.Ch8.CanonicalUnique

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- **Cassels, Ch. 8, Theorem 3.1**: *let $p \ne 2$ and let $r$ be some fixed quadratic non-residue of $p$. For
$\varepsilon = 0$ or $1$ and $m = 1, 2, \dots$ let $h(\varepsilon, m, \vec y) = y_1^{2} + \cdots + y_{m-1}^{2} +
r^{\varepsilon}y_m^{2}$. Then every non-singular $f(\vec x) \in \mathbb Q_p[\vec x]$ is $\mathbb Z_p$-equivalent to a
form $\sum_{j=1}^{J} p^{e(j)}h(\varepsilon_j, m_j, \vec y^{(j)})$ for some $J$, some $e(j)$ with $e(1) < e(2) < \cdots
< e(J)$ and some $m_j$ with $\sum m_j = n$. Further, no two distinct forms (3.11) are $\mathbb Z_p$-equivalent.*

Formally: there is exactly one list of blocks `D` satisfying (3.12)–(3.13) (`IsCanon`) whose canonical matrix (the
diagonal matrix of `canonEntries p r D`, which then has $n$ entries, i.e. $\sum m_j = n$) is $\mathbb Z_p$-equivalent
to $F$. The non-residue is any $r$ with $\lvert r\rvert_p = 1$ that is not a square in $\mathbb Q_p$ ((3.9));
$f$ is non-singular: $F^{t} = F$, $\det F \ne 0$. -/
@[kb "cassels1978" "Ch. 8, Thm. 3.1, pp. 115–117"]
theorem exists_unique_canonical (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r)
    (F : Matrix (Fin n) (Fin n) ℚ_[p]) (hF : Fᵀ = F) (hdet : F.det ≠ 0) :
    ∃! D : List CanonBlock, IsCanon D ∧ ∃ h : (canonEntries p r D).length = n, ZpEquiv F (canonMat r D h) := by
  obtain ⟨D, hD, h, hFD⟩ := exists_canonical hp2 hr1 hr F hF hdet
  refine ⟨D, ⟨hD, h, hFD⟩, fun D' ⟨hD', h', hFD'⟩ => ?_⟩
  exact (canonical_unique hp2 hr1 hr hD hD' h h' (hFD.symm.trans hFD')).symm

end QuadFormsKB.Cassels
