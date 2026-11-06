/-
# Cassels, Chapters 3 and 4: comparison lemmas for the definitions and basic facts

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, §1 (pp. 34–39) and Chapter 4, §§2–3
(pp. 58, 63).

Each declaration here is a thin comparison lemma: its proof is the corresponding Mathlib lemma (`AbsoluteValue`,
`padicNorm`, `Padic`, `PadicInt`, `IsUltrametricDist`), stated in Cassels' form so that the book item has a Lean
counterpart. Indices are $0$-based. The last section cites existing library declarations for Chapter 4, §2–3.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Literature.Cassels.Ch4.Witt

open Filter Topology

noncomputable section

namespace QuadFormsKB.Cassels.Ch3

/-- **Cassels, Ch. 3, §1, p. 34 (definition: valuation).** A valuation (absolute value) $|\cdot|$ on a field $k$,
here Mathlib's `AbsoluteValue k ℝ`, satisfies: $|a| \ge 0$ with equality if and only if $a = 0$; $|ab| = |a||b|$; and
$|a + b| \le |a| + |b|$. -/
@[kb "cassels1978" "Ch. 3, §1, p. 34 (definition: valuation)"]
theorem valuation_axioms {k : Type*} [Field k] (v : AbsoluteValue k ℝ) (a b : k) :
    0 ≤ v a ∧ (v a = 0 ↔ a = 0) ∧ v (a * b) = v a * v b ∧ v (a + b) ≤ v a + v b :=
  ⟨v.nonneg a, v.eq_zero, v.map_mul a b, v.add_le a b⟩

/-- **Cassels, Ch. 3, §1, p. 35 (the $p$-adic valuation of a rational).** For a prime $p$, an integer $\nu$ and
integers $u, v$ prime to $p$, the rational $r = p^{\nu}u/v$ has $|r|_p = p^{-\nu}$. -/
@[kb "cassels1978" "Ch. 3, §1, p. 35 (the valuation $|p^{\\nu}u/v|_p = p^{-\\nu}$)"]
theorem padicNorm_zpow_mul_div {p : ℕ} [Fact p.Prime] (ν : ℤ) {u v : ℤ} (hu : ¬ (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) : padicNorm p ((p : ℚ) ^ ν * u / v) = (p : ℚ) ^ (-ν) := by
  have hu' : padicNorm p (u : ℚ) = 1 := (padicNorm.int_eq_one_iff u).mpr hu
  have hv' : padicNorm p (v : ℚ) = 1 := (padicNorm.int_eq_one_iff v).mpr hv
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [padicNorm.div, padicNorm.mul, hu', hv', mul_one, div_one]
  have hpne : (p : ℚ) ^ ν ≠ 0 := zpow_ne_zero _ hp0
  rw [padicNorm.eq_zpow_of_nonzero hpne, padicValRat.zpow (p : ℚ), padicValRat.self (Fact.out : p.Prime).one_lt]
  simp

/-- **Cassels, Ch. 3, §1, p. 35 (the $p$-adic valuation is non-archimedean).**
$|q + r|_p \le \max(|q|_p, |r|_p)$ for rationals $q, r$. -/
@[kb "cassels1978" "Ch. 3, §1, p. 35 (the $p$-adic valuation is non-archimedean)"]
theorem padicNorm_nonarchimedean {p : ℕ} [Fact p.Prime] (q r : ℚ) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  padicNorm.nonarchimedean

/-- **Cassels, Ch. 3, §1, p. 35 (consequences of the axioms).** For a valuation $|\cdot|$ on a field,
$|1| = 1$, $|-1| = 1$ and $|-a| = |a|$. -/
@[kb "cassels1978" "Ch. 3, §1, p. 35 (consequences of the valuation axioms: $|1| = |-1| = 1$, $|-a| = |a|$)"]
theorem valuation_one_neg {k : Type*} [Field k] (v : AbsoluteValue k ℝ) (a : k) :
    v 1 = 1 ∧ v (-1) = 1 ∧ v (-a) = v a :=
  ⟨v.map_one, by simp, v.map_neg a⟩

/-- **Cassels, Ch. 3, §1, pp. 35–36 (every point of a disc is a centre, ultrametric case).** In $\mathbb Q_p$, if
$y$ lies in the open disc of radius $r$ about $x$, then the disc about $y$ of radius $r$ is the same disc. -/
@[kb "cassels1978" "Ch. 3, §1, pp. 35–36 (in the non-archimedean case every point of a disc is a centre) (open discs)"]
theorem padic_ball_eq_of_mem {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]} {r : ℝ}
    (h : y ∈ Metric.ball x r) : Metric.ball x r = Metric.ball y r :=
  IsUltrametricDist.ball_eq_of_mem h

/-- **Cassels, Ch. 3, §1, pp. 35–36 (every point of a disc is a centre, ultrametric case), closed discs.** -/
@[kb "cassels1978" "Ch. 3, §1, pp. 35–36 (in the non-archimedean case every point of a disc is a centre) (closed discs)"]
theorem padic_closedBall_eq_of_mem {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]} {r : ℝ}
    (h : y ∈ Metric.closedBall x r) : Metric.closedBall x r = Metric.closedBall y r :=
  IsUltrametricDist.closedBall_eq_of_mem h

/-- **Cassels, Ch. 3, §1, p. 37, Lemma 1.2 (the field $\mathbb Q_p$).** There is a field $\mathbb Q_p \supseteq
\mathbb Q$ with a valuation extending $|\cdot|_p$, complete, in which $\mathbb Q$ is dense: on rationals the norm of
`ℚ_[p]` is `padicNorm p`, `ℚ_[p]` is a complete space, and the image of $\mathbb Q$ is dense. -/
@[kb "cassels1978" "Ch. 3, §1, Lemma 1.2, p. 37"]
theorem padic_field_lemma (p : ℕ) [Fact p.Prime] :
    (∀ q : ℚ, ‖(q : ℚ_[p])‖ = padicNorm p q) ∧ CompleteSpace ℚ_[p] ∧
      DenseRange ((↑) : ℚ → ℚ_[p]) :=
  ⟨Padic.eq_padicNorm, inferInstance, Padic.denseRange_ratCast p⟩

/-- **Cassels, Ch. 3, §1, p. 38 (the ring $\mathbb Z_p$).** $\mathbb Z_p = \{x \in \mathbb Q_p : |x|_p \le 1\}$ is a
subring of $\mathbb Q_p$: the underlying set of `PadicInt.subring p` is the closed unit disc. -/
@[kb "cassels1978" "Ch. 3, §1, p. 38 (the $p$-adic integers form a ring)"]
theorem padicInt_subring_eq (p : ℕ) [Fact p.Prime] :
    ((PadicInt.subring p : Subring ℚ_[p]) : Set ℚ_[p]) = {x | ‖x‖ ≤ 1} := by
  ext x; rfl

/-- **Cassels, Ch. 3, §1, p. 39 (units of $\mathbb Z_p$).** An element $z \in \mathbb Z_p$ is a unit of $\mathbb Z_p$
if and only if $|z|_p = 1$. -/
@[kb "cassels1978" "Ch. 3, §1, p. 39 (the units of $\\mathbb Z_p$ are the $x$ with $|x|_p = 1$)"]
theorem padicInt_isUnit_iff {p : ℕ} [Fact p.Prime] (z : ℤ_[p]) : IsUnit z ↔ ‖z‖ = 1 :=
  PadicInt.isUnit_iff

end QuadFormsKB.Cassels.Ch3

namespace QuadFormsKB.QuadForm

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- **Cassels, Ch. 4, §2, Lemma 2.3 (i), p. 58.** The number of variables of the orthogonal sum
$f + g$ (`orthSum`) of a form $f$ in $m$ variables and a form $g$ in $n$ variables is $m + n$: the ambient
module $R^{m+n}$ of $f + g$ has rank $m + n$, the sum of the ranks of those of $f$ and $g$. (The statement is
definitional: `orthSum f g : QuadForm R (m + n)`.) -/
@[kb "cassels1978" "Ch. 4, §2, Lemma 2.3 (i), p. 58"]
theorem finrank_orthSum [Nontrivial R] (_f : QuadForm R m) (_g : QuadForm R n) :
    Module.finrank R (Fin (m + n) → R) = Module.finrank R (Fin m → R) + Module.finrank R (Fin n → R) := by
  simp

end QuadFormsKB.QuadForm

attribute [kb "cassels1978" "Ch. 4, §2, p. 58 (definition: $f + g$, the orthogonal sum)"] QuadFormsKB.QuadForm.orthSum
attribute [kb "cassels1978" "Ch. 4, §3, p. 63 (the residue map $\\mathbb Z_p \\to \\mathbb F_p$ induces $U/U^{2} \\cong \\mathbb F_p^{\\times}/\\mathbb F_p^{\\times 2}$, $p$ odd) (injectivity: units with the same residue differ by a square)"] QuadFormsKB.Cassels.exists_sq_of_unitF_eq
attribute [kb "cassels1978" "Ch. 4, §3, p. 63 (the residue map $\\mathbb Z_p \\to \\mathbb F_p$ induces $U/U^{2} \\cong \\mathbb F_p^{\\times}/\\mathbb F_p^{\\times 2}$, $p$ odd) (surjectivity: every nonzero residue lifts to a unit)"] QuadFormsKB.Cassels.unitF_liftU
attribute [kb "cassels1978" "Ch. 3, §1, p. 36 (every valued field has a completion; the case of ℚ with |·|_p: ℚ_p, special case)"] QuadFormsKB.Cassels.Ch3.padic_field_lemma
