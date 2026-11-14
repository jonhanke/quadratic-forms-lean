/-
# Kitaoka 1993, Corollary 3.1.5: the nonzero squares of $\mathbb Q_p$ form an open set

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), Chapter 3, §3.1, Corollary 3.1.5, p. 62.

**Statement.** For every prime $p$, the set of nonzero squares $(\mathbb Q_p^\times)^2 = \{x \in \mathbb Q_p \mid
x \ne 0,\ x = y^2 \text{ for some } y \in \mathbb Q_p\}$ is open in $\mathbb Q_p$ (`corollary315`).

**Proof sketch** (Hensel's lemma, valid uniformly for all primes $p$ including $p = 2$). Let $x = y^2 \ne 0$ and let
$z \in \mathbb Q_p$ satisfy $|z - x|_p < |x|_p \, |2|_p^2$. Then $s = z / x$ satisfies $|s - 1|_p < |2|_p^2 \le 1$,
so $s \in \mathbb Z_p$. The polynomial $F(T) = T^2 - s \in \mathbb Z_p[T]$ has $|F(1)|_p = |1 - s|_p < |F'(1)|_p^2 =
|2|_p^2$, so by Hensel's lemma (`hensels_lemma`) $s = w^2$ with $w \in \mathbb Z_p$. Hence $z = (yw)^2$, and
$z \ne 0$ because $|z - x|_p < |x|_p$. For odd $p$ the condition reads $|s - 1|_p < 1$, i.e. $s$ is a unit square
modulo $p$; for $p = 2$ it reads $s \equiv 1 \bmod 8$, matching the book's description.

**Lean.** `isSquare_of_norm_sub_one_lt` is the Hensel step; `corollary315` is the book statement.
-/
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Topology.MetricSpace.Basic
import QuadFormsKB.Citation

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- **Hensel step.** If $s \in \mathbb Z_p$ satisfies $|s - 1|_p < |2|_p^2$, then $s$ is a square in
$\mathbb Z_p$. -/
theorem isSquare_of_norm_sub_one_lt (p : ℕ) [Fact p.Prime] (s : ℤ_[p])
    (h : ‖s - 1‖ < ‖(2 : ℤ_[p])‖ ^ 2) : ∃ w : ℤ_[p], w * w = s := by
  have hn : ‖(Polynomial.X ^ 2 - Polynomial.C s : Polynomial ℤ_[p]).aeval (1 : ℤ_[p])‖ <
      ‖(Polynomial.X ^ 2 - Polynomial.C s : Polynomial ℤ_[p]).derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    have e1 : (Polynomial.X ^ 2 - Polynomial.C s : Polynomial ℤ_[p]).aeval (1 : ℤ_[p]) = 1 - s := by
      simp
    have e2 : (Polynomial.X ^ 2 - Polynomial.C s : Polynomial ℤ_[p]).derivative.aeval (1 : ℤ_[p])
        = 2 := by
      simp
      norm_num
    rw [e1, e2, norm_sub_rev]
    exact h
  obtain ⟨w, hw, -⟩ := hensels_lemma hn
  refine ⟨w, ?_⟩
  simp at hw
  linear_combination hw

/-- **Kitaoka 1993, Corollary 3.1.5.** The set of nonzero squares $(\mathbb Q_p^\times)^2$ is open in
$\mathbb Q_p$. -/
@[kb "kitaoka1993" "§3.1, Cor. 3.1.5, p. 62"]
theorem corollary315 (p : ℕ) [Fact p.Prime] : IsOpen {x : ℚ_[p] | x ≠ 0 ∧ IsSquare x} := by
  rw [Metric.isOpen_iff]
  rintro x ⟨hx0, y, hy⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hc : ‖(2 : ℤ_[p])‖ = ‖(2 : ℚ_[p])‖ := by
    rw [PadicInt.norm_def]
    norm_cast
  have hc1 : ‖(2 : ℚ_[p])‖ ≤ 1 := hc ▸ PadicInt.norm_le_one 2
  refine ⟨‖x‖ * ‖(2 : ℚ_[p])‖ ^ 2, ?_, ?_⟩
  · have : (0 : ℝ) < ‖(2 : ℚ_[p])‖ := norm_pos_iff.mpr two_ne_zero
    positivity
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hc0 : 0 ≤ ‖(2 : ℚ_[p])‖ := norm_nonneg _
  have hzx : ‖z - x‖ < ‖x‖ := by
    refine lt_of_lt_of_le hz ?_
    have : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hzx
  have hs : ‖z / x - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2 := by
    have e : z / x - 1 = (z - x) / x := by field_simp
    rw [e, norm_div, div_lt_iff₀ hxn]
    linarith
  have hsle : ‖z / x‖ ≤ 1 := by
    have e : z / x = (z / x - 1) + 1 := by ring
    rw [e]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ (by rw [norm_one]))
    have : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := by nlinarith
    linarith
  obtain ⟨w, hw⟩ := isSquare_of_norm_sub_one_lt p ⟨z / x, hsle⟩ (by
    rw [PadicInt.norm_def, hc]
    exact hs)
  have hw' : (w : ℚ_[p]) * w = z / x := by
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hw
    simpa using this
  refine ⟨hz0, y * w, ?_⟩
  have : z = x * (z / x) := by field_simp
  rw [this, ← hw', hy]
  ring

end QuadFormsKB.Kitaoka
