/-
# Kitaoka 1993, Section 2.1: proof of Lemma 2.1.2

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.1, Lemma 2.1.2, p. 35.

**Proves**
* `lemma212` (Lemma 2.1.2): if $g = k\,\mathrm{diag}(\alpha)\,n$ with $k$ orthogonal and $n$ upper unitriangular, and
  $\phi(g) \le \phi(g\gamma)$ for all $\gamma \in \mathrm{GL}_m(\mathbb Z)$, then $\alpha_0/\alpha_1 \le 2/\sqrt3$
  (0-based indices). The proof compares $\phi(g)$ with $\phi(g\gamma)$ for one explicit $\gamma$ whose first column is
  $c e_0 + e_1$, with $c \in \mathbb Z$ chosen so that $|n_{01} + c| \le 1/2$.
-/
import QuadFormsKB.Literature.Kitaoka.Ch2Reduction
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Order.Round

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Reduction

variable {m : ℕ}

/-- An orthogonal real matrix preserves the sum of squares of a vector. -/
theorem sum_sq_mulVec_orth {k : Matrix (Fin m) (Fin m) ℝ} (hk : k ∈ orthMat m) (v : Fin m → ℝ) :
    ∑ i, ((k *ᵥ v) i) ^ 2 = ∑ i, (v i) ^ 2 := by
  have h1 : kᵀ * k = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).1 hk
  have h2 : (k *ᵥ v) ⬝ᵥ (k *ᵥ v) = v ⬝ᵥ v := by
    have : (k *ᵥ v) ⬝ᵥ (k *ᵥ v) = v ⬝ᵥ (kᵀ *ᵥ (k *ᵥ v)) := by
      symm
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [this, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  simpa [dotProduct, sq] using h2

/-- The squared first-column norm of `g * M`, for `g = k * diagonal α * n` with `k` orthogonal. -/
theorem sum_sq_col_mul {k n : Matrix (Fin m) (Fin m) ℝ} {α : Fin m → ℝ} (hk : k ∈ orthMat m)
    (M : Matrix (Fin m) (Fin m) ℝ) (i₀ : Fin m) :
    ∑ i, ((k * diagonal α * n * M) i i₀) ^ 2 =
      ∑ i, (α i * (n *ᵥ fun j => M j i₀) i) ^ 2 := by
  have h : ∀ i, (k * diagonal α * n * M) i i₀ =
      (k *ᵥ (diagonal α *ᵥ (n *ᵥ fun j => M j i₀))) i := by
    intro i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  simp_rw [h]
  rw [sum_sq_mulVec_orth hk]
  simp [Matrix.mulVec_diagonal]

/-- An integral unimodular matrix whose column `i₀` is $c e_{i_0} + e_{i_1}$. -/
theorem exists_gl_col (i₀ i₁ : Fin m) (h : i₀ ≠ i₁) (c : ℤ) :
    ∃ γ : GL (Fin m) ℤ, ∀ j, (γ : Matrix (Fin m) (Fin m) ℤ) j i₀ =
      (if j = i₁ then 1 else 0) + c * (if j = i₀ then 1 else 0) := by
  set S : Matrix (Fin m) (Fin m) ℤ := (Equiv.swap i₀ i₁).permMatrix ℤ with hS
  set U : Matrix (Fin m) (Fin m) ℤ := Matrix.transvection i₁ i₀ c with hU
  have hdet : IsUnit (S * U).det := by
    rw [Matrix.det_mul, hS, hU, Matrix.det_permutation, Matrix.det_transvection_of_ne _ _ h.symm, mul_one]
    exact (Units.isUnit _)
  refine ⟨Matrix.nonsingInvUnit (S * U) hdet, fun j => ?_⟩
  have e1 : (S * U) j i₀ = (S *ᵥ fun l => U l i₀) j := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  show (S * U) j i₀ = _
  rw [e1, hS, Matrix.permMatrix_mulVec]
  by_cases hj0 : j = i₀
  · subst hj0
    simp [hU, Matrix.transvection, Matrix.single_apply, Matrix.one_apply, h, h.symm]
  · by_cases hj1 : j = i₁
    · subst hj1
      simp [hU, Matrix.transvection, Matrix.single_apply, Matrix.one_apply, h.symm]
    · simp only [Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hj0 hj1]
      simp [hU, Matrix.transvection, hj0, hj1, Ne.symm hj1]

/-- **Kitaoka 1993, Lemma 2.1.2** (p. 35). Let $g = k\,\mathrm{diag}(\alpha)\,n$ with $k$ orthogonal, $\alpha_i > 0$
and $n$ upper unitriangular, and suppose $\phi(g) \le \phi(g\gamma)$ for all $\gamma \in \mathrm{GL}_m(\mathbb Z)$,
where $\phi(g) = |g e_0|$. Then $\alpha_0/\alpha_1 \le 2/\sqrt3$ (0-based).

*Proof.* Since $k$ is orthogonal, $|g x|^2 = \sum_i \alpha_i^2 ((n x)_i)^2$ for every $x$. With $x = e_0$ and
$n_{00} = 1$ this gives $\phi(g)^2 \ge \alpha_0^2$. Let $u = n_{01}$ and $c = -\mathrm{round}(u) \in \mathbb Z$, so
$|u + c| \le 1/2$. Take $\gamma \in \mathrm{GL}_m(\mathbb Z)$ with first column $c e_0 + e_1$ (second column $e_0$,
a swap composed with a transvection, of determinant $-1$). Because $n$ is upper unitriangular,
$n(c e_0 + e_1) = (u + c) e_0 + e_1$, hence
$\phi(g\gamma)^2 = \alpha_0^2 (u + c)^2 + \alpha_1^2 \le \alpha_0^2/4 + \alpha_1^2$. The hypothesis gives
$\alpha_0^2 \le \alpha_0^2/4 + \alpha_1^2$, i.e. $3\alpha_0^2 \le 4\alpha_1^2$, so $\sqrt3\,\alpha_0 \le 2\alpha_1$. -/
@[kb "kitaoka1993" "§2.1, Lemma 2.1.2, p. 35"]
theorem lemma212 : Lemma212 := by
  intro m hm g k α n hk hα hn hg hmin
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have hne : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have hlt : i₀ < i₁ := by simp [hi₀, hi₁, Fin.lt_def]
  have hpos : 0 < m := by omega
  have hfc : ∀ M : Matrix (Fin m) (Fin m) ℝ,
      firstColNorm M = Real.sqrt (∑ i, (M i i₀) ^ 2) := by
    intro M; simp [firstColNorm, hpos, hi₀]
  obtain ⟨hnu, hn1⟩ := hn
  -- n entries
  have hlow : ∀ i j : Fin m, j < i → n i j = 0 := fun i j hij => hnu hij
  -- φ(g)² ≥ α₀²
  have hφ : α i₀ ^ 2 ≤ ∑ i, ((g : Matrix (Fin m) (Fin m) ℝ) i i₀) ^ 2 := by
    have := sum_sq_col_mul (n := n) (α := α) hk 1 i₀
    rw [← hg, Matrix.mul_one] at this
    rw [this]
    have hge : ∀ i ∈ Finset.univ, 0 ≤ (α i * (n *ᵥ fun j => (1 : Matrix (Fin m) (Fin m) ℝ) j i₀) i) ^ 2 :=
      fun i _ => sq_nonneg _
    refine le_trans ?_ (Finset.single_le_sum hge (Finset.mem_univ i₀))
    have : (n *ᵥ fun j => (1 : Matrix (Fin m) (Fin m) ℝ) j i₀) i₀ = 1 := by
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, hn1 i₀]
    rw [this, mul_one]
  -- choose c
  set u : ℝ := n i₀ i₁ with hu
  set c : ℤ := -round u with hc
  have hcu : |u + c| ≤ 1 / 2 := by
    have := abs_sub_round u
    simpa [hc, sub_eq_add_neg] using this
  obtain ⟨γ, hγ⟩ := exists_gl_col i₀ i₁ hne c
  have h1 := hmin γ
  rw [hfc, hfc] at h1
  have h2 : ∑ i, ((g : Matrix (Fin m) (Fin m) ℝ) i i₀) ^ 2 ≤
      ∑ i, (((g : Matrix (Fin m) (Fin m) ℝ) * intCast γ) i i₀) ^ 2 := by
    refine (Real.sqrt_le_sqrt_iff (Finset.sum_nonneg fun i _ => sq_nonneg _)).1 h1
  have h3 : ∑ i, (((g : Matrix (Fin m) (Fin m) ℝ) * intCast γ) i i₀) ^ 2 =
      α i₀ ^ 2 * (u + c) ^ 2 + α i₁ ^ 2 := by
    rw [hg, sum_sq_col_mul hk]
    have hv : ∀ i, (n *ᵥ fun j => (intCast γ : Matrix (Fin m) (Fin m) ℝ) j i₀) i =
        n i i₁ + c * n i i₀ := by
      intro i
      have hw : ∀ j, (intCast γ : Matrix (Fin m) (Fin m) ℝ) j i₀ =
          (if j = i₁ then 1 else 0) + c * (if j = i₀ then 1 else 0) := by
        intro j
        simp only [intCast, Matrix.map_apply]
        rw [hγ j]
        push_cast
        rfl
      simp only [Matrix.mulVec, dotProduct, hw, mul_add, Finset.sum_add_distrib]
      simp [mul_comm]
    have hv0 : (n *ᵥ fun j => (intCast γ : Matrix (Fin m) (Fin m) ℝ) j i₀) i₀ = u + c := by
      rw [hv]; simp [hn1 i₀, hu]
    have hv1 : (n *ᵥ fun j => (intCast γ : Matrix (Fin m) (Fin m) ℝ) j i₀) i₁ = 1 := by
      rw [hv]; simp [hn1 i₁, hlow i₁ i₀ hlt]
    rw [Finset.sum_eq_add i₀ i₁ hne]
    · rw [hv0, hv1]; ring
    · intro i _ hi
      have hlt0 : i₀ < i := by
        rcases hi with ⟨ha, hb⟩
        have : 2 ≤ i.val := by
          have := i.isLt
          simp [hi₀, hi₁, Fin.ext_iff] at ha hb
          omega
        simp [hi₀, Fin.lt_def]; omega
      have hlt1 : i₁ < i := by
        rcases hi with ⟨ha, hb⟩
        have : 2 ≤ i.val := by
          simp [hi₀, hi₁, Fin.ext_iff] at ha hb
          omega
        simp [hi₁, Fin.lt_def]; omega
      rw [hv, hlow i i₁ hlt1, hlow i i₀ hlt0]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have ht : (u + c) ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 hcu
    nlinarith [this.1, this.2]
  have hα0 := hα i₀
  have hα1 := hα i₁
  have key : 3 * α i₀ ^ 2 ≤ 4 * α i₁ ^ 2 := by
    have : α i₀ ^ 2 * (u + c) ^ 2 ≤ α i₀ ^ 2 * (1 / 4) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    nlinarith [hφ, h2, h3]
  show α i₀ / α i₁ ≤ 2 / Real.sqrt 3
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  rw [div_le_div_iff₀ hα1 h3pos]
  by_contra hcon
  have hcon := not_le.1 hcon
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have : (2 * α i₁) ^ 2 < (α i₀ * Real.sqrt 3) ^ 2 :=
    pow_lt_pow_left₀ hcon (by positivity) two_ne_zero
  nlinarith [this, hsq, key]

end QuadFormsKB.Kitaoka.Reduction
