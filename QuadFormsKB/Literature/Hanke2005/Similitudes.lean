/-
# Hanke 2005, §6: local similitudes and their multipliers

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

For a symmetric matrix $\varphi$ over a field $K$ (Hanke: $K = k_\mathfrak p$), the local group of similitudes is
$\widetilde G^\varphi = \{\tilde g\in\mathrm{GL}_n(K) : {}^t\tilde g\varphi\tilde g = \xi(\tilde g)\varphi\text{ for some }\xi(\tilde g)\in K^\times\}$
and $\Xi(\varphi) = \{\xi(\tilde g)\}$ the set of multipliers (§6, p. 20).

**Defines** `multipliers φ` ($\Xi(\varphi)$).
**Proves** the facts used in the proof of Theorem 6.3 (pp. 20–21):
* `isSquare_of_mem_multipliers` (odd $n$): every multiplier is a square, so no similitude has a multiplier of odd
  valuation (Hanke: "taking determinants gives $\mathrm{ord}(\det\tilde g^2) = \mathrm{ord}(\xi^{t_\mathfrak p})$");
* `sq_mem_multipliers`: $c^2\in\Xi(\varphi)$ ($\tilde g = c\cdot1_n$; Hanke: $\pi_\mathfrak p^2$);
* `multipliers_hyperbolic`: $\Xi(\eta_{2r}) = K^\times$ for the hyperbolic matrix
  $\eta_{2r} = \begin{pmatrix}0&1_r\\1_r&0\end{pmatrix}$ (Hanke: "one can easily compute $\Xi_\mathfrak p(\eta_{2r}) = F_\mathfrak p^\times$");
* `multipliers_fromBlocks`: $\Xi(\varphi_1)\cap\Xi(\varphi_2)\subseteq\Xi(\varphi_1\perp\varphi_2)$ (the inclusion used in
  $\Xi_\mathfrak p(\varphi) = \Xi_\mathfrak p(\eta_{2r})\cap\Xi_\mathfrak p(\theta_\mathfrak p)$);
* `multipliers_congr`: $\Xi({}^tB\varphi B) = \Xi(\varphi)$ (change of basis);
* `norm_mem_multipliers` ($t_\mathfrak p = 2$): for the binary form $c\,(x^2 - dy^2)$ ($= c\,N_{K(\sqrt d)/K}$), every nonzero
  norm $a^2 - db^2$ is a multiplier ($K(\sqrt d)^\times\subseteq\widetilde G^{\theta}$).
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The multipliers of the similitudes of $\varphi$** (Hanke thesis, §6, p. 20): $\Xi(\varphi) = \{\xi\in K^\times :
{}^t\tilde g\varphi\tilde g = \xi\varphi$ for some $\tilde g\in\mathrm{GL}_n(K)\}$. -/
@[kb "hanke2005crelle" "§6, p. 20 (similitude group and multipliers Ξ_p(φ))"]
def multipliers (φ : Matrix ι ι K) : Set K :=
  {ξ | ξ ≠ 0 ∧ ∃ g : Matrix ι ι K, IsUnit g.det ∧ gᵀ * φ * g = ξ • φ}

/-- **Odd dimension** (Hanke thesis, proof of Theorem 6.3, p. 21): if $n$ is odd and $\det\varphi\ne0$, every multiplier is a
square ($\det(\tilde g)^2 = \xi^n$). In particular no multiplier has odd valuation. -/
@[kb "hanke2005crelle" "proof of Theorem 6.3, p. 21 (t_p odd: no similitude of odd valuation)"]
theorem isSquare_of_mem_multipliers (hn : Odd (Fintype.card ι)) {φ : Matrix ι ι K} (hφ : φ.det ≠ 0) {ξ : K}
    (hξ : ξ ∈ multipliers φ) : IsSquare ξ := by
  obtain ⟨hξ0, g, hg, h⟩ := hξ
  have h1 := congrArg det h
  rw [det_mul, det_mul, det_transpose, det_smul] at h1
  obtain ⟨k, hk⟩ := hn
  have h2 : ξ ^ (2 * k + 1) = g.det * g.det := by
    apply mul_right_cancel₀ hφ
    rw [← hk]
    linear_combination -h1
  refine ⟨g.det / ξ ^ k, ?_⟩
  have : ξ ^ k ≠ 0 := pow_ne_zero _ hξ0
  field_simp
  linear_combination h2

/-- $c^2\in\Xi(\varphi)$ for $c\ne0$ (Hanke thesis, proof of Theorem 6.3, p. 21: $\tilde g = \mathrm{diag}[\pi_\mathfrak p,\dots,\pi_\mathfrak p]$). -/
@[kb "hanke2005crelle" "proof of Theorem 6.3, p. 21 (π_p² ∈ Ξ)"]
theorem sq_mem_multipliers (φ : Matrix ι ι K) {c : K} (hc : c ≠ 0) : c ^ 2 ∈ multipliers φ := by
  refine ⟨pow_ne_zero 2 hc, c • 1, ?_, ?_⟩
  · rw [det_smul, det_one, mul_one]; exact IsUnit.mk0 _ (pow_ne_zero _ hc)
  · simp [smul_smul, pow_two]

/-- **The hyperbolic space** (Hanke thesis, §6, p. 20): $\Xi(\eta_{2r}) = K^\times$ for
$\eta_{2r} = \begin{pmatrix}0&1_r\\1_r&0\end{pmatrix}$ (similitude $\mathrm{diag}[\xi1_r, 1_r]$). -/
@[kb "hanke2005crelle" "§6, p. 20 (Ξ_p(η_2r) = F_p^×)"]
theorem multipliers_hyperbolic (r : Type*) [Fintype r] [DecidableEq r] :
    multipliers (Matrix.fromBlocks (0 : Matrix r r K) (1 : Matrix r r K) (1 : Matrix r r K) (0 : Matrix r r K)) =
      {ξ | ξ ≠ 0} := by
  ext ξ
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro hξ
    refine ⟨hξ, Matrix.fromBlocks (ξ • (1 : Matrix r r K)) 0 0 1, ?_, ?_⟩
    · rw [det_fromBlocks_zero₂₁]
      simp only [det_smul, det_one, mul_one]
      exact (IsUnit.mk0 _ (pow_ne_zero _ hξ))
    · simp [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]

/-- **Orthogonal sums** (Hanke thesis, §6, p. 20): a common multiplier of $\varphi_1$ and $\varphi_2$ is a multiplier of
$\varphi_1\perp\varphi_2$. -/
@[kb "hanke2005crelle" "§6, p. 20 (Ξ_p(φ) = Ξ_p(η_2r) ∩ Ξ_p(θ_p), inclusion ⊇)"]
theorem multipliers_fromBlocks {κ : Type*} [Fintype κ] [DecidableEq κ] (φ₁ : Matrix ι ι K) (φ₂ : Matrix κ κ K) :
    multipliers φ₁ ∩ multipliers φ₂ ⊆ multipliers (Matrix.fromBlocks φ₁ 0 0 φ₂) := by
  rintro ξ ⟨⟨hξ, g₁, hg₁, h₁⟩, -, g₂, hg₂, h₂⟩
  refine ⟨hξ, Matrix.fromBlocks g₁ 0 0 g₂, ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁]; exact hg₁.mul hg₂
  · simp only [fromBlocks_transpose, fromBlocks_multiply, Matrix.transpose_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, fromBlocks_smul, smul_zero]
    rw [h₁, h₂]


theorem multipliers_subset_congr (φ : Matrix ι ι K) {B : Matrix ι ι K} (hB : IsUnit B.det) :
    multipliers φ ⊆ multipliers (Bᵀ * φ * B) := by
  rintro ξ ⟨hξ, g, hg, h⟩
  refine ⟨hξ, B⁻¹ * g * B, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact ((isUnit_nonsing_inv_det B hB).mul hg).mul hB
  · have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
    have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
    have h3 : (B⁻¹)ᵀ * Bᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
    calc (B⁻¹ * g * B)ᵀ * (Bᵀ * φ * B) * (B⁻¹ * g * B)
        = Bᵀ * gᵀ * ((B⁻¹)ᵀ * Bᵀ) * φ * (B * B⁻¹) * g * B := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = Bᵀ * (gᵀ * φ * g) * B := by
          rw [h3, h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = ξ • (Bᵀ * φ * B) := by
          rw [h]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- **Change of basis**: $\Xi({}^tB\varphi B) = \Xi(\varphi)$ for invertible $B$. -/
theorem multipliers_congr (φ : Matrix ι ι K) {B : Matrix ι ι K} (hB : IsUnit B.det) :
    multipliers (Bᵀ * φ * B) = multipliers φ := by
  apply Set.Subset.antisymm
  · intro ξ hξ
    have h := multipliers_subset_congr (Bᵀ * φ * B) (B := B⁻¹) (isUnit_nonsing_inv_det B hB) hξ
    have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
    have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
    have h3 : (B⁻¹)ᵀ * Bᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
    have h4 : Bᵀ * (B⁻¹)ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
    have : (B⁻¹)ᵀ * (Bᵀ * φ * B) * B⁻¹ = φ := by
      calc (B⁻¹)ᵀ * (Bᵀ * φ * B) * B⁻¹ = ((B⁻¹)ᵀ * Bᵀ) * φ * (B * B⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = φ := by rw [h3, h1]; simp
    rwa [this] at h
  · exact multipliers_subset_congr φ hB

/-- **Norms are multipliers of a norm form** (Hanke thesis, proof of Theorem 6.3, p. 21, case $t_\mathfrak p = 2$:
$(W_\mathfrak p,\theta_\mathfrak p)\cong(K_\mathfrak p, cN_{K_\mathfrak p/k_\mathfrak p})$, $K_\mathfrak p^\times\subseteq\widetilde G^{\theta_\mathfrak p}$): for the binary
form $c\,(x^2 - dy^2)$, multiplication by $a + b\sqrt d$ is a similitude with multiplier $a^2 - db^2$. -/
@[kb "hanke2005crelle" "proof of Theorem 6.3, p. 21 (t_p = 2: norms are multipliers)"]
theorem norm_mem_multipliers {c d a b : K} (hab : a ^ 2 - d * b ^ 2 ≠ 0) :
    a ^ 2 - d * b ^ 2 ∈ multipliers (c • !![1, 0; 0, -d]) := by
  refine ⟨hab, !![a, b * d; b, a], ?_, ?_⟩
  · rw [det_fin_two_of]; simp only [mul_comm]; convert IsUnit.mk0 _ hab using 1; ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end QuadFormsKB.Hanke2005
