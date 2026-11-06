/-
# Cassels, Chapter 13, §10: real automorphs, the general case

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §10, *Real automorphs: general case*,
pp. 320–321: for the indefinite form
$$f = x_1^2 + \cdots + x_m^2 - x_{m+1}^2 - \cdots - x_{m+l}^2 \qquad (m, l > 0) \tag{10.1–10.2}$$
the cosets $O_{\mathbb{R}}(f)/K$, $K$ the compact group (10.4)–(10.5), correspond to the $m \times l$ matrices $E$ of
operator norm $< 1$ (Lemma 10.1), and the action of $O_{\mathbb{R}}(f)$ is by "fractional-linear" maps (Lemma 10.2).

**Conventions.** The variables are indexed by `Fin m ⊕ Fin l` (the first $m$, then the last $l$), so that the
matrix of $f$ is $J = \begin{pmatrix} I_m & 0 \\ 0 & -I_l\end{pmatrix}$ (10.3) (`sigJ`), and a real matrix is written in
blocks $M = \begin{pmatrix} A & B \\ C & D\end{pmatrix}$ (10.6) (`Matrix.fromBlocks`, `Matrix.toBlocks₁₁` etc.).
$O_{\mathbb{R}}(f)$ is `realAut (sigJ m l)`. The hypotheses $m, l > 0$ are not needed.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic

open Matrix

namespace QuadFormsKB.Reduction

variable {m l : ℕ}

/-- **The matrix $J$ of (10.3)** (Cassels, Ch. 13, §10, p. 320): $J = \operatorname{diag}(I_m, -I_l)$, the matrix of
$f = x_1^2 + \cdots + x_m^2 - x_{m+1}^2 - \cdots - x_{m+l}^2$ (10.1). -/
@[kb "cassels1978" "Ch. 13, §10, (10.1)–(10.3), p. 320"]
def sigJ (m l : ℕ) : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) ℝ := fromBlocks 1 0 0 (-1)

/-- **The compact group $K$** (Cassels, Ch. 13, §10, (10.4)–(10.5), p. 320): the automorphs
$W = \begin{pmatrix} U & 0 \\ 0 & V\end{pmatrix}$ with $U^{\mathsf T}U = I_m$, $V^{\mathsf T}V = I_l$. -/
@[kb "cassels1978" "Ch. 13, §10, (10.4)–(10.5), p. 320 (the group K)"]
def blockOrth (m l : ℕ) : Subgroup (GL (Fin m ⊕ Fin l) ℝ) where
  carrier := {W | ∃ U V, Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ W.val = fromBlocks U 0 0 V}
  mul_mem' := by
    rintro a b ⟨U, V, hU, hV, ha⟩ ⟨U', V', hU', hV', hb⟩
    refine ⟨U * U', V * V', ?_, ?_, ?_⟩
    · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul, hU']
    · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul, hV']
    · rw [Units.val_mul, ha, hb, fromBlocks_multiply]; simp
  one_mem' := ⟨1, 1, by simp, by simp, by simp⟩
  inv_mem' := by
    rintro a ⟨U, V, hU, hV, ha⟩
    have hU2 : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
    have hV2 : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
    refine ⟨Uᵀ, Vᵀ, by simpa using hU2, by simpa using hV2, ?_⟩
    have h : a.val * fromBlocks Uᵀ 0 0 Vᵀ = 1 := by
      rw [ha, fromBlocks_multiply]; simp [hU2, hV2]
    calc (a⁻¹).val = (a⁻¹).val * (a.val * fromBlocks Uᵀ 0 0 Vᵀ) := by rw [h, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

/-- Block expansion of $M^{\mathsf T} J M$. -/
lemma conj_sigJ (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin l) ℝ) (C : Matrix (Fin l) (Fin m) ℝ)
    (D : Matrix (Fin l) (Fin l) ℝ) :
    (fromBlocks A B C D)ᵀ * sigJ m l * fromBlocks A B C D =
      fromBlocks (Aᵀ*A - Cᵀ*C) (Aᵀ*B - Cᵀ*D) (Bᵀ*A - Dᵀ*C) (Bᵀ*B - Dᵀ*D) := by
  unfold sigJ
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [sub_eq_add_neg]

/-- $J^2 = I$. -/
lemma sigJ_mul_sigJ : sigJ m l * sigJ m l = 1 := by
  unfold sigJ; rw [fromBlocks_multiply]; simp

/-- $K \subseteq O_{\mathbb{R}}(f)$. -/
theorem blockOrth_le : blockOrth m l ≤ realAut (sigJ m l) := by
  rintro W ⟨U, V, hU, hV, hW⟩
  show W.valᵀ * sigJ m l * W.val = sigJ m l
  rw [hW, conj_sigJ]
  unfold sigJ
  simp [hU, hV]

/-- **(10.7)–(10.9)** (Cassels, Ch. 13, §10, p. 320): $M = \begin{pmatrix} A & B \\ C & D\end{pmatrix}$ is in
$O_{\mathbb{R}}(f)$ iff
$$A^{\mathsf T}A = I_m + C^{\mathsf T}C, \qquad D^{\mathsf T}D = I_l + B^{\mathsf T}B, \qquad A^{\mathsf T}B = C^{\mathsf T}D.$$ -/
@[kb "cassels1978" "Ch. 13, §10, (10.6)–(10.9), p. 320"]
theorem transpose_mul_sigJ_mul_eq_iff (M : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) ℝ) :
    Mᵀ * sigJ m l * M = sigJ m l ↔
      M.toBlocks₁₁ᵀ * M.toBlocks₁₁ = 1 + M.toBlocks₂₁ᵀ * M.toBlocks₂₁ ∧
        M.toBlocks₂₂ᵀ * M.toBlocks₂₂ = 1 + M.toBlocks₁₂ᵀ * M.toBlocks₁₂ ∧
          M.toBlocks₁₁ᵀ * M.toBlocks₁₂ = M.toBlocks₂₁ᵀ * M.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [conj_sigJ]
  unfold sigJ
  rw [fromBlocks_inj]
  generalize M.toBlocks₁₁ = A; generalize M.toBlocks₁₂ = B
  generalize M.toBlocks₂₁ = C; generalize M.toBlocks₂₂ = D
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, sub_eq_zero.mp h2⟩
    · rw [← h1]; abel
    · calc Dᵀ * D = Bᵀ * B - (Bᵀ * B - Dᵀ * D) := by abel
        _ = _ := by rw [h4]; abel
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1]; abel
    · rw [h3, sub_self]
    · have := congrArg transpose h3
      rw [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose] at this
      rw [this, sub_self]
    · rw [h2]; abel

/-- If $A^{\mathsf T}A = I + C^{\mathsf T}C$ then $\det A$ is a unit. -/
lemma isUnit_det_of_eq {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin k) (Fin n) ℝ)
    (h : Aᵀ * A = 1 + Cᵀ * C) : IsUnit A.det := by
  have hp : (Aᵀ * A).PosDef := by
    rw [h]
    exact Matrix.PosDef.one.add_posSemidef (by simpa using Matrix.posSemidef_conjTranspose_mul_self C)
  have h1 := hp.isUnit
  rw [Matrix.isUnit_iff_isUnit_det, det_mul] at h1
  exact isUnit_of_mul_isUnit_right h1

/-- Algebraic core of `blockE_spec`. -/
lemma blockE_spec_aux (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin l) ℝ)
    (C : Matrix (Fin l) (Fin m) ℝ) (D : Matrix (Fin l) (Fin l) ℝ)
    (h1 : Aᵀ * A = 1 + Cᵀ * C) (h2 : Aᵀ * B = Cᵀ * D) (h3 : Dᵀ * D = 1 + Bᵀ * B) :
    IsUnit A.det ∧ IsUnit D.det ∧ (Aᵀ)⁻¹ * Cᵀ = B * D⁻¹ ∧
      (A * Aᵀ)⁻¹ = 1 - (B * D⁻¹) * (B * D⁻¹)ᵀ ∧ (D * Dᵀ)⁻¹ = 1 - (B * D⁻¹)ᵀ * (B * D⁻¹) := by
  have hA := isUnit_det_of_eq A C h1
  have hD := isUnit_det_of_eq D B h3
  have hPA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAP : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hQD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hD
  have hDQ : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hD
  have hAt : (Aᵀ)⁻¹ = (A⁻¹)ᵀ := (Matrix.transpose_nonsing_inv A).symm
  have hDt : (Dᵀ)⁻¹ = (D⁻¹)ᵀ := (Matrix.transpose_nonsing_inv D).symm
  have hPtAt : (A⁻¹)ᵀ * Aᵀ = 1 := by rw [← transpose_mul, hAP, transpose_one]
  have hQtDt : (D⁻¹)ᵀ * Dᵀ = 1 := by rw [← transpose_mul, hDQ, transpose_one]
  have ha : (Aᵀ)⁻¹ * Cᵀ = B * D⁻¹ := by
    rw [hAt]
    calc (A⁻¹)ᵀ * Cᵀ = (A⁻¹)ᵀ * (Cᵀ * D) * D⁻¹ := by
          rw [Matrix.mul_assoc _ _ D⁻¹, Matrix.mul_assoc, hDQ, Matrix.mul_one]
      _ = B * D⁻¹ := by rw [← h2, ← Matrix.mul_assoc, hPtAt, Matrix.one_mul]
  refine ⟨hA, hD, ha, ?_, ?_⟩
  · have e0 : (A⁻¹)ᵀ * (Aᵀ * A) * A⁻¹ = 1 := by
      rw [← Matrix.mul_assoc, hPtAt, Matrix.one_mul, hAP]
    have e1 : (A⁻¹)ᵀ * (Cᵀ * C) * A⁻¹ = 1 - (A⁻¹)ᵀ * A⁻¹ := by
      have : Cᵀ * C = Aᵀ * A - 1 := by rw [h1]; abel
      rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, e0]
    have e2 : (A⁻¹)ᵀ * Cᵀ * (C * A⁻¹) = (A⁻¹)ᵀ * (Cᵀ * C) * A⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_inv_rev, ← ha, hAt]
    simp only [transpose_mul, transpose_transpose]
    rw [e2, e1]; abel
  · have e0 : (D⁻¹)ᵀ * (Dᵀ * D) * D⁻¹ = 1 := by
      rw [← Matrix.mul_assoc, hQtDt, Matrix.one_mul, hDQ]
    have e1 : (D⁻¹)ᵀ * (Bᵀ * B) * D⁻¹ = 1 - (D⁻¹)ᵀ * D⁻¹ := by
      have : Bᵀ * B = Dᵀ * D - 1 := by rw [h3]; abel
      rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, e0]
    have e2 : (D⁻¹)ᵀ * Bᵀ * (B * D⁻¹) = (D⁻¹)ᵀ * (Bᵀ * B) * D⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_inv_rev, hDt]
    simp only [transpose_mul]
    rw [e2, e1]; abel

/-- **The matrix $E$ of (10.10)** (Cassels, Ch. 13, §10, p. 320): $E = BD^{-1}$, an $m \times l$ matrix. -/
@[kb "cassels1978" "Ch. 13, §10, (10.10), p. 320"]
noncomputable def blockE (M : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) ℝ) : Matrix (Fin m) (Fin l) ℝ :=
  M.toBlocks₁₂ * M.toBlocks₂₂⁻¹

/-- **(10.10)–(10.12)** (Cassels, Ch. 13, §10, pp. 320–321): for $M \in O_{\mathbb{R}}(f)$ the blocks $A$, $D$ are
invertible, $E = (A^{\mathsf T})^{-1}C^{\mathsf T} = BD^{-1}$, and
$$(AA^{\mathsf T})^{-1} = I_m - EE^{\mathsf T}, \qquad (DD^{\mathsf T})^{-1} = I_l - E^{\mathsf T}E.$$ -/
@[kb "cassels1978" "Ch. 13, §10, (10.10)–(10.12), pp. 320–321"]
theorem blockE_spec {M : GL (Fin m ⊕ Fin l) ℝ} (hM : M ∈ realAut (sigJ m l)) :
    IsUnit M.val.toBlocks₁₁.det ∧ IsUnit M.val.toBlocks₂₂.det ∧
      (M.val.toBlocks₁₁ᵀ)⁻¹ * M.val.toBlocks₂₁ᵀ = blockE M.val ∧
      (M.val.toBlocks₁₁ * M.val.toBlocks₁₁ᵀ)⁻¹ = 1 - blockE M.val * (blockE M.val)ᵀ ∧
      (M.val.toBlocks₂₂ * M.val.toBlocks₂₂ᵀ)⁻¹ = 1 - (blockE M.val)ᵀ * blockE M.val := by
  have h : M.val.toBlocks₁₁ᵀ * M.val.toBlocks₁₁ = 1 + M.val.toBlocks₂₁ᵀ * M.val.toBlocks₂₁ ∧
      M.val.toBlocks₂₂ᵀ * M.val.toBlocks₂₂ = 1 + M.val.toBlocks₁₂ᵀ * M.val.toBlocks₁₂ ∧
        M.val.toBlocks₁₁ᵀ * M.val.toBlocks₁₂ = M.val.toBlocks₂₁ᵀ * M.val.toBlocks₂₂ :=
    (transpose_mul_sigJ_mul_eq_iff M.val).mp hM
  obtain ⟨hA, hD, ha, hb, hc⟩ := blockE_spec_aux _ _ _ _ h.1 h.2.2 h.2.1
  exact ⟨hA, hD, ha, hb, hc⟩

/-- **The set $\mathcal E$ of (10.13)–(10.14)**: the real $m \times l$ matrices $E$ with $\vec{u}^{\mathsf T}E\vec{v} < 1$ for
all unit vectors $\vec{u} \in \mathbb{R}^m$, $\vec{v} \in \mathbb{R}^l$ (operator norm $< 1$; the supremum is attained,
by compactness, so this is Cassels' $\sup \vec{u}^{\mathsf T}E\vec{v} < 1$). *Erratum*:
Cassels calls $E$ an "$l \times m$" matrix with $\vec{u} \in \mathbb{R}^l$, $\vec{v} \in \mathbb{R}^m$; by (10.10),
$E = BD^{-1}$ has $m$ rows and $l$ columns. -/
@[kb "cassels1978" "Ch. 13, §10, Lemma 10.1, (10.13)–(10.14), p. 321 (the set ℰ)"]
def IsContraction (E : Matrix (Fin m) (Fin l) ℝ) : Prop :=
  ∀ u : Fin m → ℝ, ∀ v : Fin l → ℝ, u ⬝ᵥ u = 1 → v ⬝ᵥ v = 1 → u ⬝ᵥ (E *ᵥ v) < 1

section Aux
open scoped MatrixOrder

/-- A positive semidefinite real matrix has a symmetric square root. -/
lemma exists_symm_sqrt {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) (hP : P.PosSemidef) :
    ∃ S : Matrix (Fin k) (Fin k) ℝ, Sᵀ = S ∧ S * S = P := by
  refine ⟨CFC.sqrt P, ?_, ?_⟩
  · have := (CFC.sqrt_nonneg P).posSemidef.isHermitian
    simpa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using this
  · rw [← sq]; exact CFC.sq_sqrt P

end Aux

/-- $0 \le w \cdot w$. -/
lemma dot_self_nonneg' {k : ℕ} (w : Fin k → ℝ) : 0 ≤ w ⬝ᵥ w := by
  simpa using dotProduct_self_star_nonneg w

/-- $0 < w \cdot w$ for $w \ne 0$. -/
lemma dot_self_pos' {k : ℕ} {w : Fin k → ℝ} (hw : w ≠ 0) : 0 < w ⬝ᵥ w := by
  simpa using dotProduct_self_star_pos_iff.mpr hw

/-- The quadratic form of $I - E^{\mathsf T}E$. -/
lemma quad_one_sub (E : Matrix (Fin m) (Fin l) ℝ) (v : Fin l → ℝ) :
    star v ⬝ᵥ ((1 - Eᵀ * E) *ᵥ v) = v ⬝ᵥ v - (E *ᵥ v) ⬝ᵥ (E *ᵥ v) := by
  have key : v ⬝ᵥ (Eᵀ *ᵥ (E *ᵥ v)) = (E *ᵥ v) ⬝ᵥ (E *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, key]

/-- If $I - E^{\mathsf T}E$ is positive definite then $E$ is a contraction. -/
lemma isContraction_of_posDef (E : Matrix (Fin m) (Fin l) ℝ) (h : (1 - Eᵀ * E).PosDef) :
    IsContraction E := by
  intro u v hu hv
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have h1 := h.dotProduct_mulVec_pos hv0
  rw [quad_one_sub, hv] at h1
  have h2 := dot_self_nonneg' (u - E *ᵥ v)
  simp only [sub_dotProduct, dotProduct_sub, hu, dotProduct_comm (E *ᵥ v) u] at h2
  nlinarith

/-- If $E$ is a contraction then $I - E^{\mathsf T}E$ is positive definite. -/
lemma posDef_of_isContraction (E : Matrix (Fin m) (Fin l) ℝ) (h : IsContraction E) :
    (1 - Eᵀ * E).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simp [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul]
  · intro x hx
    rw [quad_one_sub]
    have hx0 := dot_self_pos' hx
    set s := Real.sqrt (x ⬝ᵥ x) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
    have hss : s * s = x ⬝ᵥ x := Real.mul_self_sqrt hx0.le
    have hv : (s⁻¹ • x) ⬝ᵥ (s⁻¹ • x) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
      field_simp
    have hw : (E *ᵥ (s⁻¹ • x)) ⬝ᵥ (E *ᵥ (s⁻¹ • x)) < 1 := by
      by_contra hcon
      rw [not_lt] at hcon
      set w := E *ᵥ (s⁻¹ • x) with hwdef
      have hc1 : 1 ≤ Real.sqrt (w ⬝ᵥ w) := by
        have := Real.sqrt_le_sqrt hcon
        simpa using this
      set c := Real.sqrt (w ⬝ᵥ w) with hc
      have hc0 : 0 < c := by linarith
      have hcc : c * c = w ⬝ᵥ w := Real.mul_self_sqrt (dot_self_nonneg' w)
      have hu : (c⁻¹ • w) ⬝ᵥ (c⁻¹ • w) = 1 := by
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hcc]
        field_simp
      have := h (c⁻¹ • w) (s⁻¹ • x) hu hv
      rw [← hwdef, smul_dotProduct, smul_eq_mul, ← hcc] at this
      have e : c⁻¹ * (c * c) = c := by field_simp
      linarith
    have hEx : E *ᵥ x = s • (E *ᵥ (s⁻¹ • x)) := by
      rw [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
    rw [hEx, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    nlinarith [mul_pos hs0 hs0]

/-- Blocks of the inverse of $M \in O_{\mathbb{R}}(f)$: $M^{-1} = J M^{\mathsf T} J$. -/
lemma inv_val_blocks {M : GL (Fin m ⊕ Fin l) ℝ} (hM : M ∈ realAut (sigJ m l)) :
    (M⁻¹).val = fromBlocks M.val.toBlocks₁₁ᵀ (-M.val.toBlocks₂₁ᵀ) (-M.val.toBlocks₁₂ᵀ) M.val.toBlocks₂₂ᵀ := by
  have hM' : M.valᵀ * sigJ m l * M.val = sigJ m l := hM
  have h1 : (sigJ m l * M.valᵀ * sigJ m l) * M.val = 1 := by
    calc (sigJ m l * M.valᵀ * sigJ m l) * M.val = sigJ m l * (M.valᵀ * sigJ m l * M.val) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM', sigJ_mul_sigJ]
  have h2 : M.val * (sigJ m l * M.valᵀ * sigJ m l) = 1 := mul_eq_one_comm.mp h1
  have h3 : (M⁻¹).val = sigJ m l * M.valᵀ * sigJ m l := by
    calc (M⁻¹).val = (M⁻¹).val * (M.val * (sigJ m l * M.valᵀ * sigJ m l)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [h3]
  conv_lhs => rw [← fromBlocks_toBlocks M.val]
  unfold sigJ
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

/-- Proof of `blockE_mul` (stated later, after Lemma 10.1, in the source order). -/
lemma blockE_mul_aux {M M₂ : GL (Fin m ⊕ Fin l) ℝ} (hM : M ∈ realAut (sigJ m l)) (hM₂ : M₂ ∈ realAut (sigJ m l)) :
    blockE (M * M₂).val =
      (M.val.toBlocks₁₁ * blockE M₂.val + M.val.toBlocks₁₂) *
        (M.val.toBlocks₂₁ * blockE M₂.val + M.val.toBlocks₂₂)⁻¹ := by
  have _hM := hM
  obtain ⟨-, hD₂, -⟩ := blockE_spec hM₂
  have hD₂' : M₂.val.toBlocks₂₂ * M₂.val.toBlocks₂₂⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD₂
  have hM1 := fromBlocks_toBlocks M.val
  have hM2 := fromBlocks_toBlocks M₂.val
  set A := M.val.toBlocks₁₁
  set B := M.val.toBlocks₁₂
  set C := M.val.toBlocks₂₁
  set D := M.val.toBlocks₂₂
  set B₂ := M₂.val.toBlocks₁₂
  set D₂ := M₂.val.toBlocks₂₂
  have hprod : (M * M₂).val = fromBlocks (A * M₂.val.toBlocks₁₁ + B * M₂.val.toBlocks₂₁) (A * B₂ + B * D₂)
      (C * M₂.val.toBlocks₁₁ + D * M₂.val.toBlocks₂₁) (C * B₂ + D * D₂) := by
    rw [Units.val_mul, ← hM1, ← hM2, fromBlocks_multiply]
    simp [A, B, C, D, B₂, D₂]
  have e1 : (M * M₂).val.toBlocks₁₂ = A * B₂ + B * D₂ := by rw [hprod]; simp
  have e2 : (M * M₂).val.toBlocks₂₂ = C * B₂ + D * D₂ := by rw [hprod]; simp
  unfold blockE
  rw [e1, e2]
  have f1 : A * B₂ + B * D₂ = (A * (B₂ * D₂⁻¹) + B) * D₂ := by
    rw [Matrix.add_mul, Matrix.mul_assoc A, Matrix.nonsing_inv_mul_cancel_right _ _ hD₂]
  have f2 : C * B₂ + D * D₂ = (C * (B₂ * D₂⁻¹) + D) * D₂ := by
    rw [Matrix.add_mul, Matrix.mul_assoc C, Matrix.nonsing_inv_mul_cancel_right _ _ hD₂]
  rw [f1, f2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc _ D₂, hD₂', Matrix.mul_one]

/-- An element of $O_{\mathbb{R}}(f)$ with $E = 0$ lies in $K$. -/
lemma mem_blockOrth_of_blockE_zero {N : GL (Fin m ⊕ Fin l) ℝ} (hN : N ∈ realAut (sigJ m l))
    (h : blockE N.val = 0) : N ∈ blockOrth m l := by
  obtain ⟨-, hD, -⟩ := blockE_spec hN
  have hN' : N.valᵀ * sigJ m l * N.val = sigJ m l := hN
  obtain ⟨h1, h3, h2⟩ := (transpose_mul_sigJ_mul_eq_iff N.val).mp hN'
  have hB : N.val.toBlocks₁₂ = 0 := by
    unfold blockE at h
    calc N.val.toBlocks₁₂ = N.val.toBlocks₁₂ * N.val.toBlocks₂₂⁻¹ * N.val.toBlocks₂₂ :=
          (Matrix.nonsing_inv_mul_cancel_right _ _ hD).symm
      _ = 0 := by rw [h, Matrix.zero_mul]
  have hC : N.val.toBlocks₂₁ = 0 := by
    rw [hB] at h2
    have h2' : N.val.toBlocks₂₁ᵀ * N.val.toBlocks₂₂ = 0 := by simpa using h2.symm
    have : N.val.toBlocks₂₁ᵀ = 0 := by
      calc N.val.toBlocks₂₁ᵀ = N.val.toBlocks₂₁ᵀ * N.val.toBlocks₂₂ * N.val.toBlocks₂₂⁻¹ :=
            (Matrix.mul_nonsing_inv_cancel_right _ _ hD).symm
        _ = 0 := by rw [h2', Matrix.zero_mul]
    simpa using this
  refine ⟨N.val.toBlocks₁₁, N.val.toBlocks₂₂, ?_, ?_, ?_⟩
  · rw [h1, hC]; simp
  · rw [h3, hB]; simp
  · conv_lhs => rw [← fromBlocks_toBlocks N.val]
    rw [hB, hC]

/-- For symmetric $S$ with $S S = Q^{-1}$ we have $S Q S = I$. -/
lemma sqrt_conj {k : ℕ} (S Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsUnit Q.det) (hS : S * S = Q⁻¹) :
    S * Q * S = 1 := by
  have h1 : S * (S * Q) = 1 := by
    rw [← Matrix.mul_assoc, hS, Matrix.nonsing_inv_mul _ hQ]
  rw [Matrix.mul_assoc]
  exact mul_eq_one_comm.mp h1 |> fun h => by rw [← Matrix.mul_assoc]; exact h

/-- Every real matrix with $M^{\mathsf T} J M = J$ is an element of $O_{\mathbb{R}}(f)$. -/
lemma exists_gl_of_orth (M : Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) ℝ) (h : Mᵀ * sigJ m l * M = sigJ m l) :
    ∃ g : GL (Fin m ⊕ Fin l) ℝ, g ∈ realAut (sigJ m l) ∧ g.val = M := by
  have h1 : (sigJ m l * Mᵀ * sigJ m l) * M = 1 := by
    calc (sigJ m l * Mᵀ * sigJ m l) * M = sigJ m l * (Mᵀ * sigJ m l * M) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, sigJ_mul_sigJ]
  exact ⟨⟨M, sigJ m l * Mᵀ * sigJ m l, mul_eq_one_comm.mp h1, h1⟩, h, rfl⟩

/-- Surjectivity part of Lemma 10.1. -/
lemma exists_of_isContraction (E : Matrix (Fin m) (Fin l) ℝ) (hE : IsContraction E) :
    ∃ M ∈ realAut (sigJ m l), blockE M.val = E := by
  have hP := posDef_of_isContraction E hE
  have hEt : IsContraction Eᵀ := by
    intro u v hu hv
    have := hE v u hv hu
    rwa [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have hR : (1 - E * Eᵀ).PosDef := by
    have := posDef_of_isContraction Eᵀ hEt
    simpa using this
  have hPu : IsUnit (1 - Eᵀ * E).det := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hRu : IsUnit (1 - E * Eᵀ).det := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  obtain ⟨D, hDs, hDD⟩ := exists_symm_sqrt _ hP.inv.posSemidef
  obtain ⟨A, hAs, hAA⟩ := exists_symm_sqrt _ hR.inv.posSemidef
  have kD := sqrt_conj D _ hPu hDD
  have kA := sqrt_conj A _ hRu hAA
  have hDu : IsUnit D.det := Matrix.isUnit_det_of_right_inverse (B := D * (1 - Eᵀ * E)) (by
    rw [← Matrix.mul_assoc, hDD, Matrix.nonsing_inv_mul _ hPu])
  have horth : (fromBlocks A (E * D) (Eᵀ * A) D)ᵀ * sigJ m l * fromBlocks A (E * D) (Eᵀ * A) D =
      sigJ m l := by
    rw [transpose_mul_sigJ_mul_eq_iff]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      toBlocks_fromBlocks₂₂]
    refine ⟨?_, ?_, ?_⟩
    · calc Aᵀ * A = A * A := by rw [hAs]
        _ = A * (1 - E * Eᵀ + E * Eᵀ) * A := by rw [sub_add_cancel, Matrix.mul_one]
        _ = A * (1 - E * Eᵀ) * A + A * (E * Eᵀ) * A := by rw [Matrix.mul_add, Matrix.add_mul]
        _ = 1 + (Eᵀ * A)ᵀ * (Eᵀ * A) := by
          rw [kA, transpose_mul, transpose_transpose, hAs]; simp only [Matrix.mul_assoc]
    · calc Dᵀ * D = D * D := by rw [hDs]
        _ = D * (1 - Eᵀ * E + Eᵀ * E) * D := by rw [sub_add_cancel, Matrix.mul_one]
        _ = D * (1 - Eᵀ * E) * D + D * (Eᵀ * E) * D := by rw [Matrix.mul_add, Matrix.add_mul]
        _ = 1 + (E * D)ᵀ * (E * D) := by
          rw [kD, transpose_mul, hDs]; simp only [Matrix.mul_assoc]
    · rw [transpose_mul, transpose_transpose]; simp only [Matrix.mul_assoc]
  obtain ⟨g, hg, hgv⟩ := exists_gl_of_orth _ horth
  refine ⟨g, hg, ?_⟩
  rw [hgv]; unfold blockE
  simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂]
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hDu, Matrix.mul_one]

/-- **Lemma 10.1** (Cassels, Ch. 13, §10, p. 321): (10.10) sets up a bijection between $\mathcal E$ and the cosets
$O_{\mathbb{R}}(f)/K$: $E(M) \in \mathcal E$ for $M \in O_{\mathbb{R}}(f)$; $E(MW) = E(M)$ for $W \in K$; $E(M) = E(M')$
only if $M^{-1}M' \in K$; and every $E \in \mathcal E$ is an $E(M)$. -/
@[kb "cassels1978" "Ch. 13, §10, Lemma 10.1, p. 321"]
theorem blockE_bijective :
    (∀ M ∈ realAut (sigJ m l), IsContraction (blockE M.val)) ∧
    (∀ M ∈ realAut (sigJ m l), ∀ W ∈ blockOrth m l, blockE (M * W).val = blockE M.val) ∧
    (∀ M ∈ realAut (sigJ m l), ∀ M' ∈ realAut (sigJ m l), blockE M.val = blockE M'.val →
      M⁻¹ * M' ∈ blockOrth m l) ∧
    (∀ E : Matrix (Fin m) (Fin l) ℝ, IsContraction E → ∃ M ∈ realAut (sigJ m l), blockE M.val = E) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M hM
    obtain ⟨-, hD, -, -, hc⟩ := blockE_spec hM
    apply isContraction_of_posDef
    rw [← hc]
    have hDu : IsUnit M.val.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).mpr hD
    have hinj : Function.Injective M.val.toBlocks₂₂.vecMul := Matrix.vecMul_injective_iff_isUnit.mpr hDu
    have := (Matrix.PosDef.mul_conjTranspose_self M.val.toBlocks₂₂ hinj).inv
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  · intro M hM W hW
    obtain ⟨U, V, hU, hV, hW⟩ := hW
    have hVu : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hV
    have hVV : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hVu
    have hprod : (M * W).val = fromBlocks (M.val.toBlocks₁₁ * U) (M.val.toBlocks₁₂ * V)
        (M.val.toBlocks₂₁ * U) (M.val.toBlocks₂₂ * V) := by
      rw [Units.val_mul, hW]
      conv_lhs => rw [← fromBlocks_toBlocks M.val]
      rw [fromBlocks_multiply]; simp
    unfold blockE
    rw [hprod]
    simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂]
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV, Matrix.one_mul]
  · intro M hM M' hM' hE
    have hN : M⁻¹ * M' ∈ realAut (sigJ m l) := (realAut (sigJ m l)).mul_mem ((realAut (sigJ m l)).inv_mem hM) hM'
    obtain ⟨hAu, -, ha, -, -⟩ := blockE_spec hM
    have hE0 : blockE (M⁻¹ * M').val = 0 := by
      rw [blockE_mul_aux ((realAut (sigJ m l)).inv_mem hM) hM', inv_val_blocks hM, ← hE, ← ha]
      simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
      have hAt : IsUnit (M.val.toBlocks₁₁ᵀ).det := by rwa [det_transpose]
      have : M.val.toBlocks₁₁ᵀ * ((M.val.toBlocks₁₁ᵀ)⁻¹ * M.val.toBlocks₂₁ᵀ) = M.val.toBlocks₂₁ᵀ :=
        Matrix.mul_nonsing_inv_cancel_left _ _ hAt
      rw [this, add_neg_cancel, Matrix.zero_mul]
    exact mem_blockOrth_of_blockE_zero hN hE0
  · exact exists_of_isContraction

/-- **Lemma 10.2** (Cassels, Ch. 13, §10, p. 321): for $M, M_1, M_2 \in O_{\mathbb{R}}(f)$ with $M_1 = MM_2$ (10.15),
$$E_1 = (AE_2 + B)(CE_2 + D)^{-1} \tag{10.16}$$
where $M = \begin{pmatrix} A & B \\ C & D\end{pmatrix}$ and $E_j = E(M_j)$. (The display is partly garbled in the
machine-read text; reconstructed from the proof (10.17)–(10.18).) -/
@[kb "cassels1978" "Ch. 13, §10, Lemma 10.2, (10.15)–(10.18), p. 321"]
theorem blockE_mul {M M₂ : GL (Fin m ⊕ Fin l) ℝ} (hM : M ∈ realAut (sigJ m l)) (hM₂ : M₂ ∈ realAut (sigJ m l)) :
    blockE (M * M₂).val =
      (M.val.toBlocks₁₁ * blockE M₂.val + M.val.toBlocks₁₂) *
        (M.val.toBlocks₂₁ * blockE M₂.val + M.val.toBlocks₂₂)⁻¹ :=
  blockE_mul_aux hM hM₂

end QuadFormsKB.Reduction