/-
# Cassels, Chapter 13, §7: the non-Euclidean plane

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §7, *The non-euclidean plane*, pp. 309–312: the
Beltrami–Klein model. The group $\mathcal M$ of real fractional-linear transformations of the open unit disc
$\mathcal D$ onto itself acts transitively, with stabilizer of the origin the orthogonal group (Lemma 7.1); it is
isomorphic to $SL_2^{\pm}(\mathbb{R})/\{\pm 1\}$ (Lemma 7.2); there is an invariant metric, given by (7.9) (Lemma 7.3),
whose geodesics are line segments and whose perpendicular bisectors are lines (Corollaries 1–3); and the volume of
cones gives an invariant measure (Lemma 7.4).

**Conventions.** Points of the plane are vectors $\vec{\xi} = (\xi_0, \xi_1) \in \mathbb{R}^2$ (Cassels' $(\xi_1, \xi_2)$).
A real fractional-linear transformation is given by an invertible $3 \times 3$ real matrix $P$:
$\vec{\xi} \mapsto \pi(P(\xi_0, \xi_1, 1))$, $\pi(X) = (X_0/X_2, X_1/X_2)$ (`flt`). An element of $\mathcal M$ is a
permutation of $\mathcal D$ given on $\mathcal D$ by such a map (`discGroup`). $f_0 = X_0^2 + X_1^2 - X_2^2$ (`lorentz`);
$\mathcal D$ is the image under $\pi$ of the $X$ with $f_0(X) < 0$.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic
import QuadFormsKB.Literature.Cassels.Ch13.Sec5

open Matrix

namespace QuadFormsKB.Reduction

/-- **The open unit disc $\mathcal D$** (Cassels, Ch. 13, (6.8), p. 304, and (7.1), p. 309):
$\xi_0^2 + \xi_1^2 < 1$. -/
@[kb "cassels1978" "Ch. 13, §6, (6.8), p. 304; §7, (7.1), p. 309 (the disc 𝒟)"]
def disc : Set (Fin 2 → ℝ) := {ξ | ξ 0 ^ 2 + ξ 1 ^ 2 < 1}

/-- The point $(\xi_0, \xi_1, 1)$ of $\mathbb{R}^3$ over $\vec{\xi}$. -/
def liftPt (ξ : Fin 2 → ℝ) : Fin 3 → ℝ := ![ξ 0, ξ 1, 1]

/-- **The projection $\pi(X) = (X_0/X_2, X_1/X_2)$** (Cassels, Ch. 13, (6.5)–(6.7), p. 304). -/
@[kb "cassels1978" "Ch. 13, §6, (6.5)–(6.7), p. 304 (the map π)"]
noncomputable def projPt (X : Fin 3 → ℝ) : Fin 2 → ℝ := ![X 0 / X 2, X 1 / X 2]

/-- **The fractional-linear transformation of the plane given by $P$**: $\vec{\xi} \mapsto \pi(P(\xi_0, \xi_1, 1))$
(Cassels, Ch. 13, (6.9), p. 304). -/
noncomputable def flt (P : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 2 → ℝ) : Fin 2 → ℝ := projPt (P *ᵥ liftPt ξ)

/-- **The form $f_0 = X_0^2 + X_1^2 - X_2^2$** (Cassels, Ch. 13, (6.3), p. 304; Lemma 7.4, p. 312), as a diagonal
matrix. -/
def lorentz : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, 1, -1]

/-- Helper: the lift of a projection is the rescaled vector. -/
theorem liftPt_projPt {Y : Fin 3 → ℝ} (h : Y 2 ≠ 0) : liftPt (projPt Y) = (Y 2)⁻¹ • Y := by
  ext i; fin_cases i <;> simp [liftPt, projPt] <;> field_simp

/-- Helper: projection of the lift. -/
@[simp] theorem projPt_liftPt (ξ : Fin 2 → ℝ) : projPt (liftPt ξ) = ξ := by
  ext i; fin_cases i <;> simp [liftPt, projPt]

/-- Helper: projection is invariant under non-zero scaling. -/
theorem projPt_smul {Y : Fin 3 → ℝ} {c : ℝ} (hc : c ≠ 0) : projPt (c • Y) = projPt Y := by
  ext i; fin_cases i <;> simp [projPt] <;> field_simp

/-- Helper: `P` applied to the lift of a projection. -/
theorem mulVec_liftPt_projPt (P : Matrix (Fin 3) (Fin 3) ℝ) {Y : Fin 3 → ℝ} (h : Y 2 ≠ 0) :
    P *ᵥ liftPt (projPt Y) = (Y 2)⁻¹ • (P *ᵥ Y) := by
  rw [liftPt_projPt h, Matrix.mulVec_smul]

/-- Helper: composition of fractional-linear maps. -/
theorem flt_flt (P Q : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 2 → ℝ) (h1 : (Q *ᵥ liftPt ξ) 2 ≠ 0) :
    flt P (flt Q ξ) = flt (P * Q) ξ := by
  unfold flt
  rw [mulVec_liftPt_projPt P h1, projPt_smul (inv_ne_zero h1), Matrix.mulVec_mulVec]

/-- Helper: `lorentz` is an involution. -/
theorem lorentz_mul_self : lorentz * lorentz = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lorentz, Matrix.mul_apply, Fin.sum_univ_three]

/-- Helper: `lorentz` is symmetric. -/
theorem lorentz_transpose : lorentzᵀ = lorentz := by simp [lorentz]

/-- Helper: `lorentz` applied to a vector. -/
theorem lorentz_mulVec (Y : Fin 3 → ℝ) : lorentz *ᵥ Y = ![Y 0, Y 1, -Y 2] := by
  ext i; fin_cases i <;> simp [lorentz, Matrix.mulVec_diagonal]

/-- Helper: the Lorentz bilinear form. -/
def lorB (X Y : Fin 3 → ℝ) : ℝ := X 0 * Y 0 + X 1 * Y 1 - X 2 * Y 2

/-- Helper: `lorB` as a matrix expression. -/
theorem lorB_eq (X Y : Fin 3 → ℝ) : lorB X Y = X ⬝ᵥ (lorentz *ᵥ Y) := by
  simp [lorB, lorentz_mulVec, dotProduct, Fin.sum_univ_three]; ring

/-- Helper: Lorentz matrices preserve `lorB`. -/
theorem lorB_mulVec {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz) (X Y : Fin 3 → ℝ) :
    lorB (T *ᵥ X) (T *ᵥ Y) = lorB X Y := by
  have h : Tᵀ *ᵥ (lorentz *ᵥ (T *ᵥ Y)) = lorentz *ᵥ Y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT]
  rw [lorB_eq, lorB_eq, ← h, Matrix.dotProduct_mulVec X Tᵀ, Matrix.vecMul_transpose]

/-- Helper: the inverse of a Lorentz matrix is `lorentz * Tᵀ * lorentz`, again Lorentz. -/
theorem lorentz_inv_aux {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz) :
    (lorentz * Tᵀ * lorentz) * T = 1 ∧ T * (lorentz * Tᵀ * lorentz) = 1 ∧
      (lorentz * Tᵀ * lorentz)ᵀ * lorentz * (lorentz * Tᵀ * lorentz) = lorentz := by
  have h1 : (lorentz * Tᵀ * lorentz) * T = 1 := by
    calc (lorentz * Tᵀ * lorentz) * T = lorentz * (Tᵀ * lorentz * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hT, lorentz_mul_self]
  have h2 : T * (lorentz * Tᵀ * lorentz) = 1 := mul_eq_one_comm.mp h1
  have h3 : T * lorentz * Tᵀ = lorentz := by
    calc T * lorentz * Tᵀ = (T * (lorentz * Tᵀ * lorentz)) * lorentz := by
          simp only [Matrix.mul_assoc, lorentz_mul_self, Matrix.mul_one]
      _ = lorentz := by rw [h2, Matrix.one_mul]
  refine ⟨h1, h2, ?_⟩
  simp only [Matrix.transpose_mul, lorentz_transpose, Matrix.transpose_transpose]
  calc _ = lorentz * (T * lorentz * Tᵀ) * lorentz := by
        simp only [Matrix.mul_assoc, lorentz_mul_self, Matrix.mul_one]
    _ = lorentz := by rw [h3, lorentz_mul_self, Matrix.one_mul]

/-- Helper: `lorB` on lifted points. -/
theorem lorB_lift (ξ η : Fin 2 → ℝ) : lorB (liftPt ξ) (liftPt η) = ξ 0 * η 0 + ξ 1 * η 1 - 1 := by
  simp [lorB, liftPt]

/-- Helper: a timelike vector projects into the disc. -/
theorem projPt_mem_disc {Y : Fin 3 → ℝ} (h : Y 0 ^ 2 + Y 1 ^ 2 < Y 2 ^ 2) :
    Y 2 ≠ 0 ∧ projPt Y ∈ disc := by
  have h2 : Y 2 ≠ 0 := by
    intro h0; rw [h0] at h; nlinarith [sq_nonneg (Y 0), sq_nonneg (Y 1)]
  refine ⟨h2, ?_⟩
  have hpos : 0 < Y 2 ^ 2 := by positivity
  show (projPt Y) 0 ^ 2 + (projPt Y) 1 ^ 2 < 1
  simp only [projPt, Matrix.cons_val_zero, Matrix.cons_val_one, div_pow]
  rw [← add_div, div_lt_one hpos]; exact h

/-- Helper: a Lorentz matrix maps the lift of a point of the disc to a timelike vector. -/
theorem lorentz_maps_disc {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz) {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ disc) : (T *ᵥ liftPt ξ) 2 ≠ 0 ∧ flt T ξ ∈ disc := by
  have h := lorB_mulVec hT (liftPt ξ) (liftPt ξ)
  rw [lorB_lift] at h
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  have : (T *ᵥ liftPt ξ) 0 ^ 2 + (T *ᵥ liftPt ξ) 1 ^ 2 < (T *ᵥ liftPt ξ) 2 ^ 2 := by
    unfold lorB at h; nlinarith
  exact projPt_mem_disc this

/-- **The group $\mathcal M$** (Cassels, Ch. 13, §7, p. 309): the real fractional-linear transformations which map the
disc $\mathcal D$ onto itself, as permutations of $\mathcal D$: $\sigma \in \mathcal M$ iff for some invertible $P$,
$P(\xi_0, \xi_1, 1)$ has non-zero last coordinate and $\sigma(\vec{\xi}) = \pi(P(\xi_0, \xi_1, 1))$ for every
$\vec{\xi} \in \mathcal D$. -/
@[kb "cassels1978" "Ch. 13, §7, p. 309 (the group 𝓜)"]
def discGroup : Subgroup (Equiv.Perm disc) where
  carrier := {σ | ∃ P : Matrix (Fin 3) (Fin 3) ℝ, IsUnit P.det ∧
    ∀ ξ : disc, (P *ᵥ liftPt ξ) 2 ≠ 0 ∧ (σ ξ : Fin 2 → ℝ) = flt P ξ}
  mul_mem' := by
    rintro σ τ ⟨P, hP, hσ⟩ ⟨Q, hQ, hτ⟩
    refine ⟨P * Q, by rw [Matrix.det_mul]; exact hP.mul hQ, fun ξ => ?_⟩
    obtain ⟨hQ2, hQe⟩ := hτ ξ
    obtain ⟨hP2, hPe⟩ := hσ (τ ξ)
    have hl : liftPt (↑(τ ξ) : Fin 2 → ℝ) = ((Q *ᵥ liftPt ξ) 2)⁻¹ • (Q *ᵥ liftPt ξ) := by
      rw [hQe]; exact liftPt_projPt hQ2
    rw [hl, Matrix.mulVec_smul] at hP2
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec]
      intro h0
      apply hP2
      simp only [Pi.smul_apply, smul_eq_mul, h0, mul_zero]
    · rw [Equiv.Perm.mul_apply, hPe, hQe, ← flt_flt P Q ξ hQ2]
  one_mem' := by
    refine ⟨1, by simp, fun ξ => ⟨?_, ?_⟩⟩
    · simp [liftPt]
    · simp only [Matrix.one_mulVec, flt, projPt_liftPt, Equiv.Perm.one_apply]
  inv_mem' := by
    rintro σ ⟨P, hP, hσ⟩
    refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det P hP, fun η => ?_⟩
    set ξ : disc := σ⁻¹ η with hξ
    have hση : σ ξ = η := by simp [hξ]
    obtain ⟨hP2, hPe⟩ := hσ ξ
    have hl : liftPt (↑η : Fin 2 → ℝ) = ((P *ᵥ liftPt ξ) 2)⁻¹ • (P *ᵥ liftPt ξ) := by
      rw [← hση, hPe]; exact liftPt_projPt hP2
    have hv : P⁻¹ *ᵥ liftPt (↑η : Fin 2 → ℝ) = ((P *ᵥ liftPt ξ) 2)⁻¹ • liftPt (ξ : Fin 2 → ℝ) := by
      rw [hl, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]
    refine ⟨?_, ?_⟩
    · rw [hv, Pi.smul_apply, smul_eq_mul]
      have : liftPt (ξ : Fin 2 → ℝ) 2 = 1 := rfl
      rw [this, mul_one]; exact inv_ne_zero hP2
    · unfold flt
      rw [hv, projPt_smul (inv_ne_zero hP2), projPt_liftPt]

/-- Helper: the permutation of the disc induced by a Lorentz matrix. -/
noncomputable def ltPerm (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : Tᵀ * lorentz * T = lorentz) :
    Equiv.Perm disc where
  toFun ξ := ⟨flt T ξ, (lorentz_maps_disc hT ξ.2).2⟩
  invFun ξ := ⟨flt (lorentz * Tᵀ * lorentz) ξ, (lorentz_maps_disc (lorentz_inv_aux hT).2.2 ξ.2).2⟩
  left_inv ξ := by
    apply Subtype.ext
    show flt (lorentz * Tᵀ * lorentz) (flt T ξ) = ξ
    rw [flt_flt _ _ _ (lorentz_maps_disc hT ξ.2).1, (lorentz_inv_aux hT).1]
    simp [flt]
  right_inv ξ := by
    apply Subtype.ext
    show flt T (flt (lorentz * Tᵀ * lorentz) ξ) = ξ
    rw [flt_flt _ _ _ (lorentz_maps_disc (lorentz_inv_aux hT).2.2 ξ.2).1, (lorentz_inv_aux hT).2.1]
    simp [flt]

/-- Helper: the action of `ltPerm`. -/
theorem ltPerm_apply (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : Tᵀ * lorentz * T = lorentz) (ξ : disc) :
    (ltPerm T hT ξ : Fin 2 → ℝ) = flt T ξ := rfl

/-- Helper: `ltPerm T` lies in `discGroup`. -/
theorem ltPerm_mem (T : Matrix (Fin 3) (Fin 3) ℝ) (hT : Tᵀ * lorentz * T = lorentz) :
    ltPerm T hT ∈ discGroup :=
  ⟨T, Matrix.isUnit_det_of_left_inverse (lorentz_inv_aux hT).1, fun ξ =>
    ⟨(lorentz_maps_disc hT ξ.2).1, rfl⟩⟩

/-- Helper: products of Lorentz matrices are Lorentz. -/
theorem lorentz_mul_mem {T T' : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz)
    (hT' : T'ᵀ * lorentz * T' = lorentz) : (T * T')ᵀ * lorentz * (T * T') = lorentz := by
  calc (T * T')ᵀ * lorentz * (T * T') = T'ᵀ * (Tᵀ * lorentz * T) * T' := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = lorentz := by rw [hT, hT']

/-- Helper: `ltPerm` is multiplicative. -/
theorem ltPerm_mul (T T' : Matrix (Fin 3) (Fin 3) ℝ) (hT : Tᵀ * lorentz * T = lorentz)
    (hT' : T'ᵀ * lorentz * T' = lorentz) :
    ltPerm (T * T') (lorentz_mul_mem hT hT') = ltPerm T hT * ltPerm T' hT' := by
  refine Equiv.ext fun ξ => Subtype.ext ?_
  show flt (T * T') ξ = flt T (flt T' ξ)
  rw [flt_flt _ _ _ (lorentz_maps_disc hT' ξ.2).1]

/-- Helper: elements of `discGroup` with the same projective matrix agree. -/
theorem ltPerm_eq_of_flt {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz)
    {σ : Equiv.Perm disc} (h : ∀ ξ : disc, (σ ξ : Fin 2 → ℝ) = flt T ξ) : σ = ltPerm T hT := by
  exact Equiv.ext fun ξ => Subtype.ext (h ξ)

/-- Helper: membership of a projection in the disc. -/
theorem projPt_mem_disc_iff {Y : Fin 3 → ℝ} (h : Y 2 ≠ 0) :
    projPt Y ∈ disc ↔ Y 0 ^ 2 + Y 1 ^ 2 < Y 2 ^ 2 := by
  have hpos : 0 < Y 2 ^ 2 := by positivity
  show (projPt Y) 0 ^ 2 + (projPt Y) 1 ^ 2 < 1 ↔ _
  simp only [projPt, Matrix.cons_val_zero, Matrix.cons_val_one, div_pow]
  rw [← add_div, div_lt_one hpos]

/-- Helper: coordinates of `P (ξ₀, ξ₁, 1)`. -/
theorem mulVec_liftPt_apply (P : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 2 → ℝ) (i : Fin 3) :
    (P *ᵥ liftPt ξ) i = P i 0 * ξ 0 + P i 1 * ξ 1 + P i 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, liftPt]

/-- Helper: a matrix representing a permutation of the disc maps a point to a timelike vector iff
the point lies in the disc. -/
theorem disc_iff_of_discGroup {σ : Equiv.Perm disc} {P : Matrix (Fin 3) (Fin 3) ℝ} (hPdet : IsUnit P.det)
    (hP : ∀ ξ : disc, (P *ᵥ liftPt ξ) 2 ≠ 0 ∧ (σ ξ : Fin 2 → ℝ) = flt P ξ) (ξ : Fin 2 → ℝ) :
    ξ ∈ disc ↔ (P *ᵥ liftPt ξ) 0 ^ 2 + (P *ᵥ liftPt ξ) 1 ^ 2 < (P *ᵥ liftPt ξ) 2 ^ 2 := by
  constructor
  · intro hξ
    obtain ⟨h2, he⟩ := hP ⟨ξ, hξ⟩
    have hm : flt P ξ ∈ disc := by rw [← he]; exact (σ ⟨ξ, hξ⟩).2
    exact (projPt_mem_disc_iff h2).mp hm
  · intro hlt
    obtain ⟨h2, hm⟩ := projPt_mem_disc hlt
    set Y := P *ᵥ liftPt ξ with hY
    obtain ⟨h2', he'⟩ := hP (σ.symm ⟨projPt Y, hm⟩)
    have hση : σ (σ.symm ⟨projPt Y, hm⟩) = ⟨projPt Y, hm⟩ := by simp
    have hproj : projPt (P *ᵥ liftPt ((σ.symm ⟨projPt Y, hm⟩ : disc) : Fin 2 → ℝ)) = projPt Y := by
      have := congrArg Subtype.val hση
      rw [he'] at this; exact this
    set ξ' : Fin 2 → ℝ := ((σ.symm ⟨projPt Y, hm⟩ : disc) : Fin 2 → ℝ) with hξ'
    set Y' := P *ᵥ liftPt ξ' with hY'
    have e1 : (Y' 2)⁻¹ • Y' = (Y 2)⁻¹ • Y := by
      rw [← liftPt_projPt h2', ← liftPt_projPt h2, hproj]
    have e2 : Y' = (Y' 2 / Y 2) • Y := by
      calc Y' = Y' 2 • ((Y' 2)⁻¹ • Y') := by rw [smul_smul, mul_inv_cancel₀ h2', one_smul]
        _ = Y' 2 • ((Y 2)⁻¹ • Y) := by rw [e1]
        _ = (Y' 2 / Y 2) • Y := by rw [smul_smul, div_eq_mul_inv]
    have e3 : liftPt ξ' = (Y' 2 / Y 2) • liftPt ξ := by
      have h4 : P⁻¹ *ᵥ Y' = liftPt ξ' := by
        rw [hY', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hPdet, Matrix.one_mulVec]
      have h5 : P⁻¹ *ᵥ Y = liftPt ξ := by
        rw [hY, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hPdet, Matrix.one_mulVec]
      calc liftPt ξ' = P⁻¹ *ᵥ Y' := h4.symm
        _ = P⁻¹ *ᵥ ((Y' 2 / Y 2) • Y) := by rw [← e2]
        _ = (Y' 2 / Y 2) • liftPt ξ := by rw [Matrix.mulVec_smul, h5]
    have e4 : Y' 2 / Y 2 = 1 := by
      have := congrFun e3 2
      simpa [liftPt] using this.symm
    rw [e4, one_smul] at e3
    have : ξ = ξ' := by
      ext i; fin_cases i
      · have := congrFun e3 0; simpa [liftPt] using this.symm
      · have := congrFun e3 1; simpa [liftPt] using this.symm
    rw [this]; exact (σ.symm ⟨projPt Y, hm⟩).2

/-- The origin $0$ of $\mathcal D$. -/
def discZero : disc := ⟨0, by simp [disc]⟩

/-- Helper: a continuous function positive on `[0, 1)` is non-negative at `1`. -/
theorem nonneg_at_one_of_pos {g : ℝ → ℝ} (hg : Continuous g) (hpos : ∀ t, 0 ≤ t → t < 1 → 0 < g t) :
    0 ≤ g 1 :=
  ge_of_tendsto ((hg.tendsto 1).mono_left nhdsWithin_le_nhds)
    (Filter.mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) fun t ht => (hpos t ht.1.le ht.2).le)

/-- Helper: an element of `𝓜` fixing the origin acts by an orthogonal matrix. -/
theorem stabilizer_aux {σ : Equiv.Perm disc} (hσ : σ ∈ discGroup) (h0 : σ discZero = discZero) :
    ∃ R : Matrix (Fin 2) (Fin 2) ℝ, Rᵀ * R = 1 ∧
      ∀ ξ : disc, (σ ξ : Fin 2 → ℝ) = R *ᵥ (ξ : Fin 2 → ℝ) := by
  obtain ⟨P, hPdet, hP⟩ := hσ
  obtain ⟨hc, he0⟩ := hP discZero
  have hz : (σ discZero : Fin 2 → ℝ) = 0 := by rw [h0]; rfl
  rw [hz] at he0
  have hl0 : (discZero : Fin 2 → ℝ) = 0 := rfl
  rw [hl0] at hc he0
  have hc' : P 2 2 ≠ 0 := by
    have := mulVec_liftPt_apply P 0 2
    rw [this] at hc; simpa using hc
  have hP02 : P 0 2 = 0 := by
    have e : (flt P 0) 0 = P 0 2 / P 2 2 := by simp [flt, projPt, mulVec_liftPt_apply]
    have : P 0 2 / P 2 2 = 0 := by rw [← e, ← he0]; rfl
    exact (div_eq_zero_iff.mp this).resolve_right hc'
  have hP12 : P 1 2 = 0 := by
    have e : (flt P 0) 1 = P 1 2 / P 2 2 := by simp [flt, projPt, mulVec_liftPt_apply]
    have : P 1 2 / P 2 2 = 0 := by rw [← e, ← he0]; rfl
    exact (div_eq_zero_iff.mp this).resolve_right hc'
  set c := P 2 2 with hcdef
  have hdisc := disc_iff_of_discGroup hPdet hP
  -- boundary condition
  have key : ∀ u0 u1 : ℝ, u0 ^ 2 + u1 ^ 2 = 1 →
      (P 2 0 * u0 + P 2 1 * u1 + c) ^ 2 = (P 0 0 * u0 + P 0 1 * u1) ^ 2 + (P 1 0 * u0 + P 1 1 * u1) ^ 2 := by
    intro u0 u1 hu
    set g : ℝ → ℝ := fun t => (t * (P 2 0 * u0 + P 2 1 * u1) + c) ^ 2 -
      t ^ 2 * ((P 0 0 * u0 + P 0 1 * u1) ^ 2 + (P 1 0 * u0 + P 1 1 * u1) ^ 2) with hg
    have hiff : ∀ t : ℝ, t ^ 2 < 1 ↔ 0 < g t := by
      intro t
      have h1 := hdisc ![t * u0, t * u1]
      have h2 : ((![t * u0, t * u1] : Fin 2 → ℝ) ∈ disc) ↔ t ^ 2 < 1 := by
        show (![t * u0, t * u1] 0) ^ 2 + (![t * u0, t * u1] 1) ^ 2 < 1 ↔ _
        have : (![t * u0, t * u1] 0) ^ 2 + (![t * u0, t * u1] 1) ^ 2 = t ^ 2 := by
          show (t * u0) ^ 2 + (t * u1) ^ 2 = t ^ 2
          rw [mul_pow, mul_pow, ← mul_add, hu, mul_one]
        rw [this]
      rw [← h2, h1]
      simp only [mulVec_liftPt_apply, hP02, hP12, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [hg]
      constructor <;> intro h <;> nlinarith [h]
    have hcont : Continuous g := by simp only [hg]; fun_prop
    have h1 : 0 ≤ g 1 := nonneg_at_one_of_pos hcont fun t ht0 ht1 =>
      (hiff t).mp (by nlinarith)
    have h2 : g 1 ≤ 0 := by
      by_contra hcon
      have := (hiff 1).mpr (not_le.mp hcon)
      norm_num at this
    have h3 : g 1 = 0 := le_antisymm h2 h1
    simp only [hg] at h3
    nlinarith [h3]
  have hw0 : P 2 0 = 0 := by
    have k1 := key 1 0 (by norm_num)
    have k2 := key (-1) 0 (by norm_num)
    have : c * P 2 0 = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc'
    · exact h
  have hw1 : P 2 1 = 0 := by
    have k1 := key 0 1 (by norm_num)
    have k2 := key 0 (-1) (by norm_num)
    have : c * P 2 1 = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc'
    · exact h
  have homog : ∀ v0 v1 : ℝ, (P 0 0 * v0 + P 0 1 * v1) ^ 2 + (P 1 0 * v0 + P 1 1 * v1) ^ 2 =
      c ^ 2 * (v0 ^ 2 + v1 ^ 2) := by
    intro v0 v1
    by_cases hv : v0 ^ 2 + v1 ^ 2 = 0
    · have h0 : v0 = 0 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
      have h1 : v1 = 0 := by nlinarith [sq_nonneg v0, sq_nonneg v1]
      subst h0; subst h1; simp
    · have hpos : 0 < v0 ^ 2 + v1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hv)
      set s := √(v0 ^ 2 + v1 ^ 2) with hs
      have hs2 : s ^ 2 = v0 ^ 2 + v1 ^ 2 := Real.sq_sqrt hpos.le
      have hspos : 0 < s := Real.sqrt_pos.mpr hpos
      have := key (v0 / s) (v1 / s) (by field_simp; linarith)
      rw [hw0, hw1] at this
      field_simp at this
      nlinarith [this, hs2]
  have h00 := homog 1 0
  have h01 := homog 0 1
  have h11 := homog 1 1
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc'
  refine ⟨Matrix.of ![![P 0 0 / c, P 0 1 / c], ![P 1 0 / c, P 1 1 / c]], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> field_simp <;> nlinarith
  · intro ξ
    have hY := mulVec_liftPt_apply P ξ
    obtain ⟨-, hξe⟩ := hP ξ
    rw [hξe]
    set x : Fin 2 → ℝ := (ξ : Fin 2 → ℝ) with hx
    have f0 : (flt P x) 0 = (P 0 0 * x 0 + P 0 1 * x 1) / c := by
      simp only [flt, projPt, Matrix.cons_val_zero, hY, hP02, hw0, hw1]; rw [hcdef]; ring
    have f1 : (flt P x) 1 = (P 1 0 * x 0 + P 1 1 * x 1) / c := by
      simp only [flt, projPt, Matrix.cons_val_one, Matrix.head_cons, hY, hP12, hw0, hw1]; rw [hcdef]; simp only [Matrix.cons_val_zero]; ring
    ext i; fin_cases i
    · show (flt P x) 0 = _
      rw [f0]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
    · show (flt P x) 1 = _
      rw [f1]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- Helper: the matrix of `M ↦ S M Sᵀ` on `[[X₂+X₀, X₁], [X₁, X₂-X₀]]`. -/
noncomputable def symMat (S : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(S 0 0 ^ 2 - S 0 1 ^ 2 - S 1 0 ^ 2 + S 1 1 ^ 2) / 2, S 0 0 * S 0 1 - S 1 0 * S 1 1,
      (S 0 0 ^ 2 + S 0 1 ^ 2 - S 1 0 ^ 2 - S 1 1 ^ 2) / 2;
    S 0 0 * S 1 0 - S 0 1 * S 1 1, S 0 0 * S 1 1 + S 0 1 * S 1 0, S 0 0 * S 1 0 + S 0 1 * S 1 1;
    (S 0 0 ^ 2 - S 0 1 ^ 2 + S 1 0 ^ 2 - S 1 1 ^ 2) / 2, S 0 0 * S 0 1 + S 1 0 * S 1 1,
      (S 0 0 ^ 2 + S 0 1 ^ 2 + S 1 0 ^ 2 + S 1 1 ^ 2) / 2]

/-- Helper: `symMat` is multiplicative. -/
theorem symMat_mul (S S' : Matrix (Fin 2) (Fin 2) ℝ) : symMat (S * S') = symMat S * symMat S' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

/-- Helper: `symMat` of the identity. -/
theorem symMat_one : symMat (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat]

/-- Helper: `symMat S` scales `lorentz` by `det S ^ 2`. -/
theorem symMat_lorentz_aux (S : Matrix (Fin 2) (Fin 2) ℝ) :
    (symMat S)ᵀ * lorentz * symMat S = (S.det) ^ 2 • lorentz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, lorentz, Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_two, Matrix.diagonal_apply] <;> ring

/-- Helper: `symMat S` is Lorentz when `det S = ±1`. -/
theorem symMat_lorentz {S : Matrix (Fin 2) (Fin 2) ℝ} (h : S.det = 1 ∨ S.det = -1) :
    (symMat S)ᵀ * lorentz * symMat S = lorentz := by
  rw [symMat_lorentz_aux]
  rcases h with h | h <;> simp [h]

/-- Helper: a boost moving the origin to a prescribed point of the disc. -/
theorem exists_boost {η : Fin 2 → ℝ} (hη : η ∈ disc) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ, S.det = 1 ∧ ∃ γ : ℝ, 0 < γ ∧ symMat S *ᵥ liftPt 0 = γ • liftPt η := by
  have hu : 0 < 1 - η 0 ^ 2 - η 1 ^ 2 := by
    have : η 0 ^ 2 + η 1 ^ 2 < 1 := hη
    linarith
  have hs : 0 < √(1 - η 0 ^ 2 - η 1 ^ 2) := Real.sqrt_pos.mpr hu
  set γ : ℝ := (√(1 - η 0 ^ 2 - η 1 ^ 2))⁻¹ with hγdef
  have hγ : 0 < γ := inv_pos.mpr hs
  have hγ2 : γ ^ 2 * (1 - η 0 ^ 2 - η 1 ^ 2) = 1 := by
    rw [hγdef, inv_pow, Real.sq_sqrt hu.le]; field_simp
  have h0 : 0 < 1 + η 0 := by
    have : η 0 ^ 2 + η 1 ^ 2 < 1 := hη
    nlinarith [sq_nonneg (η 1), sq_nonneg (η 0 + 1)]
  have hA : 0 < γ * (1 + η 0) := mul_pos hγ h0
  set l : ℝ := √(γ * (1 + η 0)) with hl
  have hlpos : 0 < l := Real.sqrt_pos.mpr hA
  have hl2 : l ^ 2 = γ * (1 + η 0) := Real.sq_sqrt hA.le
  set m : ℝ := γ * η 1 / l with hm
  refine ⟨!![l, 0; m, l⁻¹], ?_, γ, hγ, ?_⟩
  · simp [Matrix.det_fin_two]; field_simp
  · have key : ∀ i, (symMat !![l, 0; m, l⁻¹] *ᵥ liftPt 0) i = symMat !![l, 0; m, l⁻¹] i 2 := by
      intro i; rw [mulVec_liftPt_apply]; simp
    ext i; fin_cases i
    · simp only [Fin.zero_eta, key]
      simp [symMat, liftPt, hm]
      field_simp
      nlinarith [hl2, hγ2]
    · simp only [Fin.mk_one, key]
      simp [symMat, liftPt, hm]
      field_simp
    · simp only [Fin.reduceFinMk, key]
      simp [symMat, liftPt, hm]
      field_simp
      nlinarith [hl2, hγ2]

/-- Helper: a Lorentz matrix moving the origin to a prescribed point of the disc. -/
theorem exists_lorentz_flt_zero {η : Fin 2 → ℝ} (hη : η ∈ disc) :
    ∃ T : Matrix (Fin 3) (Fin 3) ℝ, Tᵀ * lorentz * T = lorentz ∧ flt T 0 = η := by
  obtain ⟨S, hS, γ, hγ, hv⟩ := exists_boost hη
  refine ⟨symMat S, symMat_lorentz (Or.inl hS), ?_⟩
  unfold flt
  rw [hv, projPt_smul hγ.ne', projPt_liftPt]

/-- Helper: the block matrix `diag(R, 1)`. -/
def blockRot (R : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![R 0 0, R 0 1, 0; R 1 0, R 1 1, 0; 0, 0, 1]

/-- Helper: `diag(R, 1)` is Lorentz for orthogonal `R`. -/
theorem blockRot_lorentz {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : Rᵀ * R = 1) :
    (blockRot R)ᵀ * lorentz * blockRot R = lorentz := by
  have h00 := congrFun (congrFun hR 0) 0
  have h01 := congrFun (congrFun hR 0) 1
  have h10 := congrFun (congrFun hR 1) 0
  have h11 := congrFun (congrFun hR 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockRot, lorentz, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> nlinarith

/-- Helper: `diag(R, 1)` acts on the plane by `R`. -/
theorem flt_blockRot (R : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℝ) :
    (blockRot R *ᵥ liftPt ξ) 2 ≠ 0 ∧ flt (blockRot R) ξ = R *ᵥ ξ := by
  have h2 : (blockRot R *ᵥ liftPt ξ) 2 = 1 := by
    rw [mulVec_liftPt_apply]; simp [blockRot]
  refine ⟨by rw [h2]; exact one_ne_zero, ?_⟩
  unfold flt projPt
  ext i; fin_cases i
  · show (blockRot R *ᵥ liftPt ξ) 0 / (blockRot R *ᵥ liftPt ξ) 2 = _
    rw [h2, mulVec_liftPt_apply]
    simp [blockRot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · show (blockRot R *ᵥ liftPt ξ) 1 / (blockRot R *ᵥ liftPt ξ) 2 = _
    rw [h2, mulVec_liftPt_apply]
    simp [blockRot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Every $T \in O_{\mathbb{R}}(f_0)$ induces an element of $\mathcal M$** (Cassels, Ch. 13, (6.10), p. 304): for
$T^{\mathsf T}f_0T = f_0$ there is $\sigma \in \mathcal M$ with $\sigma(\vec{\xi}) = \pi(T(\xi_0, \xi_1, 1))$. -/
@[kb "cassels1978" "Ch. 13, §6, (6.10), p. 304; §7, proof of Lemma 7.2, p. 310"]
theorem exists_discGroup_of_lorentz {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz) :
    ∃ σ ∈ discGroup, ∀ ξ : disc, (σ ξ : Fin 2 → ℝ) = flt T ξ :=
  ⟨ltPerm T hT, ltPerm_mem T hT, fun _ => rfl⟩

/-- **Every element of $\mathcal M$ comes from $O_{\mathbb{R}}(f_0)$** (Cassels, Ch. 13, proof of Lemma 7.2, p. 310:
"it is readily verified that this is in fact an isomorphism"): if $\sigma \in \mathcal M$ then
$\sigma(\vec{\xi}) = \pi(T(\xi_0, \xi_1, 1))$ on $\mathcal D$ for some $T$ with $T^{\mathsf T}f_0T = f_0$ (a matrix $P$
mapping $\mathcal D$ onto itself is a scalar multiple of such a $T$). -/
@[kb "cassels1978" "Ch. 13, §7, proof of Lemma 7.2, p. 310 (O_ℝ(f₀) → 𝓜 is onto)"]
theorem exists_lorentz_of_discGroup {σ : Equiv.Perm disc} (hσ : σ ∈ discGroup) :
    ∃ T : Matrix (Fin 3) (Fin 3) ℝ, Tᵀ * lorentz * T = lorentz ∧ ∀ ξ : disc, (σ ξ : Fin 2 → ℝ) = flt T ξ := by
  obtain ⟨B, hB, hB0⟩ := exists_lorentz_flt_zero (σ discZero).2
  set β : Equiv.Perm disc := ltPerm B hB with hβ
  have hβ0 : β discZero = σ discZero := Subtype.ext hB0
  have hτ : β⁻¹ * σ ∈ discGroup := discGroup.mul_mem (discGroup.inv_mem (ltPerm_mem B hB)) hσ
  have hτ0 : (β⁻¹ * σ) discZero = discZero := by
    rw [Equiv.Perm.mul_apply, ← hβ0]; simp
  obtain ⟨R, hR, hRe⟩ := stabilizer_aux hτ hτ0
  refine ⟨B * blockRot R, lorentz_mul_mem hB (blockRot_lorentz hR), fun ξ => ?_⟩
  have h1 : σ ξ = β ((β⁻¹ * σ) ξ) := by simp
  have h2 : ((β⁻¹ * σ) ξ : Fin 2 → ℝ) = flt (blockRot R) ξ := by
    rw [hRe ξ, (flt_blockRot R ξ).2]
  rw [h1]
  show flt B (((β⁻¹ * σ) ξ : disc) : Fin 2 → ℝ) = _
  rw [h2, flt_flt _ _ _ (flt_blockRot R ξ).1]

/-- Helper: every point of the disc is the image of the origin under an element of `𝓜`. -/
theorem exists_discGroup_zero (η : disc) : ∃ σ ∈ discGroup, σ discZero = η := by
  obtain ⟨B, hB, hB0⟩ := exists_lorentz_flt_zero η.2
  exact ⟨ltPerm B hB, ltPerm_mem B hB, Subtype.ext hB0⟩

/-- **Lemma 7.1** (Cassels, Ch. 13, §7, p. 309): (i) $\mathcal M$ acts transitively on $\mathcal D$; (ii) the stabilizer
$ST_0$ of the origin consists of the rotations about $0$ and the reflections about lines through $0$, i.e. the
$\vec{\xi} \mapsto R\vec{\xi}$ with $R^{\mathsf T}R = I$. -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.1, p. 309"]
theorem discGroup_transitive_stabilizer :
    (∀ ξ η : disc, ∃ σ ∈ discGroup, σ ξ = η) ∧
    ∀ σ ∈ discGroup, (σ discZero = discZero ↔
      ∃ R : Matrix (Fin 2) (Fin 2) ℝ, Rᵀ * R = 1 ∧ ∀ ξ : disc, (σ ξ : Fin 2 → ℝ) = R *ᵥ ξ) := by
  refine ⟨fun ξ η => ?_, fun σ hσ => ⟨fun h => stabilizer_aux hσ h, ?_⟩⟩
  · obtain ⟨σ₁, h₁, e₁⟩ := exists_discGroup_zero ξ
    obtain ⟨σ₂, h₂, e₂⟩ := exists_discGroup_zero η
    refine ⟨σ₂ * σ₁⁻¹, discGroup.mul_mem h₂ (discGroup.inv_mem h₁), ?_⟩
    rw [Equiv.Perm.mul_apply, ← e₁]; simpa using e₂
  · rintro ⟨R, -, hR⟩
    apply Subtype.ext
    rw [hR]
    show R *ᵥ (0 : Fin 2 → ℝ) = 0
    simp

/-- **Lemma 7.1, Corollary** (Cassels, Ch. 13, §7, p. 310): the points of $\mathcal D$ correspond bijectively to the
cosets $\mathcal M/ST_0$, by $\sigma ST_0 \mapsto \sigma(0)$. -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.1, Cor., p. 310"]
theorem discGroup_quotient_stabilizer :
    ∃ e : discGroup ⧸ (MulAction.stabilizer discGroup discZero) ≃ disc,
      ∀ σ : discGroup, e (QuotientGroup.mk σ) = (σ : Equiv.Perm disc) discZero := by
  have hmem : ∀ x : disc, x ∈ MulAction.orbit discGroup discZero := by
    intro x
    obtain ⟨σ, hσ, e⟩ := exists_discGroup_zero x
    exact ⟨⟨σ, hσ⟩, e⟩
  refine ⟨(MulAction.orbitEquivQuotientStabilizer discGroup discZero).symm.trans
    (Equiv.subtypeUnivEquiv hmem), fun σ => ?_⟩
  rfl

/-- **$SL_2^{\pm}(\mathbb{R})$** (Cassels, Ch. 13, (7.2)–(7.3), p. 310): the real $2 \times 2$ matrices of determinant
$\pm 1$. -/
@[kb "cassels1978" "Ch. 13, §7, (7.2)–(7.3), p. 310"]
def slPM : Subgroup (GL (Fin 2) ℝ) where
  carrier := {S | S.val.det = 1 ∨ S.val.det = -1}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;> simp [Matrix.det_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    rintro a (ha | ha) <;> simp [Matrix.coe_units_inv, Matrix.det_nonsing_inv, ha]

/-- **$K^{\pm}$** (Cassels, Ch. 13, (7.4)–(7.5), p. 310): the matrices $\begin{pmatrix}\alpha & -\beta\\ \beta & \alpha
\end{pmatrix}$ and $\begin{pmatrix}\alpha & \beta\\ \beta & -\alpha\end{pmatrix}$ with $\alpha^2 + \beta^2 = 1$, i.e. the
orthogonal $2 \times 2$ matrices (the displays are garbled in the machine-read text; reconstructed: the elements of
$SL^{\pm}_2$ fixing the point $(1, 0, 1)$ up to a scalar). -/
@[kb "cassels1978" "Ch. 13, §7, (7.4)–(7.5), p. 310 (the group K^±)"]
def kPM : Subgroup (GL (Fin 2) ℝ) where
  carrier := {S | S.valᵀ * S.val = 1}
  mul_mem' := by
    intro a b ha hb
    have ha' : a.valᵀ * a.val = 1 := ha
    have hb' : b.valᵀ * b.val = 1 := hb
    show (a * b).valᵀ * (a * b).val = 1
    simp only [Units.val_mul, Matrix.transpose_mul]
    calc _ = b.valᵀ * (a.valᵀ * a.val) * b.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', Matrix.mul_one, hb']
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    have ha' : a.valᵀ * a.val = 1 := ha
    have h1 : a.val * a.valᵀ = 1 := mul_eq_one_comm.mp ha'
    have : (a⁻¹).val = a.valᵀ := by
      rw [Matrix.coe_units_inv]; exact Matrix.inv_eq_left_inv ha'
    show (a⁻¹).valᵀ * (a⁻¹).val = 1
    rw [this, Matrix.transpose_transpose]; exact h1

/-- Helper: the entries of an orthogonal `2 × 2` matrix (both `SᵀS = 1` and `SSᵀ = 1`). -/
theorem orth_entries {S : Matrix (Fin 2) (Fin 2) ℝ} (h : Sᵀ * S = 1) :
    S 0 0 ^ 2 + S 1 0 ^ 2 = 1 ∧ S 0 0 * S 0 1 + S 1 0 * S 1 1 = 0 ∧ S 0 1 ^ 2 + S 1 1 ^ 2 = 1 ∧
    S 0 0 ^ 2 + S 0 1 ^ 2 = 1 ∧ S 0 0 * S 1 0 + S 0 1 * S 1 1 = 0 ∧ S 1 0 ^ 2 + S 1 1 ^ 2 = 1 := by
  have h' : S * Sᵀ = 1 := mul_eq_one_comm.mp h
  have a := congrFun (congrFun h 0) 0
  have b := congrFun (congrFun h 0) 1
  have c := congrFun (congrFun h 1) 1
  have a' := congrFun (congrFun h' 0) 0
  have b' := congrFun (congrFun h' 0) 1
  have c' := congrFun (congrFun h' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a b c a' b' c'
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Helper: for orthogonal `S`, `symMat S` is `diag(R, 1)` with `R` its upper-left block. -/
theorem symMat_orth {S : Matrix (Fin 2) (Fin 2) ℝ} (h : Sᵀ * S = 1) :
    symMat S = blockRot (Matrix.of ![![symMat S 0 0, symMat S 0 1], ![symMat S 1 0, symMat S 1 1]]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := orth_entries h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat, blockRot] <;> nlinarith

/-- Helper: `symMat (-1) = 1`. -/
theorem symMat_neg_one : symMat (-1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat]

/-- Helper: the determinant condition of an element of `slPM`. -/
theorem slPM_det (S : slPM) : S.1.val.det = 1 ∨ S.1.val.det = -1 := S.2

/-- Helper: the permutation of the disc induced by an element of $SL_2^{\pm}(\mathbb{R})$. -/
noncomputable def slPMPerm (S : slPM) : Equiv.Perm disc := ltPerm (symMat S.1.val) (symMat_lorentz (slPM_det S))

/-- Helper: the homomorphism $SL_2^{\pm}(\mathbb{R}) \to \mathcal M$. -/
noncomputable def slPMHom : slPM →* discGroup where
  toFun S := ⟨slPMPerm S, ltPerm_mem _ _⟩
  map_one' := by
    apply Subtype.ext
    refine Equiv.ext fun ξ => Subtype.ext ?_
    show flt (symMat (1 : slPM).1.val) ξ = ξ
    simp [flt, symMat_one]
  map_mul' S S' := by
    apply Subtype.ext
    refine Equiv.ext fun ξ => Subtype.ext ?_
    show flt (symMat (S * S' : slPM).1.val) ξ = flt (symMat S.1.val) (flt (symMat S'.1.val) ξ)
    rw [flt_flt _ _ _ (lorentz_maps_disc (symMat_lorentz (slPM_det S')) ξ.2).1, ← symMat_mul]
    rfl

/-- Helper: `slPMHom` acts on points by `flt (symMat S)`. -/
theorem slPMHom_apply (S : slPM) (ξ : disc) :
    (((slPMHom S : discGroup) : Equiv.Perm disc) ξ : Fin 2 → ℝ) = flt (symMat S.1.val) ξ := rfl

/-- Helper: entry `(0, 2)` of `symMat`. -/
theorem symMat_02 (S : Matrix (Fin 2) (Fin 2) ℝ) :
    symMat S 0 2 = (S 0 0 ^ 2 + S 0 1 ^ 2 - S 1 0 ^ 2 - S 1 1 ^ 2) / 2 := by simp [symMat]

/-- Helper: entry `(1, 2)` of `symMat`. -/
theorem symMat_12 (S : Matrix (Fin 2) (Fin 2) ℝ) : symMat S 1 2 = S 0 0 * S 1 0 + S 0 1 * S 1 1 := by
  simp [symMat]

/-- Helper: entry `(2, 2)` of `symMat`. -/
theorem symMat_22 (S : Matrix (Fin 2) (Fin 2) ℝ) :
    symMat S 2 2 = (S 0 0 ^ 2 + S 0 1 ^ 2 + S 1 0 ^ 2 + S 1 1 ^ 2) / 2 := by simp [symMat]

/-- Helper: `P₂₂ > 0` for `P = symMat S` with `det S = ±1`. -/
theorem symMat_22_pos {S : Matrix (Fin 2) (Fin 2) ℝ} (h : S.det = 1 ∨ S.det = -1) :
    0 < symMat S 2 2 := by
  rw [symMat_22]
  rw [Matrix.det_fin_two] at h
  rcases h with h | h <;> nlinarith [sq_nonneg (S 0 0 - S 1 1), sq_nonneg (S 0 1 + S 1 0),
    sq_nonneg (S 0 0 + S 1 1), sq_nonneg (S 0 1 - S 1 0)]

/-- Helper: stabilizer of the origin under `slPMHom`. -/
theorem slPMHom_stab (S : slPM) :
    ((slPMHom S : discGroup) : Equiv.Perm disc) discZero = discZero ↔ (S : GL (Fin 2) ℝ) ∈ kPM := by
  constructor
  · intro h
    have hz : flt (symMat S.1.val) 0 = 0 := congrArg Subtype.val h
    have hdet := slPM_det S
    have hp := symMat_22_pos hdet
    have e : ∀ i, (symMat S.1.val *ᵥ liftPt 0) i = symMat S.1.val i 2 := by
      intro i; rw [mulVec_liftPt_apply]; simp
    have e0 := congrFun hz 0
    have e1 := congrFun hz 1
    simp only [flt, projPt, Matrix.cons_val_zero, Matrix.cons_val_one, e, Pi.zero_apply] at e0 e1
    rw [div_eq_zero_iff] at e0 e1
    have h02 := e0.resolve_right hp.ne'
    have h12 := e1.resolve_right hp.ne'
    rw [symMat_02] at h02
    rw [symMat_12] at h12
    rw [Matrix.det_fin_two] at hdet
    set p := S.1.val 0 0
    set q := S.1.val 0 1
    set r := S.1.val 1 0
    set t := S.1.val 1 1
    have hl : (p ^ 2 + q ^ 2) * (p ^ 2 + q ^ 2) = 1 := by
      have h1 : p ^ 2 + q ^ 2 = r ^ 2 + t ^ 2 := by linarith
      have h2 : p * r + q * t = 0 := h12
      have h3 : (p * t - q * r) ^ 2 = 1 := by rcases hdet with h | h <;> rw [h] <;> norm_num
      calc (p ^ 2 + q ^ 2) * (p ^ 2 + q ^ 2) = (p ^ 2 + q ^ 2) * (r ^ 2 + t ^ 2) := by rw [← h1]
        _ = (p * t - q * r) ^ 2 + (p * r + q * t) ^ 2 := by ring
        _ = 1 := by rw [h3, h2]; norm_num
    have hl1 : p ^ 2 + q ^ 2 = 1 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hSS : S.1.val * S.1.valᵀ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
    exact mul_eq_one_comm.mp hSS
  · intro h
    have h' : S.1.valᵀ * S.1.val = 1 := h
    apply Subtype.ext
    show flt (symMat S.1.val) 0 = 0
    rw [symMat_orth h', (flt_blockRot _ _).2]
    simp

/-- Helper: half-angle formulas. -/
theorem exists_half_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c ^ 2 - s ^ 2 = a ∧ 2 * c * s = b := by
  have ha : -1 ≤ a := by nlinarith [sq_nonneg b]
  have hc2 : (√((1 + a) / 2)) ^ 2 = (1 + a) / 2 := Real.sq_sqrt (by linarith)
  set c := √((1 + a) / 2) with hc
  by_cases h0 : c = 0
  · have : a = -1 := by rw [h0] at hc2; linarith
    have hb : b = 0 := by subst this; nlinarith [sq_nonneg b]
    exact ⟨0, 1, by norm_num, by rw [this]; norm_num, by rw [hb]; ring⟩
  · have hc2' : c ^ 2 ≠ 0 := pow_ne_zero 2 h0
    refine ⟨c, b / (2 * c), ?_, ?_, ?_⟩
    · field_simp
      nlinarith
    · field_simp
      nlinarith
    · field_simp

/-- Helper: a rotation `R = [[a, -b], [b, a]]` is `symMat` of a rotation. -/
theorem exists_S_of_rot {R : Matrix (Fin 2) (Fin 2) ℝ} (h1 : R 0 0 ^ 2 + R 1 0 ^ 2 = 1)
    (e1 : R 0 1 = -R 1 0) (e2 : R 1 1 = R 0 0) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ, Sᵀ * S = 1 ∧ symMat S = blockRot R := by
  obtain ⟨c, s, hcs1, hcs2, hcs3⟩ := exists_half_angle h1
  have eR00 : R 0 0 = c ^ 2 - s ^ 2 := hcs2.symm
  have eR10 : R 1 0 = 2 * c * s := hcs3.symm
  refine ⟨!![c, -s; s, c], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [symMat, blockRot, e1, e2, eR00, eR10] <;>
      first | linarith | nlinarith [hcs1]

/-- Helper: a reflection `R = [[a, b], [b, -a]]` is `symMat` of a reflection. -/
theorem exists_S_of_refl {R : Matrix (Fin 2) (Fin 2) ℝ} (h1 : R 0 0 ^ 2 + R 1 0 ^ 2 = 1)
    (e1 : R 0 1 = R 1 0) (e2 : R 1 1 = -R 0 0) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ, Sᵀ * S = 1 ∧ symMat S = blockRot R := by
  obtain ⟨c, s, hcs1, hcs2, hcs3⟩ := exists_half_angle h1
  have eR00 : R 0 0 = c ^ 2 - s ^ 2 := hcs2.symm
  have eR10 : R 1 0 = 2 * c * s := hcs3.symm
  refine ⟨!![c, s; s, -c], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [symMat, blockRot, e1, e2, eR00, eR10] <;>
      first | linarith | nlinarith [hcs1]

/-- Helper: every orthogonal `R` is `symMat S` (on the block) for an orthogonal `S`. -/
theorem exists_S_of_orth {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : Rᵀ * R = 1) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ, Sᵀ * S = 1 ∧ symMat S = blockRot R := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := orth_entries hR
  have hdet : R.det * R.det = 1 := by
    have := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact this
  rw [Matrix.det_fin_two] at hdet
  have hdet' : (R 0 0 * R 1 1 - R 0 1 * R 1 0) = 1 ∨ (R 0 0 * R 1 1 - R 0 1 * R 1 0) = -1 :=
    mul_self_eq_one_iff.mp hdet
  rcases hdet' with hd | hd
  · have hs : (R 0 1 + R 1 0) ^ 2 + (R 1 1 - R 0 0) ^ 2 = 0 := by linarith
    have e1 : R 0 1 + R 1 0 = 0 := by nlinarith [sq_nonneg (R 0 1 + R 1 0), sq_nonneg (R 1 1 - R 0 0)]
    have e2 : R 1 1 - R 0 0 = 0 := by nlinarith [sq_nonneg (R 0 1 + R 1 0), sq_nonneg (R 1 1 - R 0 0)]
    exact exists_S_of_rot h1 (by linarith) (by linarith)
  · have hs : (R 0 1 - R 1 0) ^ 2 + (R 1 1 + R 0 0) ^ 2 = 0 := by linarith
    have e1 : R 0 1 - R 1 0 = 0 := by nlinarith [sq_nonneg (R 0 1 - R 1 0), sq_nonneg (R 1 1 + R 0 0)]
    have e2 : R 1 1 + R 0 0 = 0 := by nlinarith [sq_nonneg (R 0 1 - R 1 0), sq_nonneg (R 1 1 + R 0 0)]
    exact exists_S_of_refl h1 (by linarith) (by linarith)

/-- Helper: `slPMHom` is trivial exactly on `±1`. -/
theorem slPMHom_ker (S : slPM) :
    slPMHom S = 1 ↔ (S : GL (Fin 2) ℝ) = 1 ∨ (S : GL (Fin 2) ℝ) = -1 := by
  constructor
  · intro h
    have hf : ∀ ξ : disc, flt (symMat S.1.val) ξ = ξ := fun ξ => by
      have := congrArg (fun g : discGroup => ((g : Equiv.Perm disc) ξ : Fin 2 → ℝ)) h
      exact this
    have hz : ((slPMHom S : discGroup) : Equiv.Perm disc) discZero = discZero := by rw [h]; rfl
    have hk' : S.1.valᵀ * S.1.val = 1 := (slPMHom_stab S).mp hz
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := orth_entries hk'
    have hbl := symMat_orth hk'
    have ha : ∀ ξ : disc, symMat S.1.val 0 0 * ξ.1 0 + symMat S.1.val 0 1 * ξ.1 1 = ξ.1 0 ∧
        symMat S.1.val 1 0 * ξ.1 0 + symMat S.1.val 1 1 * ξ.1 1 = ξ.1 1 := by
      intro ξ
      have := hf ξ
      rw [hbl, (flt_blockRot _ _).2] at this
      have e0 := congrFun this 0
      have e1 := congrFun this 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
      exact ⟨e0, e1⟩
    have hx := ha ⟨![1 / 2, 0], by simp [disc]; norm_num⟩
    have hy := ha ⟨![0, 1 / 2], by simp [disc]; norm_num⟩
    simp at hx hy
    simp only [symMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.vecHead, Matrix.vecTail] at hx hy
    set p := S.1.val 0 0
    set q := S.1.val 0 1
    set r := S.1.val 1 0
    set t := S.1.val 1 1
    have hq : q = 0 := by nlinarith [sq_nonneg q, sq_nonneg r]
    have hr : r = 0 := by nlinarith [sq_nonneg q, sq_nonneg r]
    have hp2 : p * p = 1 := by rw [hq] at h4; nlinarith
    have hpt : p * t = 1 := by rw [hq, hr] at hy; linarith [hy.2]
    have htp : t = p := by nlinarith [sq_nonneg (p - t)]
    have hqM : S.1.val 0 1 = 0 := hq
    have hrM : S.1.val 1 0 = 0 := hr
    rcases mul_self_eq_one_iff.mp hp2 with hp1 | hp1
    · left
      have e00 : S.1.val 0 0 = 1 := hp1
      have e11 : S.1.val 1 1 = 1 := by show t = 1; linarith
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hqM, hrM, e00, e11]
    · right
      have e00 : S.1.val 0 0 = -1 := hp1
      have e11 : S.1.val 1 1 = -1 := by show t = -1; linarith
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hqM, hrM, e00, e11]
  · rintro (h | h)
    · have : S = 1 := Subtype.ext h
      rw [this, map_one]
    · apply Subtype.ext
      refine Equiv.ext fun ξ => Subtype.ext ?_
      show flt (symMat S.1.val) ξ = ξ
      have : S.1.val = -1 := by rw [h]; simp
      rw [this, symMat_neg_one]
      simp [flt]

/-- Helper: `slPMHom` is surjective. -/
theorem slPMHom_surj : Function.Surjective slPMHom := by
  intro σ
  obtain ⟨S0, hS0, γ, hγ, hv⟩ := exists_boost (σ.1 discZero).2
  have hB := symMat_lorentz (Or.inl hS0)
  set A := ltPerm (symMat S0) hB with hA
  have hA0 : A discZero = σ.1 discZero := by
    apply Subtype.ext
    show flt (symMat S0) 0 = _
    unfold flt
    rw [hv, projPt_smul hγ.ne', projPt_liftPt]
  have hτ : A⁻¹ * σ.1 ∈ discGroup := discGroup.mul_mem (discGroup.inv_mem (ltPerm_mem _ hB)) σ.2
  have hτ0 : (A⁻¹ * σ.1) discZero = discZero := by rw [Equiv.Perm.mul_apply, ← hA0]; simp
  obtain ⟨R, hR, hRe⟩ := stabilizer_aux hτ hτ0
  obtain ⟨S1, hS1, hS1R⟩ := exists_S_of_orth hR
  have hdet1 : S1.det = 1 ∨ S1.det = -1 := by
    have := congrArg Matrix.det hS1
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact mul_self_eq_one_iff.mp this
  have hdet : (S0 * S1).det = 1 ∨ (S0 * S1).det = -1 := by
    rw [Matrix.det_mul, hS0]; simpa using hdet1
  have hu : IsUnit (S0 * S1).det := by rcases hdet with h | h <;> rw [h] <;> simp
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' (S0 * S1) hu, hdet⟩, ?_⟩
  apply Subtype.ext
  refine Equiv.ext fun ξ => Subtype.ext ?_
  show flt (symMat (S0 * S1)) ξ = σ.1 ξ
  rw [symMat_mul, hS1R, ← flt_flt _ _ _ (flt_blockRot R ξ).1, (flt_blockRot R ξ).2, ← hRe ξ]
  have h1 : σ.1 ξ = A ((A⁻¹ * σ.1) ξ) := by simp
  exact (congrArg Subtype.val h1).symm

/-- **Lemma 7.2** (Cassels, Ch. 13, §7, p. 310): (i) $\mathcal M$ is isomorphic to $SL_2^{\pm}(\mathbb{R})/\{\pm 1\}$; (ii) the
isomorphism can be chosen so that the stabilizer $ST_0$ of the origin corresponds to $K^{\pm}/\{\pm 1\}$. Stated with a
surjective homomorphism $SL_2^{\pm}(\mathbb{R}) \to \mathcal M$ with kernel $\{\pm 1\}$, mapping $K^{\pm}$ onto $ST_0$
(Cassels: via the substitutions (7.6)–(7.8) and the matrices (5.6) of §5, `spinMat`). -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.2, (7.6)–(7.8), p. 310"]
theorem exists_slPM_hom_discGroup :
    ∃ φ : slPM →* discGroup, Function.Surjective φ ∧
      (∀ S : slPM, φ S = 1 ↔ (S : GL (Fin 2) ℝ) = 1 ∨ (S : GL (Fin 2) ℝ) = -1) ∧
      ∀ S : slPM, ((φ S : Equiv.Perm disc) discZero = discZero ↔ (S : GL (Fin 2) ℝ) ∈ kPM) :=
  ⟨slPMHom, slPMHom_surj, slPMHom_ker, slPMHom_stab⟩

/-- Helper: a surjection `f : G → X` whose fibres are the left cosets of `H` gives `G ⧸ H ≃ X`. -/
theorem nonempty_quotient_equiv {G X : Type*} [Group G] (H : Subgroup G) (f : G → X)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ H) (hs : Function.Surjective f) : Nonempty (G ⧸ H ≃ X) := by
  refine ⟨Equiv.ofBijective (Quotient.lift f fun a b hab =>
    (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)) ⟨?_, ?_⟩⟩
  · intro x y
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact fun h => Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hf _ _).mp h))
  · intro x
    obtain ⟨g, hg⟩ := hs x
    exact ⟨Quotient.mk _ g, hg⟩

/-- Helper: fibres of the orbit map of the origin, for a homomorphism into `𝓜`. -/
theorem orbit_fibre {G : Type*} [Group G] (φ : G →* discGroup) (H : Subgroup G)
    (hH : ∀ g, ((φ g : discGroup) : Equiv.Perm disc) discZero = discZero ↔ g ∈ H) (a b : G) :
    ((φ a : discGroup) : Equiv.Perm disc) discZero = ((φ b : discGroup) : Equiv.Perm disc) discZero ↔
      a⁻¹ * b ∈ H := by
  rw [← hH, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_eq_iff_eq, eq_comm]

/-- Helper: the inclusion `SL₂(ℝ) → SL₂^±(ℝ)`. -/
noncomputable def slToPM : Matrix.SpecialLinearGroup (Fin 2) ℝ →* slPM :=
  (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ℝ)).codRestrict slPM fun g => Or.inl (by simp)

/-- **Lemma 7.2, Corollary** (Cassels, Ch. 13, §7, p. 310): the points of $\mathcal D$ are identified with the cosets
$SL_2^{\pm}(\mathbb{R})/K^{\pm}$, and also with $SL_2(\mathbb{R})/K^+$ ($K^+ = K^{\pm} \cap SL_2$, the rotations). -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.2, Cor., p. 310"]
theorem disc_equiv_slPM_quotient :
    Nonempty (slPM ⧸ (kPM.subgroupOf slPM) ≃ disc) ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) ℝ ⧸
        (kPM.comap (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ℝ))) ≃ disc) := by
  constructor
  · refine nonempty_quotient_equiv _ (fun S : slPM => ((slPMHom S : discGroup) : Equiv.Perm disc) discZero)
      (orbit_fibre slPMHom _ fun g => (slPMHom_stab g)) fun x => ?_
    obtain ⟨σ, hσ, e⟩ := exists_discGroup_zero x
    obtain ⟨S, hS⟩ := slPMHom_surj ⟨σ, hσ⟩
    exact ⟨S, by show ((slPMHom S : discGroup) : Equiv.Perm disc) discZero = x; rw [hS]; exact e⟩
  · refine nonempty_quotient_equiv _
      (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => ((slPMHom (slToPM g) : discGroup) : Equiv.Perm disc) discZero)
      (orbit_fibre (slPMHom.comp slToPM) _ fun g => (slPMHom_stab (slToPM g))) fun x => ?_
    obtain ⟨S, hS, γ, hγ, hv⟩ := exists_boost x.2
    refine ⟨⟨S, hS⟩, Subtype.ext ?_⟩
    show flt (symMat S) 0 = _
    unfold flt
    rw [hv, projPt_smul hγ.ne', projPt_liftPt]

/-- **The hyperbolic cosine of the distance (7.9)**: for $\vec{\xi}, \vec{\eta} \in \mathcal D$,
$$\cosh d(\vec{\xi}, \vec{\eta}) = \frac{1 - \xi_0\eta_0 - \xi_1\eta_1}{\sqrt{(1 - \xi_0^2 - \xi_1^2)(1 - \eta_0^2 - \eta_1^2)}}.$$ -/
noncomputable def coshDist (ξ η : Fin 2 → ℝ) : ℝ :=
  (1 - ξ 0 * η 0 - ξ 1 * η 1) / √((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2))

/-- **The non-Euclidean distance (7.9)** (Cassels, Ch. 13, §7, p. 311):
$d(\vec{\xi}, \vec{\eta}) = \operatorname{arg\,cosh}\dfrac{1 - \vec{\xi}\cdot\vec{\eta}}{\sqrt{(1 - |\vec{\xi}|^2)(1 - |\vec{\eta}|^2)}}$
(the formula is garbled in the machine-read text; this is the standard distance of the Beltrami–Klein model, which
in polar coordinates gives Cassels' line element (7.11)). -/
@[kb "cassels1978" "Ch. 13, §7, (7.9), p. 311"]
noncomputable def hypDist (ξ η : Fin 2 → ℝ) : ℝ := Real.arcosh (coshDist ξ η)

/-- Helper: `1 - |ξ|² > 0` on the disc. -/
theorem disc_u_pos {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) : 0 < 1 - ξ 0 ^ 2 - ξ 1 ^ 2 := by
  have : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  linarith

/-- Helper: `1 - ξ·η > 0` on the disc. -/
theorem disc_A_pos {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    0 < 1 - ξ 0 * η 0 - ξ 1 * η 1 := by
  have h1 : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  have h2 : η 0 ^ 2 + η 1 ^ 2 < 1 := hη
  nlinarith [sq_nonneg (ξ 0 - η 0), sq_nonneg (ξ 1 - η 1)]

/-- Helper: reverse Cauchy–Schwarz on the disc, quantitative form. -/
theorem disc_key {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    (1 - ξ 0 ^ 2 - ξ 1 ^ 2) * ((ξ 0 - η 0) ^ 2 + (ξ 1 - η 1) ^ 2) ≤
      (1 - ξ 0 * η 0 - ξ 1 * η 1) ^ 2 - (1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2) := by
  nlinarith [sq_nonneg (ξ 0 * (η 0 - ξ 0) + ξ 1 * (η 1 - ξ 1))]

/-- Helper: `coshDist` as a quotient of square roots. -/
theorem coshDist_eq {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    coshDist ξ η = (1 - ξ 0 * η 0 - ξ 1 * η 1) / (√(1 - ξ 0 ^ 2 - ξ 1 ^ 2) * √(1 - η 0 ^ 2 - η 1 ^ 2)) := by
  unfold coshDist; rw [Real.sqrt_mul (disc_u_pos hξ).le]

/-- Helper: symmetry of `coshDist`. -/
theorem coshDist_comm (ξ η : Fin 2 → ℝ) : coshDist ξ η = coshDist η ξ := by
  unfold coshDist
  rw [mul_comm (1 - ξ 0 ^ 2 - ξ 1 ^ 2)]
  congr 1; ring

/-- Helper: `coshDist ≥ 1`. -/
theorem one_le_coshDist {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) : 1 ≤ coshDist ξ η := by
  unfold coshDist
  have hu := disc_u_pos hξ
  have hv := disc_u_pos hη
  have hA := disc_A_pos hξ hη
  have hk := disc_key (η := η) hξ
  have hs : 0 < √((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2)) := Real.sqrt_pos.mpr (mul_pos hu hv)
  rw [le_div_iff₀ hs, one_mul]
  apply Real.sqrt_le_iff.mpr ⟨hA.le, ?_⟩
  nlinarith [mul_nonneg hu.le (add_nonneg (sq_nonneg (ξ 0 - η 0)) (sq_nonneg (ξ 1 - η 1)))]

/-- Helper: `coshDist = 1` iff the points agree. -/
theorem coshDist_eq_one_iff {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    coshDist ξ η = 1 ↔ ξ = η := by
  constructor
  · intro h
    have hu := disc_u_pos hξ
    have hv := disc_u_pos hη
    have hA := disc_A_pos hξ hη
    have hk := disc_key (η := η) hξ
    have hs : 0 < √((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2)) := Real.sqrt_pos.mpr (mul_pos hu hv)
    unfold coshDist at h
    rw [div_eq_one_iff_eq hs.ne'] at h
    have h2 : (1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2) = (1 - ξ 0 * η 0 - ξ 1 * η 1) ^ 2 := by
      rw [h, Real.sq_sqrt (mul_pos hu hv).le]
    have h3 : (ξ 0 - η 0) ^ 2 + (ξ 1 - η 1) ^ 2 ≤ 0 := by
      by_contra hc
      replace hc := not_le.mp hc
      nlinarith [mul_pos hu hc]
    have h4 : ξ 0 = η 0 := by nlinarith [sq_nonneg (ξ 0 - η 0), sq_nonneg (ξ 1 - η 1)]
    have h5 : ξ 1 = η 1 := by nlinarith [sq_nonneg (ξ 0 - η 0), sq_nonneg (ξ 1 - η 1)]
    ext i; fin_cases i <;> simpa
  · rintro rfl
    unfold coshDist
    have hu := disc_u_pos hξ
    rw [Real.sqrt_mul_self hu.le]
    have : (1 - ξ 0 * ξ 0 - ξ 1 * ξ 1) = 1 - ξ 0 ^ 2 - ξ 1 ^ 2 := by ring
    rw [this]; exact div_self hu.ne'

/-- Helper: triangle inequality for `arcosh` from the Gram determinant condition. -/
theorem arcosh_triangle {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hG : 0 ≤ 1 + 2 * p * q * r - p ^ 2 - q ^ 2 - r ^ 2) :
    Real.arcosh r ≤ Real.arcosh p + Real.arcosh q := by
  have ha := Real.cosh_arcosh hp
  have hb := Real.cosh_arcosh hq
  have ha0 := Real.arcosh_nonneg hp
  have hb0 := Real.arcosh_nonneg hq
  have hcosh : Real.cosh (Real.arcosh p + Real.arcosh q) = p * q + √(p ^ 2 - 1) * √(q ^ 2 - 1) := by
    rw [Real.cosh_add, ha, hb, Real.sinh_arcosh hp, Real.sinh_arcosh hq]
  have hS : (√(p ^ 2 - 1) * √(q ^ 2 - 1)) ^ 2 = (p ^ 2 - 1) * (q ^ 2 - 1) := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
  have hS0 : 0 ≤ √(p ^ 2 - 1) * √(q ^ 2 - 1) := by positivity
  have hrle : r ≤ Real.cosh (Real.arcosh p + Real.arcosh q) := by
    rw [hcosh]
    by_contra hc
    replace hc := not_le.mp hc
    nlinarith
  have := (Real.arcosh_le_arcosh (by linarith) (Real.cosh_pos _)).mpr hrle
  rwa [Real.arcosh_cosh (by linarith)] at this

/-- Helper: equality case of the `arcosh` triangle inequality. -/
theorem arcosh_add_eq_iff {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    Real.arcosh r = Real.arcosh p + Real.arcosh q ↔
      (p * q ≤ r ∧ 1 + 2 * p * q * r - p ^ 2 - q ^ 2 - r ^ 2 = 0) := by
  have ha := Real.cosh_arcosh hp
  have hb := Real.cosh_arcosh hq
  have ha0 := Real.arcosh_nonneg hp
  have hb0 := Real.arcosh_nonneg hq
  have hcosh : Real.cosh (Real.arcosh p + Real.arcosh q) = p * q + √(p ^ 2 - 1) * √(q ^ 2 - 1) := by
    rw [Real.cosh_add, ha, hb, Real.sinh_arcosh hp, Real.sinh_arcosh hq]
  have hS : (√(p ^ 2 - 1) * √(q ^ 2 - 1)) ^ 2 = (p ^ 2 - 1) * (q ^ 2 - 1) := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
  have hS0 : 0 ≤ √(p ^ 2 - 1) * √(q ^ 2 - 1) := by positivity
  constructor
  · intro h
    have hr' : r = p * q + √(p ^ 2 - 1) * √(q ^ 2 - 1) := by
      rw [← hcosh, ← h, Real.cosh_arcosh hr]
    refine ⟨by linarith, ?_⟩
    have : (r - p * q) ^ 2 = (p ^ 2 - 1) * (q ^ 2 - 1) := by rw [← hS, hr']; ring
    nlinarith
  · rintro ⟨h1, h2⟩
    have h3 : (r - p * q) ^ 2 = (√(p ^ 2 - 1) * √(q ^ 2 - 1)) ^ 2 := by rw [hS]; nlinarith
    have h4 : r - p * q = √(p ^ 2 - 1) * √(q ^ 2 - 1) := (sq_eq_sq₀ (by linarith) hS0).mp h3
    have : r = Real.cosh (Real.arcosh p + Real.arcosh q) := by rw [hcosh]; linarith
    rw [this, Real.arcosh_cosh (by linarith)]

/-- Helper: abstract form of the Gram identity. -/
theorem gram_abs {a b c A1 A2 A3 D : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 * b ^ 2 * c ^ 2 + 2 * A1 * A2 * A3 - c ^ 2 * A1 ^ 2 - a ^ 2 * A2 ^ 2 - b ^ 2 * A3 ^ 2 = D ^ 2) :
    1 + 2 * (A1 / (a * b)) * (A2 / (b * c)) * (A3 / (a * c)) - (A1 / (a * b)) ^ 2 - (A2 / (b * c)) ^ 2
      - (A3 / (a * c)) ^ 2 = D ^ 2 / (a ^ 2 * b ^ 2 * c ^ 2) := by
  field_simp
  linarith

/-- Helper: the Gram determinant identity for three points of the disc (`x`, `m`, `z`). -/
theorem cosh_gram {x m z : Fin 2 → ℝ} (hx : x ∈ disc) (hm : m ∈ disc) (hz : z ∈ disc) :
    1 + 2 * coshDist x m * coshDist m z * coshDist x z - coshDist x m ^ 2 - coshDist m z ^ 2
      - coshDist x z ^ 2 =
    ((m 0 - x 0) * (z 1 - x 1) - (m 1 - x 1) * (z 0 - x 0)) ^ 2 /
      ((1 - x 0 ^ 2 - x 1 ^ 2) * (1 - m 0 ^ 2 - m 1 ^ 2) * (1 - z 0 ^ 2 - z 1 ^ 2)) := by
  rw [coshDist_eq hx hm, coshDist_eq hm hz, coshDist_eq hx hz]
  have hu := disc_u_pos hx
  have hv := disc_u_pos hm
  have hw := disc_u_pos hz
  have e1 := Real.sq_sqrt hu.le
  have e2 := Real.sq_sqrt hv.le
  have e3 := Real.sq_sqrt hw.le
  have := gram_abs (Real.sqrt_pos.mpr hu) (Real.sqrt_pos.mpr hv) (Real.sqrt_pos.mpr hw)
    (A1 := 1 - x 0 * m 0 - x 1 * m 1) (A2 := 1 - m 0 * z 0 - m 1 * z 1) (A3 := 1 - x 0 * z 0 - x 1 * z 1)
    (D := (m 0 - x 0) * (z 1 - x 1) - (m 1 - x 1) * (z 0 - x 0)) (by rw [e1, e2, e3]; ring)
  rw [this, e1, e2, e3]

/-- Helper: the triangle inequality for `hypDist`. -/
theorem hypDist_triangle {x m z : Fin 2 → ℝ} (hx : x ∈ disc) (hm : m ∈ disc) (hz : z ∈ disc) :
    hypDist x z ≤ hypDist x m + hypDist m z := by
  have hG := cosh_gram hx hm hz
  have hnn : 0 ≤ 1 + 2 * coshDist x m * coshDist m z * coshDist x z - coshDist x m ^ 2 - coshDist m z ^ 2
      - coshDist x z ^ 2 := by
    rw [hG]; exact div_nonneg (sq_nonneg _) (mul_pos (mul_pos (disc_u_pos hx) (disc_u_pos hm)) (disc_u_pos hz)).le
  exact arcosh_triangle (one_le_coshDist hx hm) (one_le_coshDist hm hz) (one_le_coshDist hx hz) hnn

/-- Helper: `hypDist` is symmetric. -/
theorem hypDist_comm (ξ η : Fin 2 → ℝ) : hypDist ξ η = hypDist η ξ := by
  unfold hypDist; rw [coshDist_comm]

/-- Helper: `hypDist` is non-negative. -/
theorem hypDist_nonneg' {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) : 0 ≤ hypDist ξ η :=
  Real.arcosh_nonneg (one_le_coshDist hξ hη)

/-- Helper: `hypDist` vanishes exactly on the diagonal. -/
theorem hypDist_eq_zero_iff {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    hypDist ξ η = 0 ↔ ξ = η := by
  unfold hypDist
  rw [Real.arcosh_eq_zero_iff (one_le_coshDist hξ hη), coshDist_eq_one_iff hξ hη]

/-- Helper: segment membership from coordinates. -/
theorem mem_segment_of_coord {x y z : Fin 2 → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h0 : z 0 = a * x 0 + b * y 0) (h1 : z 1 = a * x 1 + b * y 1) : z ∈ segment ℝ x y := by
  refine ⟨a, b, ha, hb, hab, ?_⟩
  ext i; fin_cases i
  · simpa using h0.symm
  · simpa using h1.symm

/-- Helper: additivity of `hypDist` along a segment. -/
theorem hypDist_add_of_segment {ξ η ζ : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) (hζ : ζ ∈ disc)
    (hseg : ζ ∈ segment ℝ ξ η) : hypDist ξ ζ + hypDist ζ η = hypDist ξ η := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  obtain rfl : a = 1 - b := by linarith
  symm
  refine (arcosh_add_eq_iff (one_le_coshDist hξ hζ) (one_le_coshDist hζ hη) (one_le_coshDist hξ hη)).mpr ⟨?_, ?_⟩
  · have hu := disc_u_pos hξ
    have hv := disc_u_pos hζ
    have hw := disc_u_pos hη
    rw [coshDist_eq hξ hζ, coshDist_eq hζ hη, coshDist_eq hξ hη]
    set sx := √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) with hsx
    set sm := √(1 - ((1 - b) • ξ + b • η) 0 ^ 2 - ((1 - b) • ξ + b • η) 1 ^ 2) with hsm
    set sz := √(1 - η 0 ^ 2 - η 1 ^ 2) with hsz
    have px : 0 < sx := Real.sqrt_pos.mpr hu
    have pm : 0 < sm := Real.sqrt_pos.mpr hv
    have pz : 0 < sz := Real.sqrt_pos.mpr hw
    have em : sm * sm = 1 - ((1 - b) • ξ + b • η) 0 ^ 2 - ((1 - b) • ξ + b • η) 1 ^ 2 :=
      Real.mul_self_sqrt hv.le
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk := disc_key (η := η) hξ
    have hnum : 0 ≤ (1 - ξ 0 * η 0 - ξ 1 * η 1) * (1 - ((1 - b) • ξ + b • η) 0 ^ 2 - ((1 - b) • ξ + b • η) 1 ^ 2)
        - (1 - ξ 0 * ((1 - b) • ξ + b • η) 0 - ξ 1 * ((1 - b) • ξ + b • η) 1) *
          (1 - ((1 - b) • ξ + b • η) 0 * η 0 - ((1 - b) • ξ + b • η) 1 * η 1) := by
      have : (1 - ξ 0 * η 0 - ξ 1 * η 1) * (1 - ((1 - b) • ξ + b • η) 0 ^ 2 - ((1 - b) • ξ + b • η) 1 ^ 2)
        - (1 - ξ 0 * ((1 - b) • ξ + b • η) 0 - ξ 1 * ((1 - b) • ξ + b • η) 1) *
          (1 - ((1 - b) • ξ + b • η) 0 * η 0 - ((1 - b) • ξ + b • η) 1 * η 1)
          = b * (1 - b) * ((1 - ξ 0 * η 0 - ξ 1 * η 1) ^ 2 - (1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2)) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      have h0 : 0 ≤ (1 - ξ 0 ^ 2 - ξ 1 ^ 2) * ((ξ 0 - η 0) ^ 2 + (ξ 1 - η 1) ^ 2) :=
        mul_nonneg hu.le (by positivity)
      exact mul_nonneg (mul_nonneg hb (by linarith)) (by linarith)
    have hfin : 0 ≤ ((1 - ξ 0 * η 0 - ξ 1 * η 1) * (sm * sm)
        - (1 - ξ 0 * ((1 - b) • ξ + b • η) 0 - ξ 1 * ((1 - b) • ξ + b • η) 1) *
          (1 - ((1 - b) • ξ + b • η) 0 * η 0 - ((1 - b) • ξ + b • η) 1 * η 1)) * (sx * sz) := by
      rw [em]; exact mul_nonneg hnum (by positivity)
    nlinarith [hfin]
  · rw [cosh_gram hξ hζ hη]
    have : ((((1 - b) • ξ + b • η) 0 - ξ 0) * (η 1 - ξ 1) - (((1 - b) • ξ + b • η) 1 - ξ 1) * (η 0 - ξ 0)) = 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; simp

/-- Helper: `hypDist` additivity forces the three points to be collinear. -/
theorem collinear_of_hypDist_add {ξ η ζ : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) (hζ : ζ ∈ disc)
    (h : hypDist ξ ζ + hypDist ζ η = hypDist ξ η) :
    (ζ 0 - ξ 0) * (η 1 - ξ 1) - (ζ 1 - ξ 1) * (η 0 - ξ 0) = 0 := by
  have h1 := (arcosh_add_eq_iff (one_le_coshDist hξ hζ) (one_le_coshDist hζ hη)
    (one_le_coshDist hξ hη)).mp h.symm
  have h2 := h1.2
  rw [cosh_gram hξ hζ hη] at h2
  have hpos := mul_pos (mul_pos (disc_u_pos hξ) (disc_u_pos hζ)) (disc_u_pos hη)
  rw [div_eq_zero_iff] at h2
  rcases h2 with h2 | h2
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
  · exact absurd h2 hpos.ne'

/-- Helper: Corollary 1 (proof). -/
theorem hypDist_add_eq_iff' {ξ η ζ : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) (hζ : ζ ∈ disc) :
    hypDist ξ ζ + hypDist ζ η = hypDist ξ η ↔ ζ ∈ segment ℝ ξ η := by
  refine ⟨fun h => ?_, hypDist_add_of_segment hξ hη hζ⟩
  have hD := collinear_of_hypDist_add hξ hη hζ h
  by_cases hxe : ξ = η
  · subst hxe
    have h0 : hypDist ξ ξ = 0 := (hypDist_eq_zero_iff hξ hξ).mpr rfl
    have h1 := hypDist_nonneg' hξ hζ
    have h2 := hypDist_nonneg' hζ hξ
    have : hypDist ξ ζ = 0 := by linarith
    rw [← (hypDist_eq_zero_iff hξ hζ).mp this]
    exact left_mem_segment _ _ _
  · have hδ : 0 < (η 0 - ξ 0) ^ 2 + (η 1 - ξ 1) ^ 2 := by
      by_contra hc
      apply hxe
      have h0 : η 0 - ξ 0 = 0 := by nlinarith [sq_nonneg (η 0 - ξ 0), sq_nonneg (η 1 - ξ 1)]
      have h1 : η 1 - ξ 1 = 0 := by nlinarith [sq_nonneg (η 0 - ξ 0), sq_nonneg (η 1 - ξ 1)]
      ext i; fin_cases i
      · simp; linarith
      · simp; linarith
    set δ := (η 0 - ξ 0) ^ 2 + (η 1 - ξ 1) ^ 2 with hδdef
    set s := ((ζ 0 - ξ 0) * (η 0 - ξ 0) + (ζ 1 - ξ 1) * (η 1 - ξ 1)) / δ with hs
    have hz0 : ζ 0 = ξ 0 + s * (η 0 - ξ 0) := by
      rw [hs]; field_simp
      linear_combination (η 1 - ξ 1) * hD
    have hz1 : ζ 1 = ξ 1 + s * (η 1 - ξ 1) := by
      rw [hs]; field_simp
      linear_combination (-(η 0 - ξ 0)) * hD
    by_cases hs0 : s < 0
    · -- ξ between ζ and η
      have h1s : 1 - s ≠ 0 := ne_of_gt (by linarith)
      have hseg : ξ ∈ segment ℝ ζ η := by
        refine mem_segment_of_coord (a := 1 / (1 - s)) (b := -s / (1 - s)) (by apply div_nonneg <;> linarith)
          (by apply div_nonneg <;> linarith) (by field_simp; ring) ?_ ?_
        · rw [hz0]; field_simp; ring
        · rw [hz1]; field_simp; ring
      have h2 := hypDist_add_of_segment hζ hη hξ hseg
      rw [hypDist_comm ζ ξ] at h2
      have h3 := hypDist_nonneg' hξ hζ
      have h4 : hypDist ξ ζ = 0 := by
        rw [hypDist_comm ζ η, hypDist_comm ξ η] at *
        linarith
      rw [← (hypDist_eq_zero_iff hξ hζ).mp h4]
      exact left_mem_segment _ _ _
    · by_cases hs1 : 1 < s
      · have hsne : s ≠ 0 := ne_of_gt (by linarith)
        have hseg : η ∈ segment ℝ ξ ζ := by
          refine mem_segment_of_coord (a := 1 - 1 / s) (b := 1 / s)
            (by rw [sub_nonneg, div_le_one (by linarith)]; linarith) (by positivity) (by ring) ?_ ?_
          · rw [hz0]; field_simp; ring
          · rw [hz1]; field_simp; ring
        have h2 := hypDist_add_of_segment hξ hζ hη hseg
        have h3 := hypDist_nonneg' hζ hη
        have h4 : hypDist ζ η = 0 := by
          rw [hypDist_comm η ζ] at h2
          linarith
        rw [(hypDist_eq_zero_iff hζ hη).mp h4]
        exact right_mem_segment _ _ _
      · refine mem_segment_of_coord (a := 1 - s) (b := s) (by linarith) (by linarith) (by ring) ?_ ?_
        · rw [hz0]; ring
        · rw [hz1]; ring

/-- Helper: comparing `coshDist` from a common point is a linear condition. -/
theorem coshDist_le_iff {ζ ξ η : Fin 2 → ℝ} (hζ : ζ ∈ disc) (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    coshDist ζ ξ ≤ coshDist ζ η ↔
      (√(1 - ξ 0 ^ 2 - ξ 1 ^ 2) * η 0 - √(1 - η 0 ^ 2 - η 1 ^ 2) * ξ 0) * ζ 0 +
        (√(1 - ξ 0 ^ 2 - ξ 1 ^ 2) * η 1 - √(1 - η 0 ^ 2 - η 1 ^ 2) * ξ 1) * ζ 1 ≤
      √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) - √(1 - η 0 ^ 2 - η 1 ^ 2) := by
  have pz : 0 < √(1 - ζ 0 ^ 2 - ζ 1 ^ 2) := Real.sqrt_pos.mpr (disc_u_pos hζ)
  have px : 0 < √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) := Real.sqrt_pos.mpr (disc_u_pos hξ)
  have py : 0 < √(1 - η 0 ^ 2 - η 1 ^ 2) := Real.sqrt_pos.mpr (disc_u_pos hη)
  rw [coshDist_eq hζ hξ, coshDist_eq hζ hη, div_le_div_iff₀ (by positivity) (by positivity)]
  set sz := √(1 - ζ 0 ^ 2 - ζ 1 ^ 2)
  set sx := √(1 - ξ 0 ^ 2 - ξ 1 ^ 2)
  set sy := √(1 - η 0 ^ 2 - η 1 ^ 2)
  have e1 : (1 - ζ 0 * ξ 0 - ζ 1 * ξ 1) * (sz * sy) = sz * ((1 - ζ 0 * ξ 0 - ζ 1 * ξ 1) * sy) := by ring
  have e2 : (1 - ζ 0 * η 0 - ζ 1 * η 1) * (sz * sx) = sz * ((1 - ζ 0 * η 0 - ζ 1 * η 1) * sx) := by ring
  rw [e1, e2]
  constructor
  · intro h
    have := le_of_mul_le_mul_left h pz
    nlinarith
  · intro h
    apply mul_le_mul_of_nonneg_left _ pz.le
    nlinarith

/-- Helper: `hypDist` comparison from a common point is equivalent to the `coshDist` comparison. -/
theorem hypDist_le_iff {ζ ξ η : Fin 2 → ℝ} (hζ : ζ ∈ disc) (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    hypDist ζ ξ ≤ hypDist ζ η ↔ coshDist ζ ξ ≤ coshDist ζ η :=
  Real.arcosh_le_arcosh (by linarith [one_le_coshDist hζ hξ]) (by linarith [one_le_coshDist hζ hη])

/-- Helper: equidistance from a common point is equivalent to equality of `coshDist`. -/
theorem hypDist_eq_iff_cosh {ζ ξ η : Fin 2 → ℝ} (hζ : ζ ∈ disc) (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    hypDist ζ ξ = hypDist ζ η ↔ (coshDist ζ ξ ≤ coshDist ζ η ∧ coshDist ζ η ≤ coshDist ζ ξ) := by
  rw [le_antisymm_iff, hypDist_le_iff hζ hξ hη, hypDist_le_iff hζ hη hξ]

/-- Helper: Corollary 2 (proof). -/
theorem exists_bisector' {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) (hne : ξ ≠ η) :
    ∃ (a : Fin 2 → ℝ) (c : ℝ), a ≠ 0 ∧
      (∀ ζ ∈ disc, hypDist ζ ξ = hypDist ζ η ↔ a ⬝ᵥ ζ = c) ∧
      (∀ ζ ∈ disc, hypDist ζ ξ ≤ hypDist ζ η ↔ a ⬝ᵥ ζ ≤ c) := by
  have px : 0 < √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) := Real.sqrt_pos.mpr (disc_u_pos hξ)
  have py : 0 < √(1 - η 0 ^ 2 - η 1 ^ 2) := Real.sqrt_pos.mpr (disc_u_pos hη)
  have ex := Real.sq_sqrt (disc_u_pos hξ).le
  have ey := Real.sq_sqrt (disc_u_pos hη).le
  set sx := √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) with hsx
  set sy := √(1 - η 0 ^ 2 - η 1 ^ 2) with hsy
  refine ⟨![sx * η 0 - sy * ξ 0, sx * η 1 - sy * ξ 1], sx - sy, ?_, ?_, ?_⟩
  · intro h0
    have h00 : sx * η 0 - sy * ξ 0 = 0 := by simpa using congrFun h0 0
    have h01 : sx * η 1 - sy * ξ 1 = 0 := by simpa using congrFun h0 1
    have h1 : (sx * η 0) ^ 2 + (sx * η 1) ^ 2 = (sy * ξ 0) ^ 2 + (sy * ξ 1) ^ 2 := by
      have a1 : sx * η 0 = sy * ξ 0 := by linarith
      have a2 : sx * η 1 = sy * ξ 1 := by linarith
      rw [a1, a2]
    have h2 : η 0 ^ 2 + η 1 ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 := by
      have : sx ^ 2 * (η 0 ^ 2 + η 1 ^ 2) = sy ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by nlinarith
      rw [ex, ey] at this
      nlinarith
    have h3 : sx = sy := by
      have : sx ^ 2 = sy ^ 2 := by rw [ex, ey]; linarith
      nlinarith
    apply hne
    rw [← h3] at h00 h01
    ext i; fin_cases i
    · simp; nlinarith
    · simp; nlinarith
  · intro ζ hζ
    rw [hypDist_eq_iff_cosh hζ hξ hη]
    rw [coshDist_le_iff hζ hξ hη, coshDist_le_iff hζ hη hξ]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · intro h; constructor <;> nlinarith
  · intro ζ hζ
    rw [hypDist_le_iff hζ hξ hη, coshDist_le_iff hζ hξ hη]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Iff.rfl

/-- Helper: Corollary 3 (proof). -/
theorem hypDist_eq_iff_bisector' {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {ζ : Fin 2 → ℝ} (hζ : ζ ∈ disc) :
    hypDist ζ 0 = hypDist ζ ![r, 0] ↔ ζ 0 = (1 - √(1 - r ^ 2)) / r := by
  have h0 : (0 : Fin 2 → ℝ) ∈ disc := by simp [disc]
  have hr : (![r, 0] : Fin 2 → ℝ) ∈ disc := by
    show (![r, 0] 0) ^ 2 + (![r, 0] 1) ^ 2 < 1
    have e0 : (![r, 0] : Fin 2 → ℝ) 0 = r := rfl
    have e1 : (![r, 0] : Fin 2 → ℝ) 1 = 0 := rfl
    rw [e0, e1]; nlinarith
  rw [hypDist_eq_iff_cosh hζ h0 hr]
  rw [coshDist_le_iff hζ h0 hr, coshDist_le_iff hζ hr h0]
  simp
  rw [eq_div_iff hr0.ne']
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> nlinarith

/-- Helper: `coshDist` is invariant under the fractional-linear map of a Lorentz matrix. -/
theorem coshDist_flt {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz) {ξ η : Fin 2 → ℝ}
    (hξ : ξ ∈ disc) (hη : η ∈ disc) : coshDist (flt T ξ) (flt T η) = coshDist ξ η := by
  have hu := disc_u_pos hξ
  have hv := disc_u_pos hη
  have hA := disc_A_pos hξ hη
  obtain ⟨ha, hξ'⟩ := lorentz_maps_disc hT hξ
  obtain ⟨hb, hη'⟩ := lorentz_maps_disc hT hη
  have hA' := disc_A_pos hξ' hη'
  have e1 := lorB_mulVec hT (liftPt ξ) (liftPt η)
  have e2 := lorB_mulVec hT (liftPt ξ) (liftPt ξ)
  have e3 := lorB_mulVec hT (liftPt η) (liftPt η)
  rw [lorB_lift] at e1 e2 e3
  set x := T *ᵥ liftPt ξ with hx
  set y := T *ᵥ liftPt η with hy
  unfold lorB at e1 e2 e3
  have f0 : (flt T ξ) 0 = x 0 / x 2 := rfl
  have f1 : (flt T ξ) 1 = x 1 / x 2 := rfl
  have g0 : (flt T η) 0 = y 0 / y 2 := rfl
  have g1 : (flt T η) 1 = y 1 / y 2 := rfl
  unfold coshDist
  rw [f0, f1, g0, g1]
  have hA2 : 1 - x 0 / x 2 * (y 0 / y 2) - x 1 / x 2 * (y 1 / y 2) = (1 - ξ 0 * η 0 - ξ 1 * η 1) / (x 2 * y 2) := by
    field_simp; linarith
  have hu2 : 1 - (x 0 / x 2) ^ 2 - (x 1 / x 2) ^ 2 = (1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (x 2) ^ 2 := by
    field_simp; linarith
  have hv2 : 1 - (y 0 / y 2) ^ 2 - (y 1 / y 2) ^ 2 = (1 - η 0 ^ 2 - η 1 ^ 2) / (y 2) ^ 2 := by
    field_simp; linarith
  have hpos : 0 < x 2 * y 2 := by
    have : 0 < (1 - ξ 0 * η 0 - ξ 1 * η 1) / (x 2 * y 2) := by
      rw [← hA2]
      rw [f0, f1, g0, g1] at hA'; exact hA'
    exact (div_pos_iff_of_pos_left hA).mp this
  rw [hA2, hu2, hv2]
  have hsq : (1 - ξ 0 ^ 2 - ξ 1 ^ 2) / x 2 ^ 2 * ((1 - η 0 ^ 2 - η 1 ^ 2) / y 2 ^ 2) =
      ((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2)) / (x 2 * y 2) ^ 2 := by
    field_simp
  rw [hsq, Real.sqrt_div (mul_pos hu hv).le, Real.sqrt_sq hpos.le]
  have hs : 0 < √((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2)) := Real.sqrt_pos.mpr (mul_pos hu hv)
  field_simp

/-- **Lemma 7.3** (Cassels, Ch. 13, §7, p. 311): (7.9) is a metric on $\mathcal D$ invariant under $\mathcal M$. *Update*:
Cassels adds that it "is uniquely defined up to a scalar multiple"; his proof is
about Riemannian metrics (the line element (7.11)). For metrics in general it is false ($\min(d, 1)$ is another
invariant metric), so only existence and invariance are stated. -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.3, (7.9), p. 311"]
theorem hypDist_metric :
    (∀ ξ ∈ disc, ∀ η ∈ disc, 0 ≤ hypDist ξ η ∧ (hypDist ξ η = 0 ↔ ξ = η) ∧ hypDist ξ η = hypDist η ξ) ∧
    (∀ ξ ∈ disc, ∀ η ∈ disc, ∀ ζ ∈ disc, hypDist ξ ζ ≤ hypDist ξ η + hypDist η ζ) ∧
    ∀ σ ∈ discGroup, ∀ ξ η : disc, hypDist (σ ξ) (σ η) = hypDist ξ η := by
  refine ⟨fun ξ hξ η hη => ⟨hypDist_nonneg' hξ hη, hypDist_eq_zero_iff hξ hη, hypDist_comm ξ η⟩,
    fun ξ hξ η hη ζ hζ => hypDist_triangle hξ hη hζ, fun σ hσ ξ η => ?_⟩
  obtain ⟨T, hT, hσT⟩ := exists_lorentz_of_discGroup hσ
  unfold hypDist
  rw [hσT ξ, hσT η, coshDist_flt hT ξ.2 η.2]

/-- **Lemma 7.3, Corollary 1** (Cassels, Ch. 13, §7, p. 311): the geodesics are line segments: for
$\vec{\xi}, \vec{\eta}, \vec{\zeta} \in \mathcal D$, $d(\vec{\xi}, \vec{\zeta}) + d(\vec{\zeta}, \vec{\eta}) = d(\vec{\xi}, \vec{\eta})$
iff $\vec{\zeta}$ lies on the segment $[\vec{\xi}, \vec{\eta}]$. -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.3, Cor. 1, p. 311"]
theorem hypDist_add_eq_iff {ξ η ζ : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) (hζ : ζ ∈ disc) :
    hypDist ξ ζ + hypDist ζ η = hypDist ξ η ↔ ζ ∈ segment ℝ ξ η :=
  hypDist_add_eq_iff' hξ hη hζ

/-- **Lemma 7.3, Corollary 2** (Cassels, Ch. 13, §7, p. 311): the set of points of $\mathcal D$ equidistant from two
distinct points $\vec{\xi}, \vec{\eta}$ is the set of points of $\mathcal D$ on a certain line (the "perpendicular
bisector"), and the points nearer to $\vec{\xi}$ form the intersection of $\mathcal D$ with a closed half-plane (used in
§8, p. 315). -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.3, Cor. 2, pp. 311–312; §8, p. 315 (half-planes)"]
theorem exists_bisector {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) (hne : ξ ≠ η) :
    ∃ (a : Fin 2 → ℝ) (c : ℝ), a ≠ 0 ∧
      (∀ ζ ∈ disc, hypDist ζ ξ = hypDist ζ η ↔ a ⬝ᵥ ζ = c) ∧
      (∀ ζ ∈ disc, hypDist ζ ξ ≤ hypDist ζ η ↔ a ⬝ᵥ ζ ≤ c) :=
  exists_bisector' hξ hη hne

/-- **Lemma 7.3, Corollary 3** (Cassels, Ch. 13, §7, p. 312): the perpendicular bisector of $0$ and $(r, 0)$,
$0 < r < 1$, is the segment of points $(s, t) \in \mathcal D$ with
$$s = \frac{1 - \sqrt{1 - r^2}}{r}. \tag{7.12}$$
(The formula (7.12) is lost in the machine-read text; reconstructed by solving $d((s, 0), 0) = d((s, 0), (r, 0))$.) -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.3, Cor. 3, (7.12), p. 312"]
theorem hypDist_eq_iff_bisector {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {ζ : Fin 2 → ℝ} (hζ : ζ ∈ disc) :
    hypDist ζ 0 = hypDist ζ ![r, 0] ↔ ζ 0 = (1 - √(1 - r ^ 2)) / r :=
  hypDist_eq_iff_bisector' hr0 hr1 hζ

/-- **The cone over a subset of the disc** (Cassels, Ch. 13, Lemma 7.4, p. 312): the points $X \in \mathbb{R}^3$ with
$X_2 \ne 0$, $\pi(X) \in \mathcal Y$ and $0 < X_2^2 - X_0^2 - X_1^2 \le 1$ (the conditions are partly garbled in the
machine-read text; reconstructed so that $\pi^{-1}(\mathcal Y)$ has finite volume and is mapped by $T \in O(f_0)$ to
$\pi^{-1}(T\mathcal Y)$). -/
def discCone (Y : Set (Fin 2 → ℝ)) : Set (Fin 3 → ℝ) :=
  {X | X 2 ≠ 0 ∧ projPt X ∈ Y ∧ 0 < X 2 ^ 2 - X 0 ^ 2 - X 1 ^ 2 ∧ X 2 ^ 2 - X 0 ^ 2 - X 1 ^ 2 ≤ 1}

/-- Helper: a Lorentz matrix maps the cone over `Y` into the cone over `flt T '' Y`. -/
theorem discCone_mapsTo {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz)
    (Y : Set (Fin 2 → ℝ)) {X : Fin 3 → ℝ} (hX : X ∈ discCone Y) : T *ᵥ X ∈ discCone (flt T '' Y) := by
  obtain ⟨h2, hY, h3, h4⟩ := hX
  have hl := lorB_mulVec hT X X
  simp only [lorB] at hl
  have hlt : (T *ᵥ X) 0 ^ 2 + (T *ᵥ X) 1 ^ 2 < (T *ᵥ X) 2 ^ 2 := by nlinarith
  obtain ⟨h2', -⟩ := projPt_mem_disc hlt
  refine ⟨h2', ⟨projPt X, hY, ?_⟩, by nlinarith, by nlinarith⟩
  unfold flt
  rw [liftPt_projPt h2, Matrix.mulVec_smul, projPt_smul (inv_ne_zero h2)]

/-- Helper: the determinant of a Lorentz matrix has absolute value one. -/
theorem abs_det_of_lorentz {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : Tᵀ * lorentz * T = lorentz) :
    |T.det| = 1 := by
  have h := congrArg Matrix.det hT
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hl : lorentz.det = 1 * 1 * -1 := by
    simp [lorentz, Matrix.det_diagonal, Fin.prod_univ_three]
  rw [hl] at h
  have h2 : T.det ^ 2 = 1 := by nlinarith
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp (by rw [sq_abs]; exact h2)

/-- **Lemma 7.4** (Cassels, Ch. 13, §7, p. 312): $m(\mathcal Y)$, the Lebesgue measure of the cone $\pi^{-1}(\mathcal Y)$
over $\mathcal Y \subseteq \mathcal D$, is an invariant measure under $\mathcal M$: $m(\sigma\mathcal Y) = m(\mathcal Y)$. -/
@[kb "cassels1978" "Ch. 13, §7, Lemma 7.4, p. 312"]
theorem volume_discCone_image {σ : Equiv.Perm disc} (hσ : σ ∈ discGroup) (Y : Set disc) :
    MeasureTheory.volume (discCone (Subtype.val '' (σ '' Y))) =
      MeasureTheory.volume (discCone (Subtype.val '' Y)) := by
  obtain ⟨T, hT, hσT⟩ := exists_lorentz_of_discGroup hσ
  obtain ⟨h1, h2, h3⟩ := lorentz_inv_aux hT
  set T' := lorentz * Tᵀ * lorentz with hT'
  have himg : flt T '' (Subtype.val '' Y) = Subtype.val '' (σ '' Y) := by
    ext x; simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨σ y, ⟨y, hy, rfl⟩, hσT y⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, ⟨y, hy, rfl⟩, (hσT y).symm⟩
  have himg' : flt T' '' (Subtype.val '' (σ '' Y)) ⊆ Subtype.val '' Y := by
    rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [hσT y, flt_flt _ _ _ (lorentz_maps_disc hT y.2).1, h1]
    simp [flt]
  have hset : discCone (Subtype.val '' (σ '' Y)) = Matrix.toLin' T '' discCone (Subtype.val '' Y) := by
    apply Set.Subset.antisymm
    · intro X hX
      refine ⟨T' *ᵥ X, ?_, ?_⟩
      · have := discCone_mapsTo h3 _ hX
        refine (?_ : discCone _ ⊆ _) this
        intro Z hZ
        obtain ⟨a, b, c, d⟩ := hZ
        exact ⟨a, himg' b, c, d⟩
      · simp [Matrix.mulVec_mulVec, h2]
    · rintro _ ⟨X, hX, rfl⟩
      have := discCone_mapsTo hT _ hX
      rw [himg] at this
      exact this
  rw [hset, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin', abs_det_of_lorentz hT]
  simp

end QuadFormsKB.Reduction
