/-
# Cassels, Chapter 13, §8: helper file, Lorentz matrices acting on the disc

Helper lemmas for `Ch13/Sec8.lean`: a real matrix $P$ with $P^{\mathsf T} f_0 P = f_0$ (a *Lorentz matrix*) acts on the
open unit disc by $\vec\xi \mapsto \pi(P(\xi_0, \xi_1, 1))$ (`flt`), preserves $\cosh d$, composes, and the symmetric
boosts act transitively.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec7
import QuadFormsKB.Literature.Cassels.Ch13.Sec2

open Matrix

namespace QuadFormsKB.Reduction

namespace S8

/-- The bilinear form of $f_0 = X_0^2 + X_1^2 - X_2^2$. -/
def bil (X Y : Fin 3 → ℝ) : ℝ := X 0 * Y 0 + X 1 * Y 1 - X 2 * Y 2

/-- A Lorentz matrix: $P^{\mathsf T} f_0 P = f_0$. -/
def IsLor (P : Matrix (Fin 3) (Fin 3) ℝ) : Prop := Pᵀ * lorentz * P = lorentz

theorem bil_eq (X Y : Fin 3 → ℝ) : bil X Y = X ⬝ᵥ (lorentz *ᵥ Y) := by
  simp [bil, lorentz, dotProduct, Fin.sum_univ_three, mulVec]
  ring

theorem IsLor.bil_mulVec {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) (X Y : Fin 3 → ℝ) :
    bil (P *ᵥ X) (P *ᵥ Y) = bil X Y := by
  have h : Pᵀ *ᵥ (lorentz *ᵥ (P *ᵥ Y)) = lorentz *ᵥ Y := by
    rw [mulVec_mulVec, mulVec_mulVec, hP]
  rw [bil_eq, bil_eq, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, h, dotProduct_comm]

theorem lorentz_mul_self' : lorentz * lorentz = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lorentz, Matrix.mul_apply, Fin.sum_univ_three]

theorem lorentz_transpose' : lorentzᵀ = lorentz := by
  unfold lorentz; exact diagonal_transpose _

theorem isLor_lorentz : IsLor lorentz := by
  unfold IsLor; rw [lorentz_transpose', lorentz_mul_self', Matrix.one_mul]

theorem IsLor.mul {P Q : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) (hQ : IsLor Q) : IsLor (P * Q) := by
  unfold IsLor at *
  rw [Matrix.transpose_mul]
  calc Qᵀ * Pᵀ * lorentz * (P * Q) = Qᵀ * (Pᵀ * lorentz * P) * Q := by simp only [Matrix.mul_assoc]
    _ = lorentz := by rw [hP, hQ]

/-- The Lorentz inverse $f_0 P^{\mathsf T} f_0$. -/
def lorInv (P : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := lorentz * Pᵀ * lorentz

theorem IsLor.lorInv_mul {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) : lorInv P * P = 1 := by
  unfold lorInv
  calc lorentz * Pᵀ * lorentz * P = lorentz * (Pᵀ * lorentz * P) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [show Pᵀ * lorentz * P = lorentz from hP, lorentz_mul_self']

theorem IsLor.mul_lorInv {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) : P * lorInv P = 1 :=
  mul_eq_one_comm.1 hP.lorInv_mul

theorem IsLor.isLor_lorInv {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) : IsLor (lorInv P) := by
  have h1 : P * lorentz * Pᵀ = lorentz := by
    have := hP.mul_lorInv
    unfold lorInv at this
    calc P * lorentz * Pᵀ = P * (lorentz * Pᵀ * lorentz) * lorentz := by
          simp only [Matrix.mul_assoc, lorentz_mul_self', Matrix.mul_one]
      _ = lorentz := by rw [this, Matrix.one_mul]
  unfold IsLor lorInv
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, lorentz_transpose']
  have hJ : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, lorentz * (lorentz * M) = M := fun M => by
    rw [← Matrix.mul_assoc, lorentz_mul_self', Matrix.one_mul]
  have h1' : P * (lorentz * Pᵀ) = lorentz := by rw [← Matrix.mul_assoc]; exact h1
  calc lorentz * (P * lorentz) * lorentz * (lorentz * Pᵀ * lorentz)
      = lorentz * (P * (lorentz * Pᵀ)) * lorentz := by simp only [Matrix.mul_assoc, hJ]
    _ = lorentz := by rw [h1', Matrix.mul_assoc, lorentz_mul_self', Matrix.mul_one]

theorem bil_liftPt (ξ η : Fin 2 → ℝ) : bil (liftPt ξ) (liftPt η) = ξ 0 * η 0 + ξ 1 * η 1 - 1 := by
  simp [bil, liftPt]

theorem inner_lt_one {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc) (hη : η ∈ disc) :
    ξ 0 * η 0 + ξ 1 * η 1 < 1 := by
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  have hη' : η 0 ^ 2 + η 1 ^ 2 < 1 := hη
  have h : (ξ 0 * η 0 + ξ 1 * η 1) ^ 2 ≤ (ξ 0 ^ 2 + ξ 1 ^ 2) * (η 0 ^ 2 + η 1 ^ 2) := by
    nlinarith [sq_nonneg (ξ 0 * η 1 - ξ 1 * η 0)]
  have h2 : (ξ 0 ^ 2 + ξ 1 ^ 2) * (η 0 ^ 2 + η 1 ^ 2) < 1 := by
    nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (η 0), sq_nonneg (η 1)]
  by_contra hc
  push_neg at hc
  nlinarith

theorem IsLor.cone {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    (P *ᵥ liftPt ξ) 0 ^ 2 + (P *ᵥ liftPt ξ) 1 ^ 2 < (P *ᵥ liftPt ξ) 2 ^ 2 := by
  have h := hP.bil_mulVec (liftPt ξ) (liftPt ξ)
  rw [bil_liftPt] at h
  unfold bil at h
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  nlinarith

theorem IsLor.last_ne {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    (P *ᵥ liftPt ξ) 2 ≠ 0 := by
  intro h
  have := hP.cone hξ
  rw [h] at this
  nlinarith [sq_nonneg ((P *ᵥ liftPt ξ) 0), sq_nonneg ((P *ᵥ liftPt ξ) 1)]

theorem flt_apply_zero (P : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 2 → ℝ) :
    flt P ξ 0 = (P *ᵥ liftPt ξ) 0 / (P *ᵥ liftPt ξ) 2 := by simp [flt, projPt]

theorem flt_apply_one (P : Matrix (Fin 3) (Fin 3) ℝ) (ξ : Fin 2 → ℝ) :
    flt P ξ 1 = (P *ᵥ liftPt ξ) 1 / (P *ᵥ liftPt ξ) 2 := by simp [flt, projPt]

theorem IsLor.flt_mem_disc {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    flt P ξ ∈ disc := by
  show flt P ξ 0 ^ 2 + flt P ξ 1 ^ 2 < 1
  rw [flt_apply_zero, flt_apply_one, div_pow, div_pow, ← add_div, div_lt_one]
  · exact hP.cone hξ
  · have := hP.last_ne hξ
    positivity

/-- Last coordinates of two images of disc points have the same sign. -/
theorem IsLor.last_mul_pos {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc)
    (hη : η ∈ disc) : 0 < (P *ᵥ liftPt ξ) 2 * (P *ᵥ liftPt η) 2 := by
  have hu := hP.cone hξ
  have hv := hP.cone hη
  have huv := hP.bil_mulVec (liftPt ξ) (liftPt η)
  rw [bil_liftPt] at huv
  unfold bil at huv
  have h1 := inner_lt_one hξ hη
  have hu2 := hP.last_ne hξ
  have hv2 := hP.last_ne hη
  set u := P *ᵥ liftPt ξ
  set v := P *ᵥ liftPt η
  have hCS : (u 0 * v 0 + u 1 * v 1) ^ 2 < (u 2 * v 2) ^ 2 := by
    have h : (u 0 * v 0 + u 1 * v 1) ^ 2 ≤ (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
      nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0)]
    have h' : (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) < (u 2 ^ 2) * (v 2 ^ 2) := by
      have a0 : 0 ≤ u 0 ^ 2 + u 1 ^ 2 := by positivity
      have b0 : 0 ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity
      nlinarith
    nlinarith
  by_contra hc
  push_neg at hc
  have hne : u 2 * v 2 ≠ 0 := mul_ne_zero hu2 hv2
  have hlt : u 2 * v 2 < 0 := lt_of_le_of_ne hc hne
  nlinarith

theorem projPt_smul' {c : ℝ} (hc : c ≠ 0) (X : Fin 3 → ℝ) : projPt (c • X) = projPt X := by
  ext i
  fin_cases i <;> simp [projPt, mul_div_mul_left _ _ hc]

theorem liftPt_flt_of {P : Matrix (Fin 3) (Fin 3) ℝ} {ξ : Fin 2 → ℝ} (h : (P *ᵥ liftPt ξ) 2 ≠ 0) :
    liftPt (flt P ξ) = ((P *ᵥ liftPt ξ) 2)⁻¹ • (P *ᵥ liftPt ξ) := by
  have h' : (P *ᵥ ![ξ 0, ξ 1, 1]) 2 ≠ 0 := h
  ext i
  fin_cases i <;> simp [liftPt, flt_apply_zero, flt_apply_one, h', div_eq_inv_mul]

theorem flt_mul_of {P P' : Matrix (Fin 3) (Fin 3) ℝ} {ξ : Fin 2 → ℝ} (h : (P' *ᵥ liftPt ξ) 2 ≠ 0) :
    flt (P * P') ξ = flt P (flt P' ξ) := by
  show projPt ((P * P') *ᵥ liftPt ξ) = projPt (P *ᵥ liftPt (flt P' ξ))
  rw [liftPt_flt_of h, mulVec_smul, ← mulVec_mulVec, projPt_smul' (inv_ne_zero h)]

theorem flt_one (ξ : Fin 2 → ℝ) : flt 1 ξ = ξ := by
  ext i
  fin_cases i <;> simp [flt, projPt, liftPt]

theorem IsLor.flt_lorInv {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    flt (lorInv P) (flt P ξ) = ξ := by
  rw [← flt_mul_of (hP.last_ne hξ), hP.lorInv_mul, flt_one]

theorem IsLor.flt_mul {P P' : Matrix (Fin 3) (Fin 3) ℝ} (hP' : IsLor P') {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    flt (P * P') ξ = flt P (flt P' ξ) := flt_mul_of (hP'.last_ne hξ)

/-- **$\cosh d$ is invariant under Lorentz matrices.** -/
theorem IsLor.coshDist_flt {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc)
    (hη : η ∈ disc) : coshDist (flt P ξ) (flt P η) = coshDist ξ η := by
  have hu := hP.bil_mulVec (liftPt ξ) (liftPt ξ)
  have hv := hP.bil_mulVec (liftPt η) (liftPt η)
  have huv := hP.bil_mulVec (liftPt ξ) (liftPt η)
  rw [bil_liftPt] at hu hv huv
  unfold bil at hu hv huv
  have hw := hP.last_mul_pos hξ hη
  have hu2 := hP.last_ne hξ
  have hv2 := hP.last_ne hη
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  have hη' : η 0 ^ 2 + η 1 ^ 2 < 1 := hη
  set u := P *ᵥ liftPt ξ
  set v := P *ᵥ liftPt η
  unfold coshDist
  rw [flt_apply_zero, flt_apply_zero, flt_apply_one, flt_apply_one]
  have e1 : 1 - u 0 / u 2 * (v 0 / v 2) - u 1 / u 2 * (v 1 / v 2) = (1 - ξ 0 * η 0 - ξ 1 * η 1) / (u 2 * v 2) := by
    field_simp
    linarith
  have e2 : 1 - (u 0 / u 2) ^ 2 - (u 1 / u 2) ^ 2 = (1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (u 2) ^ 2 := by
    field_simp
    linarith
  have e3 : 1 - (v 0 / v 2) ^ 2 - (v 1 / v 2) ^ 2 = (1 - η 0 ^ 2 - η 1 ^ 2) / (v 2) ^ 2 := by
    field_simp
    linarith
  have e4 : √((1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (u 2) ^ 2 * ((1 - η 0 ^ 2 - η 1 ^ 2) / (v 2) ^ 2)) =
      √((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2)) / (u 2 * v 2) := by
    have : (1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (u 2) ^ 2 * ((1 - η 0 ^ 2 - η 1 ^ 2) / (v 2) ^ 2) =
        (1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2) / (u 2 * v 2) ^ 2 := by
      field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hw.le]
  rw [e1, e2, e3, e4]
  have hpos : 0 < √((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - η 0 ^ 2 - η 1 ^ 2)) := by
    apply Real.sqrt_pos.2
    apply mul_pos <;> linarith
  field_simp

theorem IsLor.hypDist_flt {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) {ξ η : Fin 2 → ℝ} (hξ : ξ ∈ disc)
    (hη : η ∈ disc) : hypDist (flt P ξ) (flt P η) = hypDist ξ η := by
  unfold hypDist; rw [hP.coshDist_flt hξ hη]

/-- The symmetric boost taking $(0,0,1)$ to $(a, b, c)$ (for $c^2 = 1 + a^2 + b^2$). -/
noncomputable def boost (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + a ^ 2 / (c + 1), a * b / (c + 1), a; a * b / (c + 1), 1 + b ^ 2 / (c + 1), b; a, b, c]

theorem isLor_boost {a b c : ℝ} (hc : 0 < c) (h : c ^ 2 = 1 + a ^ 2 + b ^ 2) : IsLor (boost a b c) := by
  have hc1 : c + 1 ≠ 0 := by positivity
  unfold IsLor
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, lorentz, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> field_simp
  · linear_combination (-a ^ 2) * h
  · linear_combination (-a * b) * h
  · linear_combination (-a) * h
  · linear_combination (-a * b) * h
  · linear_combination (-b ^ 2) * h
  · linear_combination (-b) * h
  · linear_combination (-a) * h
  · linear_combination (-b) * h
  · linear_combination (-1) * h

/-- Every point of the disc is the image of the origin under a boost. -/
theorem exists_lorBoost {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ, IsLor B ∧
      B *ᵥ liftPt 0 = (√(1 - ξ 0 ^ 2 - ξ 1 ^ 2))⁻¹ • liftPt ξ := by
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  have hpos : 0 < 1 - ξ 0 ^ 2 - ξ 1 ^ 2 := by linarith
  set r := √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hpos
  have hr2 : r ^ 2 = 1 - ξ 0 ^ 2 - ξ 1 ^ 2 := Real.sq_sqrt hpos.le
  refine ⟨boost (r⁻¹ * ξ 0) (r⁻¹ * ξ 1) r⁻¹, isLor_boost (inv_pos.2 hr0) ?_, ?_⟩
  · field_simp
    linarith
  · ext i
    fin_cases i <;> simp [boost, liftPt, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem flt_zero_boost {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) {B : Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B *ᵥ liftPt 0 = (√(1 - ξ 0 ^ 2 - ξ 1 ^ 2))⁻¹ • liftPt ξ) : flt B 0 = ξ := by
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  have hpos : 0 < 1 - ξ 0 ^ 2 - ξ 1 ^ 2 := by linarith
  have hr0 : 0 < √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) := Real.sqrt_pos.2 hpos
  unfold flt
  rw [hB, projPt_smul' (inv_ne_zero hr0.ne')]
  ext i
  fin_cases i <;> simp [projPt, liftPt]

theorem IsLor.entry_eq {P : Matrix (Fin 3) (Fin 3) ℝ} (hP : IsLor P) (j k : Fin 3) :
    P 0 j * P 0 k + P 1 j * P 1 k - P 2 j * P 2 k = lorentz j k := by
  have := congrFun (congrFun (show Pᵀ * lorentz * P = lorentz from hP) j) k
  simp [Matrix.mul_apply, Fin.sum_univ_three, lorentz, Matrix.transpose_apply, Matrix.diagonal_apply] at this
  have e : lorentz j k = (if j = k then ![1, 1, -1] j else 0) := by simp [lorentz, Matrix.diagonal_apply]
  rw [e]
  linarith

/-- **A Lorentz matrix is bounded by its last column**: if $|W_{i2}| \le C$ for all $i$ then $|W_{ij}| \le C$. -/
theorem IsLor.entry_le {W : Matrix (Fin 3) (Fin 3) ℝ} (hW : IsLor W) {C : ℝ} (hC : ∀ i, |W i 2| ≤ C) :
    ∀ i j, |W i j| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have r22 := hW.entry_eq 2 2
  simp [lorentz] at r22
  have hc : W 2 2 ^ 2 ≤ C ^ 2 := by
    have := sq_le_sq' (abs_le.1 (hC 2)).1 (abs_le.1 (hC 2)).2
    exact this
  have key : ∀ j : Fin 3, j ≠ 2 → W 0 j ^ 2 + W 1 j ^ 2 ≤ W 2 2 ^ 2 ∧ W 2 j ^ 2 ≤ W 2 2 ^ 2 := by
    intro j hj
    have rjj := hW.entry_eq j j
    have rj2 := hW.entry_eq j 2
    have hj' : lorentz j j = 1 := by
      fin_cases j <;> simp [lorentz] at hj ⊢
    have hj2 : lorentz j 2 = 0 := by
      fin_cases j <;> simp [lorentz] at hj ⊢
    rw [hj'] at rjj
    rw [hj2] at rj2
    set p := W 0 j
    set q := W 1 j
    set s := W 2 j
    set a := W 0 2
    set b := W 1 2
    set c := W 2 2
    have h1 : (p * a + q * b) ^ 2 ≤ (p ^ 2 + q ^ 2) * (a ^ 2 + b ^ 2) := by
      nlinarith [sq_nonneg (p * b - q * a)]
    have h2 : s * c = p * a + q * b := by linarith
    have h3 : p ^ 2 + q ^ 2 ≤ c ^ 2 := by
      have : (s * c) ^ 2 ≤ (p ^ 2 + q ^ 2) * (a ^ 2 + b ^ 2) := by rw [h2]; exact h1
      have e1 : s ^ 2 = p ^ 2 + q ^ 2 - 1 := by linarith
      have e2 : a ^ 2 + b ^ 2 = c ^ 2 - 1 := by linarith
      rw [mul_pow, e1, e2] at this
      nlinarith
    refine ⟨h3, ?_⟩
    nlinarith
  intro i j
  by_cases hj : j = 2
  · subst hj; exact hC i
  · obtain ⟨k1, k2⟩ := key j hj
    apply abs_le_of_sq_le_sq _ hC0
    have e0 : W 0 j ^ 2 ≤ C ^ 2 := by nlinarith [sq_nonneg (W 1 j)]
    have e1 : W 1 j ^ 2 ≤ C ^ 2 := by nlinarith [sq_nonneg (W 0 j)]
    have e2 : W 2 j ^ 2 ≤ C ^ 2 := by nlinarith
    fin_cases i
    · exact e0
    · exact e1
    · exact e2

/-! ### Matrix entry bounds and finiteness -/

theorem exists_entry_bound (A : Matrix (Fin 3) (Fin 3) ℝ) : ∃ m : ℝ, 0 ≤ m ∧ ∀ i j, |A i j| ≤ m := by
  refine ⟨∑ i, ∑ j, |A i j|, by positivity, fun i j => ?_⟩
  calc |A i j| ≤ ∑ j, |A i j| :=
        Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, |A i j| :=
        Finset.single_le_sum (f := fun i => ∑ j, |A i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)

theorem entry_mul_le {A B : Matrix (Fin 3) (Fin 3) ℝ} {a b : ℝ} (hA : ∀ i j, |A i j| ≤ a)
    (hB : ∀ i j, |B i j| ≤ b) (i j : Fin 3) : |(A * B) i j| ≤ 3 * a * b := by
  have h : ∀ k, |A i k * B k j| ≤ a * b := fun k => by
    rw [abs_mul]
    exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ((abs_nonneg _).trans (hA i k))
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  calc |A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j|
      ≤ |A i 0 * B 0 j| + |A i 1 * B 1 j| + |A i 2 * B 2 j| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ 3 * a * b := by linarith [h 0, h 1, h 2]

theorem finite_gl_bounded (K : ℝ) : {T : GL (Fin 3) ℤ | ∀ i j, |(T.val i j : ℝ)| ≤ K}.Finite := by
  have hfin : {M : Fin 3 → Fin 3 → ℤ | ∀ i j, M i j ∈ Set.Icc (-⌊K⌋) ⌊K⌋}.Finite := by
    have h3 : (Set.pi Set.univ (fun _ : Fin 3 => Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-⌊K⌋) ⌊K⌋))).Finite :=
      Set.Finite.pi (fun _ => Set.Finite.pi (fun _ => Set.finite_Icc _ _))
    exact h3.subset (fun M hM i _ j _ => hM i j)
  refine (hfin.preimage (f := fun T : GL (Fin 3) ℤ => (T.val : Fin 3 → Fin 3 → ℤ))
    (fun T _ T' _ h => Units.ext h)).subset ?_
  intro T hT i j
  have h1 : |T.val i j| ≤ ⌊K⌋ := by
    apply Int.le_floor.2
    rw [Int.cast_abs]
    exact hT i j
  exact abs_le.1 h1

/-! ### Conjugation by $L$ -/

theorem isLor_conj {F L S : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (hF : F = Lᵀ * lorentz * L)
    (hS : Sᵀ * F * S = F) : IsLor (L * S * L⁻¹) := by
  have h1 : (L⁻¹)ᵀ * Lᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hL, Matrix.transpose_one]
  have h2 : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hL
  unfold IsLor
  calc (L * S * L⁻¹)ᵀ * lorentz * (L * S * L⁻¹)
      = (L⁻¹)ᵀ * (Sᵀ * (Lᵀ * lorentz * L) * S) * L⁻¹ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (L⁻¹)ᵀ * (Sᵀ * F * S) * L⁻¹ := by rw [← hF]
    _ = (L⁻¹)ᵀ * (Lᵀ * lorentz * L) * L⁻¹ := by rw [hS, hF]
    _ = lorentz := by
        calc (L⁻¹)ᵀ * (Lᵀ * lorentz * L) * L⁻¹ = ((L⁻¹)ᵀ * Lᵀ) * lorentz * (L * L⁻¹) := by
              simp only [Matrix.mul_assoc]
          _ = lorentz := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem automorph_of_lor {F L P : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (hF : F = Lᵀ * lorentz * L)
    (hP : IsLor P) : (L⁻¹ * P * L)ᵀ * F * (L⁻¹ * P * L) = F := by
  have h1 : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hL
  have h2 : (L⁻¹)ᵀ * Lᵀ = 1 := by
    rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have hP' : Pᵀ * lorentz * P = lorentz := hP
  calc (L⁻¹ * P * L)ᵀ * F * (L⁻¹ * P * L)
      = Lᵀ * Pᵀ * ((L⁻¹)ᵀ * Lᵀ) * lorentz * (L * L⁻¹) * P * L := by
        rw [hF]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Lᵀ * (Pᵀ * lorentz * P) * L := by rw [h1, h2]; simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    _ = F := by rw [hP', hF]

/-! ### Hyperbolic balls are Euclidean balls -/

theorem coshDist_zero_left (ζ : Fin 2 → ℝ) : coshDist 0 ζ = 1 / √(1 - ζ 0 ^ 2 - ζ 1 ^ 2) := by
  simp [coshDist]

theorem one_le_coshDist_zero {ζ : Fin 2 → ℝ} (hζ : ζ ∈ disc) : 1 ≤ coshDist 0 ζ := by
  have hζ' : ζ 0 ^ 2 + ζ 1 ^ 2 < 1 := hζ
  rw [coshDist_zero_left]
  have hpos : 0 < 1 - ζ 0 ^ 2 - ζ 1 ^ 2 := by linarith
  have hs : 0 < √(1 - ζ 0 ^ 2 - ζ 1 ^ 2) := Real.sqrt_pos.2 hpos
  rw [le_div_iff₀ hs, one_mul]
  calc √(1 - ζ 0 ^ 2 - ζ 1 ^ 2) ≤ √1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (ζ 0), sq_nonneg (ζ 1)])
    _ = 1 := Real.sqrt_one

theorem exists_ball_of_hypDist_le (R : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ ζ ∈ disc, hypDist 0 ζ ≤ R → ζ 0 ^ 2 + ζ 1 ^ 2 ≤ r ^ 2 := by
  have hch : 1 ≤ Real.cosh R := Real.one_le_cosh R
  have hch0 : 0 < Real.cosh R := by linarith
  have hq : 0 < 1 / Real.cosh R ^ 2 := by positivity
  have hq1 : 1 / Real.cosh R ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  refine ⟨√(1 - 1 / Real.cosh R ^ 2), Real.sqrt_nonneg _, ?_, fun ζ hζ hd => ?_⟩
  · rw [Real.sqrt_lt' one_pos]; linarith
  · rw [Real.sq_sqrt (by linarith)]
    have hζ' : ζ 0 ^ 2 + ζ 1 ^ 2 < 1 := hζ
    have hx := one_le_coshDist_zero hζ
    have hR0 : 0 ≤ R := (Real.arcosh_nonneg hx).trans hd
    have hxc : coshDist 0 ζ ≤ Real.cosh R := by
      have := (Real.arcosh_le_arcosh (by linarith : 0 < coshDist 0 ζ) hch0).1
        (by rw [Real.arcosh_cosh hR0]; exact hd)
      exact this
    rw [coshDist_zero_left] at hxc
    have hpos : 0 < 1 - ζ 0 ^ 2 - ζ 1 ^ 2 := by linarith
    have hs : 0 < √(1 - ζ 0 ^ 2 - ζ 1 ^ 2) := Real.sqrt_pos.2 hpos
    rw [div_le_iff₀ hs] at hxc
    have h3 : 1 ≤ Real.cosh R ^ 2 * (1 - ζ 0 ^ 2 - ζ 1 ^ 2) := by
      have := pow_le_pow_left₀ zero_le_one hxc 2
      rw [mul_pow, Real.sq_sqrt hpos.le] at this
      simpa using this
    have h4 : 1 / Real.cosh R ^ 2 ≤ 1 - ζ 0 ^ 2 - ζ 1 ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith

end S8

end QuadFormsKB.Reduction
