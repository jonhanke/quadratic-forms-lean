/-
# Cassels, Chapter 8, Lemma 4.2: auxiliary lemmas

Matrix lemmas over $\mathbb Q_2$ used in the proof of Lemma 4.2 and its Corollary (`Ch8/DyadicCancel.lean`):
integral matrices with unit determinant (`Lemma42.UM`, the matrices of $GL_n(\mathbb Z_2)$), block diagonal
algebra for `orthSumMat`, reduction to the orthogonal complement of the first basis vector (`Lemma42.RL`,
`Lemma42.RL2`), integral reflections (`Lemma42.refl_exists`), proper primitivity under equivalence
(`Lemma42.pp_of_zpEquiv`), splitting off unimodular blocks (`Lemma42.split_unimodular_block`), binary forms of
determinant $\equiv -1 \pmod 8$ (`Lemma42.even_bin_H`), and the three-dimensional computation of case (iii)
(`Lemma42.q3`). See the proof sketch in `Ch8/DyadicCancel.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Dyadic

namespace QuadFormsKB.Cassels.Lemma42

open QuadFormsKB.Cassels Matrix

/-! ### Prelude: integral matrices with unit determinant -/

/-- An integral matrix with unit determinant (a matrix of `GL_n(ℤ₂)`, viewed over `ℚ₂`). -/
def UM {n : ℕ} (S : Matrix (Fin n) (Fin n) ℚ_[2]) : Prop := (∀ i j, ‖S i j‖ ≤ 1) ∧ ‖S.det‖ = 1

theorem UM.one {n : ℕ} : UM (1 : Matrix (Fin n) (Fin n) ℚ_[2]) := by
  refine ⟨fun i j => ?_, ?_⟩
  · by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · simp

theorem UM.mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ_[2]} (hA : UM A) (hB : UM B) : UM (A * B) := by
  obtain ⟨Az, rfl⟩ := dyadic_lift_mat hA.1
  obtain ⟨Bz, rfl⟩ := dyadic_lift_mat hB.1
  have hm : Az.map PadicInt.Coe.ringHom * Bz.map PadicInt.Coe.ringHom = (Az * Bz).map PadicInt.Coe.ringHom :=
    (Matrix.map_mul (f := PadicInt.Coe.ringHom)).symm
  refine ⟨fun i j => ?_, ?_⟩
  · rw [hm]; exact PadicInt.norm_le_one _
  · rw [Matrix.det_mul, norm_mul, hA.2, hB.2, one_mul]

theorem UM.transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ_[2]} (hA : UM A) : UM Aᵀ :=
  ⟨fun i j => hA.1 j i, by rw [Matrix.det_transpose]; exact hA.2⟩

theorem UM.inv {n : ℕ} {S : Matrix (Fin n) (Fin n) ℚ_[2]} (hS : UM S) :
    UM S⁻¹ ∧ S * S⁻¹ = 1 ∧ S⁻¹ * S = 1 := by
  have hdet : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    have := hS.2
    rw [h] at this
    simp at this
  have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hdet
  refine ⟨⟨fun i j => ?_, ?_⟩, h1, h2⟩
  · obtain ⟨Sz, rfl⟩ := dyadic_lift_mat hS.1
    have hadj : (Sz.map PadicInt.Coe.ringHom).adjugate i j = ((Sz.adjugate i j : ℤ_[2]) : ℚ_[2]) :=
      (congrFun (congrFun (RingHom.map_adjugate PadicInt.Coe.ringHom Sz) i) j).symm
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, hadj, norm_mul, Ring.inverse_eq_inv', norm_inv, hS.2]
    simpa using PadicInt.norm_le_one _
  · have := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at this
    have h3 := congrArg norm this
    rw [norm_mul, hS.2, norm_one, one_mul] at h3
    exact h3

theorem UM.orthSum {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℚ_[2]} {B : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hA : UM A) (hB : UM B) : UM (orthSumMat A B) := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [dyadic_orthSumMat_eq, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
      simp [hA.1, hB.1]
  · rw [dyadic_det_orthSumMat, norm_mul, hA.2, hB.2, one_mul]

theorem UM.cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) ℚ_[2]} (hA : UM A) :
    UM (A.submatrix (Fin.cast h) (Fin.cast h)) := by
  subst h
  simpa using hA

/-- A unimodular integral substitution gives `ℤ₂`-equivalence. -/
theorem zpEquiv_of_UM {n : ℕ} {F G S : Matrix (Fin n) (Fin n) ℚ_[2]} (hS : UM S) (h : Sᵀ * F * S = G) :
    ZpEquiv F G := by
  obtain ⟨Sz, rfl⟩ := dyadic_lift_mat hS.1
  have hu : IsUnit Sz.det := by
    rw [PadicInt.isUnit_iff]
    have := hS.2
    rw [dyadic_det_map_coe] at this
    simpa using this
  have hg : IsUnit Sz := (Matrix.isUnit_iff_isUnit_det _).2 hu
  refine ⟨hg.unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact h

theorem exists_UM_of_zpEquiv {n : ℕ} {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : ZpEquiv F G) :
    ∃ S, UM S ∧ Sᵀ * F * S = G := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.val.map PadicInt.Coe.ringHom, ⟨fun i j => PadicInt.norm_le_one _, ?_⟩, hT⟩
  rw [dyadic_det_map_coe]
  have hu : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit
  have := (PadicInt.isUnit_iff).1 hu
  simpa using this

theorem orthSumMat_mul' {a b : ℕ} (A A' : Matrix (Fin a) (Fin a) ℚ_[2]) (B B' : Matrix (Fin b) (Fin b) ℚ_[2]) :
    orthSumMat A B * orthSumMat A' B' = orthSumMat (A * A') (B * B') := by
  rw [dyadic_orthSumMat_eq, dyadic_orthSumMat_eq, dyadic_orthSumMat_eq,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_multiply]
  simp

theorem orthSumMat_transpose' {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℚ_[2]) (B : Matrix (Fin b) (Fin b) ℚ_[2]) :
    (orthSumMat A B)ᵀ = orthSumMat Aᵀ Bᵀ := by
  rw [dyadic_orthSumMat_eq, dyadic_orthSumMat_eq, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
  simp

theorem orthSumMat_one' {a b : ℕ} :
    orthSumMat (1 : Matrix (Fin a) (Fin a) ℚ_[2]) (1 : Matrix (Fin b) (Fin b) ℚ_[2]) = 1 := by
  rw [dyadic_orthSumMat_eq, Matrix.fromBlocks_one]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

/-- Block form of a matrix fixing the first basis vector. -/
theorem rb_blocks {m : ℕ} (S : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2])
    (h0 : ∀ x, S x (Fin.castAdd m 0) = if x = Fin.castAdd m 0 then 1 else 0) :
    S = (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) (fun (i : Fin 1) (j : Fin m) => S (Fin.castAdd m i) (Fin.natAdd 1 j))
      0 (fun (i j : Fin m) => S (Fin.natAdd 1 i) (Fin.natAdd 1 j))).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm := by
  ext x y
  induction x using Fin.addCases with
  | left i =>
    induction y using Fin.addCases with
    | left j =>
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [h0, Matrix.fromBlocks]
    | right j => simp [Matrix.fromBlocks]
  | right i =>
    induction y using Fin.addCases with
    | left j =>
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [h0]
      simp [Fin.ext_iff, Matrix.fromBlocks]
    | right j => simp [Matrix.fromBlocks]

/-- Reduction lemma, block-matrix core. -/
theorem rb_core {m : ℕ} {u : ℚ_[2]} (hu : u ≠ 0) {A B : Matrix (Fin m) (Fin m) ℚ_[2]}
    (ρ : Matrix (Fin 1) (Fin m) ℚ_[2]) (S22 : Matrix (Fin m) (Fin m) ℚ_[2])
    (h : (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) ρ 0 S22)ᵀ * Matrix.fromBlocks !![u] 0 0 A *
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) ρ 0 S22 = Matrix.fromBlocks !![u] 0 0 B) :
    S22ᵀ * A * S22 = B := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  have h12 := congrArg Matrix.toBlocks₁₂ h
  have h22 := congrArg Matrix.toBlocks₂₂ h
  simp at h12 h22
  have hρ : ρ = 0 := by
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have := congrFun (congrFun h12 0) j
    simpa [Matrix.vecMul, dotProduct, hu] using this
  subst hρ
  simpa using h22

/-- If `S` fixes the first basis vector and `Sᵀ(⟨u⟩ ⊥ A)S = ⟨u⟩ ⊥ B`, then `A ∼ B`. -/
theorem RL {m : ℕ} {u : ℚ_[2]} (hu : u ≠ 0) {A B : Matrix (Fin m) (Fin m) ℚ_[2]}
    (S : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]) (hS : UM S)
    (h0 : ∀ x, S x (Fin.castAdd m 0) = if x = Fin.castAdd m 0 then 1 else 0)
    (h : Sᵀ * orthSumMat !![u] A * S = orthSumMat !![u] B) : ZpEquiv A B := by
  have hb := rb_blocks S h0
  set ρ : Matrix (Fin 1) (Fin m) ℚ_[2] := fun (i : Fin 1) (j : Fin m) => S (Fin.castAdd m i) (Fin.natAdd 1 j)
    with hρ
  set S22 : Matrix (Fin m) (Fin m) ℚ_[2] := fun (i j : Fin m) => S (Fin.natAdd 1 i) (Fin.natAdd 1 j) with hS22
  have hdet : S.det = S22.det := by
    rw [hb, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp
  refine zpEquiv_of_UM (S := S22) ⟨fun i j => hS.1 _ _, by rw [← hdet]; exact hS.2⟩ ?_
  refine rb_core hu ρ S22 ?_
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [dyadic_orthSumMat_eq] at h'
  rw [hb] at h'
  simp only [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective,
    Matrix.submatrix_submatrix] at h'
  simpa using h'

/-- Equivalence of the two complements for two bases with the same first vector. -/
theorem RL2 {m : ℕ} {u : ℚ_[2]} (hu : u ≠ 0) {A B E : Matrix (Fin m) (Fin m) ℚ_[2]}
    (T Y : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]) (hT : UM T) (hY : UM Y)
    (hTY : ∀ x, Y x (Fin.castAdd m 0) = T x (Fin.castAdd m 0))
    (hT' : Tᵀ * orthSumMat !![u] A * T = orthSumMat !![u] B)
    (hY' : Yᵀ * orthSumMat !![u] A * Y = orthSumMat !![u] E) : ZpEquiv B E := by
  obtain ⟨hTi, hTT, hTT'⟩ := UM.inv hT
  have key : ∀ X : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2], T⁻¹ᵀ * (Tᵀ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hTT, Matrix.transpose_one, Matrix.one_mul]
  have key2 : ∀ X : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2], T * (T⁻¹ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hTT, Matrix.one_mul]
  refine RL hu (T⁻¹ * Y) (hTi.mul hY) ?_ ?_
  · intro x
    have : (T⁻¹ * Y) x (Fin.castAdd m 0) = (T⁻¹ * T) x (Fin.castAdd m 0) := by
      simp only [Matrix.mul_apply, hTY]
    rw [this, hTT', Matrix.one_apply]
  · rw [← hT']
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, key, key2]
    simpa only [Matrix.mul_assoc] using hY'

/-- The reflection `τ_w` in `w = b - c`, `f(b) = f(c)`, mapping `c` to `b`, when it is integral. -/
theorem refl_exists {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℚ_[2]) (hΦ : Φᵀ = Φ) (b c : Fin n → ℚ_[2])
    (hbc : b ⬝ᵥ (Φ *ᵥ b) = c ⬝ᵥ (Φ *ᵥ c)) (a : ℚ_[2]) (ha : a = b ⬝ᵥ (Φ *ᵥ b) - b ⬝ᵥ (Φ *ᵥ c)) (ha0 : a ≠ 0)
    (hint : ∀ x y, ‖(b - c) x * (Φ *ᵥ (b - c)) y / a‖ ≤ 1) :
    ∃ σ : Matrix (Fin n) (Fin n) ℚ_[2], UM σ ∧ σᵀ * Φ * σ = Φ ∧ σ *ᵥ c = b := by
  have hsym : c ⬝ᵥ (Φ *ᵥ b) = b ⬝ᵥ (Φ *ᵥ c) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hΦ, dotProduct_comm]
  generalize hw : b - c = w at hint
  have hww : w ⬝ᵥ (Φ *ᵥ w) = 2 * a := by
    rw [← hw]
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [hsym, ha, hbc]; ring
  have hvc : (Φ *ᵥ w) ⬝ᵥ c = -a := by
    rw [dotProduct_comm, ← hw]
    simp only [Matrix.mulVec_sub, dotProduct_sub]
    rw [hsym, ha, hbc]; ring
  generalize hv : Φ *ᵥ w = v at hint hww hvc
  have hwv : w ⬝ᵥ v = 2 * a := by exact hww
  have hvw : v ⬝ᵥ w = 2 * a := by rw [dotProduct_comm]; exact hwv
  set k : ℚ_[2] := a⁻¹ with hk
  have hak : a * k = 1 := mul_inv_cancel₀ ha0
  have hPt : (Matrix.vecMulVec w v)ᵀ = Matrix.vecMulVec v w := Matrix.transpose_vecMulVec w v
  have hΦP : Φ * Matrix.vecMulVec w v = Matrix.vecMulVec v v := by
    rw [Matrix.mul_vecMulVec, hv]
  have hPΦ : Matrix.vecMulVec v w * Φ = Matrix.vecMulVec v v := by
    rw [Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, hΦ, hv]
  have hVP : Matrix.vecMulVec v v * Matrix.vecMulVec w v = (2 * a) • Matrix.vecMulVec v v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvw, Matrix.vecMulVec_smul]
  have hPP : Matrix.vecMulVec w v * Matrix.vecMulVec w v = (2 * a) • Matrix.vecMulVec w v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hvw, Matrix.vecMulVec_smul]
  have hkk : k * (k * (2 * a)) = k + k := by
    have : k * (k * (2 * a)) = 2 * k * (a * k) := by ring
    rw [this, hak]; ring
  refine ⟨1 - k • Matrix.vecMulVec w v, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j
    have h1 : ‖k * (w i * v j)‖ ≤ 1 := by
      have := hint i j
      rw [div_eq_inv_mul] at this
      exact this
    have h2 : ‖(1 : Matrix (Fin n) (Fin n) ℚ_[2]) i j‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    have h3 := IsUltrametricDist.norm_add_le_max ((1 : Matrix (Fin n) (Fin n) ℚ_[2]) i j) (-(k * (w i * v j)))
    rw [norm_neg] at h3
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, sub_eq_add_neg]
    exact h3.trans (max_le h2 h1)
  · have hsq : (1 - k • Matrix.vecMulVec w v) * (1 - k • Matrix.vecMulVec w v) = 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        smul_sub, hPP, smul_smul]
      rw [hkk, add_smul]
      abel
    have hd : (1 - k • Matrix.vecMulVec w v).det * (1 - k • Matrix.vecMulVec w v).det = 1 := by
      rw [← Matrix.det_mul, hsq, Matrix.det_one]
    have h4 : ‖(1 - k • Matrix.vecMulVec w v).det‖ * ‖(1 - k • Matrix.vecMulVec w v).det‖ = 1 := by
      rw [← norm_mul, hd, norm_one]
    nlinarith [norm_nonneg (1 - k • Matrix.vecMulVec w v).det]
  · rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPt]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_sub, hPΦ, hΦP, hVP, smul_smul]
    rw [hkk, add_smul]
    abel
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hvc,
      op_smul_eq_smul, ← hw]
    have : k • (-a) • (b - c) = c - b := by
      rw [smul_smul, show k * -a = -1 by linear_combination -hak, neg_smul, one_smul, neg_sub]
    rw [this]
    abel

/-- Changing the sign of the first basis vector of the second lattice. -/
theorem sign_norm {m : ℕ} {u : ℚ_[2]} {A B : Matrix (Fin m) (Fin m) ℚ_[2]}
    (T : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]) (hT : UM T)
    (hT' : Tᵀ * orthSumMat !![u] A * T = orthSumMat !![u] B) (ε : ℚ_[2]) (hε : ε = 1 ∨ ε = -1) :
    ∃ T' : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2], UM T' ∧ T'ᵀ * orthSumMat !![u] A * T' = orthSumMat !![u] B ∧
      ∀ x, T' x (Fin.castAdd m 0) = ε * T x (Fin.castAdd m 0) := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hD : UM (orthSumMat !![ε] (1 : Matrix (Fin m) (Fin m) ℚ_[2])) := by
    refine UM.orthSum ⟨fun i j => ?_, ?_⟩ UM.one
    · simp [hεn]
    · simp [hεn]
  have hc : ∀ C : Matrix (Fin m) (Fin m) ℚ_[2], orthSumMat !![ε] (1 : Matrix (Fin m) (Fin m) ℚ_[2]) *
      orthSumMat !![u] C * orthSumMat !![ε] (1 : Matrix (Fin m) (Fin m) ℚ_[2]) = orthSumMat !![u] C := by
    intro C
    rw [orthSumMat_mul', orthSumMat_mul']
    congr 1
    · ext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp
      linear_combination u * hε2
    · simp
  have hDt : (orthSumMat !![ε] (1 : Matrix (Fin m) (Fin m) ℚ_[2]))ᵀ = orthSumMat !![ε] 1 := by
    rw [orthSumMat_transpose', Matrix.transpose_one]
    congr 1
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp
  refine ⟨T * orthSumMat !![ε] 1, hT.mul hD, ?_, ?_⟩
  · calc (T * orthSumMat !![ε] 1)ᵀ * orthSumMat !![u] A * (T * orthSumMat !![ε] 1)
        = (orthSumMat !![ε] 1)ᵀ * (Tᵀ * orthSumMat !![u] A * T) * orthSumMat !![ε] 1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = orthSumMat !![u] B := by rw [hT', hDt, hc]
  · intro x
    rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.castAdd m 0)]
    · rw [dyadic_orthSumMat_cc]; simp [mul_comm]
    · intro y hy
      induction y using Fin.addCases with
      | left i =>
        obtain rfl : i = 0 := Subsingleton.elim _ _
        exact absurd rfl hy
      | right i => rw [dyadic_orthSumMat_nc]; simp

/-- Product of integral rectangular matrices is integral. -/
theorem pp_int_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℚ_[2]) (B : Matrix (Fin b) (Fin c) ℚ_[2])
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) : ∀ i j, ‖(A * B) i j‖ ≤ 1 := by
  let Az : Matrix (Fin a) (Fin b) ℤ_[2] := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let Bz : Matrix (Fin b) (Fin c) ℤ_[2] := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have h : A * B = (Az * Bz).map PadicInt.Coe.ringHom := by
    rw [Matrix.map_mul]; rfl
  intro i j
  rw [h]
  exact PadicInt.norm_le_one _

/-- A matrix times an integral vector is integral. -/
theorem pp_int_mulVec {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℚ_[2]) (y : Fin b → ℚ_[2])
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) : ∀ i, ‖(A *ᵥ y) i‖ ≤ 1 := by
  let Az : Matrix (Fin a) (Fin b) ℤ_[2] := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let yz : Fin b → ℤ_[2] := fun i => ⟨y i, hy i⟩
  have h : A *ᵥ y = fun i => ((Az *ᵥ yz) i : ℚ_[2]) := by
    ext i
    have := RingHom.map_mulVec PadicInt.Coe.ringHom Az yz i
    exact this.symm
  intro i
  rw [h]
  exact PadicInt.norm_le_one _

/-- For `z ∈ ℤ₂`, the norm is `1` iff `z` is odd. -/
theorem pp_norm_eq_one_iff (z : ℤ_[2]) : ‖(z : ℚ_[2])‖ = 1 ↔ ¬ (2 : ℤ_[2]) ∣ z := by
  constructor
  · intro h hd
    have hu : IsUnit z := PadicInt.isUnit_iff.2 (by simpa using h)
    exact dyadic_not_isUnit_of_two_dvd hd hu
  · intro h
    refine le_antisymm (PadicInt.norm_le_one z) ?_
    by_contra hlt
    push Not at hlt
    exact h (dyadic_two_dvd_of_norm_lt hlt)

/-- Divisibility by `2` in `ℤ₂` is vanishing of the reduction mod `2`. -/
theorem pp_two_dvd_iff_toZMod (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  simp

/-- Over `𝔽₂`, `aᵀ G a = ∑ i, G i i * a i` for symmetric `G`. -/
theorem pp_zmod_two_quad {n : ℕ} (G : Matrix (Fin n) (Fin n) (ZMod 2)) (hG : Gᵀ = G) (a : Fin n → ZMod 2) :
    a ⬝ᵥ (G *ᵥ a) = ∑ i, G i i * a i := by
  have hsymm : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hG i) j
    simpa [Matrix.transpose_apply] using this
  set f : Fin n × Fin n → ZMod 2 := fun x => if x.1 = x.2 then 0 else a x.1 * G x.1 x.2 * a x.2 with hf
  have h0 : ∑ x, f x = 0 := by
    refine Finset.sum_involution (fun x _ => (x.2, x.1)) ?_ ?_ ?_ ?_
    · intro x _
      by_cases h : x.1 = x.2
      · simp [hf, h]
      · have h' : x.2 ≠ x.1 := fun e => h e.symm
        simp only [hf, h, h', ite_false, hsymm x.1 x.2]
        have : ∀ y : ZMod 2, y + y = 0 := by decide
        rw [show a x.2 * G x.1 x.2 * a x.1 = a x.1 * G x.1 x.2 * a x.2 by ring]
        exact this _
    · intro x _ hx h
      apply hx
      have : x.2 = x.1 := congrArg Prod.fst h
      simp [hf, this]
    · intros; exact Finset.mem_univ _
    · intro x _; rfl
  have h1 : a ⬝ᵥ (G *ᵥ a) = ∑ x : Fin n × Fin n, a x.1 * G x.1 x.2 * a x.2 := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∀ x : Fin n × Fin n, a x.1 * G x.1 x.2 * a x.2 = f x + if x.1 = x.2 then G x.1 x.1 * a x.1 else 0 := by
    intro x
    by_cases h : x.1 = x.2
    · have sq : ∀ y : ZMod 2, y * y = y := by decide
      simp only [hf, h, ite_true, zero_add]
      rw [← h]
      linear_combination (G x.1 x.1) * sq (a x.1)
    · simp [hf, h]
  rw [h1, Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_add_distrib, h0, zero_add, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- For symmetric `F` over `ℤ₂`, `aᵀ F a - ∑ F i i a i` is even. -/
theorem pp_two_dvd_quad_diag {n : ℕ} (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (a : Fin n → ℤ_[2]) :
    (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (fun i => F i i) := by
  rw [pp_two_dvd_iff_toZMod, map_sub, sub_eq_zero]
  have hG : (F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2))ᵀ = F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [← Matrix.transpose_map, hF]
  have := pp_zmod_two_quad _ hG (fun i => PadicInt.toZMod (a i))
  have h1 : PadicInt.toZMod (a ⬝ᵥ (F *ᵥ a)) = (fun i => PadicInt.toZMod (a i)) ⬝ᵥ
      ((F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) *ᵥ (fun i => PadicInt.toZMod (a i))) := by
    simp [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]
  rw [h1, this]
  simp [dotProduct, map_sum, map_mul, Matrix.map_apply, mul_comm]

/-- Properly primitive means: some integral vector has odd value. -/
theorem pp_quad_iff {n : ℕ} {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hFi : ∀ i j, ‖F i j‖ ≤ 1) :
    (∃ j, ‖F j j‖ = 1) ↔ ∃ y : Fin n → ℚ_[2], (∀ i, ‖y i‖ ≤ 1) ∧ ‖y ⬝ᵥ (F *ᵥ y)‖ = 1 := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨Pi.single j 1, fun i => ?_, ?_⟩
    · by_cases h : i = j <;> simp [h]
    · have : (Pi.single j (1 : ℚ_[2]) : Fin n → ℚ_[2]) ⬝ᵥ (F *ᵥ Pi.single j 1) = F j j := by
        simp [dotProduct, Matrix.mulVec, Pi.single_apply]
      rw [this]; exact hj
  · rintro ⟨y, hy, hq⟩
    by_contra hno
    push Not at hno
    obtain ⟨Fz, rfl⟩ := dyadic_lift_mat hFi
    let yz : Fin n → ℤ_[2] := fun i => ⟨y i, hy i⟩
    have hFz : Fzᵀ = Fz := by
      ext i j
      have := congrFun (congrFun hF i) j
      simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
      exact this
    have hdiag : ∀ i, (2 : ℤ_[2]) ∣ Fz i i := fun i =>
      dyadic_two_dvd_of_norm_lt (lt_of_le_of_ne (hFi i i) (hno i))
    have h1 := pp_two_dvd_quad_diag Fz hFz yz
    have h2 : (2 : ℤ_[2]) ∣ yz ⬝ᵥ (fun i => Fz i i) :=
      Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (hdiag i) _
    have h3 : (2 : ℤ_[2]) ∣ yz ⬝ᵥ (Fz *ᵥ yz) := by
      have := dvd_add h1 h2
      simpa using this
    have h4 : y ⬝ᵥ (Fz.map PadicInt.Coe.ringHom *ᵥ y) = ((yz ⬝ᵥ (Fz *ᵥ yz) : ℤ_[2]) : ℚ_[2]) := by
      show _ = PadicInt.Coe.ringHom _
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]
      rfl
    rw [h4] at hq
    exact (pp_norm_eq_one_iff _).1 hq h3

/-- Quadratic value under substitution. -/
theorem pp_quad_subst {n : ℕ} (F S : Matrix (Fin n) (Fin n) ℚ_[2]) (y : Fin n → ℚ_[2]) :
    y ⬝ᵥ ((Sᵀ * F * S) *ᵥ y) = (S *ᵥ y) ⬝ᵥ (F *ᵥ (S *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- One direction of invariance of proper primitivity. -/
theorem pp_dir {n : ℕ} {F G S T : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hFi : IsClassIntegral F)
    (hSi : ∀ i j, ‖S i j‖ ≤ 1) (hTi : ∀ i j, ‖T i j‖ ≤ 1) (hST : S * T = 1) (h : Sᵀ * F * S = G)
    (hpp : IsProperlyPrimitive F) : IsProperlyPrimitive G := by
  have hSt : ∀ i j, ‖Sᵀ i j‖ ≤ 1 := fun i j => hSi j i
  have hGi : ∀ i j, ‖G i j‖ ≤ 1 := by
    rw [← h]; exact pp_int_mul _ _ (pp_int_mul _ _ hSt hFi) hSi
  have hG : Gᵀ = G := by
    rw [← h, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hF, Matrix.mul_assoc]
  have hdiag : (∃ j, ‖F j j‖ = 1) := by
    obtain ⟨⟨_, i, j, hij⟩, j', hj'⟩ := hpp
    exact ⟨j', hj'⟩
  obtain ⟨x, hx, hq⟩ := (pp_quad_iff hF hFi).1 hdiag
  have hy : ∀ i, ‖(T *ᵥ x) i‖ ≤ 1 := pp_int_mulVec T x hTi hx
  have hqG : (T *ᵥ x) ⬝ᵥ (G *ᵥ (T *ᵥ x)) = x ⬝ᵥ (F *ᵥ x) := by
    rw [← h, pp_quad_subst, Matrix.mulVec_mulVec, hST, Matrix.one_mulVec]
  have hGd := (pp_quad_iff hG hGi).2 ⟨T *ᵥ x, hy, by rw [hqG]; exact hq⟩
  obtain ⟨j, hj⟩ := hGd
  exact ⟨⟨hGi, j, j, hj⟩, j, hj⟩

theorem pp_of_zpEquiv {n : ℕ} {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hFi : IsClassIntegral F)
    (h : ZpEquiv F G) : IsProperlyPrimitive F ↔ IsProperlyPrimitive G := by
  obtain ⟨S, hS, rfl⟩ := exists_UM_of_zpEquiv h
  obtain ⟨hSinv, hSS, hSS'⟩ := UM.inv hS
  have hSt : ∀ i j, ‖Sᵀ i j‖ ≤ 1 := fun i j => hS.1 j i
  have hGi : IsClassIntegral (Sᵀ * F * S) := pp_int_mul _ _ (pp_int_mul _ _ hSt hFi) hS.1
  have hG : (Sᵀ * F * S)ᵀ = Sᵀ * F * S := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hF, Matrix.mul_assoc]
  constructor
  · exact pp_dir hF hFi hS.1 hSinv.1 hSS rfl
  · refine pp_dir hG hGi hSinv.1 hS.1 hSS' ?_
    have h1 : (S⁻¹)ᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, hSS, Matrix.transpose_one]
    calc (S⁻¹)ᵀ * (Sᵀ * F * S) * S⁻¹ = ((S⁻¹)ᵀ * Sᵀ) * F * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = F := by rw [h1, hSS]; simp

theorem pp_iff_diag {n : ℕ} {F : Matrix (Fin n) (Fin n) ℚ_[2]} :
    IsProperlyPrimitive F ↔ IsClassIntegral F ∧ ∃ j, ‖F j j‖ = 1 := by
  constructor
  · rintro ⟨⟨hi, _⟩, hj⟩
    exact ⟨hi, hj⟩
  · rintro ⟨hi, j, hj⟩
    exact ⟨⟨hi, j, j, hj⟩, j, hj⟩

/-- Splitting a `1 × 1` block off with an integral multiplier. -/
theorem pp_single_lambda {m : ℕ} (B : Matrix (Fin 1) (Fin 1) ℚ_[2]) (C : Matrix (Fin 1) (Fin m) ℚ_[2])
    (hB : B 0 0 ≠ 0) (hC : ∀ k, ‖C 0 k‖ ≤ ‖B 0 0‖) :
    ∃ Λ : Matrix (Fin 1) (Fin m) ℤ_[2], C = B * Λ.map PadicInt.Coe.ringHom := by
  have hb : ∀ k, ‖C 0 k / B 0 0‖ ≤ 1 := fun k => by
    rw [norm_div]; exact (div_le_one (norm_pos_iff.2 hB)).2 (hC k)
  refine ⟨Matrix.of fun _ k => ⟨C 0 k / B 0 0, hb k⟩, ?_⟩
  ext r k
  fin_cases r
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  show C 0 k = B 0 0 * (C 0 k / B 0 0)
  field_simp

theorem pivot_split {m : ℕ} {K : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]} (hK : Kᵀ = K)
    (hi : IsClassIntegral K) (i : Fin (1 + m)) (hii : ‖K i i‖ = 1) :
    ∃ (v : ℚ_[2]) (K1 : Matrix (Fin m) (Fin m) ℚ_[2]), ‖v‖ = 1 ∧ ZpEquiv K (orthSumMat !![v] K1) := by
  obtain ⟨σ, hσ⟩ := dyadic_front1 i
  set K' := K.submatrix σ σ with hK'
  have hK't : K'ᵀ = K' := by rw [hK', Matrix.transpose_submatrix, hK]
  have h00 : K' (Fin.castAdd m 0) (Fin.castAdd m 0) = K i i := by simp [hK', hσ]
  have hb : K' (Fin.castAdd m 0) (Fin.castAdd m 0) ≠ 0 := by
    rw [h00]; intro h; rw [h, norm_zero] at hii; exact zero_ne_one hii
  obtain ⟨Λ, hΛ⟩ := pp_single_lambda (K'.submatrix (Fin.castAdd m) (Fin.castAdd m))
    (K'.submatrix (Fin.castAdd m) (Fin.natAdd 1)) (by simpa using hb) (fun k => by
      have : ‖K' (Fin.castAdd m 0) (Fin.natAdd 1 k)‖ ≤ 1 := hi _ _
      simpa [h00, hii] using this)
  have hsp := dyadic_zpEquiv_split K' hK't Λ hΛ
  have hB : K'.submatrix (Fin.castAdd m) (Fin.castAdd m) = !![K i i] := by
    ext a b
    fin_cases a; fin_cases b
    simpa using h00
  rw [hB] at hsp
  exact ⟨K i i, _, hii, (dyadic_zpEquiv_perm K σ).trans hsp⟩

theorem split_unimodular_block {a b : ℕ} {F : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[2]} (hF : Fᵀ = F)
    (hi : IsClassIntegral F) (hB : ‖(F.submatrix (Fin.castAdd b) (Fin.castAdd b)).det‖ = 1) :
    ∃ (U : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[2]) (K : Matrix (Fin b) (Fin b) ℚ_[2]), UM U ∧
      (∀ (i : Fin a) (x : Fin (a + b)), U x (Fin.castAdd b i) = if x = Fin.castAdd b i then 1 else 0) ∧
      Kᵀ = K ∧ IsClassIntegral K ∧
      Uᵀ * F * U = orthSumMat (F.submatrix (Fin.castAdd b) (Fin.castAdd b)) K := by
  set B := F.submatrix (Fin.castAdd b) (Fin.castAdd b) with hBdef
  set C := F.submatrix (Fin.castAdd b) (Fin.natAdd a) with hCdef
  set E := F.submatrix (Fin.natAdd a) (Fin.natAdd a) with hE
  have hBt : Bᵀ = B := by
    ext i j; simp [hBdef, Matrix.transpose_apply]; exact congrFun (congrFun hF _) _
  have hBi : ∀ i j, ‖B i j‖ ≤ 1 := fun i j => hi _ _
  have hCi : ∀ i j, ‖C i j‖ ≤ 1 := fun i j => hi _ _
  have hEi : ∀ i j, ‖E i j‖ ≤ 1 := fun i j => hi _ _
  have hdet0 : B.det ≠ 0 := by
    intro h; rw [h, norm_zero] at hB; exact zero_ne_one hB
  have hdetU : IsUnit B.det := isUnit_iff_ne_zero.2 hdet0
  -- the inverse of `B` is integral
  have hBinv : ∀ i j, ‖B⁻¹ i j‖ ≤ 1 := by
    obtain ⟨Bz, hBz⟩ := dyadic_lift_mat hBi
    have hadj : B.adjugate = (Bz.adjugate).map PadicInt.Coe.ringHom := by
      rw [← hBz]; exact (RingHom.map_adjugate PadicInt.Coe.ringHom Bz).symm
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', hadj, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hB]
    simp only [inv_one, one_mul]
    exact PadicInt.norm_le_one _
  set L := B⁻¹ * C with hL
  have hLi : ∀ i j, ‖L i j‖ ≤ 1 := pp_int_mul _ _ hBinv hCi
  have hC : C = B * L := by
    rw [hL, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetU, Matrix.one_mul]
  clear_value L
  set K := E - Lᵀ * B * L with hK
  have hKs : Kᵀ = K := by
    have hEt : Eᵀ = E := by
      ext i j; simp [hE, Matrix.transpose_apply]; exact congrFun (congrFun hF _) _
    rw [hK, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBt, hEt,
      Matrix.mul_assoc]
  have hKi : ∀ i j, ‖K i j‖ ≤ 1 := by
    intro i j
    have h1 : ∀ i j, ‖(Lᵀ * B * L) i j‖ ≤ 1 :=
      pp_int_mul _ _ (pp_int_mul _ _ (fun i j => hLi j i) hBi) hLi
    rw [hK, Matrix.sub_apply, sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hEi i j) (by rw [norm_neg]; exact h1 i j))
  set U : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[2] :=
    (Matrix.fromBlocks 1 (-L) 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm with hU
  refine ⟨U, K, ⟨?_, ?_⟩, ?_, hKs, hKi, ?_⟩
  · intro x y
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [hU, Matrix.fromBlocks, Matrix.one_apply] <;> (try split_ifs) <;> simp [hLi]
  · rw [hU, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp
  · intro i x
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
    rcases x with x | x
    · simp [hU, Matrix.fromBlocks, Matrix.one_apply]
    · have hlt := i.isLt
      have hne : Fin.natAdd a x ≠ Fin.castAdd b i := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hU, Matrix.fromBlocks, hne]
  · have hFe : F = (Matrix.fromBlocks B C Cᵀ E).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      ext i j
      obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [hBdef, hCdef, hE, Matrix.transpose_apply, Matrix.fromBlocks]
      exact congrFun (congrFun hF _) _
    have hCt : Cᵀ = Lᵀ * B := by
      rw [hC, Matrix.transpose_mul, hBt]
    conv_lhs => rw [hU, hFe]
    rw [dyadic_orthSumMat_eq, Matrix.transpose_submatrix,
      ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1
    simp [hC, hBt, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, hK]
    abel

/-- The square of a unit of `ℚ₂` is `1 + 8c` with `c` integral. -/
theorem bi_sq {s : ℚ_[2]} (hs : ‖s‖ = 1) : ∃ c : ℚ_[2], ‖c‖ ≤ 1 ∧ s ^ 2 = 1 + 8 * c := by
  obtain ⟨w, u0, rfl, hw, h0, hd⟩ := dyadic_exists_lift hs
  obtain ⟨k, hk⟩ : ∃ k : ℤ, u0 ^ 2 = 1 + 8 * k := by
    rcases h0 with rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨3, by norm_num⟩, ⟨6, by norm_num⟩]
  obtain ⟨t, ht⟩ := hd
  have hw2 : w = u0 + 8 * t := by
    have : (2 : ℤ_[2]) ^ 3 = 8 := by norm_num
    rw [this] at ht; linear_combination ht
  have hk' : (u0 : ℤ_[2]) ^ 2 = 1 + 8 * (k : ℤ_[2]) := by exact_mod_cast hk
  refine ⟨(((k : ℤ_[2]) + 2 * u0 * t + 8 * t ^ 2 : ℤ_[2]) : ℚ_[2]), PadicInt.norm_le_one _, ?_⟩
  have : w ^ 2 = 1 + 8 * ((k : ℤ_[2]) + 2 * u0 * t + 8 * t ^ 2) := by
    rw [hw2]; linear_combination hk'
  exact_mod_cast congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) this

theorem even_bin_H {h : Matrix (Fin 2) (Fin 2) ℚ_[2]} (hs : hᵀ = h) (hi : ∀ i j, ‖h i j‖ ≤ 1)
    (hd : ∀ i, ‖h i i‖ < 1) (hdet : ‖h.det + 1‖ ≤ 1 / 8) : ZpEquiv h !![0, 1; 1, 0] := by
  have h10 : h 1 0 = h 0 1 := by
    have := congrFun (congrFun hs 0) 1
    simpa [Matrix.transpose_apply] using this
  have hdet2 : h.det = h 0 0 * h 1 1 - h 0 1 * h 0 1 := by
    rw [Matrix.det_fin_two, h10]
  have h8 : ‖(1 : ℚ_[2])‖ = 1 := norm_one
  have hy : ‖h 0 1‖ = 1 := by
    by_contra hne
    have hlt : ‖h 0 1‖ < 1 := lt_of_le_of_ne (hi 0 1) hne
    have h1 : ‖h.det‖ < 1 := by
      rw [hdet2, sub_eq_add_neg]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hi 1 1)).trans_lt (hd 0)
      · rw [norm_neg, norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (hi 0 1)).trans_lt hlt
    have h2 : ‖h.det + 1‖ = 1 := by
      rw [add_comm]
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : ℚ_[2])) (y := h.det)
        (by rw [h8]; exact h1.ne')
      rw [this, h8]; exact max_eq_left h1.le
    rw [h2] at hdet; norm_num at hdet
  have hh : h = !![h 0 0, h 0 1; h 0 1, h 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h10]
  rw [hh]
  rcases dyadic_block2_unit (hd 0) (hd 1) hy with H | A
  · exact H
  · exfalso
    obtain ⟨s, hs1, hs2⟩ := dyadic_zpEquiv_det_rel A
    obtain ⟨c, hc, hsq⟩ := bi_sq hs1
    have hdA : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]).det = 3 := by
      rw [Matrix.det_fin_two_of]; norm_num
    have hdh : (!![h 0 0, h 0 1; h 0 1, h 1 1] : Matrix (Fin 2) (Fin 2) ℚ_[2]).det = h.det := by
      rw [Matrix.det_fin_two_of, hdet2]
    rw [hdA, hdh] at hs2
    set e := h.det + 1 with he
    have h4 : (4 : ℚ_[2]) = s ^ 2 * e - 8 * c := by
      have : h.det = e - 1 := by rw [he]; ring
      rw [this] at hs2
      linear_combination hs2 - hsq
    have hn : ‖(4 : ℚ_[2])‖ = 1 / 4 := by
      have : (4 : ℚ_[2]) = 2 ^ 2 := by norm_num
      rw [this, norm_pow, dyadic_norm_two_q]; norm_num
    have h8n : ‖(8 : ℚ_[2])‖ = 1 / 8 := by
      have : (8 : ℚ_[2]) = 2 ^ 3 := by norm_num
      rw [this, norm_pow, dyadic_norm_two_q]; norm_num
    have hle : ‖(4 : ℚ_[2])‖ ≤ 1 / 8 := by
      rw [h4, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, norm_pow, hs1]; simpa using hdet
      · rw [norm_neg, norm_mul, h8n]
        calc 1 / 8 * ‖c‖ ≤ 1 / 8 * 1 := by gcongr
          _ = 1 / 8 := by norm_num
    rw [hn] at hle; norm_num at hle

set_option maxHeartbeats 1600000 in
/-- The integer congruence `⟨ρ₀, -ρ₀, v₀⟩ ∼ H ⊥ ⟨v₀⟩` for odd residues `ρ₀, v₀ ∈ {1,3,5,7}`. -/
theorem bi_int (ρ0 v0 : ℤ) (hρ : ρ0 = 1 ∨ ρ0 = 3 ∨ ρ0 = 5 ∨ ρ0 = 7) (hv : v0 = 1 ∨ v0 = 3 ∨ v0 = 5 ∨ v0 = 7) :
    ZpEquiv !![(ρ0 : ℚ_[2]), 0, 0; 0, -ρ0, 0; 0, 0, v0] !![0, 1, 0; 1, 0, 0; 0, 0, (v0 : ℚ_[2])] := by
  have key : ∀ T0 : Matrix (Fin 3) (Fin 3) ℤ, Odd T0.det →
      (∀ i j, (8 : ℤ) ∣ (T0ᵀ * !![ρ0, 0, 0; 0, -ρ0, 0; 0, 0, v0] * T0) i j - (!![0, 1, 0; 1, 0, 0; 0, 0, v0]) i j) →
      Odd ρ0 → Odd v0 →
      ZpEquiv !![(ρ0 : ℚ_[2]), 0, 0; 0, -ρ0, 0; 0, 0, v0] !![0, 1, 0; 1, 0, 0; 0, 0, (v0 : ℚ_[2])] := by
    intro T0 hT hd hρo hvo
    have := dyadic_zpEquiv_of_int (!![ρ0, 0, 0; 0, -ρ0, 0; 0, 0, v0] : Matrix (Fin 3) (Fin 3) ℤ)
      !![0, 1, 0; 1, 0, 0; 0, 0, v0] T0
      (by ext i j; fin_cases i <;> fin_cases j <;> rfl) (by ext i j; fin_cases i <;> fin_cases j <;> rfl)
      (by
        have : (!![ρ0, 0, 0; 0, -ρ0, 0; 0, 0, v0] : Matrix (Fin 3) (Fin 3) ℤ).det = -(ρ0 * ρ0 * v0) := by
          simp [Matrix.det_fin_three]
        rw [this]; exact ((hρo.mul hρo).mul hvo).neg) hT hd
    convert this using 1 <;> (ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hρo : Odd ρ0 := by rcases hρ with rfl | rfl | rfl | rfl <;> decide
  have hvo : Odd v0 := by rcases hv with rfl | rfl | rfl | rfl <;> decide
  rcases hρ with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
  · exact key !![-3,0,-3; -3,3,-3; 0,-3,3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-1,-3; -3,2,-3; 0,-3,1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-2,-3; -3,1,-3; 0,-3,-1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-3,-3; -3,0,-3; 0,-3,-3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-3,-3; -3,-2,-3; 0,-3,3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,0,-3; -3,1,-3; 0,-3,1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-1,-3; -3,0,-3; 0,-3,-1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-2,-3; -3,-1,-3; 0,-3,-3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-2,-3; -3,-3,-3; 0,-3,3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-3,-3; -3,4,-3; 0,-3,1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,0,-3; -3,-1,-3; 0,-3,-1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-1,-3; -3,-2,-3; 0,-3,-3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-1,-3; -3,4,-3; 0,-3,3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-2,-3; -3,3,-3; 0,-3,1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,-3,-3; -3,2,-3; 0,-3,-1] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo
  · exact key !![-3,0,-3; -3,-3,-3; 0,-3,-3] (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide)
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]) hρo hvo


/-- `orthSumMat` of a `1 × 1` and a `2 × 2` block, as an explicit `3 × 3` matrix. -/
theorem qb_orth12 (a b c d e : ℚ_[2]) :
    orthSumMat !![a] !![b, c; d, e] =
      (!![a, 0, 0; 0, b, c; 0, d, e] : Matrix (Fin (1 + 2)) (Fin (1 + 2)) ℚ_[2]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthSumMat, Matrix.reindex_apply, Matrix.fromBlocks, finSumFinEquiv, Fin.addCases]

theorem q3 {u t r β γ : ℚ_[2]} (hu : ‖u‖ ≤ 1) (ht : ‖t‖ ≤ 1) (hβ : ‖β‖ ≤ 1) (hγ1 : ‖γ‖ ≤ 1)
    (hγ : u * t ^ 2 + γ = u) :
    ∃ Q : Matrix (Fin (1 + 2)) (Fin (1 + 2)) ℚ_[2], (∀ x, Q x 0 = if x = 0 then t else if x = 2 then 1 else 0) ∧
      Q.det = β * u ∧ (∀ i j, ‖Q i j‖ ≤ 1) ∧
      Qᵀ * orthSumMat !![u] !![r, β; β, γ] * Q = orthSumMat !![u]
        !![u * β ^ 2 + u ^ 2 * t ^ 2 * r, -(u * t) * (γ * r - β ^ 2);
          -(u * t) * (γ * r - β ^ 2), γ * (γ * r - β ^ 2)] := by
  refine ⟨(!![t, β, 0; 0, -(u * t), γ; 1, 0, -β] : Matrix (Fin (1 + 2)) (Fin (1 + 2)) ℚ_[2]), ?_, ?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp
  · rw [Matrix.det_fin_three]
    simp
    linear_combination (β) * hγ
  · have h1 : ‖(1 : ℚ_[2])‖ ≤ 1 := by simp
    have h0 : ‖(0 : ℚ_[2])‖ ≤ 1 := by simp
    have hn : ‖u‖ * ‖t‖ ≤ 1 := by nlinarith [norm_nonneg u, norm_nonneg t]
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> assumption
  · rw [qb_orth12, qb_orth12]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply] <;> first | ring1 | linear_combination hγ

/-- A basis change putting `e_j` and the primitive vector `s` into the first two positions. -/
theorem norm_basis {m' : ℕ} (s : Fin (2 + m') → ℚ_[2]) (hs : ∀ i, ‖s i‖ ≤ 1) {j k : Fin (2 + m')}
    (hjk : j ≠ k) (hk : ‖s k‖ = 1) :
    ∃ S : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2], UM S ∧
      (∀ x, S x (Fin.castAdd m' 0) = if x = j then 1 else 0) ∧ (∀ x, S x (Fin.castAdd m' 1) = s x) := by
  obtain ⟨σ, h0, h1⟩ := dyadic_front2 hjk
  let R : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2] := (1 : Matrix _ _ ℚ_[2]).updateCol k s
  have hR : ∀ x z, R x z = if z = k then s x else if x = z then 1 else 0 := by
    intro x z
    simp [R, Matrix.updateCol_apply, Matrix.one_apply, eq_comm]
  have hdet : R.det = s k := by
    have := Matrix.cramer_apply (1 : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2]) s k
    rw [Matrix.cramer_one] at this
    simpa using this.symm
  refine ⟨R.submatrix id σ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    simp only [Matrix.submatrix_apply, id, hR]
    split_ifs
    · exact hs x
    · simp
    · simp
  · rw [Matrix.det_permute', norm_mul, hdet, hk]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro x
    simp only [Matrix.submatrix_apply, id, hR, h0]
    simp [hjk, eq_comm]
  · intro x
    simp [Matrix.submatrix_apply, hR, h1]

/-- An element of `ℤ₂` divisible by `8` has `ℚ₂`-norm at most `1/8`. -/
theorem cc_norm_le_eighth (z : ℤ_[2]) (h : (2 : ℤ_[2]) ^ 3 ∣ z) : ‖(z : ℚ_[2])‖ ≤ 1 / 8 := by
  obtain ⟨y, rfl⟩ := h
  have hy : ‖(y : ℚ_[2])‖ ≤ 1 := by rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one y
  have h2 : (((2 : ℤ_[2])) : ℚ_[2]) = 2 := by simpa using PadicInt.coe_natCast (p := 2) 2
  push_cast
  rw [h2, norm_mul, norm_pow, dyadic_norm_two_q]
  calc ((2 : ℝ)⁻¹) ^ 3 * ‖(y : ℚ_[2])‖ ≤ ((2 : ℝ)⁻¹) ^ 3 * 1 := by gcongr
    _ = 1 / 8 := by norm_num

/-- The square of a unit of `ℚ₂` is `≡ 1 (mod 8)`. -/
theorem cc_sq_sub_one {t : ℚ_[2]} (ht : ‖t‖ = 1) : ‖t ^ 2 - 1‖ ≤ 1 / 8 := by
  obtain ⟨w, u₀, hw, -, hu₀, hd⟩ := dyadic_exists_lift ht
  subst hw
  have hj : ∃ j : ℤ, u₀ ^ 2 - 1 = 8 * j := by
    refine ⟨(u₀ ^ 2 - 1) / 8, ?_⟩
    rcases hu₀ with rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨j, hj⟩ := hj
  obtain ⟨k, hk⟩ := hd
  have hj' : ((u₀ : ℤ_[2]) ^ 2 - 1) = 8 * (j : ℤ_[2]) := by exact_mod_cast hj
  have h8 : (2 : ℤ_[2]) ^ 3 ∣ w ^ 2 - 1 := by
    refine ⟨j + 2 * u₀ * k + 2 ^ 3 * k ^ 2, ?_⟩
    have hw : w = u₀ + 2 ^ 3 * k := by linear_combination hk
    rw [hw]
    linear_combination hj'
  have := cc_norm_le_eighth _ h8
  push_cast at this
  exact this

/-- The sum of two units of `ℚ₂` is a non-unit. -/
theorem cc_unit_add_unit {a b : ℚ_[2]} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a + b‖ < 1 := by
  obtain ⟨wa, ua, hwa, -, hua, hda⟩ := dyadic_exists_lift ha
  obtain ⟨wb, ub, hwb, -, hub, hdb⟩ := dyadic_exists_lift hb
  subst hwa hwb
  have hk : ∃ k : ℤ, ua + ub = 2 * k := by
    refine ⟨(ua + ub) / 2, ?_⟩
    rcases hua with rfl | rfl | rfl | rfl <;> rcases hub with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨k, hk⟩ := hk
  have hk' : ((ua : ℤ_[2]) + ub) = 2 * (k : ℤ_[2]) := by exact_mod_cast hk
  have h2 : (2 : ℤ_[2]) ∣ wa + wb := by
    obtain ⟨x, hx⟩ := hda
    obtain ⟨y, hy⟩ := hdb
    refine ⟨4 * x + 4 * y + k, ?_⟩
    linear_combination hx + hy + hk'
  have h3 : ‖(wa + wb : ℤ_[2])‖ < 1 := by
    have := (PadicInt.norm_lt_one_iff_dvd (p := 2) (wa + wb)).2 (by simpa using h2)
    exact this
  rw [PadicInt.norm_def] at h3
  push_cast at h3
  exact h3

/-- Conjugating a transported product by a cast of the index type. -/
theorem cc_cast_conj {n n' : ℕ} (h : n' = n) (A B C : Matrix (Fin n) (Fin n) ℚ_[2]) :
    (A.submatrix (Fin.cast h) (Fin.cast h))ᵀ * B.submatrix (Fin.cast h) (Fin.cast h) *
      C.submatrix (Fin.cast h) (Fin.cast h) = (Aᵀ * B * C).submatrix (Fin.cast h) (Fin.cast h) := by
  subst h
  simp

/-- Indices of the two blocks of an orthogonal sum are distinct. -/
theorem cc_castAdd_ne_natAdd {a b : ℕ} (i : Fin a) (j : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- The `(0,0)` entry of the equation: `u t² + γ = u`. -/
theorem cc_gamma {m' : ℕ} {u t : ℚ_[2]} {G1 G2 : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2]}
    (T : Matrix (Fin (1 + (2 + m'))) (Fin (1 + (2 + m'))) ℚ_[2])
    (hc : ∀ x, T x (Fin.castAdd (2 + m') 0) =
      if x = Fin.castAdd (2 + m') 0 then t else if x = Fin.natAdd 1 (Fin.castAdd m' 1) then 1 else 0)
    (heq : Tᵀ * orthSumMat !![u] G1 * T = orthSumMat !![u] G2) :
    u * t ^ 2 + G1 (Fin.castAdd m' 1) (Fin.castAdd m' 1) = u := by
  have gen : ∀ i j, (Tᵀ * orthSumMat !![u] G1 * T) i j =
      (fun x => T x i) ⬝ᵥ (orthSumMat !![u] G1 *ᵥ fun x => T x j) := fun i j => by
    rw [Matrix.mul_assoc]; rfl
  have hne : Fin.castAdd (2 + m') (0 : Fin 1) ≠ Fin.natAdd 1 (Fin.castAdd m' 1) := cc_castAdd_ne_natAdd _ _
  have e := congrFun (congrFun heq (Fin.castAdd (2 + m') 0)) (Fin.castAdd (2 + m') 0)
  rw [gen, dyadic_orthSumMat_cc] at e
  have hcol : (fun x => T x (Fin.castAdd (2 + m') 0)) =
      t • (Pi.single (Fin.castAdd (2 + m') 0) 1 : Fin (1 + (2 + m')) → ℚ_[2]) +
        (Pi.single (Fin.natAdd 1 (Fin.castAdd m' 1)) 1 : Fin (1 + (2 + m')) → ℚ_[2]) := by
    funext x
    rw [hc]
    by_cases h1 : x = Fin.castAdd (2 + m') 0
    · subst h1; simp [hne]
    · by_cases h2 : x = Fin.natAdd 1 (Fin.castAdd m' 1)
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [hcol] at e
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, smul_dotProduct,
    dotProduct_smul, Matrix.mulVec_single_one, single_dotProduct, smul_eq_mul] at e
  simp [dyadic_orthSumMat_cc, dyadic_orthSumMat_cn, dyadic_orthSumMat_nc, dyadic_orthSumMat_nn, hne,
    hne.symm] at e
  linear_combination e


/-- Products of integral elements are integral. -/
theorem cm_mul1 (x y : ℚ_[2]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; nlinarith [norm_nonneg x, norm_nonneg y]

/-- Sums of terms of norm `< 1` have norm `< 1`. -/
theorem cm_sum_lt {ι : Type*} (s : Finset ι) (f : ι → ℚ_[2]) (h : ∀ i ∈ s, ‖f i‖ < 1) :
    ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Sums of terms of norm `≤ 1` have norm `≤ 1`. -/
theorem cm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℚ_[2]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

/-- Integral matrices times integral vectors are integral. -/
theorem cm_mulVec_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℚ_[2]) (v : Fin b → ℚ_[2])
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) (i : Fin a) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine cm_sum_le _ _ fun j _ => ?_
  exact cm_mul1 _ _ (hA i j) (hv j)

/-- Dot products of integral vectors are integral. -/
theorem cm_dot_le {a : ℕ} (v w : Fin a → ℚ_[2]) (hv : ∀ j, ‖v j‖ ≤ 1) (hw : ∀ j, ‖w j‖ ≤ 1) :
    ‖v ⬝ᵥ w‖ ≤ 1 := by
  simp only [dotProduct]
  refine cm_sum_le _ _ fun j _ => ?_
  exact cm_mul1 _ _ (hv j) (hw j)

/-- Products of integral matrices are integral. -/
theorem cm_mul_le {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℚ_[2]) (B : Matrix (Fin b) (Fin c) ℚ_[2])
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i : Fin a) (j : Fin c) : ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine cm_sum_le _ _ fun k _ => ?_
  exact cm_mul1 _ _ (hA i k) (hB k j)

/-- Entries of `Tᵀ F T` as a bilinear form on columns. -/
theorem cm_quad_entry {n : ℕ} (T F : Matrix (Fin n) (Fin n) ℚ_[2]) (i j : Fin n) :
    (Tᵀ * F * T) i j = (fun a => T a i) ⬝ᵥ (F *ᵥ fun b => T b j) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- A block-diagonal matrix times a vector, first block. -/
theorem cm_orth_mulVec_c {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℚ_[2]) (B : Matrix (Fin b) (Fin b) ℚ_[2])
    (v : Fin (a + b) → ℚ_[2]) (i : Fin a) :
    (orthSumMat A B *ᵥ v) (Fin.castAdd b i) = (A *ᵥ fun k => v (Fin.castAdd b k)) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, dyadic_orthSumMat_cc, dyadic_orthSumMat_cn]

/-- A block-diagonal matrix times a vector, second block. -/
theorem cm_orth_mulVec_n {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℚ_[2]) (B : Matrix (Fin b) (Fin b) ℚ_[2])
    (v : Fin (a + b) → ℚ_[2]) (i : Fin b) :
    (orthSumMat A B *ᵥ v) (Fin.natAdd a i) = (B *ᵥ fun k => v (Fin.natAdd a k)) i := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, dyadic_orthSumMat_nc, dyadic_orthSumMat_nn]

/-- Splitting a dot product along `Fin (a + b)`. -/
theorem cm_dot_split {a b : ℕ} (v w : Fin (a + b) → ℚ_[2]) :
    v ⬝ᵥ w = (fun k => v (Fin.castAdd b k)) ⬝ᵥ (fun k => w (Fin.castAdd b k)) +
      (fun k => v (Fin.natAdd a k)) ⬝ᵥ (fun k => w (Fin.natAdd a k)) := by
  simp only [dotProduct, Fin.sum_univ_add]

/-- A unit `t` of `ℤ₂` (viewed in `ℚ₂`): `1 - t` is even and `1 - t²` is divisible by 8. -/
theorem cm_unit_norms (t : ℚ_[2]) (ht : ‖t‖ = 1) : ‖1 - t‖ < 1 ∧ ‖1 - t ^ 2‖ ≤ 1 / 8 := by
  have htz : ‖(⟨t, ht.le⟩ : ℤ_[2])‖ = 1 := ht
  have hU : IsUnit (⟨t, ht.le⟩ : ℤ_[2]) := PadicInt.isUnit_iff.2 htz
  obtain ⟨u₀, hu₀, hd⟩ := dyadic_exists_mod8 hU
  set z : ℤ_[2] := ⟨t, ht.le⟩ with hz
  have hzt : (z : ℚ_[2]) = t := rfl
  obtain ⟨c, hc⟩ := hd
  have hodd : ∃ k : ℤ, u₀ = 2 * k + 1 := by
    rcases hu₀ with h | h | h | h
    · exact ⟨0, by omega⟩
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨3, by omega⟩
  obtain ⟨k, hk⟩ := hodd
  have h8 : ∃ r : ℤ, u₀ ^ 2 = 8 * r + 1 := by
    rcases hu₀ with h | h | h | h
    · exact ⟨0, by subst h; norm_num⟩
    · exact ⟨1, by subst h; norm_num⟩
    · exact ⟨3, by subst h; norm_num⟩
    · exact ⟨6, by subst h; norm_num⟩
  obtain ⟨r, hr⟩ := h8
  constructor
  · have h1 : (1 : ℤ_[2]) - z = -(2 * (k : ℤ_[2])) - 8 * c := by
      have : z = (u₀ : ℤ_[2]) + 2 ^ 3 * c := by rw [← hc]; ring
      rw [this, hk]; push_cast; ring
    have h2 : (2 : ℤ_[2]) ∣ (1 : ℤ_[2]) - z := by
      rw [h1]; exact ⟨-(k : ℤ_[2]) - 4 * c, by ring⟩
    have h3 := (PadicInt.norm_lt_one_iff_dvd (p := 2) _).2 (by exact_mod_cast h2)
    have e : ((1 - z : ℤ_[2]) : ℚ_[2]) = 1 - t := by push_cast; rw [hzt]
    rw [← e]; exact h3
  · have h1 : (1 : ℤ_[2]) - z ^ 2 = -(8 * (r : ℤ_[2])) - (2 ^ 3 * c) * (z + u₀) := by
      have : z = (u₀ : ℤ_[2]) + 2 ^ 3 * c := by rw [← hc]; ring
      have hr' : ((u₀ : ℤ_[2])) ^ 2 = 8 * (r : ℤ_[2]) + 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[2]) hr
      calc (1 : ℤ_[2]) - z ^ 2 = 1 - (u₀ : ℤ_[2]) ^ 2 - (2 ^ 3 * c) * (z + u₀) := by rw [this]; ring_nf
        _ = _ := by rw [hr']; ring
    have h2 : (2 : ℤ_[2]) ^ 3 ∣ (1 : ℤ_[2]) - z ^ 2 := by
      rw [h1]; exact ⟨-(r : ℤ_[2]) - c * (z + u₀), by ring⟩
    have h3 := (PadicInt.norm_le_pow_iff_mem_span_pow _ 3).2 (Ideal.mem_span_singleton.2 (by exact_mod_cast h2))
    have h5 : (((2 : ℕ) : ℝ)) ^ (-((3 : ℕ) : ℤ)) = 1 / 8 := by norm_num
    rw [h5] at h3
    have e : ((1 - z ^ 2 : ℤ_[2]) : ℚ_[2]) = 1 - t ^ 2 := by push_cast; rw [hzt]
    rw [← e]; exact h3


/-- The matrix `⟨u⟩ ⊥ G` of a symmetric `G` is symmetric. -/
theorem mn_symm {m : ℕ} {u : ℚ_[2]} {G : Matrix (Fin m) (Fin m) ℚ_[2]} (h : Gᵀ = G) :
    (orthSumMat !![u] G)ᵀ = orthSumMat !![u] G := by
  rw [orthSumMat_transpose', h]
  congr 1
  ext i j
  fin_cases i; fin_cases j; simp

/-- Row `0` of `⟨u⟩ ⊥ G` applied to a vector. -/
theorem mn_row0 {m : ℕ} {u : ℚ_[2]} (G : Matrix (Fin m) (Fin m) ℚ_[2]) (v : Fin (1 + m) → ℚ_[2]) :
    (orthSumMat !![u] G *ᵥ v) (Fin.castAdd m 0) = u * v (Fin.castAdd m 0) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  simp [dyadic_orthSumMat_cc, dyadic_orthSumMat_cn]

/-- The Gram value of the first basis vector. -/
theorem mn_b_norm {m : ℕ} {u : ℚ_[2]} (G : Matrix (Fin m) (Fin m) ℚ_[2]) :
    (Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) ⬝ᵥ
      (orthSumMat !![u] G *ᵥ (Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2])) = u := by
  rw [single_dotProduct, mn_row0]
  simp

/-- Reflection route: an integral reflection exists, hence the complements are equivalent. -/
theorem refl_route {m : ℕ} {u : ℚ_[2]} (hu : ‖u‖ = 1) {G1 G2 : Matrix (Fin m) (Fin m) ℚ_[2]}
    (h₁ : G1ᵀ = G1) (hi₁ : IsClassIntegral G1)
    (T : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]) (hT : UM T)
    (heq : Tᵀ * orthSumMat !![u] G1 * T = orthSumMat !![u] G2)
    (ha0 : u - u * T (Fin.castAdd m 0) (Fin.castAdd m 0) ≠ 0)
    (hint : ∀ x y, ‖(((Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) -
        fun z => T z (Fin.castAdd m 0)) x) *
        ((orthSumMat !![u] G1 *ᵥ (((Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) -
        fun z => T z (Fin.castAdd m 0)))) y) / (u - u * T (Fin.castAdd m 0) (Fin.castAdd m 0))‖ ≤ 1) :
    ZpEquiv G1 G2 := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact zero_ne_one hu
  set Φ := orthSumMat !![u] G1 with hΦ
  set b : Fin (1 + m) → ℚ_[2] := Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) with hb
  set c : Fin (1 + m) → ℚ_[2] := fun z => T z (Fin.castAdd m 0) with hc
  have hΦs : Φᵀ = Φ := mn_symm h₁
  have hcT : c = T *ᵥ b := by
    ext x
    simp [hc, hb, Matrix.mulVec_single_one]
  have hbb : b ⬝ᵥ (Φ *ᵥ b) = u := mn_b_norm G1
  have hcc : c ⬝ᵥ (Φ *ᵥ c) = u := by
    have h1 : c ⬝ᵥ (Φ *ᵥ c) = b ⬝ᵥ ((Tᵀ * Φ * T) *ᵥ b) := by
      have key : ∀ y, (T *ᵥ b) ⬝ᵥ y = b ⬝ᵥ (Tᵀ *ᵥ y) := by
        intro y
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      rw [hcT, key]
      simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    rw [h1, heq, mn_b_norm]
  have hbc : b ⬝ᵥ (Φ *ᵥ c) = u * T (Fin.castAdd m 0) (Fin.castAdd m 0) := by
    rw [single_dotProduct, mn_row0]
    simp [hc]
  obtain ⟨σ, hσ, hσΦ, hσc⟩ := refl_exists Φ hΦs b c (by rw [hbb, hcc]) (u - u * T (Fin.castAdd m 0) (Fin.castAdd m 0))
    (by rw [hbb, hbc]) ha0 hint
  have hS : UM (σ * T) := UM.mul hσ hT
  have h0 : ∀ x, (σ * T) x (Fin.castAdd m 0) = if x = Fin.castAdd m 0 then 1 else 0 := by
    intro x
    have := congrFun hσc x
    rw [hcT] at this
    simp only [Matrix.mulVec_mulVec] at this
    rw [← Matrix.mulVec_mulVec] at this
    have h2 : (σ * T) x (Fin.castAdd m 0) = ((σ * T) *ᵥ b) x := by
      simp [hb, Matrix.mulVec_single_one]
    rw [h2, Matrix.mulVec_mulVec] at *
    simpa [hb, Pi.single_apply] using this
  refine RL hu0 (σ * T) hS h0 ?_
  rw [Matrix.transpose_mul]
  calc Tᵀ * σᵀ * Φ * (σ * T) = Tᵀ * (σᵀ * Φ * σ) * T := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hσΦ, ← heq]

/-- Ultrametric inequality for differences. -/
theorem mn_sub_le (x y : ℚ_[2]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)

/-- Block sums of integral matrices are integral. -/
theorem mn_Phi_int {m : ℕ} {u : ℚ_[2]} {G : Matrix (Fin m) (Fin m) ℚ_[2]} (hu : ‖u‖ ≤ 1)
    (hG : ∀ i j, ‖G i j‖ ≤ 1) (i j : Fin (1 + m)) : ‖orthSumMat !![u] G i j‖ ≤ 1 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [dyadic_orthSumMat_cc]
    fin_cases i
    fin_cases j
    simpa using hu
  · rw [dyadic_orthSumMat_cn, norm_zero]; exact zero_le_one
  · rw [dyadic_orthSumMat_nc, norm_zero]; exact zero_le_one
  · rw [dyadic_orthSumMat_nn]; exact hG _ _

/-- Integral matrices send integral vectors to integral vectors. -/
theorem mn_mulVec_int {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ_[2]} {v : Fin n → ℚ_[2]}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (i : Fin n) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _ _) (norm_nonneg _) (hv _)

/-- `e_0 - c` is integral when `T` is. -/
theorem mn_w_int {m : ℕ} {T : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]} (hT : ∀ i j, ‖T i j‖ ≤ 1)
    (x : Fin (1 + m)) :
    ‖(((Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) - fun z => T z (Fin.castAdd m 0)) x)‖ ≤ 1 := by
  simp only [Pi.sub_apply]
  refine (mn_sub_le _ _).trans (max_le ?_ (hT _ _))
  by_cases h : x = Fin.castAdd m 0
  · subst h; simp
  · simp [Pi.single_apply, h]

/-- A norm less than one is at most one half. -/
theorem mn_le_half {x : ℚ_[2]} (h : ‖x‖ < 1) : ‖x‖ ≤ 1 / 2 := by
  have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one x (-1)).2 (by norm_num; exact h)
  norm_num at this
  exact this

/-- A unit `t` of `ℤ₂` satisfies `‖1 - t‖ ≤ 1/2` and `‖1 + t‖ ≤ 1/2`. -/
theorem mn_unit_sub {t : ℚ_[2]} (ht : ‖t‖ = 1) : ‖1 - t‖ ≤ 1 / 2 ∧ ‖1 + t‖ ≤ 1 / 2 := by
  obtain ⟨w, u₀, hw, -, hu₀, h8⟩ := dyadic_exists_lift ht
  have h2 : (2 : ℤ_[2]) ∣ w - u₀ := (dvd_pow_self (2 : ℤ_[2]) (by norm_num : 3 ≠ 0)).trans h8
  have hm : (2 : ℤ) ∣ u₀ - 1 := by rcases hu₀ with rfl | rfl | rfl | rfl <;> decide
  have hp : (2 : ℤ) ∣ u₀ + 1 := by rcases hu₀ with rfl | rfl | rfl | rfl <;> decide
  have hm' : (2 : ℤ_[2]) ∣ ((u₀ : ℤ_[2]) - 1) := by
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, by exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[2]) hk⟩
  have hp' : (2 : ℤ_[2]) ∣ ((u₀ : ℤ_[2]) + 1) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, by exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[2]) hk⟩
  have d1 : (2 : ℤ_[2]) ∣ w - 1 := by
    have := dvd_add h2 hm'
    simpa using this
  have d2 : (2 : ℤ_[2]) ∣ w + 1 := by
    have := dvd_sub (dvd_add h2 hp') (dvd_refl (2 : ℤ_[2]))
    have e : w - (u₀ : ℤ_[2]) + ((u₀ : ℤ_[2]) + 1) - 2 = w - 1 := by ring
    have e2 : w + 1 = (w - (u₀ : ℤ_[2]) + ((u₀ : ℤ_[2]) + 1)) := by ring
    rw [e2]
    exact dvd_add h2 hp'
  have n1 := (PadicInt.norm_lt_one_iff_dvd (p := 2) (w - 1)).2 (by simpa using d1)
  have n2 := (PadicInt.norm_lt_one_iff_dvd (p := 2) (w + 1)).2 (by simpa using d2)
  rw [PadicInt.norm_def] at n1 n2
  push_cast at n1 n2
  rw [hw] at n1 n2
  constructor
  · rw [← norm_neg]; simpa using mn_le_half n1
  · rw [add_comm]; exact mn_le_half n2

/-- Choice of a sign making `‖1 - ε t‖ = 1/2` for a unit `t`. -/
theorem mn_sign {t : ℚ_[2]} (ht : ‖t‖ = 1) : ∃ ε : ℚ_[2], (ε = 1 ∨ ε = -1) ∧ ‖1 - ε * t‖ = 1 / 2 := by
  obtain ⟨h1, h2⟩ := mn_unit_sub ht
  by_cases h : ‖1 - t‖ = 1 / 2
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have hlt : ‖1 - t‖ < 1 / 2 := lt_of_le_of_ne h1 h
    have h2n : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
      have := Padic.norm_p (p := 2)
      simpa using this
    have hsum : (2 : ℚ_[2]) = (1 - t) + (1 + t) := by ring
    have hle : ‖(2 : ℚ_[2])‖ ≤ max ‖1 - t‖ ‖1 + t‖ := by
      rw [hsum]; exact IsUltrametricDist.norm_add_le_max _ _
    rw [h2n] at hle
    have : 1 / 2 ≤ ‖1 + t‖ := by
      rcases le_max_iff.1 hle with h3 | h3
      · exact absurd hlt (not_lt.2 h3)
      · exact h3
    have e : (1 : ℚ_[2]) - -1 * t = 1 + t := by ring
    rw [e]
    exact le_antisymm h2 this

end QuadFormsKB.Cassels.Lemma42
