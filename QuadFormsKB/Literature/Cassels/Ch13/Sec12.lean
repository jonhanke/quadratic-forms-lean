/-
# Cassels, Chapter 13, §12: effectiveness (Siegel's algorithm)

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §12, *Effectiveness*, pp. 324–327: the set
$\mathfrak M(f)$ of Hermite majorants of $f$ (Lemmas 12.1, 12.2 and Corollary), bounds for Hermite-reduced forms
(Lemma 12.3 and Corollary), the sets $\mathfrak M(f; h)$ (12.2)–(12.3) (Lemmas 12.4, 12.5) and Siegel's bound for an
equivalence between Hermite-reduced forms (Theorem 12.1).

**Effectivity.** Cassels' statements say that certain constants "can be effectively calculated". The Lean
statements give the existence of the constants (depending only on the stated data); the effective computability,
which follows from the proofs, is not formalized.

Conventions as in `Ch13/Sec2.lean`; `img T` $= T\mathfrak R$ is the image of the Minkowski-reduced forms under
$T \in \mathrm{GL}_n(\mathbb{Z})$ (Ch. 12, §7); $T^{-1}g$ is the form $g(T^{-1}\vec{x})$, i.e. `act T⁻¹ G`.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec11
import QuadFormsKB.Literature.Cassels.Ch12.Sec7

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-! ### Helpers: the converse of Lemma 11.1 -/

section Aux
open scoped MatrixOrder

/-- Helper: a positive semidefinite real matrix has a symmetric square root (as in `Ch13/Sec10.lean`). -/
private theorem exists_symm_sqrt' {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) (hP : P.PosSemidef) :
    ∃ S : Matrix (Fin k) (Fin k) ℝ, Sᵀ = S ∧ S * S = P := by
  refine ⟨CFC.sqrt P, ?_, ?_⟩
  · have := (CFC.sqrt_nonneg P).posSemidef.isHermitian
    simpa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using this
  · rw [← sq]; exact CFC.sq_sqrt P

end Aux

/-- Helper: a symmetric real matrix $Q$ with $Q^2 = 1$ is $U\operatorname{diag}(\varepsilon)U^{\mathsf T}$ with $U$
orthogonal and $\varepsilon_i = \pm 1$ (spectral theorem). -/
private theorem exists_orth_diag_sign {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Qᵀ = Q) (hQQ : Q * Q = 1) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ), U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
      (∀ i, ε i = 1 ∨ ε i = -1) ∧ Q = U * diagonal ε * Uᵀ := by
  classical
  have hH : Q.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hQ
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  set lam := hH.eigenvalues with hlam
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [hUdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hUU' : Uᵀ * U = 1 := by
    have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [hUdef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hspec : Q = U * diagonal lam * Uᵀ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hUdef, hlam, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  refine ⟨U, lam, hUU, hUU', fun i => ?_, hspec⟩
  have h2 : diagonal (fun i => lam i * lam i) = 1 := by
    have : Uᵀ * (Q * Q) * U = diagonal (fun i => lam i * lam i) := by
      rw [hspec]
      calc Uᵀ * (U * diagonal lam * Uᵀ * (U * diagonal lam * Uᵀ)) * U
          = (Uᵀ * U) * diagonal lam * (Uᵀ * U) * diagonal lam * (Uᵀ * U) := by
            simp only [Matrix.mul_assoc]
        _ = diagonal (fun i => lam i * lam i) := by
            simp only [hUU', Matrix.one_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    rw [← this, hQQ]; simp [hUU']
  have h3 : lam i * lam i = 1 := by
    have := congrFun (congrFun h2 i) i
    simpa using this
  have : (lam i - 1) * (lam i + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · left; linarith
  · right; linarith

/-- Helper (converse of Lemma 11.1): if $G$ is positive definite and $FG^{-1}F = G$ with $F$ symmetric, then
$G$ is a Hermite majorant of $F$. -/
private theorem isHermiteMajorant_of_inv {F G : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hG : G.PosDef)
    (h : F * G⁻¹ * F = G) : IsHermiteMajorant F G := by
  classical
  obtain ⟨L, hLs, hLL⟩ := exists_symm_sqrt' G hG.posSemidef
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  have hLu : IsUnit L.det := by
    rw [← hLL, Matrix.det_mul] at hGu
    exact isUnit_of_mul_isUnit_left hGu
  have hLi : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hLu
  have hLi' : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hLu
  have hGi : G⁻¹ = L⁻¹ * L⁻¹ := by rw [← hLL, Matrix.mul_inv_rev]
  have hLis : (L⁻¹)ᵀ = L⁻¹ := by rw [Matrix.transpose_nonsing_inv, hLs]
  have hFs : Fᵀ = F := hF
  set Q : Matrix (Fin n) (Fin n) ℝ := L⁻¹ * F * L⁻¹ with hQdef
  have hQs : Qᵀ = Q := by
    rw [hQdef, Matrix.transpose_mul, Matrix.transpose_mul, hLis, hFs, Matrix.mul_assoc]
  have hQQ : Q * Q = 1 := by
    calc Q * Q = L⁻¹ * (F * (L⁻¹ * L⁻¹) * F) * L⁻¹ := by simp only [hQdef, Matrix.mul_assoc]
      _ = L⁻¹ * G * L⁻¹ := by rw [← hGi, h]
      _ = 1 := by
        rw [← hLL]
        calc L⁻¹ * (L * L) * L⁻¹ = (L⁻¹ * L) * (L * L⁻¹) := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hLi, hLi', Matrix.mul_one]
  obtain ⟨U, ε, hUU, hUU', hε, hQU⟩ := exists_orth_diag_sign hQs hQQ
  have hUu : IsUnit U.det := Matrix.isUnit_det_of_right_inverse hUU
  have hUtu : IsUnit (Uᵀ).det := by rwa [Matrix.det_transpose]
  refine ⟨Uᵀ * L, ε, ?_, hε, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hUtu.mul hLu
  · have hFQ : F = L * Q * L := by
      calc F = (L * L⁻¹) * F * (L⁻¹ * L) := by rw [hLi, hLi', Matrix.one_mul, Matrix.mul_one]
        _ = L * Q * L := by simp only [hQdef, Matrix.mul_assoc]
    rw [hFQ, hQU]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hLs, Matrix.mul_assoc]
  · rw [← hLL]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hLs, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U, hUU, Matrix.one_mul]

/-! ### Helpers: Sylvester's law and Lemma 12.2 -/

/-- Helper: the value of $L^{\mathsf T}\operatorname{diag}(\varepsilon)L$ is $\sum_i \varepsilon_i (L\vec{y})_i^2$. -/
private theorem val_conj_diag (L : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ) (y : Fin n → ℝ) :
    val (Lᵀ * diagonal ε * L) y = ∑ i, ε i * (L *ᵥ y) i ^ 2 := by
  rw [val_conj, val_diagonal]

/-- Helper: a representation $F = L^{\mathsf T}\operatorname{diag}(\varepsilon)L$ of a regular $F$ has $L$ invertible. -/
private theorem isUnit_of_rep {F L : Matrix (Fin n) (Fin n) ℝ} {ε : Fin n → ℝ} (hdet : F.det ≠ 0)
    (hF : Lᵀ * diagonal ε * L = F) : IsUnit L.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hdet
  rw [← hF, Matrix.det_mul, Matrix.det_mul, h0]; simp

/-- Helper: the number of positive signs is determined by $F$ (Sylvester's law of inertia). -/
private theorem ncard_pos_eq {F L L₀ : Matrix (Fin n) (Fin n) ℝ} {ε ε₀ : Fin n → ℝ} (hdet : F.det ≠ 0)
    (hF : Lᵀ * diagonal ε * L = F) (hF₀ : L₀ᵀ * diagonal ε₀ * L₀ = F) :
    {i | 0 < ε i}.ncard = {i | 0 < ε₀ i}.ncard := by
  have hL := isUnit_of_rep hdet hF
  have hL₀ := isUnit_of_rep hdet hF₀
  set C := L * L₀⁻¹ with hCdef
  have hC : IsUnit C.det := Matrix.isUnit_det_of_right_inverse (B := L₀ * L⁻¹) (by
    rw [hCdef, Matrix.mul_assoc, ← Matrix.mul_assoc L₀⁻¹, Matrix.nonsing_inv_mul _ hL₀, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hL])
  have hCinv : Invertible C := Matrix.invertibleOfIsUnitDet C hC
  have e : QuadraticMap.Equivalent (QuadraticMap.weightedSumSquares ℝ ε₀)
      (QuadraticMap.weightedSumSquares ℝ ε) := by
    refine ⟨⟨Matrix.toLinearEquiv' C hCinv, fun y => ?_⟩⟩
    have h1 : ∑ i, ε i * (L *ᵥ (L₀⁻¹ *ᵥ y)) i ^ 2 = ∑ i, ε₀ i * y i ^ 2 := by
      rw [← val_conj_diag, hF, ← hF₀, val_conj_diag, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL₀,
        Matrix.one_mulVec]
    rw [Matrix.mulVec_mulVec] at h1
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    change ∑ x, ε x * ((C *ᵥ y) x * (C *ᵥ y) x) = ∑ x, ε₀ x * (y x * y x)
    simpa [pow_two] using h1
  have h1 := QuadraticForm.sigPos_of_equiv_weightedSumSquares e
  have h2 := QuadraticForm.sigPos_of_equiv_weightedSumSquares (Q := QuadraticMap.weightedSumSquares ℝ ε₀)
    (w := ε₀) ⟨QuadraticMap.IsometryEquiv.refl _⟩
  exact h1.symm.trans h2

/-- Helper: sign vectors with the same number of positive entries differ by a permutation. -/
private theorem exists_perm_signs {ε ε₀ : Fin n → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hε₀ : ∀ i, ε₀ i = 1 ∨ ε₀ i = -1) (h : {i | 0 < ε i}.ncard = {i | 0 < ε₀ i}.ncard) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, ε₀ i = ε (σ i) := by
  classical
  have hs : ∀ x : ℝ, (x = 1 ∨ x = -1) → (0 < x ↔ x = 1) := by
    rintro x (rfl | rfl) <;> norm_num
  set p : Fin n → Prop := fun i => 0 < ε i with hp
  set p₀ : Fin n → Prop := fun i => 0 < ε₀ i with hp₀
  have hc : Fintype.card {i // p₀ i} = Fintype.card {i // p i} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have h1 : Nat.card {i // p i} = {i | 0 < ε i}.ncard := Nat.card_coe_set_eq _
    have h2 : Nat.card {i // p₀ i} = {i | 0 < ε₀ i}.ncard := Nat.card_coe_set_eq _
    rw [h1, h2, h]
  have hc' : Fintype.card {i // ¬ p₀ i} = Fintype.card {i // ¬ p i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hc]
  let e₁ := Fintype.equivOfCardEq hc
  let e₂ := Fintype.equivOfCardEq hc'
  let σ : Equiv.Perm (Fin n) :=
    (Equiv.sumCompl p₀).symm.trans ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl p))
  refine ⟨σ, fun i => ?_⟩
  by_cases hi : p₀ i
  · have h1 : σ i = (e₁ ⟨i, hi⟩).1 := by
      simp [σ, Equiv.sumCompl_symm_apply_of_pos hi]
    have h2 : p (σ i) := by rw [h1]; exact (e₁ ⟨i, hi⟩).2
    rw [(hs _ (hε₀ i)).1 hi, (hs _ (hε _)).1 h2]
  · have h1 : σ i = (e₂ ⟨i, hi⟩).1 := by
      simp [σ, Equiv.sumCompl_symm_apply_of_neg hi]
    have h2 : ¬ p (σ i) := by rw [h1]; exact (e₂ ⟨i, hi⟩).2
    have h3 : ε₀ i = -1 := by
      rcases hε₀ i with h | h
      · exact absurd (by show 0 < ε₀ i; rw [h]; norm_num) hi
      · exact h
    have h4 : ε (σ i) = -1 := by
      rcases hε (σ i) with h | h
      · exact absurd (by show 0 < ε (σ i); rw [h]; norm_num) h2
      · exact h
    rw [h3, h4]

/-- Helper: permuting the rows of $L$ together with the signs. -/
private theorem submatrix_rep (L : Matrix (Fin n) (Fin n) ℝ) (ε ε₀ : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (h : ∀ i, ε₀ i = ε (σ i)) :
    (L.submatrix σ id)ᵀ * diagonal ε₀ * L.submatrix σ id = Lᵀ * diagonal ε * L ∧
      (L.submatrix σ id)ᵀ * L.submatrix σ id = Lᵀ * L := by
  have key : ∀ (e : Fin n → ℝ) (f : Fin n → ℝ) (hf : ∀ i, f i = e (σ i)) (a b : Fin n),
      ((L.submatrix σ id)ᵀ * diagonal f * L.submatrix σ id) a b = (Lᵀ * diagonal e * L) a b := by
    intro e f hf a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.submatrix_apply, id]
    exact Fintype.sum_equiv σ _ _ (fun i => by rw [hf])
  constructor
  · ext a b; exact key ε ε₀ h a b
  · have h1 : ∀ M : Matrix (Fin n) (Fin n) ℝ, Mᵀ * M = Mᵀ * diagonal (fun _ => (1 : ℝ)) * M := by
      intro M; simp
    rw [h1, h1 L]
    ext a b
    exact key (fun _ => 1) (fun _ => 1) (fun _ => rfl) a b

/-! ### Helpers: connectedness via the Cayley transform -/

/-- Helper: $0 \le w \cdot w$. -/
private theorem dot_self_nonneg'' (w : Fin n → ℝ) : 0 ≤ w ⬝ᵥ w := by
  simpa using dotProduct_self_star_nonneg w

/-- Helper: $X$ is a strict contraction: $|X\vec{u}| < |\vec{u}|$ for $\vec{u} \ne 0$. -/
private def Contr (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ u : Fin n → ℝ, u ≠ 0 → (X *ᵥ u) ⬝ᵥ (X *ᵥ u) < u ⬝ᵥ u

private theorem Contr.neg {X : Matrix (Fin n) (Fin n) ℝ} (h : Contr X) : Contr (-X) := by
  intro u hu
  simpa [Matrix.neg_mulVec] using h u hu

/-- Helper: $1 - X$ is invertible for a strict contraction $X$. -/
private theorem Contr.isUnit_det {X : Matrix (Fin n) (Fin n) ℝ} (h : Contr X) : IsUnit (1 - X).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have h1 : (1 - X) *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
  by_contra hne
  have hw : u - v ≠ 0 := sub_ne_zero.2 hne
  have := h _ hw
  rw [← h1] at this
  exact lt_irrefl _ this

private theorem Contr.convex_combo {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : Contr X) (hY : Contr Y) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : Contr (a • X + b • Y) := by
  intro u hu
  have h1 := hX u hu
  have h2 := hY u hu
  have hd := dot_self_nonneg'' (X *ᵥ u - Y *ᵥ u)
  set x := X *ᵥ u
  set y := Y *ᵥ u
  have hlin : (a • X + b • Y) *ᵥ u = a • x + b • y := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  rw [hlin]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    sub_dotProduct, dotProduct_sub] at hd ⊢
  rw [dotProduct_comm y x] at hd ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key : a * (x ⬝ᵥ x) + (1 - a) * (y ⬝ᵥ y) < u ⬝ᵥ u := by
    by_cases ha0 : a = 0
    · subst ha0; simpa using h2
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith [mul_lt_mul_of_pos_left h1 hapos, mul_le_mul_of_nonneg_left h2.le hb]
  nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) hd]

/-- Helper: $GDG = D$ and $D^2 = 1$ give $DG^{-1}D = G$. -/
private theorem conj_inv_of_GDG {D G : Matrix (Fin n) (Fin n) ℝ} (hDD : D * D = 1) (h : G * D * G = D) :
    D * G⁻¹ * D = G := by
  have h1 : G * (D * G * D) = 1 := by
    calc G * (D * G * D) = (G * D * G) * D := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, hDD]
  have h2 : G⁻¹ = D * G * D := Matrix.inv_eq_right_inv h1
  rw [h2]
  calc D * (D * G * D) * D = (D * D) * G * (D * D) := by simp only [Matrix.mul_assoc]
    _ = G := by rw [hDD, Matrix.one_mul, Matrix.mul_one]

/-- Helper: $DG^{-1}D = G$ and $D^2 = 1$ give $GDG = D$. -/
private theorem GDG_of_conj_inv {D G : Matrix (Fin n) (Fin n) ℝ} (hDD : D * D = 1) (hGu : IsUnit G.det)
    (h : D * G⁻¹ * D = G) : G * D * G = D := by
  have h2 : G⁻¹ = D * G * D := by
    calc G⁻¹ = (D * D) * G⁻¹ * (D * D) := by rw [hDD, Matrix.one_mul, Matrix.mul_one]
      _ = D * (D * G⁻¹ * D) * D := by simp only [Matrix.mul_assoc]
      _ = D * G * D := by rw [h]
  have h1 : G * (D * G * D) = 1 := by rw [← h2]; exact Matrix.mul_nonsing_inv _ hGu
  calc G * D * G = (G * (D * G * D)) * D := by
        calc G * D * G = G * D * G * (D * D) := by rw [hDD, Matrix.mul_one]
          _ = (G * (D * G * D)) * D := by simp only [Matrix.mul_assoc]
    _ = D := by rw [h1, Matrix.one_mul]

/-- Helper: the Cayley transform $(1+X)(1-X)^{-1}$ of a strict contraction $X$ anticommuting with $D$ is a Hermite
majorant of $D$ (for $D$ symmetric with $D^2 = 1$). -/
private theorem cayley_isHermiteMajorant {D X : Matrix (Fin n) (Fin n) ℝ} (hDs : Dᵀ = D) (hDD : D * D = 1)
    (hX : Xᵀ = X) (hXD : X * D = -(D * X)) (hc : Contr X) :
    IsHermiteMajorant D ((1 + X) * (1 - X)⁻¹) := by
  have hAu : IsUnit (1 - X).det := hc.isUnit_det
  have hBu : IsUnit (1 + X).det := by
    have := hc.neg.isUnit_det
    simpa [sub_neg_eq_add] using this
  set A : Matrix (Fin n) (Fin n) ℝ := 1 - X with hA
  set B : Matrix (Fin n) (Fin n) ℝ := 1 + X with hB
  have hAs : Aᵀ = A := by simp [hA, Matrix.transpose_sub, hX]
  have hAB : A * B = B * A := by
    simp only [hA, hB, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_one]
    abel
  have hDX : D * X = -(X * D) := by rw [hXD, neg_neg]
  have hAD : A * D = D * B := by
    show (1 - X) * D = D * (1 + X)
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hXD]
    abel
  have hBD : B * D = D * A := by
    show (1 + X) * D = D * (1 - X)
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hXD]
    abel
  have hAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hAu
  have hAi' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hAu
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have hBi' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBu
  set G : Matrix (Fin n) (Fin n) ℝ := B * A⁻¹ with hG
  have e1 : A⁻¹ * D = D * B⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (B * B⁻¹) := by rw [hBi, Matrix.mul_one]
      _ = A⁻¹ * (D * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * D) * B⁻¹ := by rw [hAD]
      _ = D * B⁻¹ := by rw [← Matrix.mul_assoc A⁻¹, hAi', Matrix.one_mul]
  have hGDG : G * D * G = D := by
    calc G * D * G = B * (A⁻¹ * D) * B * A⁻¹ := by simp only [hG, Matrix.mul_assoc]
      _ = B * D * (B⁻¹ * B) * A⁻¹ := by rw [e1]; simp only [Matrix.mul_assoc]
      _ = D * A * A⁻¹ := by rw [hBi', Matrix.mul_one, hBD]
      _ = D := by rw [Matrix.mul_assoc, hAi, Matrix.mul_one]
  have hGs : Gᵀ = G := by
    have hcomm : A⁻¹ * B = B * A⁻¹ := by
      calc A⁻¹ * B = A⁻¹ * B * (A * A⁻¹) := by rw [hAi, Matrix.mul_one]
        _ = A⁻¹ * (B * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
        _ = A⁻¹ * (A * B) * A⁻¹ := by rw [hAB]
        _ = B * A⁻¹ := by rw [← Matrix.mul_assoc A⁻¹, hAi', Matrix.one_mul]
    have hBs : Bᵀ = B := by simp [hB, Matrix.transpose_add, hX]
    rw [hG, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hAs, hBs, hcomm]
  have hGp : G.PosDef := by
    rw [posDef_iff]
    refine ⟨hGs, fun v hv => ?_⟩
    set w := A⁻¹ *ᵥ v with hw
    have hvw : v = A *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hAi, Matrix.one_mulVec]
    have hw0 : w ≠ 0 := by
      intro h0; apply hv; rw [hvw, h0, Matrix.mulVec_zero]
    have hGv : G *ᵥ v = B *ᵥ w := by rw [hG, ← Matrix.mulVec_mulVec]
    have hdot : (A *ᵥ w) ⬝ᵥ (B *ᵥ w) = w ⬝ᵥ w - (X *ᵥ w) ⬝ᵥ (X *ᵥ w) := by
      simp only [hA, hB, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, sub_dotProduct,
        dotProduct_add]
      rw [dotProduct_comm (X *ᵥ w) w]; ring
    show 0 < v ⬝ᵥ (G *ᵥ v)
    rw [hGv, hvw, hdot]
    have := hc w hw0
    linarith
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 hGp.isUnit
  exact isHermiteMajorant_of_inv (by simpa [Matrix.IsSymm] using hDs) hGp
    (conj_inv_of_GDG hDD hGDG)

/-- Helper: every positive definite $G$ with $DG^{-1}D = G$ is the Cayley transform of a strict contraction $X$
anticommuting with $D$ (namely $X = (G+1)^{-1}(G-1)$). -/
private theorem exists_cayley {D G : Matrix (Fin n) (Fin n) ℝ} (hDD : D * D = 1) (hG : G.PosDef)
    (h : D * G⁻¹ * D = G) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, Xᵀ = X ∧ X * D = -(D * X) ∧ Contr X ∧ (1 + X) * (1 - X)⁻¹ = G := by
  have hGu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  obtain ⟨hGs', hGpos⟩ := (posDef_iff G).1 hG
  have hGs : Gᵀ = G := hGs'
  have hGDG : G * D * G = D := GDG_of_conj_inv hDD hGu h
  have hGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hGu
  have hGi' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
  have hGD : G * D = D * G⁻¹ := by
    calc G * D = G * D * (G * G⁻¹) := by rw [hGi, Matrix.mul_one]
      _ = (G * D * G) * G⁻¹ := by simp only [Matrix.mul_assoc]
      _ = D * G⁻¹ := by rw [hGDG]
  set P : Matrix (Fin n) (Fin n) ℝ := G + 1 with hP
  set R : Matrix (Fin n) (Fin n) ℝ := G - 1 with hR
  have hPpos : P.PosDef := by
    rw [posDef_iff]
    refine ⟨?_, fun x hx => ?_⟩
    · show (G + 1)ᵀ = G + 1
      rw [Matrix.transpose_add, hGs, Matrix.transpose_one]
    · have h1 := hGpos x hx
      have h2 : 0 < x ⬝ᵥ x := by
        have := dotProduct_self_star_pos_iff.mpr hx
        simpa using this
      simp only [val, hP, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add] at h1 ⊢
      linarith
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hPpos.isUnit
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPu
  have hPi' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hPu
  have hRP : R * P = P * R := by
    simp only [hR, hP, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul,
      Matrix.mul_one]
    abel
  set X : Matrix (Fin n) (Fin n) ℝ := P⁻¹ * R with hX
  have hPX : P * X = R := by rw [hX, ← Matrix.mul_assoc, hPi, Matrix.one_mul]
  have hXP : X * P = R := by rw [hX, Matrix.mul_assoc, hRP, ← Matrix.mul_assoc, hPi', Matrix.one_mul]
  have hXs : Xᵀ = X := by
    have hPs : Pᵀ = P := by rw [hP, Matrix.transpose_add, hGs, Matrix.transpose_one]
    have hRs : Rᵀ = R := by rw [hR, Matrix.transpose_sub, hGs, Matrix.transpose_one]
    have : X = R * P⁻¹ := by
      calc X = P⁻¹ * R * (P * P⁻¹) := by rw [hX, hPi, Matrix.mul_one]
        _ = P⁻¹ * (R * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P⁻¹ * (P * R) * P⁻¹ := by rw [hRP]
        _ = R * P⁻¹ := by rw [← Matrix.mul_assoc P⁻¹, hPi', Matrix.one_mul]
    rw [hX, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hPs, hRs]
    exact this.symm
  have hPD : P * D = D * G⁻¹ * P := by
    calc P * D = G * D + D := by rw [hP, Matrix.add_mul, Matrix.one_mul]
      _ = D * G⁻¹ + D := by rw [hGD]
      _ = D * G⁻¹ * (G + 1) := by
          rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc, hGi', Matrix.mul_one, add_comm]
  have hRD : R * D = D * (G⁻¹ - 1) := by
    rw [hR, Matrix.sub_mul, Matrix.one_mul, hGD, Matrix.mul_sub, Matrix.mul_one]
  have hanti : X * D = -(D * X) := by
    have h1 : P * (X * D) = P * (-(D * X)) := by
      calc P * (X * D) = R * D := by rw [← Matrix.mul_assoc, hPX]
        _ = D * (G⁻¹ - 1) := hRD
        _ = -(D * G⁻¹ * R) := by
          have e : G⁻¹ * R = 1 - G⁻¹ := by rw [hR, Matrix.mul_sub, hGi', Matrix.mul_one]
          rw [Matrix.mul_assoc, e, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one]
          abel
        _ = P * (-(D * X)) := by
          rw [Matrix.mul_neg, ← Matrix.mul_assoc, hPD, Matrix.mul_assoc _ P, hPX]
    calc X * D = P⁻¹ * (P * (X * D)) := by rw [← Matrix.mul_assoc, hPi', Matrix.one_mul]
      _ = P⁻¹ * (P * (-(D * X))) := by rw [h1]
      _ = -(D * X) := by rw [← Matrix.mul_assoc, hPi', Matrix.one_mul]
  have hc : Contr X := by
    intro u hu
    set w := P⁻¹ *ᵥ u with hw
    have huw : u = P *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hPi, Matrix.one_mulVec]
    have hw0 : w ≠ 0 := by
      intro h0; apply hu; rw [huw, h0, Matrix.mulVec_zero]
    have hXu : X *ᵥ u = R *ᵥ w := by rw [huw, Matrix.mulVec_mulVec, hXP]
    have hpos := hGpos w hw0
    simp only [val] at hpos
    have hPw : P *ᵥ w = G *ᵥ w + w := by rw [hP, Matrix.add_mulVec, Matrix.one_mulVec]
    have hRw : R *ᵥ w = G *ᵥ w - w := by rw [hR, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hXu]
    rw [huw, hPw, hRw]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm (G *ᵥ w) w]
    linarith
  refine ⟨X, hXs, hanti, hc, ?_⟩
  have h1 : 1 + X = G * (1 - X) := by
    have : P * X = R := hPX
    rw [hP, hR, Matrix.add_mul, Matrix.one_mul] at this
    rw [Matrix.mul_sub, Matrix.mul_one]
    have h2 : X + G * X = G - 1 := by rw [add_comm]; exact this
    -- 1 + X = G - G X
    have h3 : G * X = G - 1 - X := by rw [← h2]; abel
    rw [h3]; abel
  rw [h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hc.isUnit_det, Matrix.mul_one]

/-- Helper: the Hermite majorants of a diagonal sign form $D$ form a preconnected set: they are the image of the
convex set of strict contractions anticommuting with $D$ under the (continuous) Cayley transform. -/
private theorem isPreconnected_majorants_diag {ε : Fin n → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    IsPreconnected {G : Matrix (Fin n) (Fin n) ℝ | IsHermiteMajorant (diagonal ε) G} := by
  set D : Matrix (Fin n) (Fin n) ℝ := diagonal ε with hD
  have hDs : Dᵀ = D := Matrix.diagonal_transpose ε
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; rcases hε i with h | h <;> simp [h]
    · simp [hij]
  set dom : Set (Matrix (Fin n) (Fin n) ℝ) := {X | Xᵀ = X ∧ X * D = -(D * X) ∧ Contr X} with hdom
  have hconv : Convex ℝ dom := by
    intro X hX Y hY a b ha hb hab
    refine ⟨?_, ?_, hX.2.2.convex_combo hY.2.2 ha hb hab⟩
    · simp [Matrix.transpose_add, Matrix.transpose_smul, hX.1, hY.1]
    · rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hX.2.1, hY.2.1, Matrix.mul_add,
        Matrix.mul_smul, Matrix.mul_smul]
      simp only [smul_neg]
      abel
  have hcont : ContinuousOn (fun X : Matrix (Fin n) (Fin n) ℝ => (1 + X) * (1 - X)⁻¹) dom := by
    intro X hX
    have hu := hX.2.2.isUnit_det
    have hinv : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) (1 - X) :=
      continuousAt_matrix_inv _ (by
        rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (isUnit_iff_ne_zero.1 hu))
    have h1 : ContinuousAt (fun Z : Matrix (Fin n) (Fin n) ℝ => 1 - Z) X :=
      (continuous_const.sub continuous_id).continuousAt
    have h2 : ContinuousAt (fun Z : Matrix (Fin n) (Fin n) ℝ => (1 - Z)⁻¹) X := hinv.comp h1
    have h3 : ContinuousAt (fun Z : Matrix (Fin n) (Fin n) ℝ => 1 + Z) X :=
      (continuous_const.add continuous_id).continuousAt
    have hmul : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact (hmul.continuousAt.comp (h3.prodMk h2)).continuousWithinAt
  have himg : {G : Matrix (Fin n) (Fin n) ℝ | IsHermiteMajorant D G} =
      (fun X : Matrix (Fin n) (Fin n) ℝ => (1 + X) * (1 - X)⁻¹) '' dom := by
    ext G
    constructor
    · intro hG
      obtain ⟨X, hXs, hXD, hc, hXG⟩ := exists_cayley hDD hG.posDef hG.mul_inv_mul
      exact ⟨X, ⟨hXs, hXD, hc⟩, hXG⟩
    · rintro ⟨X, ⟨hXs, hXD, hc⟩, rfl⟩
      exact cayley_isHermiteMajorant hDs hDD hXs hXD hc
  rw [himg]
  exact (hconv.isPreconnected).image _ hcont

/-! ### Helpers: the set of majorants as a proper image -/

/-- Helper: the sign vectors $\varepsilon \in \{\pm 1\}^n$. -/
private def signVecs (n : ℕ) : Set (Fin n → ℝ) := {ε | ∀ i, ε i = 1 ∨ ε i = -1}

private theorem signVecs_finite (n : ℕ) : (signVecs n).Finite := by
  have : signVecs n = Set.pi Set.univ (fun _ : Fin n => ({1, -1} : Set ℝ)) := by
    ext ε; simp [signVecs]
  rw [this]
  exact Set.Finite.pi (fun _ => (Set.toFinite _))

/-- Helper: the set of $L$ with $F = L^{\mathsf T}\operatorname{diag}(\varepsilon)L$ for some sign vector $\varepsilon$. -/
private def sigRep (F : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {L | ∃ ε ∈ signVecs n, Lᵀ * diagonal ε * L = F}

private theorem isClosed_sigRep (F : Matrix (Fin n) (Fin n) ℝ) : IsClosed (sigRep F) := by
  have : sigRep F = ⋃ ε ∈ signVecs n, {L | Lᵀ * diagonal ε * L = F} := by
    ext L; simp [sigRep]
  rw [this]
  refine (signVecs_finite n).isClosed_biUnion fun ε _ => isClosed_eq ?_ continuous_const
  exact (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id

private theorem isHermiteMajorant_iff_image {F G : Matrix (Fin n) (Fin n) ℝ} (hdet : F.det ≠ 0) :
    IsHermiteMajorant F G ↔ G ∈ (fun L : Matrix (Fin n) (Fin n) ℝ => Lᵀ * L) '' sigRep F := by
  constructor
  · rintro ⟨L, ε, hL, hε, hF, hG⟩
    exact ⟨L, ⟨ε, hε, hF.symm⟩, hG.symm⟩
  · rintro ⟨L, ⟨ε, hε, hF⟩, rfl⟩
    refine ⟨L, ε, ?_, hε, hF.symm, rfl⟩
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    rw [← hF, Matrix.det_mul, Matrix.det_mul, h0]; simp

private theorem isClosed_image_gram (F : Matrix (Fin n) (Fin n) ℝ) :
    IsClosed ((fun L : Matrix (Fin n) (Fin n) ℝ => Lᵀ * L) '' sigRep F) := by
  set Φ : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ := fun L => Lᵀ * L with hΦ
  have hΦc : Continuous Φ := continuous_id.matrix_transpose.matrix_mul continuous_id
  refine isClosed_of_closure_subset fun x hx => ?_
  set R : ℝ := 1 + ∑ i, |x i i| with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ ∑ i, |x i i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  set N : Set (Matrix (Fin n) (Fin n) ℝ) := {G | ∀ i, G i i < R} with hN
  have hNo : IsOpen N := by
    have : N = ⋂ i, {G : Matrix (Fin n) (Fin n) ℝ | G i i < R} := by ext; simp [hN]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_id.matrix_elem i i) continuous_const
  have hxN : x ∈ N := by
    intro i
    have : |x i i| ≤ ∑ j, |x j j| :=
      Finset.single_le_sum (f := fun j => |x j j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have := le_abs_self (x i i)
    linarith
  set K : Set (Matrix (Fin n) (Fin n) ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-R) R
    with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : N ∩ Φ '' sigRep F ⊆ Φ '' (sigRep F ∩ K) := by
    rintro _ ⟨hGN, L, hL, rfl⟩
    refine ⟨L, ⟨hL, ?_⟩, rfl⟩
    intro i _ j _
    have h1 := hGN j
    have h2 : (Φ L) j j = ∑ k, L k j * L k j := by
      simp [hΦ, Matrix.mul_apply]
    have h3 : L i j * L i j ≤ ∑ k, L k j * L k j :=
      Finset.single_le_sum (f := fun k => L k j * L k j) (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
    have h4 : (L i j) ^ 2 ≤ R ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq' h4 (by linarith)
  have hcl : IsClosed (Φ '' (sigRep F ∩ K)) :=
    ((hKc.inter_left (isClosed_sigRep F)).image hΦc).isClosed
  have hx' : x ∈ closure (N ∩ Φ '' sigRep F) := hNo.inter_closure ⟨hxN, hx⟩
  have := closure_mono hsub hx'
  rw [hcl.closure_eq] at this
  obtain ⟨L, ⟨hL, -⟩, rfl⟩ := this
  exact ⟨L, hL, rfl⟩

/-- **Lemma 12.1** (Cassels, Ch. 13, §12, p. 325): the set $\mathfrak M(f)$ of Hermite majorants of a real regular form
$f$ is closed in the set of positive definite forms; in fact (Cassels' footnote) it is closed in the space of all
(symmetric) matrices, since $d(g) = |d(f)|$ is constant on $\mathfrak M(f)$. -/
@[kb "cassels1978" "Ch. 13, §12, Lemma 12.1 and footnote, p. 325"]
theorem isClosed_hermiteMajorants {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    IsClosed {G : Matrix (Fin n) (Fin n) ℝ | IsHermiteMajorant F G} := by
  have : {G : Matrix (Fin n) (Fin n) ℝ | IsHermiteMajorant F G} =
      (fun L : Matrix (Fin n) (Fin n) ℝ => Lᵀ * L) '' sigRep F := by
    ext G; exact isHermiteMajorant_iff_image hdet
  rw [this]; exact isClosed_image_gram F

/-- **Lemma 12.2** (Cassels, Ch. 13, §12, p. 325): $\mathfrak M(f)$ consists of the $g(S\vec{x})$, $S \in O_{\mathbb{R}}(f)$,
for any fixed $g \in \mathfrak M(f)$. -/
@[kb "cassels1978" "Ch. 13, §12, Lemma 12.2, (12.1), p. 325"]
theorem hermiteMajorants_eq {F G₀ : Matrix (Fin n) (Fin n) ℝ} (hG₀ : IsHermiteMajorant F G₀) :
    {G | IsHermiteMajorant F G} = (fun S : GL (Fin n) ℝ => S.valᵀ * G₀ * S.val) '' (realAut F : Set _) := by
  ext G
  constructor
  · intro hG
    obtain ⟨-, hdet⟩ := hG₀.isSymm_det_ne_zero
    obtain ⟨L, ε, hL, hε, hF, hGd⟩ := hG
    obtain ⟨L₀, ε₀, hL₀, hε₀, hF₀, hG₀d⟩ := hG₀
    obtain ⟨σ, hσ⟩ := exists_perm_signs hε hε₀ (ncard_pos_eq hdet hF.symm hF₀.symm)
    obtain ⟨hr1, hr2⟩ := submatrix_rep L ε ε₀ σ hσ
    set L₂ := L.submatrix σ id with hL₂def
    have hL₂ : IsUnit L₂.det := isUnit_of_rep hdet (hr1.trans hF.symm)
    set S := L₀⁻¹ * L₂ with hSdef
    have hSu : IsUnit S.det := Matrix.isUnit_det_of_right_inverse (B := L₂⁻¹ * L₀) (by
      rw [hSdef, Matrix.mul_assoc, ← Matrix.mul_assoc L₂, Matrix.mul_nonsing_inv _ hL₂, Matrix.one_mul,
        Matrix.nonsing_inv_mul _ hL₀])
    have e1 : (L₀⁻¹)ᵀ * L₀ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hL₀, Matrix.transpose_one]
    have e2 : L₀ * L₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hL₀
    have hSF : Sᵀ * F * S = F := by
      have : Sᵀ * F * S = L₂ᵀ * ((L₀⁻¹)ᵀ * L₀ᵀ) * diagonal ε₀ * (L₀ * L₀⁻¹) * L₂ := by
        rw [hSdef, hF₀]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, e1, e2, hF]
      rw [← hr1]; simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    have hSG : Sᵀ * G₀ * S = G := by
      have : Sᵀ * G₀ * S = L₂ᵀ * ((L₀⁻¹)ᵀ * L₀ᵀ) * (L₀ * L₀⁻¹) * L₂ := by
        rw [hSdef, hG₀d]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, e1, e2, hGd, ← hr2]; simp only [Matrix.one_mul, Matrix.mul_one]
    refine ⟨⟨S, S⁻¹, Matrix.mul_nonsing_inv _ hSu, Matrix.nonsing_inv_mul _ hSu⟩, ?_, hSG⟩
    exact hSF
  · rintro ⟨S, hS, rfl⟩
    exact hG₀.of_automorph hS ((Matrix.isUnit_iff_isUnit_det _).1 S.isUnit)

/-- **Lemma 12.2, Corollary** (Cassels, Ch. 13, §12, p. 325): $\mathfrak M(f)$ is connected. *Update* (proof gap): Cassels argues that $\mathfrak M(f)$ is "the continuous image of the connected set
$O_{\mathbb{R}}(f)$ [cf. Chapter 2, example 14]"; but $O_{\mathbb{R}}(f)$ is not connected ($\det = \pm 1$), and for
indefinite $f$ not even $O^+_{\mathbb{R}}(f)$ is (Ch. 2, Example 14 (iii) holds for definite spaces only). The
conclusion is true: $\mathfrak M(f)$ is the continuous image of a convex set (the matrices of operator norm $< 1$,
cf. Lemma 10.1). -/
@[kb "cassels1978" "Ch. 13, §12, Lemma 12.2, Cor., p. 325"]
theorem isConnected_hermiteMajorants {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0) :
    IsConnected {G : Matrix (Fin n) (Fin n) ℝ | IsHermiteMajorant F G} := by
  obtain ⟨G₀, hG₀⟩ := exists_isHermiteMajorant hF hdet
  refine ⟨⟨G₀, hG₀⟩, ?_⟩
  obtain ⟨L₀, ε₀, hL₀, hε₀, hF₀, hG₀d⟩ := hG₀
  have hLi : IsUnit (L₀⁻¹).det :=
    Matrix.isUnit_det_of_right_inverse (B := L₀) (Matrix.nonsing_inv_mul _ hL₀)
  have e1 : (L₀⁻¹)ᵀ * L₀ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hL₀, Matrix.transpose_one]
  have e1' : L₀ᵀ * (L₀⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hL₀, Matrix.transpose_one]
  have e2 : L₀ * L₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hL₀
  have e2' : L₀⁻¹ * L₀ = 1 := Matrix.nonsing_inv_mul _ hL₀
  have himg : {G : Matrix (Fin n) (Fin n) ℝ | IsHermiteMajorant F G} =
      (fun G' => L₀ᵀ * G' * L₀) '' {G | IsHermiteMajorant (diagonal ε₀) G} := by
    ext G
    constructor
    · intro hG
      have h1 := hG.conj hLi
      refine ⟨(L₀⁻¹)ᵀ * G * L₀⁻¹, ?_, ?_⟩
      · have : (L₀⁻¹)ᵀ * F * L₀⁻¹ = diagonal ε₀ := by
          rw [hF₀]
          calc (L₀⁻¹)ᵀ * (L₀ᵀ * diagonal ε₀ * L₀) * L₀⁻¹
              = ((L₀⁻¹)ᵀ * L₀ᵀ) * diagonal ε₀ * (L₀ * L₀⁻¹) := by simp only [Matrix.mul_assoc]
            _ = diagonal ε₀ := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
        rwa [this] at h1
      · show L₀ᵀ * ((L₀⁻¹)ᵀ * G * L₀⁻¹) * L₀ = G
        calc L₀ᵀ * ((L₀⁻¹)ᵀ * G * L₀⁻¹) * L₀ = (L₀ᵀ * (L₀⁻¹)ᵀ) * G * (L₀⁻¹ * L₀) := by
              simp only [Matrix.mul_assoc]
          _ = G := by rw [e1', e2', Matrix.one_mul, Matrix.mul_one]
    · rintro ⟨G', hG', rfl⟩
      have := hG'.conj hL₀
      rwa [← hF₀] at this
  rw [himg]
  exact (isPreconnected_majorants_diag hε₀).image _
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn

/-! ### Helpers: finiteness of Hermite-reduced forms of given determinant (from Theorem 11.1) -/

/-- Helper: $2Q$ has real matrix $2F$. -/
private theorem realMat_two_smul (Q : IntQF n) : realMat ((2 : ℤ) • Q) = (2 : ℝ) • realMat Q := by
  ext i j
  simp only [realMat, QuadForm.hessian, QuadForm.smul_coeff, Matrix.transpose_smul, Matrix.smul_apply,
    Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  norm_num <;> ring

/-- Helper: $Q \mapsto 2Q$ is injective. -/
private theorem two_smul_injective : Function.Injective (fun Q : IntQF n => (2 : ℤ) • Q) := by
  intro Q Q' h
  have h1 := congrArg QuadForm.coeff h
  simp only [QuadForm.smul_coeff] at h1
  have h2 : Q.coeff = Q'.coeff := smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0) h1
  cases Q; cases Q'
  simp only at h2
  subst h2
  rfl

/-- Helper: a positive multiple of a Hermite-reduced form is Hermite-reduced (copy of the private lemma of
`Ch13/Sec2.lean`). -/
private theorem isMajorantReduced_smul {F : Matrix (Fin n) (Fin n) ℝ} (h : IsMajorantReduced F) {c : ℝ}
    (hc : 0 < c) : IsMajorantReduced (c • F) := by
  obtain ⟨G, ⟨L, ε, hL, hε, hF, hG⟩, hred⟩ := h
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hss : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  refine ⟨c • G, ⟨Real.sqrt c • L, ε, ?_, hε, ?_, ?_⟩, ?_⟩
  · rw [Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hs.ne')).mul hL
  · rw [hF]
    simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss]
  · rw [hG]
    simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss]
  · have hval : ∀ x, val (c • G) x = c * val G x := fun x => by
      simp [val, Matrix.smul_mulVec, dotProduct_smul]
    refine ⟨?_, fun j e he => ?_⟩
    · rw [posDef_iff]
      obtain ⟨hs', hp⟩ := (posDef_iff G).1 hred.1
      refine ⟨?_, fun x hx => ?_⟩
      · show (c • G)ᵀ = c • G
        rw [Matrix.transpose_smul]; congr 1
      · rw [hval]; exact mul_pos hc (hp x hx)
    · have := hred.2 j e he
      rw [hval]
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left this hc.le

/-- Helper: finiteness of the integral Hermite-reduced forms of given $|\det|$ (Theorem 11.1 applied to $2Q$). -/
private theorem finite_absDet_aux (n : ℕ) (D : ℝ) :
    {Q : IntQF n | |(realMat Q).det| = D ∧ IsMajorantReduced (realMat Q)}.Finite := by
  by_cases hD : D = 0
  · refine Set.Finite.subset (Set.finite_empty) fun Q ⟨h1, h2⟩ => ?_
    obtain ⟨G, hG, -⟩ := h2
    exact absurd (h1.trans hD) (abs_ne_zero.2 hG.isSymm_det_ne_zero.2)
  have hpos : (0 : ℝ) < 2 ^ n * D ∨ 2 ^ n * D < 0 := by
    rcases lt_or_gt_of_ne hD with h | h
    · exact Or.inr (mul_neg_of_pos_of_neg (by positivity) h)
    · exact Or.inl (by positivity)
  have hd1 : (2 : ℝ) ^ n * D ≠ 0 := mul_ne_zero (by positivity) hD
  have hd2 : -((2 : ℝ) ^ n * D) ≠ 0 := neg_ne_zero.2 hd1
  have hfin := (finite_isMajorantReduced_classical n _ hd1).union (finite_isMajorantReduced_classical n _ hd2)
  refine Set.Finite.subset (hfin.preimage (two_smul_injective.injOn)) fun Q ⟨h1, h2⟩ => ?_
  have hdet : (realMat ((2 : ℤ) • Q)).det = (2 : ℝ) ^ n * (realMat Q).det := by
    rw [realMat_two_smul, Matrix.det_smul, Fintype.card_fin]
  rw [Set.mem_preimage]
  show _ ∈ _ ∪ _
  rcases abs_choice (realMat Q).det with h | h
  · left
    refine ⟨two_smul_isClassicallyIntegral Q, ?_, ?_⟩
    · rw [hdet]; congr 1; rw [← h1, h]
    · rw [realMat_two_smul]; exact isMajorantReduced_smul h2 (by norm_num)
  · right
    refine ⟨two_smul_isClassicallyIntegral Q, ?_, ?_⟩
    · rw [hdet, ← h1, h]; ring
    · rw [realMat_two_smul]; exact isMajorantReduced_smul h2 (by norm_num)

/-- Helper: entries of a product of integer matrices. -/
private theorem abs_mul_entry_le (S T : GL (Fin n) ℤ) {a b : ℝ} (hS : ∀ i j, |(S.val i j : ℝ)| ≤ a)
    (hT : ∀ i j, |(T.val i j : ℝ)| ≤ b) (i j : Fin n) : |(((S * T).val i j : ℤ) : ℝ)| ≤ n * (a * b) := by
  rw [Units.val_mul, Matrix.mul_apply]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l, |(S.val i l : ℝ) * (T.val l j : ℝ)| ≤ ∑ _l : Fin n, a * b :=
        Finset.sum_le_sum fun l _ => by
          rw [abs_mul]
          exact mul_le_mul (hS i l) (hT l j) (abs_nonneg _) ((abs_nonneg _).trans (hS i l))
    _ = n * (a * b) := by simp

/-- Helper: the real matrix of a substituted form. -/
private theorem realMat_compMat (Q : IntQF n) (U : Matrix (Fin n) (Fin n) ℤ) :
    realMat (Q.compMat U) = act U (realMat Q) := halfHessian_compMat Q U

/-- **Lemma 12.3** (Cassels, Ch. 13, §12, p. 325): for integers $D > 0$ and $n$ there is $B = B(n, D)$ such that the
coefficients of every Hermite-reduced integral form $f$ of dimension $n$ with $|d(f)| = D$ are at most $B$ in
absolute value (Cassels: $B$ can be effectively calculated, by reworking the proof of Theorem 11.1). Here $f$ is
integer-valued (the classically integral $2f$ is Hermite-reduced with $|d(2f)| = 2^nD$). -/
@[kb "cassels1978" "Ch. 13, §12, Lemma 12.3, p. 325"]
theorem exists_isMajorantReduced_bound (n : ℕ) (D : ℝ) : ∃ B : ℝ, ∀ Q : IntQF n, |(realMat Q).det| = D →
    IsMajorantReduced (realMat Q) → ∀ i j, |realMat Q i j| ≤ B := by
  obtain ⟨B, hB⟩ := ((finite_absDet_aux n D).image
    (fun Q : IntQF n => ∑ i, ∑ j, |realMat Q i j|)).bddAbove
  refine ⟨B, fun Q h1 h2 i j => le_trans ?_ (hB ⟨Q, ⟨h1, h2⟩, rfl⟩)⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, |realMat Q i j|)
    (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => |realMat Q i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)

/-- **Lemma 12.3, Corollary** (Cassels, Ch. 13, §12, p. 326): there are at most $A = A(n, D)$ distinct Hermite-reduced
integral forms of dimension $n$ with $|d(f)| = D$ (finitely many). -/
@[kb "cassels1978" "Ch. 13, §12, Lemma 12.3, Cor., p. 326"]
theorem finite_isMajorantReduced_absDet (n : ℕ) (D : ℝ) :
    {Q : IntQF n | |(realMat Q).det| = D ∧ IsMajorantReduced (realMat Q)}.Finite :=
  finite_absDet_aux n D

/-- **The set $\mathfrak M(f; h)$** (Cassels, Ch. 13, §12, (12.2)–(12.3), p. 326): for a Hermite-reduced $h$ equivalent
to $f$, the union of the $\mathfrak M(f) \cap T\mathfrak R$ over the $T \in \mathrm{GL}_n(\mathbb{Z})$ with $T^{-1}f = h$;
i.e. the majorants $g$ of $f$ such that $T^{-1}g$ is Minkowski-reduced for some $T$ with $T^{-1}f = h$. -/
@[kb "cassels1978" "Ch. 13, §12, (12.2)–(12.3), p. 326"]
def majorantsRed (F H : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {G | IsHermiteMajorant F G ∧ ∃ T : GL (Fin n) ℤ, G ∈ img T ∧ act T⁻¹.val F = H}

/-- **Every majorant lies in some $\mathfrak M(f; h)$** (Cassels, Ch. 13, §12, p. 326): every $g \in \mathfrak M(f)$
lies in some $T\mathfrak R$, and then $h = T^{-1}f$ is Hermite-reduced (with Minkowski-reduced majorant $T^{-1}g$);
every Hermite-reduced $h$ equivalent to $f$ arises in this way. -/
@[kb "cassels1978" "Ch. 13, §12, p. 326 (the sets 𝔐(f; h) cover 𝔐(f))"]
theorem exists_mem_majorantsRed {F G : Matrix (Fin n) (Fin n) ℝ} (hG : IsHermiteMajorant F G) :
    ∃ T : GL (Fin n) ℤ, G ∈ majorantsRed F (act T⁻¹.val F) ∧ IsMajorantReduced (act T⁻¹.val F) := by
  have hmem : G ∈ ⋃ T : GL (Fin n) ℤ, img T := by rw [← thm_7_1]; exact hG.posDef
  obtain ⟨T, hT⟩ := Set.mem_iUnion.1 hmem
  refine ⟨T, ⟨hG, T, hT, rfl⟩, act T⁻¹.val G, ?_, ?_⟩
  · exact hG.act T⁻¹
  · exact (mem_img_iff_red7 T G).1 hT

/-- **Lemma 12.4** (Cassels, Ch. 13, §12, p. 326): $\mathfrak M(f; h)$ is closed (in $\mathcal P^{\circ}$; here: in the space
of matrices). Proof: each $\mathfrak M(f) \cap T\mathfrak R$ is closed (Ch. 12, Lemma 5.3 (ii), and Lemma 12.1), and the
cover of $\mathcal P^{\circ}$ by the $T\mathfrak R$ is locally finite (Ch. 12, Thm. 7.6). -/
@[kb "cassels1978" "Ch. 13, §12, Lemma 12.4, p. 326"]
theorem isClosed_majorantsRed {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (H : Matrix (Fin n) (Fin n) ℝ) : IsClosed (majorantsRed F H) := by
  have hM := isClosed_hermiteMajorants hF hdet
  refine isClosed_of_closure_subset fun x hx => ?_
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds x
  set K : Set (Matrix (Fin n) (Fin n) ℝ) := {G | IsHermiteMajorant F G} ∩ C with hK
  have hKc : IsCompact K := hCc.inter_left hM
  have hfin := thm_7_6 hKc (fun G hG => hG.1.posDef)
  have hS : majorantsRed F H ∩ C =
      ⋃ T ∈ {T : GL (Fin n) ℤ | (img T ∩ K).Nonempty ∧ act T⁻¹.val F = H}, (K ∩ clR7 T) := by
    ext G
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨⟨hG, T, hT, hTH⟩, hGC⟩
      exact ⟨T, ⟨⟨G, hT, hG, hGC⟩, hTH⟩, ⟨hG, hGC⟩, ((mem_img_iff7 T G).1 hT).1⟩
    · rintro ⟨T, ⟨-, hTH⟩, ⟨hG, hGC⟩, hcl⟩
      exact ⟨⟨hG, T, (mem_img_iff7 T G).2 ⟨hcl, hG.posDef⟩, hTH⟩, hGC⟩
  have hcl : IsClosed (majorantsRed F H ∩ C) := by
    rw [hS]
    exact (hfin.subset fun T hT => hT.1).isClosed_biUnion fun T _ => hKc.isClosed.inter (isClosed_clR7 T)
  have hx' : x ∈ closure (majorantsRed F H ∩ C) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨G, hGt, hGS⟩ := mem_closure_iff_nhds.1 hx (t ∩ C) (Filter.inter_mem ht hCn)
    exact ⟨G, hGt.1, hGS, hGt.2⟩
  rw [hcl.closure_eq] at hx'
  exact hx'.1

/-- **Lemma 12.5** (Cassels, Ch. 13, §12, p. 326): there is $E$ depending only on $n$ such that if
$\mathfrak M(f; h_1) \cap \mathfrak M(f; h_2) \ne \emptyset$ then $h_2 = Sh_1$ (i.e. $h_2(\vec{x}) = h_1(S\vec{x})$) for some
$S \in \mathrm{GL}_n(\mathbb{Z})$ all of whose elements are at most $E$ in absolute value. -/
@[kb "cassels1978" "Ch. 13, §12, Lemma 12.5, p. 326"]
theorem exists_bounded_of_majorantsRed (n : ℕ) : ∃ E : ℝ, ∀ F H₁ H₂ : Matrix (Fin n) (Fin n) ℝ,
    (majorantsRed F H₁ ∩ majorantsRed F H₂).Nonempty →
      ∃ S : GL (Fin n) ℤ, act S.val H₁ = H₂ ∧ ∀ i j, |(S.val i j : ℝ)| ≤ E := by
  obtain ⟨E, hE⟩ := (((sigma_finite n).image
    (fun S : GL (Fin n) ℤ => ∑ i, ∑ j, |(S.val i j : ℝ)|)).bddAbove)
  refine ⟨E, fun F H₁ H₂ ⟨G, ⟨_, T₁, hG₁, hT₁⟩, ⟨_, T₂, hG₂, hT₂⟩⟩ => ?_⟩
  obtain ⟨S, hS, hST⟩ := (thm_7_5 T₁ T₂).1 ⟨G, hG₁, hG₂⟩
  have hinv : T₂⁻¹ = T₁⁻¹ * S := by rw [hST]; group
  refine ⟨S, ?_, fun i j => ?_⟩
  · rw [← hT₁, ← hT₂, hinv, Units.val_mul, act_mul]
  · refine le_trans ?_ (hE ⟨S, hS, rfl⟩)
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, |(S.val i j : ℝ)|)
      (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => |(S.val i j : ℝ)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)

/-- **Theorem 12.1** (Cassels, Ch. 13, §12, pp. 326–327): let $f_1, f_2$ be integral Hermite-reduced forms which are
integrally equivalent. Then $f_2 = Tf_1$ ($f_2(\vec{x}) = f_1(T\vec{x})$) for some $T \in \mathrm{GL}_n(\mathbb{Z})$ whose
elements do not exceed a constant $K$ depending only on $n$ and the determinant (Cassels: $K$ can be specified
effectively). This gives a decision procedure for integral equivalence (Problem 2, p. 325). -/
@[kb "cassels1978" "Ch. 13, §12, Thm. 12.1, pp. 326–327"]
theorem exists_bounded_equiv_of_isMajorantReduced (n : ℕ) (D : ℝ) : ∃ K : ℝ, ∀ Q₁ Q₂ : IntQF n,
    |(realMat Q₁).det| = D → IsMajorantReduced (realMat Q₁) → IsMajorantReduced (realMat Q₂) →
    Siegel.IntEquiv Q₁ Q₂ → ∃ T : GL (Fin n) ℤ, act T.val (realMat Q₁) = realMat Q₂ ∧
      ∀ i j, |(T.val i j : ℝ)| ≤ K := by
  classical
  obtain ⟨E, hE⟩ := exists_bounded_of_majorantsRed n
  set E' : ℝ := max E 1 with hE'
  set c : ℝ := max ((n : ℝ) * E') 1 with hc
  set SD : Set (IntQF n) := {Q : IntQF n | |(realMat Q).det| = D ∧ IsMajorantReduced (realMat Q)} with hSDdef
  have hSD : SD.Finite := finite_absDet_aux n D
  have hc1 : 1 ≤ c := le_max_right _ _
  have hnE : (n : ℝ) * E ≤ c :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg n)) (le_max_left _ _)
  refine ⟨c ^ SD.ncard, ?_⟩
  intro Q₁ Q₂ hdet h₁ h₂ heq
  set F := realMat Q₁ with hFdef
  obtain ⟨g, hg⟩ := heq
  have hgF : act g.val F = realMat Q₂ := by
    have : Q₁.compMat g.val = Q₂ :=
      QuadForm.eq_of_eval_eq (fun x => by rw [QuadForm.eval_compMat]; exact hg x)
    rw [← this]; exact (halfHessian_compMat Q₁ g.val).symm
  obtain ⟨G₁, hG₁, hG₁r⟩ := h₁
  obtain ⟨G₂, hG₂, hG₂r⟩ := h₂
  have hFs := hG₁.isSymm_det_ne_zero
  set Hset : Set (Matrix (Fin n) (Fin n) ℝ) := {H | (majorantsRed F H).Nonempty} with hHset
  have hHsub : Hset ⊆ realMat '' SD := by
    rintro _ ⟨G, hGM, T, hGT, rfl⟩
    refine ⟨Q₁.compMat T⁻¹.val, ⟨?_, ?_⟩, ?_⟩
    · rw [realMat_compMat, det_act, hdet]
    · rw [realMat_compMat]
      exact ⟨act T⁻¹.val G, hGM.act T⁻¹, (mem_img_iff_red7 T G).1 hGT⟩
    · exact realMat_compMat Q₁ _
  have hHfin : Hset.Finite := (hSD.image realMat).subset hHsub
  have : Fintype Hset := hHfin.fintype
  have hcard : Fintype.card Hset ≤ SD.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hHsub (hSD.image _)).trans (Set.ncard_image_le hSD)
  -- the graph
  let r : Hset → Hset → Prop := fun u v => (majorantsRed F u.1 ∩ majorantsRed F v.1).Nonempty
  let Γ : SimpleGraph Hset := SimpleGraph.fromRel r
  have hwalk : ∀ (u v : Hset) (p : Γ.Walk u v), ∃ T : GL (Fin n) ℤ, act T.val u.1 = v.1 ∧
      ∀ i j, |(T.val i j : ℝ)| ≤ c ^ p.length := by
    intro u v p
    induction p with
    | nil =>
      refine ⟨1, by simp [act_one], fun i j => ?_⟩
      simp only [SimpleGraph.Walk.length_nil, pow_zero, Units.val_one, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij]
    | @cons u w v hadj p ih =>
      obtain ⟨T', hT', hb'⟩ := ih
      obtain ⟨-, hr⟩ := (SimpleGraph.fromRel_adj r u w).1 hadj
      have hn : (majorantsRed F u.1 ∩ majorantsRed F w.1).Nonempty := by
        rcases hr with h | h
        · exact h
        · have h' : (majorantsRed F w.1 ∩ majorantsRed F u.1).Nonempty := h
          rwa [Set.inter_comm] at h'
      obtain ⟨S, hS, hSb⟩ := hE F u.1 w.1 hn
      refine ⟨S * T', by rw [Units.val_mul, act_mul, hS, hT'], fun i j => ?_⟩
      refine (abs_mul_entry_le S T' hSb hb' i j).trans ?_
      rw [SimpleGraph.Walk.length_cons, pow_succ]
      calc (n : ℝ) * (E * c ^ p.length) = ((n : ℝ) * E) * c ^ p.length := by ring
        _ ≤ c * c ^ p.length := mul_le_mul_of_nonneg_right hnE (pow_nonneg (by linarith) _)
        _ = c ^ p.length * c := mul_comm _ _
  -- the two vertices
  have hv1 : F ∈ Hset := by
    refine ⟨G₁, hG₁, 1, ?_, ?_⟩
    · rw [mem_img_iff_red7]; simpa [act_one] using hG₁r
    · simp [act_one]
  have hv2 : realMat Q₂ ∈ Hset := by
    have hF' : act g⁻¹.val (realMat Q₂) = F := by rw [← hgF]; exact act_inv_act7 g F
    refine ⟨act g⁻¹.val G₂, ?_, g⁻¹, ⟨G₂, hG₂r, rfl⟩, ?_⟩
    · have := hG₂.act g⁻¹
      rwa [hF'] at this
    · rw [inv_inv]; exact hgF
  let v₁ : Hset := ⟨F, hv1⟩
  let v₂ : Hset := ⟨realMat Q₂, hv2⟩
  have hreach : Γ.Reachable v₁ v₂ := by
    by_contra hnr
    set C : Set Hset := {v | Γ.Reachable v₁ v} with hC
    have hU : IsClosed (⋃ v ∈ C, majorantsRed F v.1) :=
      (Set.toFinite C).isClosed_biUnion fun v _ => isClosed_majorantsRed hFs.1 hFs.2 _
    have hW : IsClosed (⋃ v ∈ Cᶜ, majorantsRed F v.1) :=
      (Set.toFinite Cᶜ).isClosed_biUnion fun v _ => isClosed_majorantsRed hFs.1 hFs.2 _
    have hpre := (isConnected_hermiteMajorants hFs.1 hFs.2).isPreconnected
    rw [isPreconnected_closed_iff] at hpre
    have hsubM : ∀ H, majorantsRed F H ⊆ {G | IsHermiteMajorant F G} := fun H G hG => hG.1
    have hcov : {G | IsHermiteMajorant F G} ⊆
        (⋃ v ∈ C, majorantsRed F v.1) ∪ (⋃ v ∈ Cᶜ, majorantsRed F v.1) := by
      intro G hG
      obtain ⟨T, hGm, -⟩ := exists_mem_majorantsRed hG
      by_cases hv : (⟨act T⁻¹.val F, ⟨G, hGm⟩⟩ : Hset) ∈ C
      · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨_, hv, hGm⟩
      · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨_, hv, hGm⟩
    have hneU : ({G | IsHermiteMajorant F G} ∩ ⋃ v ∈ C, majorantsRed F v.1).Nonempty := by
      obtain ⟨G, hG⟩ := hv1
      refine ⟨G, hG.1, ?_⟩
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨v₁, SimpleGraph.Reachable.refl _, hG⟩
    have hneW : ({G | IsHermiteMajorant F G} ∩ ⋃ v ∈ Cᶜ, majorantsRed F v.1).Nonempty := by
      obtain ⟨G, hG⟩ := hv2
      refine ⟨G, hG.1, ?_⟩
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨v₂, hnr, hG⟩
    obtain ⟨G, -, hGU, hGW⟩ := hpre _ _ hU hW hcov hneU hneW
    simp only [Set.mem_iUnion, exists_prop] at hGU hGW
    obtain ⟨u, hu, hGu⟩ := hGU
    obtain ⟨w, hw, hGw⟩ := hGW
    by_cases huw : u = w
    · exact hw (huw ▸ hu)
    · exact hw (hu.trans (SimpleGraph.Adj.reachable
        ((SimpleGraph.fromRel_adj r u w).2 ⟨huw, Or.inl ⟨G, hGu, hGw⟩⟩)))
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  obtain ⟨T, hT, hb⟩ := hwalk v₁ v₂ p
  refine ⟨T, hT, fun i j => (hb i j).trans ?_⟩
  exact pow_le_pow_right₀ hc1 (hp.length_lt.le.trans hcard)

end QuadFormsKB.Reduction
