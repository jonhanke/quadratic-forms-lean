import Mathlib
import QuadFormsKB.Citation

/-!
# Cassels, Chapter 13, §5: the ternary form $x_0x_2 - x_1^{2}$ and binary forms

Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §5 (*Isotropic ternary forms*), pp. 301–302.

**Setting.** $f_0(\vec{x}) = x_0x_2 - x_1^{2}$ (`f₀`) is the determinant of the binary form
$\varphi_{\vec{x}}(\vec{u}) = x_0u_0^{2} + 2x_1u_0u_1 + x_2u_1^{2}$; a $2\times2$ matrix $S$ acts on the coefficient vectors
$\vec{x}$ by `symSq S`, multiplying $f_0$ by $(\det S)^{2}$, so $T(S) = (\det S)^{-1}\mathrm{symSq}(S)$ (`spinRep`) is an automorph
of $f_0$ with $\det T(S) = 1$ (5.6)–(5.7).

**What is proved.**
* Lemma 5.1 (`lemma_5_1`), over any field: $S \mapsto T(S)$ is a homomorphism $GL_2 \to O^{+}(f_0)$, onto, with kernel
  the scalars.
* Lemma 5.2 (`lemma_5_2`): over $\mathbb Z$, $SL^{\pm}_2(\mathbb Z) \to O^{+}(f_0)$ is onto with kernel $\pm I$.
* Lemma 5.3 (`lemma_5_3`): orbits of the image $\mathfrak G$ of $SL_2(\mathbb Z)$ correspond to proper classes of
  classically integral binary forms (`phi`).

**Proof notes.** Surjectivity follows Cassels: move the first column of $T$ (an isotropic vector) to $\vec{e}_0$ by
some $T(S_1)$ (`exists_spinRep_col`, `spinRep_surjective_int`), then an automorph fixing $\vec{e}_0$ is $T$ of a
unipotent matrix (`eq_spinRep_of_fix`). Over $\mathbb Z$ the first column is primitive (cofactor expansion of
$\det T = 1$), so its first and last entries are coprime and Mathlib's `Int.sq_of_isCoprime` gives
$(\pm\alpha^{2}, \alpha\gamma, \pm\gamma^{2})$.

**Conventions.** Indices are 0-based. The display (5.6) is partly lost in the machine-read text. With the action
$\varphi_{\vec{x}}(S\vec{u})$ the map would be an anti-homomorphism; we use the transposed matrix (the action
$\varphi_{\vec{x}}(S^{\mathsf T}\vec{u})$), which makes $S \mapsto T(S)$ a homomorphism as Cassels states. The group $O^{+}(f_0)$
of proper automorphs is expressed as the matrices of $SL_3$ preserving $f_0$.
-/

open Matrix

namespace QuadFormsKB.Cassels.Ch13

variable {R : Type*} [CommRing R]

/-- The ternary form $f_0(\vec{x}) = x_0x_2 - x_1^{2}$ (Cassels (5.1), $x_1x_3 - x_2^{2}$ in his 1-based indexing): the determinant of the binary form $\varphi_{\vec{x}}(u_0,u_1) = x_0u_0^{2} + 2x_1u_0u_1 + x_2u_1^{2}$ (5.2). -/
@[kb "cassels1978" "Ch. 13, §5, (5.1)–(5.2), p. 301"]
def f₀ (x : Fin 3 → R) : R := x 0 * x 2 - x 1 ^ 2

/-- For $S = \begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}$, the $3\times3$ matrix $\begin{pmatrix}\alpha^{2}&2\alpha\beta&\beta^{2}\\\alpha\gamma&\alpha\delta+\beta\gamma&\beta\delta\\\gamma^{2}&2\gamma\delta&\delta^{2}\end{pmatrix}$ by which $S$ acts on the coefficient vectors $(x_0,x_1,x_2)$ of the binary forms $\varphi_{\vec{x}}$: $\varphi_{\vec{x}}(S^{\mathsf T}\vec{u}) = \varphi_{\mathrm{symSq}(S)\vec{x}}(\vec{u})$. It is $\det(S)\,T(S)$ in Cassels' notation (5.6). -/
def symSq (S : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![S 0 0 ^ 2, 2 * S 0 0 * S 0 1, S 0 1 ^ 2;
     S 0 0 * S 1 0, S 0 0 * S 1 1 + S 0 1 * S 1 0, S 0 1 * S 1 1;
     S 1 0 ^ 2, 2 * S 1 0 * S 1 1, S 1 1 ^ 2]

/-- $\mathrm{symSq}(SS') = \mathrm{symSq}(S)\,\mathrm{symSq}(S')$. -/
theorem symSq_mul (S S' : Matrix (Fin 2) (Fin 2) R) : symSq (S * S') = symSq S * symSq S' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symSq, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

/-- $\mathrm{symSq}(I) = I$. -/
theorem symSq_one : symSq (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symSq, sq]

/-- $\det \mathrm{symSq}(S) = (\det S)^{3}$. -/
theorem det_symSq (S : Matrix (Fin 2) (Fin 2) R) : (symSq S).det = S.det ^ 3 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]; simp [symSq]; ring

/-- $f_0(\mathrm{symSq}(S)\vec{x}) = (\det S)^{2} f_0(\vec{x})$ ("the determinant of $\varphi_x(Su)$ is $\det(S)^2$ times the determinant of $\varphi_x(u)$", p. 301). -/
theorem f₀_symSq (S : Matrix (Fin 2) (Fin 2) R) (x : Fin 3 → R) :
    f₀ (symSq S *ᵥ x) = S.det ^ 2 * f₀ x := by
  simp [f₀, symSq, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_two]; ring

/-- The map $S \mapsto T(S) = (\det S)^{-1}\,\mathrm{symSq}(S)$ (Cassels (5.6)) as a group homomorphism $GL_2(R) \to SL_3(R)$ (5.7), for any commutative ring $R$; for $R = \mathbb Q$ this is Cassels' map on $GL$, for $R = \mathbb Z$ his map on $SL^{\pm}$ ($\det S = \pm 1$, (5.17)–(5.18)). -/
@[kb "cassels1978" "Ch. 13, §5, (5.6)–(5.7), p. 301"]
def spinRep : GL (Fin 2) R →* SpecialLinearGroup (Fin 3) R where
  toFun S := ⟨(((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) • symSq (S : Matrix (Fin 2) (Fin 2) R), by
    rw [Matrix.det_smul, det_symSq, Fintype.card_fin, ← GeneralLinearGroup.val_det_apply, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    simp [symSq_one]
  map_mul' S S' := by
    apply Subtype.ext
    show (((GeneralLinearGroup.det (S * S'))⁻¹ : Rˣ) : R) • symSq ((S * S' : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = ((((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) • symSq (S : Matrix (Fin 2) (Fin 2) R)) *
        ((((GeneralLinearGroup.det S')⁻¹ : Rˣ) : R) • symSq (S' : Matrix (Fin 2) (Fin 2) R))
    rw [Units.val_mul, symSq_mul, map_mul, _root_.mul_inv_rev, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Units.val_mul, mul_comm]

/-- $T(S)$ is an automorph of $f_0$: $f_0(T(S)\vec{x}) = f_0(\vec{x})$. -/
theorem f₀_spinRep (S : GL (Fin 2) R) (x : Fin 3 → R) :
    f₀ ((spinRep S : Matrix (Fin 3) (Fin 3) R) *ᵥ x) = f₀ x := by
  show f₀ (((((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) • symSq (S : Matrix (Fin 2) (Fin 2) R)) *ᵥ x) = f₀ x
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul]
  have h1 : f₀ (symSq (S : Matrix (Fin 2) (Fin 2) R) *ᵥ ((((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) • x)) =
      (S : Matrix (Fin 2) (Fin 2) R).det ^ 2 * f₀ ((((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) • x) :=
    f₀_symSq _ _
  rw [h1]
  have h2 : (S : Matrix (Fin 2) (Fin 2) R).det * (((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [f₀, Pi.smul_apply, smul_eq_mul]
  linear_combination (x 0 * x 2 - x 1 ^ 2) * ((S : Matrix (Fin 2) (Fin 2) R).det * (((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) + 1) * h2


/-- The matrix of $T(S)$ is $(\det S)^{-1}\mathrm{symSq}(S)$. -/
theorem coe_spinRep (S : GL (Fin 2) R) :
    ((spinRep S : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) • symSq (S : Matrix (Fin 2) (Fin 2) R) := rfl

/-- Over an integral domain, the kernel of $S \mapsto T(S)$ is the scalar matrices. -/
theorem spinRep_eq_one_iff [IsDomain R] (S : GL (Fin 2) R) :
    spinRep S = 1 ↔ ∃ c : R, (S : Matrix (Fin 2) (Fin 2) R) = c • 1 := by
  have hdu : (S : Matrix (Fin 2) (Fin 2) R).det * (((GeneralLinearGroup.det S)⁻¹ : Rˣ) : R) = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : spinRep S = 1 ↔
      symSq (S : Matrix (Fin 2) (Fin 2) R) = (S : Matrix (Fin 2) (Fin 2) R).det • (1 : Matrix (Fin 3) (Fin 3) R) := by
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [coe_spinRep] at h'
      change _ = (1 : Matrix (Fin 3) (Fin 3) R) at h'
      rw [← h', smul_smul, hdu, one_smul]
    · intro h
      apply Subtype.ext
      rw [coe_spinRep, h, smul_smul, mul_comm, hdu, one_smul]; rfl
  rw [key]
  set M := (S : Matrix (Fin 2) (Fin 2) R)
  have hdet : M.det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdu; exact zero_ne_one hdu
  constructor
  · intro h
    have e02 := congrFun (congrFun h 0) 2
    have e20 := congrFun (congrFun h 2) 0
    have e00 := congrFun (congrFun h 0) 0
    have e22 := congrFun (congrFun h 2) 2
    simp [symSq] at e02 e20 e00 e22
    rw [Matrix.det_fin_two, e02, e20] at e00 e22 hdet
    simp at e00 e22 hdet
    have h1 : M 0 0 * (M 0 0 - M 1 1) = 0 := by linear_combination e00
    have h2 : M 0 0 = M 1 1 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hdet.1
      · exact sub_eq_zero.1 h
    refine ⟨M 0 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [e02, e20, h2]
  · rintro ⟨c, hc⟩
    rw [hc]
    ext i j; fin_cases i <;> fin_cases j <;> simp [symSq, sq]

/-- Over $\mathbb Z$, the kernel of $S \mapsto T(S)$ is $\{\pm I\}$. -/
theorem spinRep_eq_one_iff_int (S : GL (Fin 2) ℤ) : spinRep S = 1 ↔ S = 1 ∨ S = -1 := by
  rw [spinRep_eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    have hdet := (GeneralLinearGroup.det S).isUnit
    rw [GeneralLinearGroup.val_det_apply, hc, Matrix.det_smul, Fintype.card_fin, det_one, mul_one] at hdet
    have hc1 : IsUnit c := (isUnit_pow_iff two_ne_zero).1 hdet
    rcases Int.isUnit_iff.1 hc1 with rfl | rfl
    · left; exact Units.ext (by rw [hc, one_smul]; rfl)
    · right; exact Units.ext (by rw [hc, neg_one_smul]; rfl)
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩


/-- $f_0(T\vec{x})$ in coordinates for $\vec{x} = (x_0, x_1, x_2)$. -/
theorem f₀_mulVec_apply (T : Matrix (Fin 3) (Fin 3) R) (x₀ x₁ x₂ : R) :
    f₀ (T *ᵥ ![x₀, x₁, x₂]) = (T 0 0 * x₀ + T 0 1 * x₁ + T 0 2 * x₂) * (T 2 0 * x₀ + T 2 1 * x₁ + T 2 2 * x₂)
      - (T 1 0 * x₀ + T 1 1 * x₁ + T 1 2 * x₂) ^ 2 := by
  simp [f₀, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- An automorph $T \in SL_3(R)$ of $f_0$ fixing $\vec{e}_0$ is $T(S)$ for the unipotent $S = \begin{pmatrix}1&t_{12}\\0&1\end{pmatrix}$ (the "diagonal case" at the end of the proof of Lemma 5.1, after the reduction (5.12)–(5.16)). -/
theorem eq_spinRep_of_fix (T : SpecialLinearGroup (Fin 3) R)
    (hT : ∀ x, f₀ ((T : Matrix (Fin 3) (Fin 3) R) *ᵥ x) = f₀ x)
    (h0 : (T : Matrix (Fin 3) (Fin 3) R) 0 0 = 1) (h1 : (T : Matrix (Fin 3) (Fin 3) R) 1 0 = 0)
    (h2 : (T : Matrix (Fin 3) (Fin 3) R) 2 0 = 0) :
    ∃ S : GL (Fin 2) R, spinRep S = T := by
  set M := (T : Matrix (Fin 3) (Fin 3) R) with hM
  have e1 := hT ![0, 1, 0]
  have e2 := hT ![0, 0, 1]
  have e01 := hT ![1, 1, 0]
  have e02 := hT ![1, 0, 1]
  have e12 := hT ![0, 1, 1]
  simp only [f₀_mulVec_apply] at e1 e2 e01 e02 e12
  simp [f₀, h0, h1, h2] at e1 e2 e01 e02 e12
  have hdet := T.prop
  rw [Matrix.det_fin_three, ← hM, h0, h1, h2] at hdet
  have hM21 : M 2 1 = 0 := by linear_combination e01 - e1
  have hM22 : M 2 2 = 1 := by linear_combination e02 - e2
  have hM11 : M 1 1 = 1 := by rw [hM21, hM22] at hdet; linear_combination hdet
  have hM02 : M 0 2 = M 1 2 ^ 2 := by rw [hM22] at e2; linear_combination e2
  have hM01 : M 0 1 = 2 * M 1 2 := by
    rw [hM21, hM22, hM11, hM02] at e12; linear_combination e12
  have hU : IsUnit (!![(1 : R), M 1 2; 0, 1] : Matrix (Fin 2) (Fin 2) R).det := by
    simp [Matrix.det_fin_two]
  refine ⟨Matrix.nonsingInvUnit _ hU, ?_⟩
  apply Subtype.ext
  rw [coe_spinRep]
  have hd : GeneralLinearGroup.det (Matrix.nonsingInvUnit _ hU) = 1 := by
    ext; rw [GeneralLinearGroup.val_det_apply]; simp [Matrix.nonsingInvUnit, Matrix.det_fin_two]
  rw [hd, inv_one, Units.val_one, one_smul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symSq, Matrix.nonsingInvUnit, ← hM, h0, h1, h2, hM21, hM22, hM11, hM02, hM01]

/-- Reduction step of the proof of Lemmas 5.1 and 5.2: if the first column of an automorph $T$ of $f_0$ is the first column of some $T(S_1)$, then $T$ is in the image of $S \mapsto T(S)$. -/
theorem exists_spinRep_of_col (T : SpecialLinearGroup (Fin 3) R)
    (hT : ∀ x, f₀ ((T : Matrix (Fin 3) (Fin 3) R) *ᵥ x) = f₀ x) (S₁ : GL (Fin 2) R)
    (hS₁ : ∀ i, (spinRep S₁ : Matrix (Fin 3) (Fin 3) R) i 0 = (T : Matrix (Fin 3) (Fin 3) R) i 0) :
    ∃ S : GL (Fin 2) R, spinRep S = T := by
  have hmul : ∀ A B : SpecialLinearGroup (Fin 3) R,
      ((A * B : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = A * B := fun _ _ => rfl
  obtain ⟨T', hT'def⟩ : ∃ T', T' = (spinRep S₁)⁻¹ * T := ⟨_, rfl⟩
  have hT' : ∀ x, f₀ ((T' : Matrix (Fin 3) (Fin 3) R) *ᵥ x) = f₀ x := by
    intro x
    rw [hT'def, hmul, ← Matrix.mulVec_mulVec, ← map_inv, f₀_spinRep, hT]
  have hcol : (T : Matrix (Fin 3) (Fin 3) R) *ᵥ ![1, 0, 0] =
      (spinRep S₁ : Matrix (Fin 3) (Fin 3) R) *ᵥ ![1, 0, 0] := by
    ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hS₁]
  have hcol' : (T' : Matrix (Fin 3) (Fin 3) R) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
    rw [hT'def, hmul, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_mulVec, ← hmul, inv_mul_cancel]
    exact Matrix.one_mulVec _
  have hc0 := congrFun hcol' 0
  have hc1 := congrFun hcol' 1
  have hc2 := congrFun hcol' 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hc0 hc1 hc2
  obtain ⟨S₂, hS₂⟩ := eq_spinRep_of_fix T' hT' hc0 hc1 hc2
  refine ⟨S₁ * S₂, ?_⟩
  rw [map_mul, hS₂, hT'def, mul_inv_cancel_left]

/-- Over a field, the matrix of $T(S)$ is $(\det S)^{-1}\mathrm{symSq}(S)$. -/
theorem coe_spinRep_field {K : Type*} [Field K] (S : GL (Fin 2) K) :
    ((spinRep S : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((S : Matrix (Fin 2) (Fin 2) K).det)⁻¹ • symSq (S : Matrix (Fin 2) (Fin 2) K) := by
  rw [coe_spinRep, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]

/-- Over a field, every nonzero $\vec{c}$ with $f_0(\vec{c}) = 0$ is the first column of some $T(S_1)$ ((5.9)–(5.11)). -/
theorem exists_spinRep_col {K : Type*} [Field K] (c : Fin 3 → K) (hc : f₀ c = 0) (hc0 : c ≠ 0) :
    ∃ S : GL (Fin 2) K, ∀ i, (spinRep S : Matrix (Fin 3) (Fin 3) K) i 0 = c i := by
  simp only [f₀] at hc
  by_cases h0 : c 0 = 0
  · have h1 : c 1 = 0 := by rw [h0] at hc; simpa using hc
    have h2 : c 2 ≠ 0 := by
      intro h2; apply hc0; ext i; fin_cases i <;> simp [h0, h1, h2]
    have hdet : (!![0, -1 / c 2; 1, 0] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      simp [Matrix.det_fin_two, h2]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, fun i => ?_⟩
    rw [coe_spinRep_field]
    fin_cases i <;> simp [symSq, GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two, h0, h1, div_neg]
  · have hdet : (!![1, 0; c 1 / c 0, 1 / c 0] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      simp [Matrix.det_fin_two, h0]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, fun i => ?_⟩
    rw [coe_spinRep_field]
    fin_cases i <;> simp [symSq, GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]
    · field_simp
    · field_simp; linear_combination -hc

/-- Over a field, every automorph of $f_0$ in $SL_3$ is some $T(S)$. -/
theorem spinRep_surjective {K : Type*} [Field K] (T : SpecialLinearGroup (Fin 3) K)
    (hT : ∀ x, f₀ ((T : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = f₀ x) :
    ∃ S : GL (Fin 2) K, spinRep S = T := by
  set c : Fin 3 → K := fun i => (T : Matrix (Fin 3) (Fin 3) K) i 0
  have hcv : (T : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = c := by
    ext i; simp [c, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hc : f₀ c = 0 := by rw [← hcv, hT]; simp [f₀]
  have hc0 : c ≠ 0 := by
    intro h
    have hdet := T.prop
    have h0 : ∀ i, (T : Matrix (Fin 3) (Fin 3) K) i 0 = 0 := fun i => congrFun h i
    rw [Matrix.det_fin_three, h0, h0, h0] at hdet
    simp at hdet
  obtain ⟨S₁, hS₁⟩ := exists_spinRep_col c hc hc0
  exact exists_spinRep_of_col T hT S₁ hS₁


/-- Over $\mathbb Z$, the matrix of $T(S)$ is $\det(S)\,\mathrm{symSq}(S)$ (as $\det S = \pm1$). -/
theorem coe_spinRep_int (S : GL (Fin 2) ℤ) :
    ((spinRep S : SpecialLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
      (S : Matrix (Fin 2) (Fin 2) ℤ).det • symSq (S : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [coe_spinRep, Int.units_inv_eq_self, GeneralLinearGroup.val_det_apply]

/-- Over $\mathbb Z$, every integral automorph of $f_0$ in $SL_3(\mathbb Z)$ is $T(S)$ for an integral $S$ with $\det S = \pm1$: the first column of $T$ is primitive with $t_{00}t_{20} = t_{10}^{2}$, hence $\pm(\alpha^{2}, \alpha\gamma, \gamma^{2})$ with $\gcd(\alpha,\gamma) = 1$ (proof of Lemma 5.2). -/
theorem spinRep_surjective_int (T : SpecialLinearGroup (Fin 3) ℤ)
    (hT : ∀ x, f₀ ((T : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ x) = f₀ x) :
    ∃ S : GL (Fin 2) ℤ, spinRep S = T := by
  set M := (T : Matrix (Fin 3) (Fin 3) ℤ) with hM
  have hc : M 0 0 * M 2 0 = M 1 0 ^ 2 := by
    have := hT ![1, 0, 0]
    rw [f₀_mulVec_apply] at this
    simp [f₀] at this; linear_combination this
  have hdet := T.prop
  rw [Matrix.det_fin_three, ← hM] at hdet
  -- the first column is primitive, so `M 0 0` and `M 2 0` are coprime
  have hcop : IsCoprime (M 0 0) (M 2 0) := by
    set A := M 1 1 * M 2 2 - M 1 2 * M 2 1
    set B := M 0 2 * M 2 1 - M 0 1 * M 2 2
    set C := M 0 1 * M 1 2 - M 0 2 * M 1 1
    have hE : M 0 0 * A + M 1 0 * B + M 2 0 * C = 1 := by
      simp only [A, B, C]; linear_combination hdet
    set L := M 0 0 * A + M 2 0 * C
    refine ⟨A * L + 2 * M 1 0 * B * A + M 2 0 * B ^ 2, C * L + 2 * M 1 0 * B * C, ?_⟩
    simp only [L]
    linear_combination (M 0 0 * A + M 1 0 * B + M 2 0 * C + 1) * hE + B ^ 2 * hc
  obtain ⟨a, ha⟩ := Int.sq_of_isCoprime hcop (by rw [hc])
  obtain ⟨ε, hε, hεa⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ M 0 0 = ε * a ^ 2 := by
    rcases ha with h | h
    · exact ⟨1, by norm_num, by rw [h]; ring⟩
    · exact ⟨-1, by norm_num, by rw [h]; ring⟩
  by_cases ha0 : a = 0
  · rw [ha0] at hεa
    have h00 : M 0 0 = 0 := by simpa using hεa
    have h10 : M 1 0 = 0 := by rw [h00] at hc; simpa using hc.symm
    rw [h00] at hcop
    have hu : IsUnit (M 2 0) := isCoprime_zero_left.1 hcop
    have hU : IsUnit (!![(0 : ℤ), -M 2 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simpa [Matrix.det_fin_two] using hu
    refine exists_spinRep_of_col T hT (Matrix.nonsingInvUnit _ hU) (fun i => ?_)
    rw [coe_spinRep_int]
    rcases Int.isUnit_iff.1 hu with h | h <;>
      fin_cases i <;> simp [symSq, Matrix.nonsingInvUnit, Matrix.det_fin_two, ← hM, h00, h10, h]
  · have hdvd : a ^ 2 ∣ M 1 0 ^ 2 := ⟨ε * M 2 0, by rw [← hc, hεa]; ring⟩
    obtain ⟨k, hk⟩ := (Int.pow_dvd_pow_iff two_ne_zero).1 hdvd
    have h20 : M 2 0 = ε * k ^ 2 := by
      have : a ^ 2 * (ε * M 2 0) = a ^ 2 * k ^ 2 := by
        linear_combination hεa * 0 + hc - 0 * hk + (M 1 0 + a * k) * hk - (M 2 0) * hεa
      have h' := mul_left_cancel₀ (pow_ne_zero 2 ha0) this
      linear_combination ε * h' - M 2 0 * hε
    -- Bezout for `a` and `k`
    obtain ⟨u, v, huv⟩ := hcop
    rw [hεa, h20] at huv
    have hD : (!![a, -(ε * v * k); ε * k, u * a] : Matrix (Fin 2) (Fin 2) ℤ).det = ε := by
      rw [Matrix.det_fin_two_of]; linear_combination ε * huv - u * a ^ 2 * hε
    refine exists_spinRep_of_col T hT (Matrix.nonsingInvUnit _ (hD ▸ IsUnit.of_mul_eq_one ε hε))
      (fun i => ?_)
    rw [coe_spinRep_int]
    have hD' : (Matrix.nonsingInvUnit _ (hD ▸ IsUnit.of_mul_eq_one ε hε) : Matrix (Fin 2) (Fin 2) ℤ).det = ε := hD
    rw [hD']
    fin_cases i <;> simp [symSq, Matrix.nonsingInvUnit, ← hM, hεa, hk, h20]
    · linear_combination (a * k) * hε
    · left; linear_combination k ^ 2 * hε


/-- **Lemma 5.1**: over a field $K$, $S \mapsto T(S)$ is a homomorphism of $GL_2(K)$ onto the group $O^{+}_K(f_0)$ of proper automorphs of $f_0 = x_0x_2 - x_1^{2}$, with kernel the scalar matrices. (Cassels states it for $K = \mathbb Q$.) -/
@[kb "cassels1978" "Ch. 13, §5, Lemma 5.1, p. 301"]
theorem lemma_5_1 {K : Type*} [Field K] :
    (∀ (S : GL (Fin 2) K) (x : Fin 3 → K), f₀ ((spinRep S : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = f₀ x) ∧
    (∀ T : SpecialLinearGroup (Fin 3) K, (∀ x, f₀ ((T : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = f₀ x) →
      ∃ S : GL (Fin 2) K, spinRep S = T) ∧
    (∀ S : GL (Fin 2) K, spinRep S = 1 ↔ ∃ c : K, (S : Matrix (Fin 2) (Fin 2) K) = c • 1) :=
  ⟨f₀_spinRep, spinRep_surjective, spinRep_eq_one_iff⟩

/-- **Lemma 5.2**: $S \mapsto T(S)$ is a homomorphism of $SL^{\pm}_2(\mathbb Z) = GL_2(\mathbb Z)$ onto the group $O^{+}(f_0)$ of proper integral automorphs of $f_0 = x_0x_2 - x_1^{2}$, with kernel $\{\pm I\}$. -/
@[kb "cassels1978" "Ch. 13, §5, Lemma 5.2, p. 302"]
theorem lemma_5_2 :
    (∀ (S : GL (Fin 2) ℤ) (x : Fin 3 → ℤ), f₀ ((spinRep S : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ x) = f₀ x) ∧
    (∀ T : SpecialLinearGroup (Fin 3) ℤ, (∀ x, f₀ ((T : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ x) = f₀ x) →
      ∃ S : GL (Fin 2) ℤ, spinRep S = T) ∧
    (∀ S : GL (Fin 2) ℤ, spinRep S = 1 ↔ S = 1 ∨ S = -1) :=
  ⟨f₀_spinRep, spinRep_surjective_int, spinRep_eq_one_iff_int⟩


/-- The classically integral binary form $\varphi_{\vec{x}}(u_0,u_1) = x_0u_0^{2} + 2x_1u_0u_1 + x_2u_1^{2}$ with coefficient vector $\vec{x}$ (Cassels (5.2)); its determinant $x_0x_2 - x_1^{2}$ is $f_0(\vec{x})$, and $\vec{x} \mapsto \varphi_{\vec{x}}$ is a bijection from $\mathbb Z^{3}$ onto the classically integral binary forms. -/
@[kb "cassels1978" "Ch. 13, §5, (5.2), p. 301"]
def phi (x : Fin 3 → R) (u : Fin 2 → R) : R := x 0 * u 0 ^ 2 + 2 * x 1 * u 0 * u 1 + x 2 * u 1 ^ 2

/-- $\varphi_{\mathrm{symSq}(S)\vec{x}}(\vec{u}) = \varphi_{\vec{x}}(S^{\mathsf T}\vec{u})$. -/
theorem phi_symSq (S : Matrix (Fin 2) (Fin 2) R) (x : Fin 3 → R) (u : Fin 2 → R) :
    phi (symSq S *ᵥ x) u = phi x (Sᵀ *ᵥ u) := by
  simp [phi, symSq, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]; ring

/-- A binary form determines its coefficient vector (characteristic $0$). -/
theorem eq_of_phi_eq {x y : Fin 3 → R} [IsDomain R] [CharZero R] (h : ∀ u, phi x u = phi y u) : x = y := by
  have h1 := h ![1, 0]
  have h2 := h ![0, 1]
  have h3 := h ![1, 1]
  simp [phi] at h1 h2 h3
  have h4 : (2 : R) * (x 1 - y 1) = 0 := by linear_combination h3 - h1 - h2
  have h5 : x 1 = y 1 := sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left two_ne_zero)
  ext i; fin_cases i <;> simp [h1, h2, h5]

/-- For $\det S = 1$, $T(S) = \mathrm{symSq}(S)$. -/
theorem coe_spinRep_toGL (S : SpecialLinearGroup (Fin 2) R) :
    ((spinRep (SpecialLinearGroup.toGL S) : SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      symSq (S : Matrix (Fin 2) (Fin 2) R) := by
  rw [coe_spinRep]
  have : GeneralLinearGroup.det (SpecialLinearGroup.toGL S) = 1 := by
    ext; rw [GeneralLinearGroup.val_det_apply]; exact S.prop
  rw [this, inv_one, Units.val_one, one_smul]; rfl

/-- The transpose of a matrix in $SL_2$. -/
def trSL (U : SpecialLinearGroup (Fin 2) R) : SpecialLinearGroup (Fin 2) R :=
  ⟨(U : Matrix (Fin 2) (Fin 2) R)ᵀ, by rw [Matrix.det_transpose]; exact U.prop⟩

/-- The matrix of `trSL U` is $U^{\mathsf T}$. -/
theorem coe_trSL (U : SpecialLinearGroup (Fin 2) R) :
    ((trSL U : SpecialLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (U : Matrix (Fin 2) (Fin 2) R)ᵀ := rfl

/-- **Lemma 5.3**: two integral vectors $\vec{b}, \vec{b}'$ lie in the same orbit of the group $\mathfrak G = \{T(S) : S \in SL_2(\mathbb Z)\}$ if and only if the binary forms $\varphi_{\vec{b}}$, $\varphi_{\vec{b}'}$ are properly equivalent ($\varphi_{\vec{b}'}(\vec{u}) = \varphi_{\vec{b}}(U\vec{u})$, $U \in SL_2(\mathbb Z)$). Since $f_0(\vec{b})$ is the determinant of $\varphi_{\vec{b}}$ and $\vec{b} \mapsto \varphi_{\vec{b}}$ is a bijection onto the classically integral binary forms (`phi`), the $\mathfrak G$-orbits of the $\vec{b}$ with $f_0(\vec{b}) = m$ correspond bijectively to the proper classes of classically integral binary forms of determinant $m$. -/
@[kb "cassels1978" "Ch. 13, §5, Lemma 5.3, p. 303"]
theorem lemma_5_3 (b b' : Fin 3 → ℤ) :
    (∃ S : SpecialLinearGroup (Fin 2) ℤ,
      (spinRep (SpecialLinearGroup.toGL S) : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ b = b') ↔
    ∃ U : SpecialLinearGroup (Fin 2) ℤ, ∀ u : Fin 2 → ℤ,
      phi b' u = phi b ((U : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨trSL S, fun u => ?_⟩
    rw [← hS, coe_spinRep_toGL, phi_symSq, coe_trSL]
  · rintro ⟨U, hU⟩
    refine ⟨trSL U, ?_⟩
    apply eq_of_phi_eq
    intro u
    rw [coe_spinRep_toGL, coe_trSL, phi_symSq, Matrix.transpose_transpose, hU]

end QuadFormsKB.Cassels.Ch13
