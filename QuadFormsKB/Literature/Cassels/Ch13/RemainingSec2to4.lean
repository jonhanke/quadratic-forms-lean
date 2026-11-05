/-
# Cassels, Chapter 13, §§2–4: remaining items

Formalization of six items of Cassels, *Rational Quadratic Forms* (1978), Chapter 13, *Automorphs of integral forms*,
that were not covered by `Sec2.lean`, `Sec3.lean`, `Sec4.lean`:

* the Note after Theorem 2.2 (p. 287): the conclusion of Theorem 2.2 fails for every isotropic integral form, and the
  example $x_0x_1$ (`not_exists_aut_mul_bounded`, `not_exists_aut_bounded`, `xy_realAut`, `xy_aut_finite`);
* (3.1) (p. 289): a real indefinite binary form is real-equivalent to $xy$ (`binary_real_equiv_xy`);
* Example (ii) (p. 293): $a^2 - 82b^2 = 2$ is soluble in $\mathbb{R}$ and in every $\mathbb{Z}_p$ but not in $\mathbb{Z}$
  (`sq_sub_82_sq_padic`, `no_local_global_sq_sub_82`);
* (4.2) (p. 299): the form $ax^2 - by^2 - cz^2$ (`f42_fixZ_infinite`, `f42_fixY_infinite`, `f42_nonabelian`);
* the example after Theorem 4.2 (p. 300): $2x_0x_1 + x_2^2$ (`f5_nonabelian`, `f5_A_unipotent`);
* the remark on unipotent automorphs (p. 300) (`unipotent_automorph_isotropic`).

**Conventions.** As in `Sec2.lean`: the real matrix of a form is `realMat Q` (half the Hessian), a real automorph is a
real matrix $S$ with $S^{\mathsf T}FS = F$, integral automorphs are `Siegel.Aut Q`. Indices are 0-based, so Cassels'
variables $x, y, z$ of (4.2) are $x_0, x_1, x_2$ and his $x_1, x_2, x_3$ of the example on p. 300 are $x_0, x_1, x_2$.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec2
import QuadFormsKB.Literature.Cassels.Ch13.Sec3
import QuadFormsKB.Literature.Cassels.Ch1Sec1

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-! ### Linear algebra helpers -/

/-- Helper: a matrix is determined by its bilinear form. -/
theorem ext_bilin {K : Type*} [CommRing K] {A B : Matrix (Fin n) (Fin n) K}
    (h : ∀ x y : Fin n → K, x ⬝ᵥ A *ᵥ y = x ⬝ᵥ B *ᵥ y) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one] using this

/-- Helper: the bilinear form of a symmetric matrix is symmetric. -/
theorem bilin_symm {K : Type*} [CommRing K] {F : Matrix (Fin n) (Fin n) K} (hF : F.IsSymm)
    (x y : Fin n → K) : x ⬝ᵥ F *ᵥ y = y ⬝ᵥ F *ᵥ x := by
  calc x ⬝ᵥ F *ᵥ y = (x ᵥ* F) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
    _ = y ⬝ᵥ (x ᵥ* F) := dotProduct_comm _ _
    _ = y ⬝ᵥ F *ᵥ x := by rw [← Matrix.vecMul_transpose, hF.eq]

/-- Helper: $x^{\mathsf T}(P^{\mathsf T}FP)y = (Px)^{\mathsf T}F(Py)$. -/
theorem bilin_conj {K : Type*} [CommRing K] (P F : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    x ⬝ᵥ (Pᵀ * F * P) *ᵥ y = (P *ᵥ x) ⬝ᵥ F *ᵥ (P *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Helper: a nonzero matrix has a vector with nonzero image. -/
theorem exists_mulVec_ne_zero' {K : Type*} [CommRing K] {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0) :
    ∃ u, A *ᵥ u ≠ 0 := by
  by_contra h
  push Not at h
  apply hA
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

/-- Helper: the real matrix of a nondegenerate integral form is symmetric with nonzero determinant. -/
theorem realMat_symm_det' (Q : IntQF n) (hQ : Q.Nondegenerate) :
    (realMat Q).IsSymm ∧ (realMat Q).det ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have hs : Q.hessian.transpose = Q.hessian := by
      simp [QuadForm.hessian, Matrix.transpose_add, add_comm]
    show ((1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ))ᵀ = _
    rw [Matrix.transpose_smul, ← Matrix.transpose_map, hs]
  · have h1 : (Q.hessian.map (algebraMap ℤ ℝ)).det = algebraMap ℤ ℝ Q.hessian.det := by
      have := (algebraMap ℤ ℝ).map_det Q.hessian
      simpa [RingHom.mapMatrix_apply] using this.symm
    rw [Matrix.det_smul, h1]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) fun h => hQ ((algebraMap ℤ ℝ).injective_int (by rw [h, map_zero]))

/-- Helper: a real matrix with $S^{\mathsf T}FS = F$, $\det F \ne 0$ is invertible. -/
theorem isUnit_det_of_automorph' {F S : Matrix (Fin n) (Fin n) ℝ} (hdet : F.det ≠ 0)
    (hS : Sᵀ * F * S = F) : IsUnit S.det := by
  have h1 := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : S.det * S.det = 1 := by
    have : F.det * (S.det * S.det) = F.det * 1 := by linear_combination h1
    exact mul_left_cancel₀ hdet this
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0] at h2; simp at h2

/-! ### Row 13.r8a: the Note after Theorem 2.2 (p. 287) -/

/-- Helper: for $b \ne 0$ with $b^{\mathsf T}Fb = 0$ there is $c$ with $b^{\mathsf T}Fc = 1$, $c^{\mathsf T}Fc = 0$. -/
theorem exists_dual_isotropic {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0)
    {b : Fin n → ℝ} (hb : b ≠ 0) (hbb : b ⬝ᵥ F *ᵥ b = 0) :
    ∃ c : Fin n → ℝ, b ⬝ᵥ F *ᵥ c = 1 ∧ c ⬝ᵥ F *ᵥ c = 0 := by
  have hw : F *ᵥ b ≠ 0 := by
    intro h; apply hb
    have hFi : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    calc b = (F⁻¹ * F) *ᵥ b := by rw [hFi, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  set w := F *ᵥ b with hwdef
  have hs : 0 < w ⬝ᵥ w := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h => hw (dotProduct_self_eq_zero.1 h))
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  set s := w ⬝ᵥ w with hsdef
  set c0 : Fin n → ℝ := s⁻¹ • w with hc0
  have h1 : c0 ⬝ᵥ F *ᵥ b = 1 := by
    rw [hc0, smul_dotProduct, smul_eq_mul, ← hwdef, ← hsdef, inv_mul_cancel₀ hs.ne']
  have h2 : b ⬝ᵥ F *ᵥ c0 = 1 := by rw [bilin_symm hF, h1]
  have hbb' : b ⬝ᵥ F *ᵥ b = 0 := hbb
  set t := c0 ⬝ᵥ F *ᵥ c0 with ht
  refine ⟨c0 - (t / 2) • b, ?_, ?_⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, h2, hbb']
    ring
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, h1, h2, hbb', ← ht]
    ring

/-- Helper: **the real automorph scaling an isotropic vector.** If $b \ne 0$ is a zero of the regular real form $F$,
then for every $s \ne 0$ there is a real automorph $S$ with $Sb = sb$ (a "boost" in a hyperbolic plane containing $b$). -/
theorem exists_automorph_scale {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) (hdet : F.det ≠ 0)
    {b : Fin n → ℝ} (hb : b ≠ 0) (hbb : b ⬝ᵥ F *ᵥ b = 0) {s : ℝ} (hs : s ≠ 0) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, Sᵀ * F * S = F ∧ S *ᵥ b = s • b := by
  obtain ⟨c, hbc, hcc⟩ := exists_dual_isotropic hF hdet hb hbb
  have hcb : c ⬝ᵥ F *ᵥ b = 1 := by rw [bilin_symm hF, hbc]
  set α := s - 1 with hα
  set β := s⁻¹ - 1 with hβ
  have hrel : α * β + α + β = 0 := by
    simp only [hα, hβ]; field_simp; ring
  set S : Matrix (Fin n) (Fin n) ℝ :=
    1 + α • vecMulVec b (c ᵥ* F) + β • vecMulVec c (b ᵥ* F) with hS
  have hSx : ∀ x, S *ᵥ x = x + (α * (c ⬝ᵥ F *ᵥ x)) • b + (β * (b ⬝ᵥ F *ᵥ x)) • c := by
    intro x
    simp only [hS, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
      ← Matrix.dotProduct_mulVec, op_smul_eq_smul, smul_smul]
  refine ⟨S, ?_, ?_⟩
  · apply ext_bilin
    intro x y
    rw [bilin_conj, hSx, hSx]
    have e1 : x ⬝ᵥ F *ᵥ b = b ⬝ᵥ F *ᵥ x := bilin_symm hF _ _
    have e2 : x ⬝ᵥ F *ᵥ c = c ⬝ᵥ F *ᵥ x := bilin_symm hF _ _
    have e3 : y ⬝ᵥ F *ᵥ b = b ⬝ᵥ F *ᵥ y := bilin_symm hF _ _
    have e4 : y ⬝ᵥ F *ᵥ c = c ⬝ᵥ F *ᵥ y := bilin_symm hF _ _
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hbb, hcc, hbc, hcb, e1, e2, e3, e4]
    set u := c ⬝ᵥ F *ᵥ x
    set v := b ⬝ᵥ F *ᵥ x
    set u' := c ⬝ᵥ F *ᵥ y
    set v' := b ⬝ᵥ F *ᵥ y
    linear_combination (u * v' + v * u') * hrel
  · rw [hSx]
    simp only [hcb, hbb, mul_one, mul_zero, zero_smul, add_zero]
    rw [← one_smul ℝ b, smul_smul, ← add_smul]
    simp only [one_smul]
    congr 1
    simp [hα]

/-- Helper: a rational zero of an integral form gives a nonzero integral zero (clear denominators), whose real
value $f(\vec{b}) = \vec{b}^{\mathsf T}F\vec{b}$ vanishes. -/
theorem exists_int_zero_of_isotropic (Q : IntQF n) (hQ : Q.IsotropicIn ℚ) :
    ∃ b : Fin n → ℤ, b ≠ 0 ∧ cast b ⬝ᵥ realMat Q *ᵥ cast b = 0 := by
  obtain ⟨x, hx0, hx⟩ := hQ
  set D : ℕ := ∏ i, (x i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (x i).den_pos
  have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = D * x i := by
    intro i
    obtain ⟨m, hm⟩ : (x i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨(x i).num * m, ?_⟩
    rw [hm]; push_cast
    rw [← Rat.mul_den_eq_num]; ring
  choose z hz using hint
  have hz' : (fun i => (z i : ℚ)) = (D : ℚ) • x := by
    funext i; simp [hz]
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  refine ⟨z, ?_, ?_⟩
  · intro h0
    apply hx0
    funext i
    have := hz i
    rw [h0] at this
    simp only [Pi.zero_apply, Int.cast_zero] at this
    have h3 : (D : ℚ) * x i = 0 := this.symm
    simpa [hDq] using h3
  · have h1 : ((QuadForm.eval Q z : ℤ) : ℚ) = 0 := by
      have e : ((QuadForm.eval Q z : ℤ) : ℚ) = Q.evalIn ℚ (fun i => (z i : ℚ)) := by
        simp [QuadForm.evalIn]
      have homog : Q.evalIn ℚ ((D : ℚ) • x) = (D : ℚ) ^ 2 * Q.evalIn ℚ x := by
        rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
          smul_dotProduct, smul_eq_mul, smul_eq_mul]
        ring
      rw [e, hz', homog, hx, mul_zero]
    have h0 : QuadForm.eval Q z = 0 := by exact_mod_cast h1
    have h2 : val (realMat Q) (cast z) = ((QuadForm.eval Q z : ℤ) : ℝ) := by
      rw [← QuadForm.evalIn_real_eq_val]
      simp [QuadForm.evalIn, cast]
    show val (realMat Q) (cast z) = 0
    rw [h2, h0]; simp

/-- **The Note after Theorem 2.2** (Cassels, Ch. 13, §2, p. 287), the conclusion of Theorem 2.2 fails for every
isotropic form. Let $f$ be an integral regular form that is isotropic over $\mathbb{Q}$ and let $k \in \mathbb{R}$. There
is a real automorph $S$ of $f$ such that for **every** integral automorph $T \in O(f)$ some entry of $TS^{-1}$ exceeds
$k$ in absolute value. (This is the failure of the first half of Theorem 2.2, `exists_aut_mul_bounded`, for isotropic
$f$; `not_exists_aut_bounded` below states the negation of the whole conclusion.) The proof: a rational zero $\vec{b}$
of $f$, made integral, is scaled by the real automorph $S_s$ of `exists_automorph_scale` ($S_s\vec{b} = s\vec{b}$), so
$TS_s^{-1}\vec{b} = s^{-1}T\vec{b}$ with $T\vec{b}$ a nonzero integral vector; take $s$ small. -/
@[kb "cassels1978" "Ch. 13, §2, Note after Thm. 2.2, p. 287 (conclusion fails for isotropic f)"]
theorem not_exists_aut_mul_bounded (Q : IntQF n) (hreg : Q.Nondegenerate) (hiso : Q.IsotropicIn ℚ) (k : ℝ) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, Sᵀ * realMat Q * S = realMat Q ∧
      ∀ T ∈ Siegel.Aut Q, ∃ i j, k < |(castM T.val * S⁻¹) i j| := by
  obtain ⟨hs, hdet⟩ := realMat_symm_det' Q hreg
  obtain ⟨bz, hbz0, hbz⟩ := exists_int_zero_of_isotropic Q hiso
  set b : Fin n → ℝ := cast bz with hb
  have hb0 : b ≠ 0 := by
    intro h; apply hbz0; funext i
    have := congrFun h i
    simpa [hb, cast] using this
  set β0 : ℝ := ∑ j, |b j| with hβ0
  set L : ℝ := |k| * β0 + 1 with hL
  have hβ0nn : 0 ≤ β0 := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hLpos : 0 < L := by positivity
  obtain ⟨S, hS, hSb⟩ := exists_automorph_scale hs hdet hb0 hbz (inv_ne_zero hLpos.ne')
  refine ⟨S, hS, fun T hT => ?_⟩
  by_contra hcon
  push Not at hcon
  have hSu := isUnit_det_of_automorph' hdet hS
  have hSinv : S⁻¹ *ᵥ b = L • b := by
    have h1 : S⁻¹ *ᵥ (S *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mulVec]
    rw [hSb, Matrix.mulVec_smul] at h1
    have h2 := congrArg (fun v => L • v) h1
    simp only [smul_smul, mul_inv_cancel₀ hLpos.ne', one_smul] at h2
    exact h2
  have hTb : castM T.val *ᵥ b = cast (T.val *ᵥ bz) := castM_mulVec_cast _ _
  have hTnz : T.val *ᵥ bz ≠ 0 := by
    intro h; apply hbz0
    have h1 : (T⁻¹).val *ᵥ (T.val *ᵥ bz) = bz := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at h1
    exact h1.symm
  obtain ⟨i, hi⟩ : ∃ i, (T.val *ᵥ bz) i ≠ 0 := by
    by_contra h; push Not at h; exact hTnz (funext h)
  have hent : (castM T.val * S⁻¹) *ᵥ b = L • cast (T.val *ᵥ bz) := by
    rw [← Matrix.mulVec_mulVec, hSinv, Matrix.mulVec_smul, hTb]
  have h1 : L ≤ |((castM T.val * S⁻¹) *ᵥ b) i| := by
    rw [hent]
    have : (1 : ℝ) ≤ |(cast (T.val *ᵥ bz) : Fin n → ℝ) i| := by
      have := Int.one_le_abs hi
      simpa [cast] using (by exact_mod_cast this : (1 : ℝ) ≤ |((T.val *ᵥ bz) i : ℝ)|)
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hLpos]
    nlinarith
  have h2 : |((castM T.val * S⁻¹) *ᵥ b) i| ≤ |k| * β0 := by
    rw [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(castM T.val * S⁻¹) i j * b j| = ∑ j, |(castM T.val * S⁻¹) i j| * |b j| := by
          simp only [abs_mul]
      _ ≤ ∑ j, |k| * |b j| := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right ((hcon i j).trans (le_abs_self k)) (abs_nonneg _)
      _ = |k| * β0 := by rw [← Finset.mul_sum]
  linarith

/-- **The Note after Theorem 2.2, negated conclusion** (Cassels, Ch. 13, §2, p. 287): for an integral regular form
$f$ that is isotropic over $\mathbb{Q}$ there is **no** constant $k$ such that for every real automorph $S$ there are
integral automorphs $T, W \in O(f)$ with all entries of $TS^{-1}$ and of $S^{-1}W$ at most $k$ in absolute value (the
conclusion of Theorem 2.2, `exists_aut_mul_bounded`, is false). Already the condition on $T$ alone fails
(`not_exists_aut_mul_bounded`). -/
@[kb "cassels1978" "Ch. 13, §2, Note after Thm. 2.2, p. 287 (Thm. 2.2 false for isotropic f)"]
theorem not_exists_aut_bounded (Q : IntQF n) (hreg : Q.Nondegenerate) (hiso : Q.IsotropicIn ℚ) :
    ¬ ∃ k : ℝ, ∀ S : Matrix (Fin n) (Fin n) ℝ, Sᵀ * realMat Q * S = realMat Q →
      ∃ T ∈ Siegel.Aut Q, ∃ W ∈ Siegel.Aut Q,
        ∀ i j, |(castM T.val * S⁻¹) i j| ≤ k ∧ |(S⁻¹ * castM W.val) i j| ≤ k := by
  rintro ⟨k, hk⟩
  obtain ⟨S, hS, hT⟩ := not_exists_aut_mul_bounded Q hreg hiso k
  obtain ⟨T, hT', W, hW, h⟩ := hk S hS
  obtain ⟨i, j, hij⟩ := hT T hT'
  exact absurd (h i j).1 (not_le.2 hij)

/-- **The form $x_0x_1$ as an integral binary form** (Cassels' $x_1x_2$, the example of the Note on p. 287). -/
def xyForm : BinQF := BinQF.mk 0 1 0

/-- The real matrix of $x_0x_1$ is $\begin{pmatrix}0 & 1/2\\ 1/2 & 0\end{pmatrix}$. -/
theorem realMat_xyForm : realMat xyForm = !![0, 1 / 2; 1 / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xyForm, QuadForm.hessian, BinQF.mk, QuadForm.ofUpper]

/-- The value of $x_0x_1$ is the product of the coordinates. -/
theorem eval_xyForm (x : Fin 2 → ℤ) : QuadForm.eval xyForm x = x 0 * x 1 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, xyForm, BinQF.mk, QuadForm.ofUpper]

/-- **The example of the Note after Theorem 2.2, real automorphs** (Cassels, Ch. 13, §2, p. 287): for every real
$s \ne 0$ the substitution $x_0 \mapsto sx_0$, $x_1 \mapsto s^{-1}x_1$ is a real automorph of $f = x_0x_1$
(Cassels' $x_1, x_2$). -/
@[kb "cassels1978" "Ch. 13, §2, Note after Thm. 2.2, p. 287 (x₁x₂ has real automorphs x₁→sx₁, x₂→s⁻¹x₂)"]
theorem xy_realAut (s : ℝ) (hs : s ≠ 0) :
    ∃ S ∈ realAut (realMat xyForm), S.val = !![s, 0; 0, s⁻¹] := by
  refine ⟨⟨!![s, 0; 0, s⁻¹], !![s⁻¹, 0; 0, s], ?_, ?_⟩, ?_, rfl⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
  · show !![s, 0; 0, s⁻¹]ᵀ * realMat xyForm * !![s, 0; 0, s⁻¹] = realMat xyForm
    rw [realMat_xyForm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

/-- **The example of the Note after Theorem 2.2, integral automorphs** (Cassels, Ch. 13, §2, p. 287): the group of
integral automorphs of $x_0x_1$ is finite (in fact $\{\pm I, \pm\begin{pmatrix}0&1\\1&0\end{pmatrix}\}$). -/
@[kb "cassels1978" "Ch. 13, §2, Note after Thm. 2.2, p. 287 (the group of integral automorphs of x₁x₂ is finite)"]
theorem xy_aut_finite : (Siegel.Aut xyForm : Set (GL (Fin 2) ℤ)).Finite := by
  refine Set.Finite.of_injOn (f := fun T : GL (Fin 2) ℤ => T.val)
    (t := Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => Set.Icc (-1 : ℤ) 1) ?_ ?_
    (Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _)
  · intro T hT i _ j _
    have hA : ∀ x : Fin 2 → ℤ, QuadForm.eval xyForm (T.val *ᵥ x) = QuadForm.eval xyForm x := hT
    have h1 := hA ![1, 0]
    have h2 := hA ![0, 1]
    have h3 := hA ![1, 1]
    simp only [eval_xyForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2 h3
    simp at h1 h2 h3
    have hu : ∀ x y : ℤ, x * y = 1 → x = 1 ∨ x = -1 := fun x y h => Int.eq_one_or_neg_one_of_mul_eq_one h
    rcases h1 with ha | hc <;> rcases h2 with hb | hd
    · exfalso; rw [ha, hb] at h3; simp at h3
    · have hbc : T.val 0 1 * T.val 1 0 = 1 := by rw [ha, hd] at h3; simpa using h3
      have e1 := hu _ _ hbc
      have e2 := hu _ _ (by rw [mul_comm]; exact hbc : T.val 1 0 * T.val 0 1 = 1)
      fin_cases i <;> fin_cases j <;> simp [Set.mem_Icc] <;> omega
    · have hbc : T.val 0 0 * T.val 1 1 = 1 := by rw [hc, hb] at h3; simpa using h3
      have e1 := hu _ _ hbc
      have e2 := hu _ _ (by rw [mul_comm]; exact hbc : T.val 1 1 * T.val 0 0 = 1)
      fin_cases i <;> fin_cases j <;> simp [Set.mem_Icc] <;> omega
    · exfalso; rw [hc, hd] at h3; simp at h3
  · intro T _ T' _ h
    exact Units.ext h

/-! ### Row 13.r9: (3.1), a real indefinite binary form is equivalent to $xy$ -/

/-- Helper: a factorization $F = L^{\mathsf T}JL$ with $L$ invertible gives $S^{\mathsf T}FS = J$ for $S = L^{-1}$. -/
theorem exists_realEquiv_of_factor {F J L : Matrix (Fin 2) (Fin 2) ℝ} (hL : L.det ≠ 0)
    (h : Lᵀ * J * L = F) : ∃ S : GL (Fin 2) ℝ, S.valᵀ * F * S.val = J := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  refine ⟨⟨L⁻¹, L, Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu⟩, ?_⟩
  show (L⁻¹)ᵀ * F * L⁻¹ = J
  rw [← h]
  calc (L⁻¹)ᵀ * (Lᵀ * J * L) * L⁻¹ = (L * L⁻¹)ᵀ * J * (L * L⁻¹) := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J := by rw [Matrix.mul_nonsing_inv _ hu]; simp

/-- **(3.1): a real indefinite binary form is real-equivalent to $f_0(x, y) = xy$** (Cassels, Ch. 13, §3, p. 289).
Let $F$ be a symmetric real $2\times 2$ matrix with $\det F < 0$ (i.e. the real binary form $f$ with matrix $F$ is
regular and indefinite). Then there is $S \in \mathrm{GL}_2(\mathbb{R})$ with $S^{\mathsf T}FS$ the matrix
$\begin{pmatrix}0 & 1/2\\ 1/2 & 0\end{pmatrix}$ of $f_0 = xy$ (`realMat_xyForm`), i.e. $f(S\vec{x}) = x_0x_1$.
Proof: factor $f$ into two independent real linear forms (the discriminant $\beta^2 - \alpha\gamma$ is positive). -/
@[kb "cassels1978" "Ch. 13, §3, (3.1), p. 289 (indefinite real binary form ≃ xy)"]
theorem binary_real_equiv_xy {F : Matrix (Fin 2) (Fin 2) ℝ} (hF : F.IsSymm) (hdet : F.det < 0) :
    ∃ S : GL (Fin 2) ℝ, S.valᵀ * F * S.val = !![0, 1 / 2; 1 / 2, 0] := by
  obtain ⟨α, β, γ, rfl⟩ : ∃ α β γ : ℝ, F = !![α, β; β, γ] := by
    refine ⟨F 0 0, F 0 1, F 1 1, ?_⟩
    have h10 := hF.apply 0 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10]
  have hd' : α * γ - β ^ 2 < 0 := by
    rw [Matrix.det_fin_two_of] at hdet; linarith
  have hD : 0 < β ^ 2 - α * γ := by linarith
  obtain ⟨δ, hδ, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * δ = β ^ 2 - α * γ :=
    ⟨√(β ^ 2 - α * γ), Real.sqrt_pos.mpr hD, Real.mul_self_sqrt hD.le⟩
  by_cases hα : α = 0
  · subst hα
    have hβ : β ≠ 0 := by
      rintro rfl; simp at hd'
    refine exists_realEquiv_of_factor (L := !![0, 1; 2 * β, γ]) ?_ ?_
    · rw [Matrix.det_fin_two_of]; simpa using hβ
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · refine exists_realEquiv_of_factor (L := !![α, β + δ; 1, (β - δ) / α]) ?_ ?_
    · rw [Matrix.det_fin_two_of]
      have : α * ((β - δ) / α) - (β + δ) * 1 = -2 * δ := by field_simp; ring
      rw [this]; intro h; linarith
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
        | ring1
        | (field_simp; ring1)
        | (field_simp; linear_combination (-2) * hδ2)
        | (field_simp; linear_combination -hδ2)
        | (field_simp; linear_combination hδ2)

/-! ### Row 13.r16: Example (ii), $a^2 - 82b^2 = 2$ (p. 293) -/

/-- **Example (ii), local solubility** (Cassels, Ch. 13, §3, p. 293): for every prime $p$ the equation
$a^2 - 82b^2 = 2$ has a solution $a, b \in \mathbb{Z}_p$. Proof (as for $x^2 + 82y^2 = 2$, Ch. 1, §1, p. 3): for $p = 2$,
$(a, b) = (2, 1/\sqrt{41})$ ($41 \equiv 1 \bmod 8$); for $p = 41$, $(\sqrt{2}, 0)$ ($2 \equiv 17^2 \bmod 41$); for the other
$p$ Chevalley's theorem gives a solution modulo $p$ with $a \ne 0$ or $b \ne 0$, lifted by Hensel's lemma. -/
@[kb "cassels1978" "Ch. 13, §3, Example (ii), p. 293 (a² − 82b² = 2 is soluble in every ℤ_p)"]
theorem sq_sub_82_sq_padic (p : ℕ) [Fact p.Prime] : ∃ a b : ℤ_[p], a ^ 2 - 82 * b ^ 2 = 2 := by
  have hp := (Fact.out : p.Prime)
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨z, hz⟩ := QuadFormsKB.Binary.exists_sq_padic_two (c := 41) (by decide)
    push_cast at hz
    have h41 : IsUnit (41 : ℤ_[2]) := by
      apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
      rw [map_ofNat]; decide +revert
    have hu : IsUnit z := (isUnit_pow_iff two_ne_zero).mp (hz ▸ h41)
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    exact ⟨2, w, by linear_combination (2 * w ^ 2) * hz - (2 * (z * w + 1)) * hw⟩
  by_cases hp41 : p = 41
  · subst hp41
    obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod (p := 41) (by norm_num) (2 : ℤ_[41])
      (s := 17) (by decide +revert) (by rw [map_ofNat]; decide +revert)
    exact ⟨z, 0, by linear_combination hz⟩
  have h82 : (82 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((82 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have : p ∣ 2 * 41 := h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    · exact hp41 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)
  have h2' : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact Nat.odd_iff.mp (hp.eq_two_or_odd.resolve_left hp2 |> fun h => Nat.odd_iff.mpr h)
  have h82' : (-82 : ZMod p) ≠ 0 := neg_ne_zero.2 h82
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial (ZMod p)))
    (g := Polynomial.C (-82 : ZMod p) * Polynomial.X ^ 2 - Polynomial.C 2)
    (by rw [Polynomial.degree_X_pow]; rfl)
    (by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
      rw [Polynomial.degree_C_mul_X_pow _ h82'] <;> simp [Polynomial.degree_C h2'])
    hodd
  simp at hab
  have hab' : a ^ 2 - 82 * b ^ 2 = 2 := by linear_combination hab
  have h82u : IsUnit (82 : ℤ_[p]) := by
    apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
    rw [map_ofNat]; exact h82
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2'
      linear_combination -hab'
    obtain ⟨w, hw⟩ := h82u.exists_left_inv
    have hw' : PadicInt.toZMod w * 82 = 1 := by
      have := congrArg PadicInt.toZMod hw
      rw [map_mul, map_ofNat, map_one] at this
      exact this
    obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (-2 * w) (s := b) hb (by
      rw [map_mul, map_neg, map_ofNat]
      linear_combination (b ^ 2) * hw' + (PadicInt.toZMod w) * hab')
    exact ⟨0, z, by linear_combination (-82) * hz + 2 * hw⟩
  · set bt : ℤ_[p] := (b.val : ℤ_[p])
    have hbt : PadicInt.toZMod bt = b := by simp [bt]
    obtain ⟨z, hz⟩ := Siegel.Kneser.exists_sq_eq_of_toZMod hp2 (2 + 82 * bt ^ 2) (s := a) ha (by
      rw [map_add, map_mul, map_pow, hbt, map_ofNat, map_ofNat]
      linear_combination -hab')
    exact ⟨z, bt, by linear_combination hz⟩

/-- **Example (ii), local solubility, congruence form**: $a^2 - 82b^2 \equiv 2 \pmod{M}$ is soluble in integers for every
$M \ge 1$ (from `sq_sub_82_sq_padic` by reduction modulo prime powers and the Chinese remainder theorem). -/
theorem sq_sub_82_sq_modEq (M : ℕ) (hM : M ≠ 0) : ∃ a b : ℤ, (M : ℤ) ∣ a ^ 2 - 82 * b ^ 2 - 2 := by
  have hF := Cassels.exists_zmod_root_of_padic
    (MvPolynomial.X 0 ^ 2 - 82 * MvPolynomial.X 1 ^ 2 - 2 : MvPolynomial (Fin 2) ℤ)
    (fun p _ => by
      obtain ⟨a, b, hab⟩ := sq_sub_82_sq_padic p
      exact ⟨![a, b], by simp; linear_combination hab⟩) M hM
  obtain ⟨x, hx⟩ := hF
  exact ⟨x 0, x 1, by simpa using hx⟩

/-- **Example (ii): no local-to-global principle for integral representations** (Cassels, Ch. 13, §3, p. 293): the
equation $a^2 - 82b^2 = 2$ is soluble in $\mathbb{R}$ and in $\mathbb{Z}_p$ for every prime $p$, but has no solution
in integers $a, b \in \mathbb{Z}$ (`not_exists_sq_sub_82_sq`, via Pell's equation $t^2 - 82u^2 = -1$ and Lemma 3.3). -/
@[kb "cassels1978" "Ch. 13, §3, Example (ii), p. 293 (no local-global principle for integral representations)"]
theorem no_local_global_sq_sub_82 :
    (∃ a b : ℝ, a ^ 2 - 82 * b ^ 2 = 2) ∧ (∀ (p : ℕ) [Fact p.Prime], ∃ a b : ℤ_[p], a ^ 2 - 82 * b ^ 2 = 2) ∧
      ¬ ∃ a b : ℤ, a ^ 2 - 82 * b ^ 2 = 2 :=
  ⟨⟨√2, 0, by rw [Real.sq_sqrt (by norm_num)]; ring⟩, fun p _ => sq_sub_82_sq_padic p,
    fun h => not_exists_sq_sub_82_sq 2 (Or.inl rfl) h⟩

/-! ### Row 13.r25: unipotent automorphs (p. 300) -/

section Unipotent

variable {K : Type*} [Field K] [CharZero K]

/-- Helper: if $N^{k+1} = 0 \ne N^k$ ($k \ge 1$), where $N = T - 1$ and $T^{\mathsf T}FT = F$ with $F$ regular, then
$(N^k)^{\mathsf T}FN^k = 0$, so every nonzero vector in the image of $N^k$ is isotropic. Proof: the adjoint of $N$ with
respect to $F$ is $T^{-1} - 1 = -T^{-1}N$, which commutes with $N$; hence the adjoint of $N^k$ is $(-T^{-1})^kN^k$ and
$(N^k)^{\mathsf T}FN^k = F(-T^{-1})^kN^{2k} = 0$ since $2k \ge k + 1$. -/
theorem unipotent_isotropic {F T : Matrix (Fin n) (Fin n) K} (hdet : F.det ≠ 0)
    (hT : Tᵀ * F * T = F) {k : ℕ} (hk : 1 ≤ k) (hN : (T - 1) ^ (k + 1) = 0) (hNk : (T - 1) ^ k ≠ 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ x ⬝ᵥ F *ᵥ x = 0 := by
  set N := T - 1 with hNdef
  have hdT : IsUnit T.det := by
    have h1 := congrArg Matrix.det hT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
    have h2 : T.det * T.det = 1 := by
      have : F.det * (T.det * T.det) = F.det * 1 := by linear_combination h1
      exact mul_left_cancel₀ hdet this
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0] at h2; simp at h2
  have hTi : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdT
  have hiT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hdT
  have hadj : Nᵀ * F = F * (T⁻¹ - 1) := by
    have h1 : Tᵀ * F = F * T⁻¹ := by
      calc Tᵀ * F = Tᵀ * F * (T * T⁻¹) := by rw [hTi, Matrix.mul_one]
        _ = (Tᵀ * F * T) * T⁻¹ := by simp only [Matrix.mul_assoc]
        _ = F * T⁻¹ := by rw [hT]
    simp only [hNdef, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, Matrix.mul_one, h1]
  have hM : T⁻¹ - 1 = (-T⁻¹) * N := by
    simp only [hNdef, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_one, hiT]
    abel
  have hcomm : Commute (-T⁻¹) N := by
    refine Commute.neg_left ?_
    show T⁻¹ * N = N * T⁻¹
    simp only [hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hTi, hiT]
  have hpow : ∀ j : ℕ, (N ^ j)ᵀ * F = F * (T⁻¹ - 1) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hadj, Matrix.mul_assoc,
        ← pow_succ' (T⁻¹ - 1)]
  have hzero : (N ^ k)ᵀ * F * N ^ k = 0 := by
    rw [hpow, Matrix.mul_assoc, hM, hcomm.mul_pow, Matrix.mul_assoc, ← pow_add]
    have : N ^ (k + k) = 0 := by
      have : N ^ (k + 1) ∣ N ^ (k + k) := pow_dvd_pow _ (by omega)
      obtain ⟨c, hc⟩ := this
      rw [hc, hN, zero_mul]
    rw [this]; simp
  obtain ⟨u, hu⟩ := exists_mulVec_ne_zero' hNk
  refine ⟨N ^ k *ᵥ u, hu, ?_⟩
  have hq : u ⬝ᵥ ((N ^ k)ᵀ * F * N ^ k) *ᵥ u = (N ^ k *ᵥ u) ⬝ᵥ F *ᵥ (N ^ k *ᵥ u) := bilin_conj _ _ _ _
  rw [← hq, hzero]; simp

/-- Helper: a nilpotent matrix has a nilpotency index: $N^{k+1} = 0 \ne N^k$ with $k \ge 1$ when $N \ne 0$. -/
theorem exists_nilp_index {N : Matrix (Fin n) (Fin n) K} (hnil : IsNilpotent N) (hN : N ≠ 0) :
    ∃ k, 1 ≤ k ∧ N ^ (k + 1) = 0 ∧ N ^ k ≠ 0 := by
  classical
  have : Nontrivial (Matrix (Fin n) (Fin n) K) := nontrivial_of_ne N 0 hN
  have hex : ∃ m, N ^ m = 0 := hnil
  set m := Nat.find hex with hm
  have hm0 : N ^ m = 0 := Nat.find_spec hex
  have hmne : m ≠ 0 := by
    intro h; rw [h, pow_zero] at hm0; exact one_ne_zero hm0
  have hm1 : m ≠ 1 := by
    intro h; rw [h, pow_one] at hm0; exact hN hm0
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · rwa [show m - 1 + 1 = m by omega]
  · exact Nat.find_min hex (by omega)

/-- Helper: a nilpotent matrix over a field has determinant $0$ (when $n \ge 1$). -/
theorem det_eq_zero_of_pow [Nonempty (Fin n)] {N : Matrix (Fin n) (Fin n) K} {m : ℕ} (hm : m ≠ 0)
    (h : N ^ m = 0) : N.det = 0 := by
  have : N.det ^ m = 0 := by rw [← Matrix.det_pow, h, Matrix.det_zero]
  exact (pow_eq_zero_iff hm).1 this

/-- **Unipotent automorphs, matrix form** (Cassels, Ch. 13, §4, p. 300): let $F$ be a regular symmetric matrix over a
field $K$ of characteristic $0$, and $T$ an automorph ($T^{\mathsf T}FT = F$) with $T \ne I$ and $T - I$ nilpotent. Then the
form $\vec{x}^{\mathsf T}F\vec{x}$ is isotropic over $K$ and $n \ge 3$.
Proof: the image of $(T - I)^k$, $k$ the nilpotency index minus one, is totally isotropic (`unipotent_isotropic`); for
$n = 2$ with $N = T - I$ one has $N^2 = 0$ (Cayley–Hamilton), so $N$ is skew-adjoint, $FN$ is skew-symmetric of
determinant $0$, hence $FN = 0$ and $N = 0$; $n \le 1$ is trivial. -/
theorem unipotent_core {F T : Matrix (Fin n) (Fin n) K} (hF : F.IsSymm) (hdet : F.det ≠ 0)
    (hT : Tᵀ * F * T = F) (hnil : IsNilpotent (T - 1)) (hne : T ≠ 1) :
    (∃ x : Fin n → K, x ≠ 0 ∧ x ⬝ᵥ F *ᵥ x = 0) ∧ 3 ≤ n := by
  have hN : T - 1 ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨k, hk, hk1, hk0⟩ := exists_nilp_index hnil hN
  refine ⟨unipotent_isotropic hdet hT hk hk1 hk0, ?_⟩
  by_contra hlt
  push Not at hlt
  set N := T - 1 with hNdef
  interval_cases n
  · exact hne (Subsingleton.elim _ _)
  · have hd : N.det = 0 := det_eq_zero_of_pow (by omega) hk1
    rw [Matrix.det_unique] at hd
    apply hN
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simpa using hd
  · have hd0 : N.det = 0 := det_eq_zero_of_pow (by omega) hk1
    have hd := hd0
    have htr : N.trace = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    rw [Matrix.det_fin_two] at hd
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at htr
    have hN2 : N * N = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination (N 0 0) * htr - hd
      · linear_combination (N 0 1) * htr
      · linear_combination (N 1 0) * htr
      · linear_combination (N 1 1) * htr - hd
    have hT1 : T = 1 + N := by rw [hNdef]; abel
    have hinv : T * (1 - N) = 1 := by
      rw [hT1]; simp [Matrix.add_mul, Matrix.mul_sub, hN2]
    have hadj : Nᵀ * F = -(F * N) := by
      have h1 : Tᵀ * F = F * (1 - N) := by
        calc Tᵀ * F = Tᵀ * F * (T * (1 - N)) := by rw [hinv, Matrix.mul_one]
          _ = (Tᵀ * F * T) * (1 - N) := by simp only [Matrix.mul_assoc]
          _ = F * (1 - N) := by rw [hT]
      simp only [hNdef, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul] at *
      rw [h1]; simp [Matrix.mul_sub]
    have hGsk : (F * N)ᵀ = -(F * N) := by
      rw [Matrix.transpose_mul, hF.eq, hadj]
    have h2 : ∀ x : K, x = -x → x = 0 := fun x h => by
      have : (2 : K) * x = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h two_ne_zero
      · exact h
    have g00 : (F * N) 0 0 = 0 := by
      apply h2; simpa using congrFun (congrFun hGsk 0) 0
    have g11 : (F * N) 1 1 = 0 := by
      apply h2; simpa using congrFun (congrFun hGsk 1) 1
    have g10 : (F * N) 1 0 = -(F * N) 0 1 := by simpa using congrFun (congrFun hGsk 0) 1
    have hdG : (F * N).det = 0 := by rw [Matrix.det_mul, hd0, mul_zero]
    have g01 : (F * N) 0 1 = 0 := by
      rw [Matrix.det_fin_two, g00, g11, g10] at hdG
      have : (F * N) 0 1 * (F * N) 0 1 = 0 := by linear_combination hdG
      exact mul_self_eq_zero.1 this
    have hG : F * N = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [g00, g11, g01, g10]
    apply hN
    have hFi : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
    calc N = F⁻¹ * (F * N) := by rw [← Matrix.mul_assoc, hFi, Matrix.one_mul]
      _ = 0 := by rw [hG, Matrix.mul_zero]

end Unipotent

/-- Helper: $Q(\vec{x}) = \tfrac12\,\vec{x}^{\mathsf T}H\vec{x}$ over a field $K$ of characteristic $0$, $H$ the Hessian. -/
theorem evalIn_eq_half_hessian {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra R K]
    (Q : QuadForm R n) (x : Fin n → K) :
    Q.evalIn K x = (1 / 2 : K) * (x ⬝ᵥ (Q.hessian.map (algebraMap R K)) *ᵥ x) := by
  rw [QuadForm.evalIn_eq_dotProduct]
  have h : x ⬝ᵥ ((Q.coeff.map (algebraMap R K))ᵀ *ᵥ x) = x ⬝ᵥ (Q.coeff.map (algebraMap R K) *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [QuadForm.hessian, Matrix.map_add _ (map_add _), Matrix.transpose_map]
  simp only [Matrix.add_mulVec, dotProduct_add, h]
  ring

/-- Helper: the Hessian of a nondegenerate form is symmetric and invertible over any field extending $R$. -/
theorem hessian_symm_det {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (Q : QuadForm R n) (hQ : Q.Nondegenerate) :
    (Q.hessian.map (algebraMap R K)).IsSymm ∧ (Q.hessian.map (algebraMap R K)).det ≠ 0 := by
  refine ⟨?_, ?_⟩
  · show (Q.hessian.map (algebraMap R K))ᵀ = _
    rw [← Matrix.transpose_map]
    congr 1
    simp [QuadForm.hessian, Matrix.transpose_add, add_comm]
  · have : (Q.hessian.map (algebraMap R K)).det = algebraMap R K Q.hessian.det := by
      have := (algebraMap R K).map_det Q.hessian
      simpa [RingHom.mapMatrix_apply] using this.symm
    rw [this]
    exact fun h => hQ (hinj (by rw [h, map_zero]))

/-- **A unipotent automorph exists only for isotropic forms in more than two variables** (Cassels, Ch. 13, §4,
p. 300: "an automorph $\mathbf{T} \ne \mathbf{I}$ which is unipotent exists only if the form is isotropic and has more
than $2$ variables"). Let $Q$ be a regular quadratic form over a commutative ring $R$ (for instance $\mathbb{Z}$ or
$\mathbb{Q}$), $K$ a field of characteristic $0$ extending $R$ (for instance $\mathbb{Q}$ or $\mathbb{R}$), and
$T \in M_n(K)$ an automorph, $Q(T\vec{x}) = Q(\vec{x})$ for all $\vec{x} \in K^n$, that is *unipotent* ($T - I$
nilpotent, equivalently all eigenvalues equal $1$) and $T \ne I$. Then $Q$ is isotropic over $K$ and $n \ge 3$. -/
@[kb "cassels1978" "Ch. 13, §4, p. 300 (unipotent automorph ≠ I only if isotropic and n > 2)"]
theorem unipotent_automorph_isotropic {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) (Q : QuadForm R n) (hQ : Q.Nondegenerate)
    (T : Matrix (Fin n) (Fin n) K) (hT : ∀ x : Fin n → K, Q.evalIn K (T *ᵥ x) = Q.evalIn K x)
    (hnil : IsNilpotent (T - 1)) (hne : T ≠ 1) : Q.IsotropicIn K ∧ 3 ≤ n := by
  obtain ⟨hHs, hHdet⟩ := hessian_symm_det hinj Q hQ
  have hTH : Tᵀ * Q.hessian.map (algebraMap R K) * T = Q.hessian.map (algebraMap R K) := by
    apply ext_bilin
    intro x y
    rw [bilin_conj]
    have h1 := QuadForm.polar_eq_hessian K Q (T *ᵥ x) (T *ᵥ y)
    have h2 := QuadForm.polar_eq_hessian K Q x y
    rw [← Matrix.mulVec_add, hT, hT, hT] at h1
    exact h1.symm.trans h2
  obtain ⟨⟨x, hx0, hx⟩, h3⟩ := unipotent_core hHs hHdet hTH hnil hne
  exact ⟨⟨x, hx0, by rw [evalIn_eq_half_hessian, hx, mul_zero]⟩, h3⟩

/-- **Unipotent integral automorphs** (Cassels, Ch. 13, §4, p. 300): if an integral form $Q$ has a unipotent integral
automorph $T \ne I$ ($T - I$ nilpotent) then $Q$ is isotropic over $\mathbb{Q}$ and $n \ge 3$. -/
@[kb "cassels1978" "Ch. 13, §4, p. 300 (unipotent integral automorph ≠ I only if isotropic and n > 2)"]
theorem unipotent_integral_automorph_isotropic (Q : IntQF n) (hQ : Q.Nondegenerate) (T : GL (Fin n) ℤ)
    (hT : T ∈ Siegel.Aut Q) (hnil : IsNilpotent (T.val - 1)) (hne : T ≠ 1) : Q.IsotropicIn ℚ ∧ 3 ≤ n := by
  obtain ⟨hHs, hHdet⟩ := hessian_symm_det (algebraMap ℤ ℚ).injective_int Q hQ
  set f : ℤ →+* ℚ := algebraMap ℤ ℚ with hf
  have hTH0 : T.valᵀ * Q.hessian * T.val = Q.hessian := (Siegel.eval_mulVec_eq_iff_hessian Q Q T.val).1 hT
  have hTH : (T.val.map f)ᵀ * Q.hessian.map f * T.val.map f = Q.hessian.map f := by
    have := congrArg (fun M => M.map f) hTH0
    simpa [Matrix.map_mul, Matrix.transpose_map] using this
  have hnil' : IsNilpotent (T.val.map f - 1) := by
    have := hnil.map (RingHom.mapMatrix f)
    simpa [RingHom.mapMatrix_apply, Matrix.map_sub, Matrix.map_one] using this
  have hne' : T.val.map f ≠ 1 := by
    intro h
    apply hne
    apply Units.ext
    have h' : T.val.map f = (1 : Matrix (Fin n) (Fin n) ℤ).map f := by rw [h]; simp
    rw [Units.val_one]
    exact Matrix.map_injective (algebraMap ℤ ℚ).injective_int h'
  obtain ⟨⟨x, hx0, hx⟩, h3⟩ := unipotent_core hHs hHdet hTH hnil' hne'
  exact ⟨⟨x, hx0, by rw [evalIn_eq_half_hessian, hx, mul_zero]⟩, h3⟩

/-! ### Row 13.r22: the form $f_0 = ax^2 - by^2 - cz^2$ (4.2), p. 299 -/

/-- **Cassels' form (4.2)** $f_0(x, y, z) = ax^2 - by^2 - cz^2$ ($a, b, c$ positive integers), with $(x, y, z) = (x_0, x_1, x_2)$. -/
def f42 (a b c : ℤ) : IntQF 3 := QuadForm.ofUpper ![![a, 0, 0], ![0, -b, 0], ![0, 0, -c]]

/-- The real matrix of $f_0$ is $\operatorname{diag}(a, -b, -c)$. -/
theorem realMat_f42 (a b c : ℤ) : realMat (f42 a b c) = !![(a : ℝ), 0, 0; 0, -b, 0; 0, 0, -c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f42, QuadForm.hessian, QuadForm.ofUpper] <;> ring

/-- **Automorphs of $ax^2 - by^2$ acting on $(x, y)$ and fixing $z$**: for an integral solution of Pell's equation
$t^2 - abu^2 = 1$, $(x, y, z) \mapsto (tx + buy,\ aux + ty,\ z)$ (Cassels, Ch. 13, §4, (4.2), p. 299). -/
def gXY (a b t u : ℤ) (h : t ^ 2 - a * b * u ^ 2 = 1) : GL (Fin 3) ℤ :=
  ⟨!![t, b * u, 0; a * u, t, 0; 0, 0, 1], !![t, -(b * u), 0; -(a * u), t, 0; 0, 0, 1],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | linear_combination h | ring,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | linear_combination h | ring⟩

/-- **Automorphs of $ax^2 - cz^2$ acting on $(x, z)$ and fixing $y$**: for $t^2 - acu^2 = 1$,
$(x, y, z) \mapsto (tx + cuz,\ y,\ aux + tz)$. -/
def gXZ (a c t u : ℤ) (h : t ^ 2 - a * c * u ^ 2 = 1) : GL (Fin 3) ℤ :=
  ⟨!![t, 0, c * u; 0, 1, 0; a * u, 0, t], !![t, 0, -(c * u); 0, 1, 0; -(a * u), 0, t],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | linear_combination h | ring,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | linear_combination h | ring⟩

/-- `gXY` is an integral automorph of $f_0$. -/
theorem gXY_mem (a b c t u : ℤ) (h : t ^ 2 - a * b * u ^ 2 = 1) : gXY a b t u h ∈ Siegel.Aut (f42 a b c) := by
  rw [mem_aut_iff_act]
  have h' : (t : ℝ) ^ 2 - a * b * u ^ 2 = 1 := by exact_mod_cast h
  rw [realMat_f42]
  unfold act castM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gXY, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    first | linear_combination (a : ℝ) * h' | linear_combination (-(b : ℝ)) * h' | ring

/-- `gXZ` is an integral automorph of $f_0$. -/
theorem gXZ_mem (a b c t u : ℤ) (h : t ^ 2 - a * c * u ^ 2 = 1) : gXZ a c t u h ∈ Siegel.Aut (f42 a b c) := by
  rw [mem_aut_iff_act]
  have h' : (t : ℝ) ^ 2 - a * c * u ^ 2 = 1 := by exact_mod_cast h
  rw [realMat_f42]
  unfold act castM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gXZ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
    first | linear_combination (a : ℝ) * h' | linear_combination (-(c : ℝ)) * h' | ring

/-- **The integral automorphs of $f_0$ that keep $z$ fixed** (they act on $(x, y)$ only: $x' , y'$ do not involve $z$
and $z' = z$). They form a group, the group of automorphs of $ax^2 - by^2$ extended by the identity on $z$. -/
def f42FixZ (a b c : ℤ) : Set (GL (Fin 3) ℤ) :=
  {T | T ∈ Siegel.Aut (f42 a b c) ∧ T.val 0 2 = 0 ∧ T.val 1 2 = 0 ∧ T.val 2 0 = 0 ∧ T.val 2 1 = 0 ∧ T.val 2 2 = 1}

/-- **The integral automorphs of $f_0$ that keep $y$ fixed** ($x', z'$ do not involve $y$ and $y' = y$). -/
def f42FixY (a b c : ℤ) : Set (GL (Fin 3) ℤ) :=
  {T | T ∈ Siegel.Aut (f42 a b c) ∧ T.val 0 1 = 0 ∧ T.val 1 0 = 0 ∧ T.val 1 2 = 0 ∧ T.val 2 1 = 0 ∧ T.val 1 1 = 1}

theorem gXY_mem_fixZ (a b c t u : ℤ) (h : t ^ 2 - a * b * u ^ 2 = 1) : gXY a b t u h ∈ f42FixZ a b c :=
  ⟨gXY_mem a b c t u h, by simp [gXY], by simp [gXY], by simp [gXY], by simp [gXY], by simp [gXY]⟩

theorem gXZ_mem_fixY (a b c t u : ℤ) (h : t ^ 2 - a * c * u ^ 2 = 1) : gXZ a c t u h ∈ f42FixY a b c :=
  ⟨gXZ_mem a b c t u h, by simp [gXZ], by simp [gXZ], by simp [gXZ], by simp [gXZ], by simp [gXZ]⟩

/-- Helper: a fundamental solution of Pell's equation $t^2 - du^2 = 1$ ($d$ positive, not a square) has infinitely many
distinct powers, giving infinitely many solutions with $u \ne 0$. -/
theorem infinite_pell_solutions (d : ℤ) (hd : 0 < d) (hns : ¬ IsSquare d) :
    ∃ g : ℤ → ℤ × ℤ, Function.Injective g ∧ ∀ m, (g m).1 ^ 2 - d * (g m).2 ^ 2 = 1 := by
  obtain ⟨a₁, ha₁⟩ := Pell.IsFundamental.exists_of_not_isSquare hd hns
  refine ⟨fun m => ((a₁ ^ m).x, (a₁ ^ m).y), fun m m' h => ?_, fun m => (a₁ ^ m).prop⟩
  have hx : (a₁ ^ m).x = (a₁ ^ m').x := congrArg Prod.fst h
  have hy : (a₁ ^ m).y = (a₁ ^ m').y := congrArg Prod.snd h
  have heq : a₁ ^ m = a₁ ^ m' := Pell.Solution₁.ext hx hy
  have h1 := (ha₁.zpow_eq_one_iff (m - m')).1 (by rw [_root_.zpow_sub, heq, mul_inv_cancel])
  omega

/-- **(4.2), automorphs fixing $z$** (Cassels, Ch. 13, §4, p. 299): if $a, b > 0$ and $ab$ is not a perfect square,
the binary form $ax^2 - by^2$ has an infinite group of automorphs, and these extend (by $z \mapsto z$) to infinitely
many integral automorphs of $f_0 = ax^2 - by^2 - cz^2$ (`f42FixZ`). Explicitly they are `gXY` for the solutions of
Pell's equation $t^2 - abu^2 = 1$. -/
@[kb "cassels1978" "Ch. 13, §4, (4.2), p. 299 (infinitely many automorphs of ax²−by²−cz² fixing z)"]
theorem f42_fixZ_infinite (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : ¬ IsSquare (a * b)) :
    (f42FixZ a b c).Infinite := by
  obtain ⟨g, hg, hgp⟩ := infinite_pell_solutions (a * b) (mul_pos ha hb) hab
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ => gXY a b (g m).1 (g m).2 (hgp m)) (fun m m' h => ?_) fun m => gXY_mem_fixZ a b c _ _ _
  have h00 := congrArg (fun T : GL (Fin 3) ℤ => T.val 0 0) h
  have h01 := congrArg (fun T : GL (Fin 3) ℤ => T.val 0 1) h
  simp only [gXY] at h00 h01
  simp at h00 h01
  apply hg
  exact Prod.ext h00 (by
    rcases h01 with h01 | h01
    · exact h01
    · exact absurd h01 hb.ne')

/-- **(4.2), automorphs fixing $y$** (Cassels, Ch. 13, §4, p. 299): if $a, c > 0$ and $ac$ is not a perfect square,
there are infinitely many integral automorphs of $f_0$ keeping $y$ fixed (`f42FixY`), namely `gXZ` for the solutions
of $t^2 - acu^2 = 1$. -/
@[kb "cassels1978" "Ch. 13, §4, (4.2), p. 299 (infinitely many automorphs of ax²−by²−cz² fixing y)"]
theorem f42_fixY_infinite (a b c : ℤ) (ha : 0 < a) (hc : 0 < c) (hac : ¬ IsSquare (a * c)) :
    (f42FixY a b c).Infinite := by
  obtain ⟨g, hg, hgp⟩ := infinite_pell_solutions (a * c) (mul_pos ha hc) hac
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ => gXZ a c (g m).1 (g m).2 (hgp m)) (fun m m' h => ?_) fun m => gXZ_mem_fixY a b c _ _ _
  have h00 := congrArg (fun T : GL (Fin 3) ℤ => T.val 0 0) h
  have h02 := congrArg (fun T : GL (Fin 3) ℤ => T.val 0 2) h
  simp only [gXZ] at h00 h02
  simp at h00 h02
  apply hg
  exact Prod.ext h00 (by
    rcases h02 with h02 | h02
    · exact h02
    · exact absurd h02 hc.ne')

/-- **(4.2), the two sets generate a nonabelian group** (Cassels, Ch. 13, §4, p. 299): if $a, b, c > 0$ and neither
$ab$ nor $ac$ is a perfect square, there are an automorph $A$ of $f_0$ fixing $z$ and an automorph $B$ fixing $y$ that do
not commute; so the subgroup of $O(f_0)$ generated by the two sets (a subgroup of $O(f_0)$ by construction) is
nonabelian. -/
@[kb "cassels1978" "Ch. 13, §4, (4.2), p. 299 (the two groups generate a nonabelian subgroup of O(f₀))"]
theorem f42_nonabelian (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : ¬ IsSquare (a * b))
    (hac : ¬ IsSquare (a * c)) :
    Subgroup.closure (f42FixZ a b c ∪ f42FixY a b c) ≤ Siegel.Aut (f42 a b c) ∧
      ∃ A ∈ f42FixZ a b c, ∃ B ∈ f42FixY a b c, A * B ≠ B * A := by
  refine ⟨(Subgroup.closure_le _).2 (Set.union_subset (fun T hT => hT.1) (fun T hT => hT.1)), ?_⟩
  obtain ⟨t, u, h, hu⟩ := Pell.exists_of_not_isSquare (mul_pos ha hb) hab
  obtain ⟨t', u', h', hu'⟩ := Pell.exists_of_not_isSquare (mul_pos ha hc) hac
  refine ⟨gXY a b t u h, gXY_mem_fixZ a b c t u h, gXZ a c t' u' h', gXZ_mem_fixY a b c t' u' h', fun hcomm => ?_⟩
  have := congrArg (fun T : GL (Fin 3) ℤ => T.val 1 2) hcomm
  simp [gXY, gXZ, Matrix.mul_apply, Fin.sum_univ_three, ha.ne', hc.ne', hu, hu'] at this

/-! ### Row 13.r24: the example $2x_0x_1 + x_2^2$ (p. 300) -/

/-- **The example form** $f = 2x_0x_1 + x_2^2$ (Cassels' $2x_1x_2 + x_3^2$, p. 300; indices shifted by one). -/
def f5 : IntQF 3 := QuadForm.ofUpper ![![0, 2, 0], ![0, 0, 0], ![0, 0, 1]]

/-- The real matrix of $2x_0x_1 + x_2^2$. -/
theorem realMat_f5 : realMat f5 = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f5, QuadForm.hessian, QuadForm.ofUpper]

/-- **First family of automorphs** of $2x_0x_1 + x_2^2$ (Cassels' $x_1 \to x_1 - 2k^2x_2 - 2kx_3,\ x_2 \to x_2,\
x_3 \to x_3 + 2kx_2$, indices shifted): $(x_0, x_1, x_2) \mapsto (x_0 - 2k^2x_1 - 2kx_2,\ x_1,\ x_2 + 2kx_1)$.
*Erratum:* the book prints $x_3 \to x_3 + kx_2$; this is an automorph only for even multipliers $2k$ (it is the case
$k_3 = 2k \equiv 0 \bmod 2f_{12}$ of (4.7)); see `f5_printed_not_aut`. -/
def autA (k : ℤ) : GL (Fin 3) ℤ :=
  ⟨!![1, -2 * k ^ 2, -2 * k; 0, 1, 0; 0, 2 * k, 1], !![1, -2 * k ^ 2, 2 * k; 0, 1, 0; 0, -2 * k, 1],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring⟩

/-- **Second family of automorphs**, obtained from the first by interchanging the roles of $x_0$ and $x_1$:
$(x_0, x_1, x_2) \mapsto (x_0,\ x_1 - 2k^2x_0 - 2kx_2,\ x_2 + 2kx_0)$. -/
def autB (k : ℤ) : GL (Fin 3) ℤ :=
  ⟨!![1, 0, 0; -2 * k ^ 2, 1, -2 * k; 2 * k, 0, 1], !![1, 0, 0; -2 * k ^ 2, 1, 2 * k; -2 * k, 0, 1],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring⟩

/-- The substitutions `autA k` are integral automorphs of $2x_0x_1 + x_2^2$. -/
theorem autA_mem (k : ℤ) : autA k ∈ Siegel.Aut f5 := by
  rw [mem_aut_iff_act, realMat_f5]
  unfold act castM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [autA, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring

/-- The substitutions `autB k` are integral automorphs of $2x_0x_1 + x_2^2$. -/
theorem autB_mem (k : ℤ) : autB k ∈ Siegel.Aut f5 := by
  rw [mem_aut_iff_act, realMat_f5]
  unfold act castM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [autB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;> ring

/-- **Example after Theorem 4.2: the two families generate a nonabelian group** (Cassels, Ch. 13, §4, p. 300): the
automorphs `autA k` and `autB k` of $2x_0x_1 + x_2^2$ do not commute for $k = 1$ (`autA 1 * autB 1 ≠ autB 1 * autA 1`),
so the subgroup of $O(f)$ generated by them is nonabelian. -/
@[kb "cassels1978" "Ch. 13, §4, Example after Thm. 4.2, p. 300 (two families of automorphs generating a nonabelian group)"]
theorem f5_nonabelian :
    Subgroup.closure (Set.range autA ∪ Set.range autB) ≤ Siegel.Aut f5 ∧ autA 1 * autB 1 ≠ autB 1 * autA 1 := by
  refine ⟨(Subgroup.closure_le _).2 (Set.union_subset ?_ ?_), fun h => ?_⟩
  · rintro _ ⟨k, rfl⟩; exact autA_mem k
  · rintro _ ⟨k, rfl⟩; exact autB_mem k
  · have := congrArg (fun T : GL (Fin 3) ℤ => T.val 0 2) h
    simp [autA, autB, Matrix.mul_apply, Fin.sum_univ_three] at this

/-- **Example after Theorem 4.2: unipotent** (Cassels, Ch. 13, §4, p. 300, "all its eigenvalues are 1"): $(A_k - I)^3 = 0$,
so the automorph `autA k` is unipotent. (The same holds for `autB k`, `autB_unipotent`.) -/
@[kb "cassels1978" "Ch. 13, §4, Example after Thm. 4.2, p. 300 (the automorph (4.7) is unipotent)"]
theorem autA_unipotent (k : ℤ) : IsNilpotent ((autA k).val - 1) := by
  refine ⟨3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [autA, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.one_apply] <;> ring

theorem autB_unipotent (k : ℤ) : IsNilpotent ((autB k).val - 1) := by
  refine ⟨3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [autB, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.one_apply] <;> ring

/-- **Erratum check:** the substitution printed in the book's example, $x_1 \to x_1 - 2x_2 - 2x_3,\ x_2 \to x_2,\
x_3 \to x_3 + x_2$ ($k = 1$ with multiplier $k$ rather than $2k$), is **not** an automorph of $2x_1x_2 + x_3^2$:
in the present indexing it sends $e_1$ to $(-2, 1, 1)$ where $f$ takes the value $-3 \ne 0 = f(e_1)$. -/
theorem f5_printed_not_aut :
    ¬ ∀ x : Fin 3 → ℤ, QuadForm.eval f5 (!![1, -2, -2; 0, 1, 0; 0, 1, 1] *ᵥ x) = QuadForm.eval f5 x := by
  intro h
  have := h ![0, 1, 0]
  simp [QuadForm.eval, QuadForm.evalIn, f5, QuadForm.ofUpper, Fin.sum_univ_three, Matrix.mulVec, dotProduct] at this

end QuadFormsKB.Reduction
