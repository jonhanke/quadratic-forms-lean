/-
# A lower bound for $|\det(CZ+D)|$ on the Siegel upper half space

**Layer:** real and complex linear algebra.

**Statement** (`exists_norm_det_CZD_ge`).  Let $Z\in\mathbb H_r$ (`WeilRep.Genus.siegelH r`).  There is $c>0$ such that for every
real $r\times 2r$ matrix $E=(C\ D)$ with $CD^{\mathsf T}=DC^{\mathsf T}$ (the rows of $E$ span a Lagrangian subspace) such that some
$r$ columns of $E$ (selected by $h:\mathrm{Fin}\,r\to\mathrm{Fin}\,r\oplus\mathrm{Fin}\,r$) form the identity matrix, and for every
entry $E_{ix}$,
$$c\cdot\max(1,|E_{ix}|)\ \le\ |\det(CZ+D)|.$$
The constant $c$ depends only on $Z$ (not on $C$, $D$, $h$).

**Proof.**  Write $Z=X+iY$ with $X,Y$ real symmetric, $Y>0$, and $W=CZ+D=(CX+D)+iCY$.
1. *Key identity* (`key_identity`): $W\,Y^{-1}\,W^{*}=H:=(CX+D)Y^{-1}(CX+D)^{\mathsf T}+CYC^{\mathsf T}$, the imaginary part
   $i\,(C(CX+D)^{\mathsf T}-(CX+D)C^{\mathsf T})=i\,(CD^{\mathsf T}-DC^{\mathsf T})$ vanishing by hypothesis.  Hence
   $|\det W|^2=\det Y\cdot\det H$.
2. *Coercivity* (`exists_quad_coercive`, `quad_form_bound`): there is $\mu>0$ (depending on $X,Y$ only) with
   $w^{\mathsf T}Hw\ge\mu\,|E^{\mathsf T}w|^2$ for all $w$.
3. *Frame bounds* (`frame_dot_le`, `frame_sum_ge`): because $E$ contains an identity block, $|E^{\mathsf T}w|\ge|w|$, so
   $B=H-\mu I\succeq0$, and $\operatorname{tr}H\ge\mu\|E\|_F^2\ge\mu\,(r+E_{ix}^2-1)$.
4. *Determinant of $1+P$* (`one_add_trace_le_det_one_add`): for $P\succeq 0$, $\det(1+P)\ge 1+\operatorname{tr}P$
   (the coefficients of $\det(1+tP)$ are sums of principal minors, all $\ge 0$).  Applied to $P=\mu^{-1}B$
   (`det_ge_of_sub_psd`) this gives $\det H\ge\mu^r\max(1,E_{ix}^2)$.
5. Hence $|\det W|^2=\det Y\det H\ge(\det Y\,\mu^r)\max(1,|E_{ix}|)^2$, and $c=\sqrt{\det Y\,\mu^r}$ works.

Sources: standard (cf. Siegel, *Symplectic geometry*, Amer. J. Math. 65 (1943); Freitag, *Siegelsche Modulfunktionen* (1983),
Ch. I) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.SiegelSpace
import QuadFormsKB.SiegelWeil.Forms.ThetaR

open Matrix Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-- For $P\succeq 0$ real symmetric, $1+\operatorname{tr}P\le\det(1+P)$. -/
lemma one_add_trace_le_det_one_add {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ}
    (hP : P.PosSemidef) : 1 + P.trace ≤ (1 + P).det := by
  have h := Matrix.det_one_add_smul (1 : ℝ) P
  rw [one_smul] at h
  rw [h]
  have hc : ∀ k, 0 ≤ (det (1 + (X : ℝ[X]) • P.map C)).coeff k := fun k => by
    rw [coeff_det_one_add_X_smul_eq_sum_minors]
    exact Finset.sum_nonneg fun s _ => (hP.submatrix _).det_nonneg
  have : 0 ≤ ((det (1 + (X : ℝ[X]) • P.map C)).divX.divX).eval 1 := by
    rw [eval_eq_sum_range]
    exact Finset.sum_nonneg fun i _ => by simpa [coeff_divX] using hc _
  nlinarith

/-- If $H-\mu I\succeq 0$ and $\operatorname{tr}(H-\mu I)\ge\mu(t-1)$ then $\det H\ge\mu^r\max(1,t)$. -/
lemma det_ge_of_sub_psd {r : ℕ} {H : Matrix (Fin r) (Fin r) ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hB : (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef) (t : ℝ)
    (ht : μ * (t - 1) ≤ (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).trace) :
    μ ^ r * max 1 t ≤ H.det := by
  have hP : (μ⁻¹ • (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ))).PosSemidef :=
    hB.smul (inv_nonneg.2 hμ.le)
  have h1 := one_add_trace_le_det_one_add hP
  have e1 : (1 : Matrix (Fin r) (Fin r) ℝ) + μ⁻¹ • (H - μ • 1) = μ⁻¹ • H := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]; abel
  rw [e1, det_smul, trace_smul] at h1
  simp only [Fintype.card_fin, smul_eq_mul] at h1
  have htr : 0 ≤ (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).trace := hB.trace_nonneg
  have h2 : max 1 t ≤ 1 + μ⁻¹ * (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).trace := by
    apply max_le
    · have := mul_nonneg (inv_nonneg.2 hμ.le) htr; linarith
    · have : t - 1 ≤ μ⁻¹ * (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).trace := by
        rwa [le_inv_mul_iff₀ hμ]
      linarith
  have h3 : max 1 t ≤ (μ⁻¹) ^ r * H.det := h2.trans h1
  have : μ ^ r * max 1 t ≤ μ ^ r * ((μ⁻¹) ^ r * H.det) :=
    mul_le_mul_of_nonneg_left h3 (pow_nonneg hμ.le _)
  rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hμ.ne', one_pow, one_mul] at this

section Frames
variable {r : ℕ} {E : Matrix (Fin r) (Fin r ⊕ Fin r) ℝ} {h : Fin r → Fin r ⊕ Fin r}

/-- If the columns `h k` of `E` form the identity matrix then they are the unit vectors. -/
lemma frame_col (hE : E.submatrix id h = 1) (k' k : Fin r) :
    E k' (h k) = (1 : Matrix (Fin r) (Fin r) ℝ) k' k := by
  simpa using congrFun (congrFun hE k') k

/-- The column selector `h` is injective. -/
lemma frame_inj (hE : E.submatrix id h = 1) : Function.Injective h := by
  intro a b hab
  have h1 := frame_col hE a a
  have h2 := frame_col hE a b
  rw [← hab] at h2
  rw [h2] at h1
  by_contra hne
  simp [hne] at h1

/-- $|w|^2\le|E^{\mathsf T}w|^2$ when $E$ contains an identity block. -/
lemma frame_dot_le (hE : E.submatrix id h = 1) (w : Fin r → ℝ) :
    w ⬝ᵥ w ≤ (Eᵀ *ᵥ w) ⬝ᵥ (Eᵀ *ᵥ w) := by
  have hf : ∀ k, (Eᵀ *ᵥ w) (h k) = w k := by
    intro k
    simp [Matrix.mulVec, dotProduct, frame_col hE, Matrix.one_apply]
  calc w ⬝ᵥ w = ∑ k, (Eᵀ *ᵥ w) (h k) * (Eᵀ *ᵥ w) (h k) := by simp [dotProduct, hf]
    _ = ∑ y ∈ Finset.univ.image h, (Eᵀ *ᵥ w) y * (Eᵀ *ᵥ w) y := by
        rw [Finset.sum_image (fun a _ b _ hab => frame_inj hE hab)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => mul_self_nonneg _)

/-- A column in the identity block has squared norm one. -/
lemma frame_colsq (hE : E.submatrix id h = 1) (k : Fin r) :
    ∑ k', E k' (h k) ^ 2 = 1 := by
  simp [frame_col hE, Matrix.one_apply]

/-- $\|E\|_F^2\ge r+E_{ix}^2-1$ when $E$ contains an identity block. -/
lemma frame_sum_ge (hE : E.submatrix id h = 1) (i : Fin r) (x : Fin r ⊕ Fin r) :
    (r : ℝ) + (E i x) ^ 2 - 1 ≤ ∑ y, ∑ k, E k y ^ 2 := by
  have hnn : ∀ y, 0 ≤ ∑ k, E k y ^ 2 := fun y => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hr : (r : ℝ) = ∑ y ∈ Finset.univ.image h, ∑ k, E k y ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ hab => frame_inj hE hab)]
    simp [frame_colsq hE]
  by_cases hx : x ∈ Finset.univ.image h
  · obtain ⟨k0, -, rfl⟩ := Finset.mem_image.1 hx
    have h1 : E i (h k0) ^ 2 ≤ 1 := by
      rw [frame_col hE]; simp only [Matrix.one_apply]; split_ifs <;> norm_num
    have h2 : ∑ y ∈ Finset.univ.image h, ∑ k, E k y ^ 2 ≤ ∑ y, ∑ k, E k y ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hnn y)
    linarith
  · have h1 : E i x ^ 2 ≤ ∑ k, E k x ^ 2 :=
      Finset.single_le_sum (f := fun k => E k x ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ y ∈ insert x (Finset.univ.image h), ∑ k, E k y ^ 2 ≤ ∑ y, ∑ k, E k y ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hnn y)
    rw [Finset.sum_insert hx] at h2
    linarith

end Frames

/-- Coercivity of $(u,v)\mapsto(Xu+v)^{\mathsf T}Y_i(Xu+v)+u^{\mathsf T}Yu$ for positive definite $Y$, $Y_i$. -/
lemma exists_quad_coercive {r : ℕ} (X : Matrix (Fin r) (Fin r) ℝ) {Y Yi : Matrix (Fin r) (Fin r) ℝ}
    (hY : Y.PosDef) (hYi : Yi.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ u v : Fin r → ℝ,
      μ * (u ⬝ᵥ u + v ⬝ᵥ v) ≤
        (X *ᵥ u + v) ⬝ᵥ Yi *ᵥ (X *ᵥ u + v) + u ⬝ᵥ Y *ᵥ u := by
  obtain ⟨α, hα, hαY⟩ := exists_coercive hYi
  obtain ⟨β, hβ, hβY⟩ := exists_coercive hY
  set K : ℝ := ∑ i, ∑ j, X i j ^ 2 with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨min (α / 2) (β / (1 + 2 * K)), lt_min (by positivity) (by positivity), fun u v => ?_⟩
  set μ := min (α / 2) (β / (1 + 2 * K)) with hμ
  have hμ0 : 0 ≤ μ := (lt_min (by positivity) (by positivity) : 0 < μ).le
  have hμ1 : 2 * μ ≤ α := by
    have := min_le_left (α / 2) (β / (1 + 2 * K)); linarith
  have hμ2 : μ * (1 + 2 * K) ≤ β := by
    have := min_le_right (α / 2) (β / (1 + 2 * K))
    rwa [le_div_iff₀ (by positivity)] at this
  have hXu : (X *ᵥ u) ⬝ᵥ (X *ᵥ u) ≤ K * (u ⬝ᵥ u) := by
    have hi : ∀ i, (X *ᵥ u) i * (X *ᵥ u) i ≤ (∑ j, X i j ^ 2) * (u ⬝ᵥ u) := by
      intro i
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) u
      simpa [sq, mulVec, dotProduct] using this
    calc (X *ᵥ u) ⬝ᵥ (X *ᵥ u) = ∑ i, (X *ᵥ u) i * (X *ᵥ u) i := rfl
      _ ≤ ∑ i, (∑ j, X i j ^ 2) * (u ⬝ᵥ u) := Finset.sum_le_sum fun i _ => hi i
      _ = K * (u ⬝ᵥ u) := by rw [hK, Finset.sum_mul]
  have hvv : v ⬝ᵥ v ≤ 2 * ((X *ᵥ u + v) ⬝ᵥ (X *ᵥ u + v)) + 2 * ((X *ᵥ u) ⬝ᵥ (X *ᵥ u)) := by
    simp only [dotProduct, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (2 * (X *ᵥ u) i + v i)]
  have h1 := hαY (X *ᵥ u + v)
  have h2 := hβY u
  have a0 : 0 ≤ (X *ᵥ u + v) ⬝ᵥ (X *ᵥ u + v) := dotProduct_self_star_nonneg _
  have u0 : 0 ≤ u ⬝ᵥ u := dotProduct_self_star_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hμ1 a0, mul_le_mul_of_nonneg_right hμ2 u0,
    mul_le_mul_of_nonneg_left hvv hμ0, mul_le_mul_of_nonneg_left hXu hμ0]

/-- **Key identity:** for $Z=X+iY$ with $X,Y$ symmetric, $YY_i=Y_iY=1$ and $CD^{\mathsf T}=DC^{\mathsf T}$,
$(CZ+D)\,Y_i\,(CZ+D)^{*}=(CX+D)Y_i(CX+D)^{\mathsf T}+CYC^{\mathsf T}$ (a real matrix). -/
lemma key_identity {r : ℕ} {X Y Yi : Matrix (Fin r) (Fin r) ℝ} (C D : Matrix (Fin r) (Fin r) ℝ)
    (hXs : Xᵀ = X) (hYs : Yᵀ = Y) (hYi : Y * Yi = 1) (hYi' : Yi * Y = 1)
    (hCD : C * Dᵀ = D * Cᵀ) {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z = X.map (↑) + Complex.I • Y.map (↑)) :
    (C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ) * Yi.map (↑) *
        (C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ)ᴴ =
      ((C * X + D) * Yi * (C * X + D)ᵀ + C * Y * Cᵀ).map (↑) := by
  set φ : Matrix (Fin r) (Fin r) ℝ →+* Matrix (Fin r) (Fin r) ℂ := Complex.ofRealHom.mapMatrix with hφ
  have e : ∀ M : Matrix (Fin r) (Fin r) ℝ, M.map (↑) = φ M := fun _ => rfl
  have ec : ∀ M : Matrix (Fin r) (Fin r) ℝ, (φ M)ᴴ = φ Mᵀ := by
    intro M; ext i j; simp [hφ, conjTranspose_apply]
  have hW : (C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ) =
      φ (C * X + D) + Complex.I • φ (C * Y) := by
    rw [hZ, e, e, e, e]
    simp only [mul_add, mul_smul_comm, map_add, map_mul]
    abel
  have hCA : C * (C * X + D)ᵀ = (C * X + D) * Cᵀ := by
    rw [transpose_add, transpose_mul, hXs, mul_add, hCD, add_mul, mul_assoc]
  have r1 : C * Y * Yi * (C * Y)ᵀ = C * Y * Cᵀ := by
    rw [transpose_mul, hYs]
    calc C * Y * Yi * (Y * Cᵀ) = C * (Y * Yi * Y) * Cᵀ := by simp only [mul_assoc]
      _ = C * Y * Cᵀ := by rw [hYi, one_mul]
  have r2 : C * Y * Yi * (C * X + D)ᵀ = C * (C * X + D)ᵀ := by
    rw [mul_assoc C Y Yi, hYi, mul_one]
  have r3 : (C * X + D) * Yi * (C * Y)ᵀ = (C * X + D) * Cᵀ := by
    rw [transpose_mul, hYs]
    calc (C * X + D) * Yi * (Y * Cᵀ) = (C * X + D) * (Yi * Y) * Cᵀ := by simp only [mul_assoc]
      _ = _ := by rw [hYi', mul_one]
  have c1 : φ (C * Y) * φ Yi * φ (C * Y)ᵀ = φ (C * Y * Cᵀ) := by
    rw [← map_mul, ← map_mul, r1]
  have c2 : φ (C * Y) * φ Yi * φ (C * X + D)ᵀ = φ ((C * X + D) * Cᵀ) := by
    rw [← map_mul, ← map_mul, r2, hCA]
  have c3 : φ (C * X + D) * φ Yi * φ (C * Y)ᵀ = φ ((C * X + D) * Cᵀ) := by
    rw [← map_mul, ← map_mul, r3]
  rw [hW, conjTranspose_add, conjTranspose_smul, ec, ec, e, Complex.star_def, Complex.conj_I]
  calc (φ (C * X + D) + Complex.I • φ (C * Y)) * φ Yi *
        (φ (C * X + D)ᵀ + (-Complex.I) • φ (C * Y)ᵀ)
      = φ (C * X + D) * φ Yi * φ (C * X + D)ᵀ + (Complex.I * -Complex.I) • (φ (C * Y) * φ Yi * φ (C * Y)ᵀ)
        + Complex.I • (φ (C * Y) * φ Yi * φ (C * X + D)ᵀ)
        + (-Complex.I) • (φ (C * X + D) * φ Yi * φ (C * Y)ᵀ) := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
        module
    _ = _ := by
        have hII : Complex.I * -Complex.I = 1 := by simp
        rw [c1, c2, c3, hII, one_smul, e]
        simp only [map_add, map_mul]
        module

/-- Sandwich identity $w^{\mathsf T}(MNM^{\mathsf T})w=(M^{\mathsf T}w)^{\mathsf T}N(M^{\mathsf T}w)$. -/
lemma dot_sandwich {r : ℕ} (M N : Matrix (Fin r) (Fin r) ℝ) (w : Fin r → ℝ) :
    w ⬝ᵥ (M * N * Mᵀ) *ᵥ w = (Mᵀ *ᵥ w) ⬝ᵥ N *ᵥ (Mᵀ *ᵥ w) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose M w]

/-- The real quadratic-form bound $\mu\,|E^{\mathsf T}w|^2\le w^{\mathsf T}Hw$ for $E=(C\ D)$ and
$H=(CX+D)Y_i(CX+D)^{\mathsf T}+CYC^{\mathsf T}$, given the coercivity of the form of `exists_quad_coercive`. -/
lemma quad_form_bound {r : ℕ} {X Y Yi : Matrix (Fin r) (Fin r) ℝ} (C D : Matrix (Fin r) (Fin r) ℝ)
    (hXs : Xᵀ = X) {μ : ℝ}
    (hμ : ∀ u v : Fin r → ℝ, μ * (u ⬝ᵥ u + v ⬝ᵥ v) ≤
        (X *ᵥ u + v) ⬝ᵥ Yi *ᵥ (X *ᵥ u + v) + u ⬝ᵥ Y *ᵥ u) (w : Fin r → ℝ) :
    μ * (((fromCols C D)ᵀ *ᵥ w) ⬝ᵥ ((fromCols C D)ᵀ *ᵥ w)) ≤
      w ⬝ᵥ ((C * X + D) * Yi * (C * X + D)ᵀ + C * Y * Cᵀ) *ᵥ w := by
  have e1 : ((fromCols C D)ᵀ *ᵥ w) ⬝ᵥ ((fromCols C D)ᵀ *ᵥ w) =
      (Cᵀ *ᵥ w) ⬝ᵥ (Cᵀ *ᵥ w) + (Dᵀ *ᵥ w) ⬝ᵥ (Dᵀ *ᵥ w) := by
    simp [dotProduct, Fintype.sum_sum_type, mulVec, fromCols_apply_inl, fromCols_apply_inr, transpose_apply]
  have ha : (C * X + D)ᵀ *ᵥ w = X *ᵥ (Cᵀ *ᵥ w) + Dᵀ *ᵥ w := by
    rw [transpose_add, transpose_mul, hXs, add_mulVec, mulVec_mulVec]
  have e2 : w ⬝ᵥ ((C * X + D) * Yi * (C * X + D)ᵀ + C * Y * Cᵀ) *ᵥ w =
      (X *ᵥ (Cᵀ *ᵥ w) + Dᵀ *ᵥ w) ⬝ᵥ Yi *ᵥ (X *ᵥ (Cᵀ *ᵥ w) + Dᵀ *ᵥ w) +
        (Cᵀ *ᵥ w) ⬝ᵥ Y *ᵥ (Cᵀ *ᵥ w) := by
    rw [add_mulVec, dotProduct_add, dot_sandwich, dot_sandwich, ha]
  rw [e1, e2]
  exact hμ _ _

/-- **Lower bound for $|\det(CZ + D)|$ on the Siegel upper half space.**  For $Z\in\mathbb H_r$ there is $c>0$ such that, for
every real $r\times 2r$ matrix $E=(C\ D)$ with $CD^{\mathsf T}=DC^{\mathsf T}$ having $r$ columns (selected by `h`) forming the
identity matrix, $c\max(1,|E_{ix}|)\le|\det(CZ+D)|$ for all entries $E_{ix}$.  The constant depends only on $Z$. -/
theorem exists_norm_det_CZD_ge {r : ℕ} {Z : Matrix (Fin r) (Fin r) ℂ}
    (hZ : Z ∈ WeilRep.Genus.siegelH r) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C D : Matrix (Fin r) (Fin r) ℝ), C * Dᵀ = D * Cᵀ →
      ∀ h : Fin r → Fin r ⊕ Fin r, (Matrix.fromCols C D).submatrix id h = 1 →
        ∀ (i : Fin r) (x : Fin r ⊕ Fin r),
          c * max 1 |Matrix.fromCols C D i x| ≤
            ‖(C.map (↑) * Z + D.map (↑) : Matrix (Fin r) (Fin r) ℂ).det‖ := by
  obtain ⟨hZs, hY⟩ := hZ
  set X : Matrix (Fin r) (Fin r) ℝ := Z.map Complex.re with hXdef
  set Y : Matrix (Fin r) (Fin r) ℝ := Z.map Complex.im with hYdef
  have hXs : Xᵀ = X := by rw [hXdef, ← Matrix.transpose_map, hZs]
  have hYs : Yᵀ = Y := by rw [hYdef, ← Matrix.transpose_map, hZs]
  have hZeq : Z = X.map (↑) + Complex.I • Y.map (↑) := by
    ext i j
    simp only [hXdef, hYdef, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
  have hdetY : 0 < Y.det := hY.det_pos
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.2 hdetY.ne'
  have hYYi : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hYu
  have hYiY : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y hYu
  have hYiPD : Y⁻¹.PosDef := hY.inv
  obtain ⟨μ, hμ0, hμ⟩ := exists_quad_coercive X hY hYiPD
  have hdd : Y.det * Y⁻¹.det = 1 := by rw [← det_mul, hYYi, det_one]
  refine ⟨√(Y.det * μ ^ r), Real.sqrt_pos.2 (mul_pos hdetY (pow_pos hμ0 r)), ?_⟩
  intro C D hCD h hh i x
  set E : Matrix (Fin r) (Fin r ⊕ Fin r) ℝ := fromCols C D with hEdef
  set H : Matrix (Fin r) (Fin r) ℝ := (C * X + D) * Y⁻¹ * (C * X + D)ᵀ + C * Y * Cᵀ with hHdef
  have hQ : ∀ w, μ * ((Eᵀ *ᵥ w) ⬝ᵥ (Eᵀ *ᵥ w)) ≤ w ⬝ᵥ H *ᵥ w :=
    quad_form_bound (Y := Y) (Yi := Y⁻¹) C D hXs hμ
  -- H is symmetric
  have hHs : Hᵀ = H := by
    have hYis : (Y⁻¹)ᵀ = Y⁻¹ := by rw [transpose_nonsing_inv, hYs]
    rw [hHdef, transpose_add, transpose_mul, transpose_mul, transpose_mul, transpose_transpose,
      hYis, transpose_mul, transpose_transpose, hYs]
    simp only [mul_assoc]
  have hBs : (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ))ᵀ = H - μ • 1 := by
    rw [transpose_sub, transpose_smul, transpose_one, hHs]
  -- B = H - μ 1 is positive semidefinite
  have hB : (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (by rw [isHermitian_iff_isSymm]; exact hBs)
      fun w => ?_
    have h1 := hQ w
    have h2 := frame_dot_le hh w
    have h3 := mul_le_mul_of_nonneg_left h2 hμ0.le
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
    linarith
  -- trace bound
  have hdiag : ∀ k, μ * ∑ y, E k y ^ 2 ≤ H k k := by
    intro k
    have h1 := hQ (Pi.single k 1)
    have e3 : (Pi.single k (1 : ℝ)) ⬝ᵥ H *ᵥ Pi.single k 1 = H k k := by
      simp [mulVec_single]
    have e4 : (Eᵀ *ᵥ Pi.single k (1 : ℝ)) ⬝ᵥ (Eᵀ *ᵥ Pi.single k (1 : ℝ)) = ∑ y, E k y ^ 2 := by
      simp [mulVec_single, dotProduct, sq]
    rw [e3, e4] at h1
    exact h1
  have htrH : μ * ∑ y, ∑ k, E k y ^ 2 ≤ H.trace := by
    calc μ * ∑ y, ∑ k, E k y ^ 2 = ∑ k, μ * ∑ y, E k y ^ 2 := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ k, H k k := Finset.sum_le_sum fun k _ => hdiag k
      _ = H.trace := by simp [trace]
  have hS := frame_sum_ge hh i x
  have htrB : μ * (E i x ^ 2 - 1) ≤ (H - μ • (1 : Matrix (Fin r) (Fin r) ℝ)).trace := by
    rw [trace_sub, trace_smul, trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hS hμ0.le]
  have hdetH := det_ge_of_sub_psd hμ0 hB (E i x ^ 2) htrB
  -- the complex identity
  have hkey := key_identity (Y := Y) (Yi := Y⁻¹) C D hXs hYs hYYi hYiY hCD hZeq
  have hdc : ∀ M : Matrix (Fin r) (Fin r) ℝ, (M.map (↑) : Matrix (Fin r) (Fin r) ℂ).det =
      ((M.det : ℝ) : ℂ) := fun M => (RingHom.map_det Complex.ofRealHom M).symm
  set W : Matrix (Fin r) (Fin r) ℂ := C.map (↑) * Z + D.map (↑) with hWdef
  have hdet := congrArg Matrix.det hkey
  rw [det_mul, det_mul, det_conjTranspose, hdc, hdc] at hdet
  have hnorm : Y⁻¹.det * ‖W.det‖ ^ 2 = H.det := by
    have hmc : W.det * star W.det = ((‖W.det‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h1 : (((Y⁻¹.det * ‖W.det‖ ^ 2 : ℝ)) : ℂ) = ((H.det : ℝ) : ℂ) := by
      calc (((Y⁻¹.det * ‖W.det‖ ^ 2 : ℝ)) : ℂ) = (Y⁻¹.det : ℂ) * (W.det * star W.det) := by
            rw [hmc]; push_cast; ring
        _ = W.det * (Y⁻¹.det : ℂ) * star W.det := by ring
        _ = _ := hdet
    exact_mod_cast h1
  have hn2 : ‖W.det‖ ^ 2 = Y.det * H.det := by
    calc ‖W.det‖ ^ 2 = (Y.det * Y⁻¹.det) * ‖W.det‖ ^ 2 := by rw [hdd, one_mul]
      _ = Y.det * (Y⁻¹.det * ‖W.det‖ ^ 2) := by ring
      _ = _ := by rw [hnorm]
  -- conclusion
  have hm2 : (max 1 |E i x|) ^ 2 ≤ max 1 (E i x ^ 2) := by
    rcases le_total 1 |E i x| with h1 | h1
    · rw [max_eq_right h1, sq_abs]; exact le_max_right _ _
    · rw [max_eq_left h1]; simp
  have hc2 : (√(Y.det * μ ^ r)) ^ 2 = Y.det * μ ^ r :=
    Real.sq_sqrt (mul_pos hdetY (pow_pos hμ0 r)).le
  have hsq : (√(Y.det * μ ^ r) * max 1 |E i x|) ^ 2 ≤ ‖W.det‖ ^ 2 := by
    rw [mul_pow, hc2, hn2]
    have h1 : μ ^ r * (max 1 |E i x|) ^ 2 ≤ H.det :=
      le_trans (mul_le_mul_of_nonneg_left hm2 (pow_nonneg hμ0.le r)) hdetH
    nlinarith [mul_le_mul_of_nonneg_left h1 hdetY.le]
  have hcm : 0 ≤ √(Y.det * μ ^ r) * max 1 |E i x| :=
    mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left _ _))
  exact (pow_le_pow_iff_left₀ hcm (norm_nonneg _) (by norm_num)).1 hsq

end QuadFormsKB.SiegelWeil.Forms
