import QuadFormsKB.HilbertModular.Theta

/-!
# Theta series over a totally real field II: the inversion formula

Notation of `Theta.lean`: $F$ totally real of degree $d$, real embeddings $\varphi_v$, a lattice $L = \bigoplus_iI_ie_i$
(`𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ`) with Gram matrix $A$ ($\varphi_v(A)$ positive definite for all $v$), and
$\theta_{A,L}$ = `thetaLat A 𝔞`, $\theta^\#_{A,L}$ = `thetaLatDual A 𝔞` (the dual lattice $L^\# = \bigoplus_iI_i^\vee$,
$I_i^\vee = I_i^{-1}\mathfrak d^{-1}$ the trace dual, with the form $Q^\#(\mu) = \frac14\mu^{\mathsf T}A^{-1}\mu$).

**Inversion formula** (`thetaLat_inversion`): for $z \in \mathbb{C}^d$ with $\operatorname{Im} z_v > 0$ at every place,
$$\theta_{A,L}(-1/z) = \frac{1}{\sqrt{N_{F/\mathbb{Q}}(\det A)}\ \prod_i\Delta(I_i)}\ \prod_v\Big(\frac{-iz_v}{2}\Big)^{n/2}\ \theta^\#_{A,L}(z),$$
where $-1/z = (-1/z_v)_v$, $(\cdot)^{n/2}$ is the principal branch (`Complex.cpow`; $-iz_v/2$ lies in the right half plane),
$\sqrt{N(\det A)} = \prod_v\sqrt{\det\varphi_v(A)}$, and $\Delta(I) = |\det(\varphi_v(\beta_l))_{v,l}|$ (`embDet`) for a
$\mathbb{Z}$-basis $\beta$ of $I$; `embDet_sq`, `embDet_sq_eq`: $\Delta(I)^2 = \operatorname{disc}_{\mathbb{Q}}(\beta) = N(I)^2d_F$
(so $d_F > 0$ and $\Delta(\mathcal{O}_F) = d_F^{1/2}$, `embDet_one`, the covolume of $\mathcal{O}_F$ in $\mathbb{R}^d$).
`thetaQ_inversion`: the case $L = \mathcal{O}_F^n$ of a form over $\mathcal{O}_F$, with the factor $N(\det A)^{-1/2}d_F^{-n/2}$.

*Normalization check, $F = \mathbb{Q}$* ($d = 1$, $\Delta(\mathbb{Z}) = 1$, $N(\det A) = \det A$): the formula reads
$\theta_A(-1/z) = (\det A)^{-1/2}(-iz/2)^{n/2}\theta_{A^{-1}/4}(z)$, which is `QuadFormsKB.Siegel.thetaGram_S` /
`QuadFormsKB.Siegel.theta_S` ($D = \det A$).

*Proof.* Each term of $\theta_{A,L}(w)$ is the diagonal complex Gaussian $G_b(M\vec k)$ with rates $b = -2iw_v$ and
$M = DK$ (`thetaTerm_eq_gaussAt`); the dual terms are $G_{b^{-1}}(M'\vec m)$ with $M' = D^{-1}K^\vee$, $M^{\mathsf T}M' = 1$
(trace duality $\sum_v\varphi_v(\beta_l\beta^\vee_{l'}) = \delta_{ll'}$, `latMat_transpose_mul`). Poisson summation
`tsum_gaussAt` with $w = -1/z$ (so $b^{-1} = -iz_v/2$) and $|\det M| = \prod_v\det\varphi_v(A)^{1/2}\prod_i\Delta(I_i)$
(`abs_det_latMat`). This is Poisson summation over the lattice $L \subset (F\otimes\mathbb{R})^n$, the "adelic Poisson
summation at the infinite places", in coordinates.

Sources: Freitag, *Hilbert Modular Forms*, Ch. I §4 [unverified]; Garrett, *Holomorphic Hilbert Modular Forms*, Ch. 2
[unverified].
-/

open Matrix NumberField NumberField.InfinitePlace Complex
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "dq" => Module.finrank ℚ F

/-- **The embedding determinant** $\Delta(I) = |\det(\varphi_v(\beta_l))_{v,l}|$ of a $\mathbb{Z}$-basis $\beta$ of $I$ (the covolume
of $I$ in $\mathbb{R}^d$; independent of the basis, `embDet_sq`). -/
def embDet (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : ℝ := |(embMat (QuadFormsKB.Analysis.bq I)).det|

lemma det_blockMat (B : InfinitePlace F → Matrix (Fin n) (Fin n) ℝ) :
    (blockMat B).det = ∏ v, (B v).det := by
  rw [blockMat, det_blockDiagonal]
  exact (placeEquiv (F := F)).prod_comp fun v => (B v).det

lemma det_coordMat (Y : Fin n → Fin (Module.finrank ℚ F) → F) :
    (coordMat Y).det = ∏ i, (embMat (Y i)).det := by
  rw [coordMat, det_reindex_self, det_blockDiagonal]

/-- $|\det M| = \prod_v\sqrt{\det\varphi_v(A)}\cdot\prod_i\Delta(I_i)$. -/
lemma abs_det_latMat {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    |(latMat A 𝔞).det| = (∏ v, Real.sqrt (A.map (realEmb F v)).det) * ∏ i, embDet (𝔞 i) := by
  rw [latMat, det_mul, det_blockMat, det_coordMat, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [gramSqrt_det hA, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma map_inv_realEmb {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F) :
    A⁻¹.map (realEmb F v) = (A.map (realEmb F v))⁻¹ := by
  have hdet : A.det ≠ 0 := by
    intro h
    have := (hA v).det_pos
    rw [show (A.map (realEmb F v)).det = realEmb F v A.det from (RingHom.map_det _ _).symm, h,
      map_zero] at this
    exact lt_irrefl _ this
  symm
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.map_one _
    (map_zero _) (map_one _)]

lemma gramSqrt_inv_spec {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) (v : InfinitePlace F) :
    ((gramSqrt A v)⁻¹)ᵀ * (gramSqrt A v)⁻¹ = A⁻¹.map (realEmb F v) := by
  rw [map_inv_realEmb hA, Matrix.transpose_nonsing_inv, (gramSqrt_spec hA v).1,
    ← Matrix.mul_inv_rev, (gramSqrt_spec hA v).2]

/-- **The dual terms are diagonal Gaussians**: $G_{b^{-1}}(M'\vec m) = \exp(-\pi\sum_vw_v^{-1}\varphi_v(\mu^{\mathsf T}A^{-1}\mu))$ for
rates $b_{(i,j)} = w_{v_j}$ and $\mu$ = `dualLatVec 𝔞 m`. -/
theorem gaussAt_dualMat {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (w : InfinitePlace F → ℂ) (m : Fin n × Fin dq → ℤ) :
    gaussAt (fun p => (w (placeEquiv p.2))⁻¹) (dualMat A 𝔞) m =
      cexp (-Real.pi * ∑ v, (w v)⁻¹ *
        (realEmb F v (qv A⁻¹ (dualLatVec 𝔞 (Equiv.curry _ _ _ m))) : ℂ)) := by
  rw [dualMat, gaussAt_blockMat_coordMat A⁻¹ _ (gramSqrt_inv_spec hA) _ (fun v => (w v)⁻¹),
    dualLatVec_curry]

lemma qv_smul (c : F) (A : Matrix (Fin n) (Fin n) F) (x : Fin n → F) : qv (c • A) x = c * qv A x := by
  simp [qv, smul_mulVec, dotProduct_smul]

lemma prod_rate_cpow (c : InfinitePlace F → ℂ) :
    ∏ p : Fin n × Fin dq, c (placeEquiv p.2) ^ (1 / 2 : ℂ) =
      ∏ v, c v ^ ((n : ℂ) / 2) := by
  simp only [Fintype.prod_prod_type]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    (placeEquiv (F := F)).prod_comp (fun v => c v ^ (1 / 2 : ℂ)), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Complex.cpow_nat_mul]
  congr 1
  ring

/-- **The inversion formula for theta series over a totally real field.** For a lattice $L = \bigoplus_iI_ie_i$ with
totally positive definite Gram matrix $A$ and $z \in \mathbb{C}^d$ with $\operatorname{Im}z_v > 0$ at every real place:
$$\theta_{A,L}(-1/z) = \Big(\prod_v\sqrt{\det\varphi_v(A)}\Big)^{-1}\Big(\prod_i\Delta(I_i)\Big)^{-1}
  \prod_v\Big(\frac{-iz_v}{2}\Big)^{n/2}\,\theta^\#_{A,L}(z),$$
$-1/z = (-1/z_v)_v$, principal branch of $(\cdot)^{n/2}$, $\Delta$ = `embDet` ($\Delta(\mathcal{O}_F) = |d_F|^{1/2}$), and
$\theta^\#_{A,L}$ the theta series of the dual lattice $\bigoplus_iI_i^{-1}\mathfrak d^{-1}$ with the form $\frac14\mu^{\mathsf T}A^{-1}\mu$.
For $F = \mathbb{Q}$ it is `QuadFormsKB.Siegel.thetaGram_S`. -/
@[kb "freitag1990" "Ch. I §4, theta inversion [unverified]"]
theorem thetaLat_inversion {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (𝔞 : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {z : InfinitePlace F → ℂ} (hz : ∀ v, 0 < (z v).im) :
    thetaLat A 𝔞 (fun v => -(z v)⁻¹) =
      (((∏ v, Real.sqrt (A.map (realEmb F v)).det)⁻¹ * (∏ i, embDet (𝔞 i))⁻¹ : ℝ) : ℂ) *
        (∏ v, (-Complex.I * z v / 2) ^ ((n : ℂ) / 2)) * thetaLatDual A 𝔞 z := by
  have hz0 : ∀ v, z v ≠ 0 := fun v h => by have := hz v; rw [h] at this; simp at this
  have hw : ∀ v, 0 < (-(z v)⁻¹).im := fun v => by
    have := hz v
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos this (Complex.normSq_pos.2 (hz0 v))
  set w : InfinitePlace F → ℂ := fun v => -2 * Complex.I * (-(z v)⁻¹)
  have hwinv : ∀ v, (w v)⁻¹ = -Complex.I * z v / 2 := fun v => by
    simp only [w]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have h := tsum_gaussAt (latMat A 𝔞) (dualMat A 𝔞) (latMat_transpose_mul hA 𝔞)
    (fun p => w (placeEquiv p.2)) (rate_re_pos (n := n) hw)
  rw [thetaLat, ← (Equiv.curry (Fin n) (Fin dq) ℤ).tsum_eq]
  simp_rw [thetaTerm_eq_gaussAt hA 𝔞 (fun v => -(z v)⁻¹)]
  rw [h, abs_det_latMat hA, thetaLatDual, ← (Equiv.curry (Fin n) (Fin dq) ℤ).tsum_eq]
  simp_rw [gaussAt_dualMat hA 𝔞 w, hwinv, prod_rate_cpow (fun v => -Complex.I * z v / 2)]
  rw [mul_inv]
  push_cast
  congr 1
  refine tsum_congr fun m => ?_
  rw [thetaTerm]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [qv_smul, map_mul]
  simp only [map_div₀, map_one, map_ofNat]
  push_cast
  ring_nf

/-! ### $\Delta(I)^2$ is the discriminant of the $\mathbb{Z}$-basis of $I$ -/

/-- The complex embedding $\varphi_v : F \to \mathbb{R} \subset \mathbb{C}$ as a $\mathbb{Q}$-algebra map. -/
def complexEmb (v : InfinitePlace F) : F →ₐ[ℚ] ℂ :=
  (Complex.ofRealHom.comp (realEmb F v)).toRatAlgHom

lemma complexEmb_apply (v : InfinitePlace F) (x : F) : complexEmb v x = (realEmb F v x : ℂ) := rfl

lemma complexEmb_injective : Function.Injective (complexEmb (F := F)) := by
  intro v w h
  have h1 : ∀ x, v.embedding x = w.embedding x := fun x => by
    have := congrArg (fun σ : F →ₐ[ℚ] ℂ => σ x) h
    simp only [complexEmb_apply, realEmb, embedding_of_isReal_apply] at this
    exact this
  have h2 : v.embedding = w.embedding := RingHom.ext h1
  rw [← mk_embedding v, ← mk_embedding w, h2]

/-- The real places, enumerated by `placeEquiv`, are all the complex embeddings of $F$. -/
def embEquiv : Fin (Module.finrank ℚ F) ≃ (F →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective (fun j => complexEmb (placeEquiv j)) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨complexEmb_injective.comp placeEquiv.injective, ?_⟩
    rw [Fintype.card_fin, AlgHom.card]

/-- **$\Delta(I)^2 = \operatorname{disc}_{\mathbb{Q}}(\beta)$** for the $\mathbb{Z}$-basis $\beta$ = `bq I` of $I$ (`Algebra.discr`; for $I = \mathcal{O}_F$
this is the field discriminant $d_F$, `embDet_one_sq`). -/
theorem embDet_sq (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    embDet I ^ 2 = (Algebra.discr ℚ (QuadFormsKB.Analysis.bq I) : ℝ) := by
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
    (QuadFormsKB.Analysis.bq I : Fin (Module.finrank ℚ F) → F) (embEquiv (F := F))
  have hM : Algebra.embeddingsMatrixReindex ℚ ℂ (QuadFormsKB.Analysis.bq I) (embEquiv (F := F)) =
      ((embMat (QuadFormsKB.Analysis.bq I))ᵀ).map Complex.ofRealHom := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, embEquiv, embMat,
      complexEmb_apply]
  rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_transpose] at h
  rw [embDet, sq_abs]
  have h' : ((Algebra.discr ℚ (QuadFormsKB.Analysis.bq I) : ℝ) : ℂ) =
      (((embMat (QuadFormsKB.Analysis.bq I)).det ^ 2 : ℝ) : ℂ) := by
    rw [ofReal_pow]
    rw [ofRealHom_eq_coe, eq_ratCast] at h
    rw [← h]
    simp
  exact (Complex.ofReal_injective h').symm

/-- **$\operatorname{disc}_{\mathbb{Q}}(\beta) = N(I)^2d_F$** for the $\mathbb{Z}$-basis $\beta$ = `bq I` of $I$ (`FractionalIdeal.absNorm`;
Mathlib's `det_basisOfFractionalIdeal_eq_absNorm`). -/
theorem discr_bq (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Algebra.discr ℚ (QuadFormsKB.Analysis.bq I) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F)) ^ 2 * (NumberField.discr F : ℚ) := by
  classical
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ Module.Free.ChooseBasisIndex ℤ I :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
        NumberField.fractionalIdeal_rank])
  set v := (basisOfFractionalIdeal F I).reindex e.symm
  have h1 : Algebra.discr ℚ (QuadFormsKB.Analysis.bq I) = Algebra.discr ℚ v := by
    rw [QuadFormsKB.Analysis.bq, Module.Basis.coe_reindex, Algebra.discr_reindex, Module.Basis.coe_reindex,
      Algebra.discr_reindex]
  have h2 := Algebra.discr_of_matrix_vecMul (A := ℚ) (integralBasis F)
    ((integralBasis F).toMatrix v)
  rw [Module.Basis.toMatrix_map_vecMul] at h2
  have h3 := NumberField.det_basisOfFractionalIdeal_eq_absNorm F I e
  rw [Module.Basis.det_apply] at h3
  rw [h1, h2, ← NumberField.coe_discr, ← sq_abs, h3]

/-- **$\Delta(I)^2 = N(I)^2d_F$**; in particular $d_F > 0$ for totally real $F$ and $\Delta(\mathcal{O}_F) = d_F^{1/2}$ (`embDet_one`). -/
theorem embDet_sq_eq (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    embDet I ^ 2 =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ)) ^ 2 * (NumberField.discr F : ℝ) := by
  rw [embDet_sq, discr_bq]
  push_cast
  ring

theorem embDet_one : embDet (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) = Real.sqrt (NumberField.discr F : ℝ) := by
  have h := embDet_sq_eq (F := F) 1
  rw [Units.val_one, FractionalIdeal.absNorm_one] at h
  simp only [Rat.cast_one, one_pow, one_mul] at h
  rw [← h]
  exact (Real.sqrt_sq (abs_nonneg _)).symm

/-- **Inversion for a form $Q$ over $\mathcal{O}_F$** ($L = \mathcal{O}_F^n$, $A = \frac12H$): for $z, w \in \mathbb{H}^d$ with
$w_v = -1/z_v$,
$$\theta_Q(w) = N_{F/\mathbb{Q}}(\det A)^{-1/2}\,d_F^{-n/2}\prod_v\Big(\frac{-iz_v}{2}\Big)^{n/2}\,\theta^\#_Q(z),$$
$\theta^\#_Q$ the theta series of $(\mathfrak d^{-1})^n$ with the form $\frac14\mu^{\mathsf T}A^{-1}\mu$, and
$\sqrt{N(\det A)} = \prod_v\sqrt{\det\varphi_v(A)}$. For $F = \mathbb{Q}$ ($d_F = 1$) this is `QuadFormsKB.Siegel.theta_S`. -/
@[kb "freitag1990" "Ch. I §4, theta inversion [unverified]"]
theorem thetaQ_inversion {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    (z w : InfinitePlace F → UpperHalfPlane) (hw : ∀ v, (w v : ℂ) = -((z v : ℂ))⁻¹) :
    thetaQ Q w =
      (((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
          (Real.sqrt (NumberField.discr F : ℝ) ^ n)⁻¹ : ℝ) : ℂ) *
        (∏ v, (-Complex.I * (z v : ℂ) / 2) ^ ((n : ℂ) / 2)) *
          thetaLatDual (gramF Q) (fun _ => 1) fun v => (z v : ℂ) := by
  rw [thetaQ_eq_thetaLatH, thetaLatH]
  have : (fun v => (w v : ℂ)) = fun v => -((z v : ℂ))⁻¹ := funext hw
  rw [this, thetaLat_inversion hQ _ fun v => (z v).im_pos]
  simp only [embDet_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end QuadFormsKB.HilbertModular
