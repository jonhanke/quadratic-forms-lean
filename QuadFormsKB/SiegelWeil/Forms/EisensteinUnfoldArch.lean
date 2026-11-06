/-
# The archimedean kernel of the big cell in unfolding coordinates

**Layer:** archimedean, over a totally real number field $F$ with real places $w$ ($d = [F:\mathbb Q]$).

**Setting.** With $Z(t) = X(t) + iY$ (`zPt`) the horizontal slice of $\mathbb H_r^d$ at a height $Y = (Y_w)_w$, $Y_w$ positive definite,
the archimedean kernel of the big cell is
$$g_\infty(Z) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\Big(\prod_w\det(-Z_w)\Big)^{-m}\qquad(\texttt{gInfR}).$$

**Results.**
* `zPt_mem_siegelHF`: $Z(t) \in \mathbb H_r^d$ for every $t$;
* `det_ne_zero_of_mem_siegelH`: $\det Z \neq 0$ for $Z \in \mathbb H_r$;
* `continuous_gInfR_zPt`, `gInfR_zPt_ne_zero`: $t \mapsto g_\infty(Z(t))$ is continuous and nowhere zero;
* **`integrable_gInfR_zPt`**: for $m > r$, $t \mapsto g_\infty(Z(t))$ is integrable on $\mathbb R^J$ ($J$ = `JR F r`). This is
  Hua's integral (`ArchR.integrable_inv_norm_det_pow_sharp`) at each place, a product over $w$, transported along the linear
  isomorphism $t \mapsto (X_w(t))_w$ of $\mathbb R^J$ onto $\mathrm{Sym}_r(\mathbb R)^d$.

Sources: Hua, *Harmonic analysis of functions of several complex variables in the classical domains* (1963), §2.1 [unverified];
Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldCoord
import QuadFormsKB.SiegelWeil.Forms.ArchHua

open Matrix NumberField MeasureTheory
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus
open QuadFormsKB.Tamagawa.ArchVol (symU)

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

/-- The archimedean kernel $g_\infty(Z) = \prod_w\det(\operatorname{Im}Z_w)^{m/2}\cdot\big(\prod_w\det(-Z_w)\big)^{-m}$. -/
def gInfR (m : ℕ) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  (∏ w, ((((Z w).map Complex.im).det : ℝ) : ℂ) ^ ((m : ℂ) / 2)) * (∏ w, (-(Z w)).det) ^ (-(m : ℤ))

section

variable (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hY : ∀ w, (Y w).PosDef)
include hY

/-- The imaginary part of $Z(t)_w$ is $Y_w$. -/
lemma zPt_im (t : JR F r → ℝ) (w : InfinitePlace F) : (zPt Y t w).map Complex.im = Y w := by
  ext i j
  simp [zPt]

/-- $Z(t) = X(t) + iY$ lies in $\mathbb H_r^d$ (with $Y_w$ positive definite). -/
lemma zPt_mem_siegelHF (t : JR F r → ℝ) : zPt Y t ∈ siegelHF F r := by
  intro w
  refine ⟨?_, by rw [zPt_im Y hY]; exact hY w⟩
  have hX : (xMat t w)ᵀ = xMat t w := symOf_transpose _
  have hYs : (Y w)ᵀ = Y w := (hY w).isHermitian.eq
  unfold zPt
  rw [Matrix.transpose_add, ← Matrix.transpose_map, ← Matrix.transpose_map, hX, hYs]

end

/-- $\det Z \ne 0$ for $Z \in \mathbb H_r$. -/
lemma det_ne_zero_of_mem_siegelH {Z : Matrix (Fin r) (Fin r) ℂ} (hZ : Z ∈ siegelH r) : Z.det ≠ 0 := by
  obtain ⟨R, d, hR, rfl⟩ := ArchR.exists_decomp_siegelH hZ
  have hdR : (cR R).det = (R.det : ℂ) := by
    rw [show cR R = R.map Complex.ofRealHom from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hdRT : (cR Rᵀ).det = (R.det : ℂ) := by
    rw [show cR Rᵀ = Rᵀ.map Complex.ofRealHom from rfl, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_transpose]
    rfl
  rw [det_mul, det_mul, hdR, hdRT, det_diagonal]
  have hR' : (R.det : ℂ) ≠ 0 := by exact_mod_cast hR
  refine mul_ne_zero (mul_ne_zero hR' (Finset.prod_ne_zero_iff.2 fun j _ => ?_)) hR'
  intro h
  have := congrArg Complex.im h
  simp at this

section

variable (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hY : ∀ w, (Y w).PosDef)
include hY

/-- $\det Z(t)_w \ne 0$. -/
lemma det_zPt_ne_zero (t : JR F r → ℝ) (w : InfinitePlace F) : (zPt Y t w).det ≠ 0 :=
  det_ne_zero_of_mem_siegelH (zPt_mem_siegelHF Y hY t w)

omit hY in
/-- $t \mapsto \det Z(t)_w$ is continuous. -/
lemma continuous_zPt_det (w : InfinitePlace F) : Continuous fun t : JR F r → ℝ => (zPt Y t w).det := by
  have hc : Continuous fun t : JR F r → ℝ => xCoord t := by
    unfold xCoord
    refine continuous_pi fun p => ?_
    exact (oBasis F).equivFun.symm.toContinuousLinearEquiv.continuous.comp
      (continuous_pi fun j => continuous_apply (p, j))
  unfold zPt
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Matrix.add_apply, map_apply]
  refine Continuous.add ?_ continuous_const
  refine Complex.continuous_ofReal.comp ?_
  simp only [xMat, symOf, of_apply]
  split_ifs
  · exact (continuous_apply w).comp ((continuous_apply _).comp hc)
  · exact (continuous_apply w).comp ((continuous_apply _).comp hc)

/-- $g_\infty(Z(t))$ with the constant first factor made explicit. -/
lemma gInfR_zPt_eq (m : ℕ) (t : JR F r → ℝ) :
    gInfR m (zPt Y t) = (∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)) * (∏ w, (-(zPt Y t w)).det) ^ (-(m : ℤ)) := by
  unfold gInfR
  simp only [zPt_im Y hY]

/-- $t \mapsto g_\infty(Z(t))$ is continuous. -/
lemma continuous_gInfR_zPt (m : ℕ) : Continuous fun t : JR F r → ℝ => gInfR m (zPt Y t) := by
  simp_rw [gInfR_zPt_eq Y hY]
  refine continuous_const.mul (Continuous.zpow₀ ?_ _ fun t => Or.inl ?_)
  · refine continuous_finsetProd _ fun w _ => ?_
    simp only [det_neg]
    exact continuous_const.mul (continuous_zPt_det Y w)
  · refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (det_zPt_ne_zero Y hY t w)

/-- $g_\infty(Z(t)) \ne 0$. -/
lemma gInfR_zPt_ne_zero (m : ℕ) (t : JR F r → ℝ) : gInfR m (zPt Y t) ≠ 0 := by
  rw [gInfR_zPt_eq Y hY]
  refine mul_ne_zero ?_ (zpow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun w _ => ?_))
  · refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    have h : ((Y w).det : ℂ) ≠ 0 := by exact_mod_cast (hY w).det_pos.ne'
    rw [Ne, Complex.cpow_eq_zero_iff]
    tauto
  · rw [det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (det_zPt_ne_zero Y hY t w)

end

/-- The linear isomorphism $t \mapsto (X_w(t))_w$ in upper coordinates, $\mathbb R^J \to (\mathbb R^{\mathrm{SymIdx}})^{d}$. -/
def phiR (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (r : ℕ) :
    (JR F r → ℝ) ≃ₗ[ℝ] (InfinitePlace F → SymIdx r → ℝ) where
  toFun t w p := xCoord t p w
  map_add' t s := by
    ext w p; simp [xCoord_add]
  map_smul' c t := by
    ext w p
    simp only [xCoord, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    have : (fun j => c * t (p, j)) = c • fun j => t (p, j) := rfl
    rw [this, map_smul]; rfl
  invFun x q := (oBasis F).equivFun (fun w => x w q.1) q.2
  left_inv t := by
    ext q
    obtain ⟨p, j⟩ := q
    show (oBasis F).equivFun ((oBasis F).equivFun.symm (fun j => t (p, j))) j = t (p, j)
    rw [LinearEquiv.apply_symm_apply]
  right_inv x := by
    ext w p
    simp only [xCoord]
    have : (oBasis F).equivFun.symm (fun j => (oBasis F).equivFun (fun w => x w p) j) = fun w => x w p := by
      exact (oBasis F).equivFun.symm_apply_apply _
    rw [this]

/-- Coordinates of `phiR`. -/
lemma phiR_apply (t : JR F r → ℝ) (w : InfinitePlace F) (p : SymIdx r) : phiR F r t w p = xCoord t p w := rfl

/-- Integrability transfers along a linear isomorphism of finite-dimensional real spaces (with Haar measures). -/
lemma integrable_comp_linearEquiv {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E'] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]
    (Φ : E ≃ₗ[ℝ] E') {g : E' → ℝ} (hg : Integrable g ν) : Integrable (g ∘ Φ) μ := by
  have hH : (μ.map Φ).IsAddHaarMeasure := inferInstance
  have hmap : μ.map Φ = (Measure.addHaarScalarFactor (μ.map Φ) ν) • ν :=
    Measure.isAddLeftInvariant_eq_smul _ _
  let e : E ≃ᵐ E' := Φ.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hint : Integrable g (μ.map e) := by
    show Integrable g (μ.map Φ)
    rw [hmap]; exact hg.smul_measure ENNReal.coe_ne_top
  exact (e.measurableEmbedding.integrable_map_iff (μ := μ) (f := e) (g := g)).1 hint

section

variable (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hY : ∀ w, (Y w).PosDef)
include hY

/-- $Z(t)_w = iY_w + \mathrm{symU}(\Phi(t)_w)$. -/
lemma zPt_eq (t : JR F r → ℝ) (w : InfinitePlace F) :
    zPt Y t w = (Y w).map (fun y => (y : ℂ) * Complex.I) + cR (symU (phiR F r t w)) := by
  have : symU (phiR F r t w) = xMat t w := by
    ext i j; simp [symU, xMat, symOf, phiR_apply]
  rw [this, zPt, add_comm]

/-- **Main:** for $m > r$, $t \mapsto g_\infty(Z(t))$ is integrable on $\mathbb R^J$. -/
theorem integrable_gInfR_zPt {m : ℕ} (hm : r < m) :
    Integrable (fun t : JR F r → ℝ => gInfR m (zPt Y t)) := by
  set G : (InfinitePlace F → SymIdx r → ℝ) → ℝ :=
    fun x => ∏ w, ‖(((Y w).map (fun y => (y : ℂ) * Complex.I)) + cR (symU (x w))).det‖⁻¹ ^ m with hG
  have hGint : Integrable G (volume : Measure (InfinitePlace F → SymIdx r → ℝ)) := by
    rw [volume_pi]
    refine Integrable.fintype_prod (f := fun w (b : SymIdx r → ℝ) =>
      ‖(((Y w).map (fun y => (y : ℂ) * Complex.I)) + cR (symU b)).det‖⁻¹ ^ m) (fun w => ?_)
    refine ArchR.integrable_inv_norm_det_pow_sharp hm ⟨?_, ?_⟩
    · ext i j
      have hYs : (Y w)ᵀ = Y w := (hY w).isHermitian.eq
      have := congrFun (congrFun hYs i) j
      simp only [transpose_apply] at this
      simp [this]
    · convert hY w using 1
      ext i j; simp
  have hcomp := integrable_comp_linearEquiv (volume : Measure (JR F r → ℝ))
    (volume : Measure (InfinitePlace F → SymIdx r → ℝ)) (phiR F r) hGint
  set C : ℝ := ‖∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)‖ with hC
  refine (hcomp.const_mul C).mono' (continuous_gInfR_zPt Y hY m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => le_of_eq ?_)
  rw [gInfR_zPt_eq Y hY, norm_mul, norm_zpow]
  simp only [Function.comp, hG]
  congr 1
  rw [_root_.zpow_neg, zpow_natCast, norm_prod, ← inv_pow, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← zPt_eq Y hY t w, det_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

end

end QuadFormsKB.SiegelWeil.Forms
