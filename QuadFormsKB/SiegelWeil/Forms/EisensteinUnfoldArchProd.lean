/-
# The archimedean integral of the unfolding as a product over the real places
**Layer:** archimedean, over a totally real number field $F$ with real places $w$.

**Setting.** $Y = (Y_w)_w$ with every $Y_w$ positive definite, $m > r$, $T$ a quadratic form in $r$ variables over $F$ with Gram matrix $T_G$.
The archimedean integral of the unfolding is $\int_{\mathbb R^J}g_\infty(X(t)+iY)\,e_T(-X(t))\,dt$ (`archIntR`), $J$ = `JR F r`.
Along the linear isomorphism $\Phi = $ `phiR` $:\mathbb R^J\to\mathrm{Sym}_r(\mathbb R)^d$ the integrand becomes a constant times a product of
functions of the separate $X_w$.

**Definitions.**
* `archPlaceR m T Y w`: $\displaystyle\int_{\mathrm{Sym}_r(\mathbb R)}\det(-(iY_w+x))^{-m}\,e\big(-\operatorname{tr}(\sigma_w(T_G)x)\big)\,dx$.
* `phiDetR F r`: the factor by which $\Phi$ multiplies Lebesgue measure, i.e. $|\det\Phi|$ (the Haar scalar factor with
  $\mathrm{vol}_{\mathbb R^J}\circ\Phi^{-1} = |\det\Phi|^{-1}\,\mathrm{vol}$). `LinearMap.det` is unavailable because $\Phi$ is a map between two
  different spaces; this is the intrinsic replacement.

**Results.**
* `integral_comp_phiR`: $\int_{\mathbb R^J}g(\Phi t)\,dt = |\det\Phi|^{-1}\int g$;
* **`archIntR_eq_prod`**:
$$\int_{\mathbb R^J}g_\infty(Z(t))\,\chi_T(t)\,dt=\Big(\prod_w\det(Y_w)^{m/2}\Big)\cdot|\det\Phi|^{-1}\cdot\prod_w\texttt{archPlaceR}_w .$$

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935) [unverified];
Hua, *Harmonic analysis of functions of several complex variables in the classical domains* (1963), §2.1 [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfold
open Matrix NumberField MeasureTheory
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus
open QuadFormsKB.Tamagawa.ArchVol (symU)
set_option linter.unusedSectionVars false
noncomputable section
namespace QuadFormsKB.SiegelWeil.Forms
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

/-- The archimedean integral at one real place: $\int_{\mathrm{Sym}_r(\mathbb R)}\det(-(iY_w + x))^{-m}\,e(-\operatorname{tr}(\sigma_w(T_G)x))\,dx$. -/
def archPlaceR (m : ℕ) (T : QuadForm F r) (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (w : InfinitePlace F) : ℂ :=
  ∫ x : SymIdx r → ℝ, (-((Y w).map (fun y => (y : ℂ) * Complex.I) + cR (symU x))).det ^ (-(m : ℤ)) *
    Complex.exp (-(2 * Real.pi * Complex.I) * ∑ i, ∑ j, ((realEmb F w (gramT T i j) : ℝ) : ℂ) * ((symU x j i : ℝ) : ℂ))

/-- Lebesgue measure on $\mathrm{Sym}_r(\mathbb R)^d$ (a product of products of $\mathbb R$) is an additive Haar measure. -/
instance instAddHaarVolumeSymPlaces :
    (volume : Measure (InfinitePlace F → SymIdx r → ℝ)).IsAddHaarMeasure := by
  rw [volume_pi]
  infer_instance

/-- The pushforward of Lebesgue measure on $\mathbb R^J$ along `phiR` is an additive Haar measure. -/
instance instAddHaarMapPhiR :
    ((volume : Measure (JR F r → ℝ)).map (phiR F r)).IsAddHaarMeasure :=
  Measure.MapLinearEquiv.isAddHaarMeasure (𝕜 := ℝ) (volume : Measure (JR F r → ℝ)) (phiR F r)

/-- The volume expansion factor $|\det\Phi|$ of the linear isomorphism `phiR F r` (as the inverse of the Haar scalar factor of
$\mathrm{vol}\circ\Phi^{-1}$ relative to $\mathrm{vol}$). -/
def phiDetR (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (r : ℕ) : ℝ :=
  ((Measure.addHaarScalarFactor ((volume : Measure (JR F r → ℝ)).map (phiR F r))
    (volume : Measure (InfinitePlace F → SymIdx r → ℝ)) : NNReal) : ℝ)⁻¹

/-- Change of variables along `phiR`: $\int g(\Phi t)\,dt = |\det\Phi|^{-1}\int g$. -/
lemma integral_comp_phiR (g : (InfinitePlace F → SymIdx r → ℝ) → ℂ) :
    ∫ t, g (phiR F r t) = ((phiDetR F r)⁻¹ : ℝ) • ∫ y, g y := by
  have hH : ((volume : Measure (JR F r → ℝ)).map (phiR F r)).IsAddHaarMeasure := inferInstance
  have hmap : (volume : Measure (JR F r → ℝ)).map (phiR F r) =
      (Measure.addHaarScalarFactor ((volume : Measure (JR F r → ℝ)).map (phiR F r))
        (volume : Measure (InfinitePlace F → SymIdx r → ℝ))) • (volume : Measure (InfinitePlace F → SymIdx r → ℝ)) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  let e : (JR F r → ℝ) ≃ᵐ (InfinitePlace F → SymIdx r → ℝ) :=
    (phiR F r).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have h1 : ∫ t, g (phiR F r t) = ∫ y, g y ∂((volume : Measure (JR F r → ℝ)).map (phiR F r)) := by
    have := e.measurableEmbedding.integral_map (μ := (volume : Measure (JR F r → ℝ))) g
    exact this.symm
  rw [h1, hmap, integral_smul_nnreal_measure, phiDetR, inv_inv]
  rfl

/-- The characteristic $\chi_T(t)$ as a product over the real places. -/
lemma chiT_eq_prod (T : QuadForm F r) (t : JR F r → ℝ) :
    chiT T t = ∏ w, Complex.exp (-(2 * Real.pi * Complex.I) *
      ∑ i, ∑ j, ((realEmb F w (gramT T i j) : ℝ) : ℂ) * ((symU (phiR F r t w) j i : ℝ) : ℂ)) := by
  unfold chiT eT trPair
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hs : symU (phiR F r t w) = xMat t w := by
    ext i j; simp [symU, xMat, symOf, phiR_apply]
  rw [hs]
  congr 1
  simp [Finset.mul_sum, Finset.sum_neg_distrib]

/-- **Main:** the archimedean integral of the unfolding factors over the real places. -/
theorem archIntR_eq_prod (Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ) (hY : ∀ w, (Y w).PosDef)
    {m : ℕ} (hm : r < m) (T : QuadForm F r) :
    archIntR m T Y = (∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2)) *
      (((phiDetR F r : ℝ)) : ℂ)⁻¹ * ∏ w, archPlaceR m T Y w := by
  have _ := hm
  set C : ℂ := ∏ w, ((((Y w).det : ℝ) : ℂ)) ^ ((m : ℂ) / 2) with hC
  set gw : InfinitePlace F → (SymIdx r → ℝ) → ℂ := fun w x =>
    (-((Y w).map (fun y => (y : ℂ) * Complex.I) + cR (symU x))).det ^ (-(m : ℤ)) *
      Complex.exp (-(2 * Real.pi * Complex.I) *
        ∑ i, ∑ j, ((realEmb F w (gramT T i j) : ℝ) : ℂ) * ((symU x j i : ℝ) : ℂ)) with hgw
  have hint : ∀ t : JR F r → ℝ, gInfR m (zPt Y t) * chiT T t =
      C * ∏ w, gw w (phiR F r t w) := by
    intro t
    have h2 : (∏ w, (-(zPt Y t w)).det) ^ (-(m : ℤ)) =
        ∏ w, (-((Y w).map (fun y => (y : ℂ) * Complex.I) + cR (symU (phiR F r t w)))).det ^ (-(m : ℤ)) := by
      rw [← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun w _ => by rw [zPt_eq Y hY t w]
    rw [gInfR_zPt_eq Y hY, chiT_eq_prod, h2, mul_assoc, ← Finset.prod_mul_distrib]
  unfold archIntR
  simp_rw [hint]
  rw [integral_const_mul, integral_comp_phiR (fun x => ∏ w, gw w (x w)),
    integral_fintype_prod_volume_eq_prod gw]
  rw [Complex.real_smul]
  simp only [archPlaceR]
  push_cast
  ring
end QuadFormsKB.SiegelWeil.Forms
