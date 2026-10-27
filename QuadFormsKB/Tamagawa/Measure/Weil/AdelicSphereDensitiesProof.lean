import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereBoxFormula
import QuadFormsKB.Tamagawa.Indefinite.SphereGauge
import QuadFormsKB.Siegel.NFMainTerm
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarTernary

/-!
# The input `AdelicSphereDensities`, proved

Totally real $F$, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = k+1\ge4$ variables, $m\in\mathcal O_F\setminus0$
represented over $F$. For the constructed adelic sphere data (`AdelicSphereSetup.sphereData`):

* **`sigV_intSph`**: $\sigma_v(T_v\cap L_v) = \beta_v(L, m)$ (`lerayMeasure_latL`, $\operatorname{vol}(\mathcal O_v) = 1$);
* **`map_restrict_sphereMeasure`**: the image of $\sigma_{\mathbb A}$ restricted to $\{y_f\in\hat L\}$ under the projection to
  $T_\infty = \prod_wT(m)_w$ is $|d_F|^{-(N-1)/2}\prod_v\beta_v(L, m)\cdot\sigma_\infty$, $\sigma_\infty$ = `sigInf` (the box
  formula and uniqueness of product measures);
* **`adelicSphereDensities`**: hence `AdelicSphereDensities Q₀ A (sigInf Q₀ m) (τInf Q₀ m)`.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Tamagawa.Measure.LerayFinite QuadFormsKB.Analysis
  QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)}

namespace AdelicSphereSetup

/-- **The Leray volume of the integral points of the local sphere is the local density.** -/
theorem sigV_intSph (hQ : Q₀.Nondegenerate) (m : 𝓞 F) (hm : (m : F) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    sigV Q₀ (m : F) hQ v (intSph Q₀ (m : F) v) = ENNReal.ofReal (LocalDensity.NF.localDensity v Q₀ m) := by
  have hs : MeasurableSet (sphV Q₀ (m : F) v) := (FibreLeray.isClosed_sphereV v Q₀ _).measurableSet
  rw [sigV, (MeasurableEmbedding.subtype_coe hs).comap_apply]
  have himg : Subtype.val '' intSph Q₀ (m : F) v = sphV Q₀ (m : F) v ∩ LocalZeta.latL v (k + 1) := by
    ext x
    simp only [mem_image, intSph, mem_setOf_eq, Subtype.exists, exists_and_right, exists_eq_right, mem_inter_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
  rw [himg]
  have hcompl := FibreLeray.sig_sph_compl v Q₀ hQ (σV v (m : F))
  rw [inter_comm, measure_inter_conull' (measure_mono_null (fun x hx => hx.2) hcompl)]
  have hι : ((LocalDensity.NF.ι v m : v.adicCompletionIntegers F) : v.adicCompletion F) = σV v (m : F) := rfl
  have hm' : m ≠ 0 := fun h => hm (by simp [h])
  rw [← hι, lerayMeasure_latL v (haarV v) (LocalDensity.NF.Qp v Q₀) (LocalDensity.NF.nondegenerate_Qp v hQ) (n := k + 1) (by omega)
    (LocalDensity.NF.ι v m) (LocalDensity.NF.ι_ne_zero v hm'), LocalZeta.haarV_real_O, one_pow, mul_one,
    ← LocalDensity.NF.localDensity_eq_completion]


theorem toReal_sigV_intSph (hQ : Q₀.Nondegenerate) (m : 𝓞 F) (hm : (m : F) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    (sigV Q₀ (m : F) hQ v (intSph Q₀ (m : F) v)).toReal = LocalDensity.NF.localDensity v Q₀ m := by
  have hm' : m ≠ 0 := fun h => hm (by simp [h])
  rw [sigV_intSph hQ m hm v, ENNReal.toReal_ofReal (QuadFormsKB.Siegel.localDensityNF_nonneg v Q₀ hQ hm')]

/-- **The constant of the box formula is the local side of Siegel's formula**:
$\frac{c_F(N)}{c_F(N-1)}\prod_v\sigma_v(T_v\cap L_v) = |d_F|^{-(N-1)/2}\prod_v\beta_v(L, m)$. -/
theorem boxConst_eq (hQ : Q₀.Nondegenerate) (m : 𝓞 F) (hm : (m : F) ≠ 0) :
    cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ (m : F) hQ v (intSph Q₀ (m : F) v)).toReal = finDensityProduct Q₀ m := by
  simp_rw [toReal_sigV_intSph hQ m hm]
  rw [finDensityProduct, cF_succ_eq, mul_div_assoc, div_self cF_pos'.ne', mul_one]
  congr 2
  push_cast
  ring

variable {ρ : F}

variable (Q₀ ρ) in
/-- **The projection of the adelic sphere to the real places**, $y\mapsto(y_w)_w$. -/
def projR (y : adelicSphere Q₀ ρ) : ∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ) :=
  fun w => ⟨adR y.1 w, (mem_sphR_iff Q₀ ρ w _).mpr (y.2.1 w)⟩

theorem measurable_projR : Measurable (projR Q₀ ρ) :=
  measurable_pi_iff.mpr fun w => (measurable_adR Q₀ ρ w).subtype_mk

section TotallyReal

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

variable (F k) in
/-- The point of the (empty) product over the complex places. -/
def ptC : ∀ _j : {w : InfinitePlace F // w.IsComplex}, Fin (k + 1) → ℂ := fun j => isEmptyElim j

variable (Q₀ ρ) in
/-- **The projection of the adelic sphere to $T_\infty$** (the parameter space; no complex places). -/
def projT (y : adelicSphere Q₀ ρ) : TInf Q₀ ρ := (projR Q₀ ρ y, ptC F k)

theorem measurable_projT : Measurable (projT Q₀ ρ) :=
  measurable_projR.prodMk measurable_const

theorem τInf_projT (y : adelicSphere Q₀ ρ) : τInf Q₀ ρ (projT Q₀ ρ y) = archVec y.1 := by
  refine Prod.ext rfl ?_
  funext j
  exact isEmptyElim j

/-- **The test function on the adelic sphere**: $(\Phi\otimes1_{\hat L})(y) = 1_{y_f\in\hat L}\,\Phi(\tau_\infty(y_\infty))$. -/
theorem testFn_eq (Φ : VInf F (k + 1) → ℝ≥0∞) (y : adelicSphere Q₀ ρ) :
    testFn Φ y.1 = (boxA Q₀ ρ fun _ => univ).indicator (fun y => Φ (τInf Q₀ ρ (projT Q₀ ρ y))) y := by
  have hiff : Indefinite.finVec y.1 ∈ latHat F (k + 1) ↔ y ∈ boxA Q₀ ρ fun _ => univ := by
    simp only [latHat, Indefinite.finVec, boxA, mem_setOf_eq, mem_univ, implies_true, true_and, IntVec, adV,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    exact forall_comm
  rw [testFn, ← τInf_projT y]
  by_cases h : y ∈ boxA Q₀ ρ fun _ => univ
  · rw [indicator_of_mem h, indicator_of_mem (hiff.mpr h), Pi.one_apply, mul_one]
  · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.mp h), mul_zero]

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)

open Classical in
/-- **The image of $\sigma_{\mathbb A}$ on $\{y_f\in\hat L\}$ at the real places** is
$\frac{c_F(N)}{c_F(N-1)}\prod_v\sigma_v(T_v\cap L_v)\cdot\bigotimes_w\sigma_w$ (the box formula and uniqueness of
product measures). -/
theorem map_projR_restrict (hfin : ∀ v, sigV Q₀ ρ hQ v (intSph Q₀ ρ v) ≠ ⊤) :
    ((S.sphereMeasure hρ hQ hk).restrict (boxA Q₀ ρ fun _ => univ)).map (projR Q₀ ρ) =
      ENNReal.ofReal (cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal) •
        Measure.pi fun w => sig (QRe Q₀ w) (σR w ρ) := by
  set D := cF F (k + 1) / cF F k * ∏' v, (sigV Q₀ ρ hQ v (intSph Q₀ ρ v)).toReal
  have hσ : ∀ w, SigmaFinite (sig (QRe Q₀ w) (σR w ρ)) := fun w => sigmaFinite_sig ((map_ne_zero _).mpr hρ)
  obtain ⟨w₀⟩ : Nonempty {w : InfinitePlace F // w.IsReal} := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact ⟨⟨w, not_isComplex_iff_isReal.mp fun h => isEmptyElim (⟨w, h⟩ : {w : InfinitePlace F // w.IsComplex})⟩⟩
  classical
  set c : {w : InfinitePlace F // w.IsReal} → NNReal := fun w => if w = w₀ then D.toNNReal else 1
  have key : ∀ μ' : Measure (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w ρ)),
      (∀ s : ∀ w, Set (Sph (QRe Q₀ w) (σR w ρ)), (∀ w, MeasurableSet (s w)) →
        μ' (univ.pi s) = ENNReal.ofReal D * ∏ w, sig (QRe Q₀ w) (σR w ρ) (s w)) →
      Measure.pi (fun w => c w • sig (QRe Q₀ w) (σR w ρ)) = μ' := fun μ' h => by
    refine Measure.pi_eq fun s hs => ?_
    rw [h s hs]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
    congr 1
    rw [← ENNReal.ofNNReal_finsetProd]
    simp only [c, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    rfl
  refine (key _ fun s hs => ?_).symm.trans (key _ fun s hs => ?_)
  · rw [Measure.map_apply measurable_projR (MeasurableSet.univ_pi hs),
      Measure.restrict_apply (measurable_projR (MeasurableSet.univ_pi hs))]
    have : projR Q₀ ρ ⁻¹' univ.pi s ∩ (boxA Q₀ ρ fun _ => univ) = boxA Q₀ ρ s := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_univ_pi, boxA, mem_setOf_eq, mem_univ, implies_true,
        true_and, projR]
    rw [this, S.sphereMeasure_boxA hρ hQ hk s hs hfin]
  · rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]

/-- **`AdelicSphereDensities` for the constructed data** (totally real $F$, $m\in\mathcal O_F\setminus0$, $N\ge4$):
$\int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)
\int_{T_\infty}\Phi\circ\tau_\infty\,d\sigma_\infty$. -/
@[kb "weil1965" "Sur la formule de Siegel: Tamagawa measure of the sphere = ∏ local densities [unverified]"]
theorem adelicSphereDensities {m : 𝓞 F} (S : AdelicSphereSetup Q₀ (m : F)) (hm : (m : F) ≠ 0) :
    AdelicSphereDensities Q₀ (S.sphereData hm hQ hk) (sigInf Q₀ (m : F)) (τInf Q₀ (m : F)) := by
  refine ⟨fun Φ hΦ => ?_⟩
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (Indefinite.mR_ne_zero hm w)
  have hfin : ∀ v, sigV Q₀ (m : F) hQ v (intSph Q₀ (m : F) v) ≠ ⊤ := fun v => by
    rw [sigV_intSph hQ m hm v]; exact ENNReal.ofReal_ne_top
  have hW := measurableSet_boxA (Q₀ := Q₀) (ρ := (m : F)) (fun _ => univ) fun _ => MeasurableSet.univ
  have hf : Measurable fun t => Φ (τInf Q₀ (m : F) t) := hΦ.comp (measurable_τInf Q₀ _)
  show ∫⁻ x, testFn Φ x.1 ∂S.sphereMeasure hm hQ hk = _
  simp_rw [testFn_eq]
  rw [lintegral_indicator hW,
    ← lintegral_map (f := fun t => Φ (τInf Q₀ (m : F) t)) hf measurable_projT]
  have hT : projT Q₀ (m : F) = (fun x => (x, ptC F k)) ∘ projR Q₀ (m : F) := rfl
  have hmap : ((S.sphereMeasure hm hQ hk).restrict (boxA Q₀ (m : F) fun _ => univ)).map
      ((fun x => (x, ptC F k)) ∘ projR Q₀ (m : F)) =
      (((S.sphereMeasure hm hQ hk).restrict (boxA Q₀ (m : F) fun _ => univ)).map (projR Q₀ (m : F))).map
        (fun x => (x, ptC F k)) :=
    (Measure.map_map (measurable_id.prodMk measurable_const) measurable_projR).symm
  rw [hT, hmap, S.map_projR_restrict hm hQ hk hfin, Measure.map_smul, ← Measure.prod_dirac, lintegral_smul_measure,
    boxConst_eq hQ m hm]
  congr 2
  · rw [sigInf]
    congr 1
    classical
    exact (Measure.pi_of_empty _ (ptC F k)).symm
  · exact (measurable_id.prodMk measurable_const).aemeasurable

end TotallyReal

end AdelicSphereSetup

/-! ### Consumers: Siegel's formula for indefinite forms without the sphere inputs -/

section Consumers

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

/-- **Siegel's formula for indefinite forms over a totally real field, without the sphere inputs**
($N = k+1\ge4$, $m\in\mathcal O_F\setminus0$ with a rational point $\xi$ on $Q = m$): `AdelicSphereFibration` and
`AdelicSphereDensities` are proved for the constructed adelic sphere data, so only $\tau(SO(V)) = 2$ and
$\tau = 2$ for the forms in $k$ variables remain:
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_classical_totallyReal_of_tau (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) (hτ : TamagawaNumberTwoAdelic Q₀ hQ)
    (hτ' : ∀ (Q' : QuadForm (𝓞 F) k) (hQ' : Q'.Nondegenerate), TamagawaNumberTwoAdelic Q' hQ') :
    cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  obtain ⟨S⟩ := exists_adelicSphereSetup hQ hm ξ (by omega)
  exact siegelIndefinite_classical_totallyReal Q₀ hQ (by omega) hm (S.sphereFibration hm hQ hk)
    (S.adelicSphereDensities hQ hk hm) hτ (hτ' _ _)

/-- **The ratio form**, under the hypotheses of `siegelIndefinite_classical_totallyReal_of_tau`:
$c_\infty(m)\sum_i\rho(M_i, m)/\sum_iv(M_i) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)$. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem siegelIndefinite_classical_div_totallyReal_of_tau (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) (hτ : TamagawaNumberTwoAdelic Q₀ hQ)
    (hτ' : ∀ (Q' : QuadForm (𝓞 F) k) (hQ' : Q'.Nondegenerate), TamagawaNumberTwoAdelic Q' hQ') :
    (cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i) /
        ∑' i, unitVolume Q₀ hQ i =
      ENNReal.ofReal (finDensityProduct Q₀ m) := by
  obtain ⟨S⟩ := exists_adelicSphereSetup hQ hm ξ (by omega)
  exact siegelIndefinite_classical_div_totallyReal Q₀ hQ (by omega) hm (S.sphereFibration hm hQ hk)
    (S.adelicSphereDensities hQ hk hm) hτ (hτ' _ _)

/-- **Quaternary forms** ($N = 4$): $\tau = 2$ for the ternary complement is proved (`covolume_muTam_ternary`), so
Siegel's formula is conditional only on $\tau(SO(V)) = 2$:
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-3/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real; N = 4) [unverified]"]
theorem siegelIndefinite_classical_quaternary_of_tau (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) (hτ : TamagawaNumberTwoAdelic Q₀ hQ) :
    cInf (k := 3) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i :=
  siegelIndefinite_classical_totallyReal_of_tau hQ le_rfl hm ξ hτ covolume_muTam_ternary

end Consumers

end QuadFormsKB.Tamagawa.Measure.Weil

end
