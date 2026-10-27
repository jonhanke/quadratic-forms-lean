import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerExhaust

/-!
# The adelic cone integral of a product test function

$F$ totally real, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$), $S\supseteq$ `badCone`,
$K_v$ ($v\in S$) measurable. Restricting $\sigma_C$ to $Y = \{x : x_v\in K_v\ (v\in S),\ x_v\in L_v\ (v\notin S)\}$
and pushing forward to $\prod_w C^\circ_w$ gives $\kappa(S)\,\mathrm{boxMass}(S,K)\cdot\prod_w\sigma_{C,w}$
(`map_restrict_coneMeasure`, by uniqueness of product measures; $\sigma_{C,w}$ is σ-finite, `sigmaFinite_sigCone`),
$\kappa(S) = M(S)/P(S)$ (`coneConst`). Hence (**`lintegral_coneMeasure_prod`**)
$$\int_{C^\circ(\mathbb A)}\mathbf 1_Y(x)\prod_w\varphi_w(x_w)\,d\sigma_C(x) =
  \kappa(S)\,\mathrm{boxMass}(S,K)\prod_w\int_{C^\circ_w}\varphi_w\,d\sigma_{C,w}.$$
-/

open MeasureTheory Set Matrix Filter Topology
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra QuadFormsKB.Tamagawa.Measure.LerayReal

/-- **The real cone measure is σ-finite** ($k\ge1$): the closed balls have finite measure. -/
theorem sigmaFinite_sigCone {k : ℕ} {c : ℝ} {Q' : QuadForm ℝ k} (hc : c ≠ 0) (hQ' : Siegel.gramDetR Q' ≠ 0)
    (hk : 1 ≤ k) : SigmaFinite (ConeReal.sigCone (Q' := Q') hc) :=
  ⟨⟨{ set := fun n : ℕ => {z | ‖(z : Fin (k + 1 + 1) → ℝ)‖ ≤ n}
      set_mem := fun _ => trivial
      finite := fun n => ConeReal.sigCone_closedBall_lt_top hc hQ' hk n
      spanning := by
        refine eq_univ_of_forall fun z => mem_iUnion.mpr ?_
        obtain ⟨n, hn⟩ := exists_nat_ge ‖(z : Fin (k + 1 + 1) → ℝ)‖
        exact ⟨n, hn⟩ }⟩⟩

variable {F : Type} [Field F] [NumberField F] {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k}
  (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-- The finite conditions: $x_v\in K_v$ ($v\in S$), $x_v\in L_v$ ($v\notin S$). -/
def Yset (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) : Set (adelicCone QC) :=
  {x | ∀ v, adV x.1 v ∈ ConeAdelic.boxSet S K v}

theorem measurableSet_Yset {S : Finset (HeightOneSpectrum (𝓞 F))}
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v)) :
    MeasurableSet (Yset (c₀ := c₀) (Q₀' := Q₀') S K) := by
  have : Yset (c₀ := c₀) (Q₀' := Q₀') S K = ⋂ v, (fun x : adelicCone QC => coneVpt x v) ⁻¹'
      (Subtype.val ⁻¹' ConeAdelic.boxSet S K v) := by
    ext x; simp only [Yset, mem_iInter, mem_preimage, mem_setOf_eq]; rfl
  rw [this]
  exact MeasurableSet.iInter fun v => measurable_coneVpt v (measurable_subtype_coe (measurableSet_boxSet hK v))

/-- The archimedean components of a point of the adelic cone. -/
def archPt (x : adelicCone QC) : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w) :=
  fun w => coneRpt x w

theorem measurable_archPt : Measurable (archPt (c₀ := c₀) (Q₀' := Q₀')) :=
  measurable_pi_iff.mpr fun w => measurable_coneRpt w

section Product

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

/-- **The constant** $\kappa(S) = M(S)/P(S)$. -/
def coneConst (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ≥0∞ :=
  boxConst hc hQ' S / ENNReal.ofReal (primProd hc hQ' S)

theorem coneConst_ne_top (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) :
    coneConst hc hQ' S ≠ ⊤ :=
  ENNReal.div_ne_top (boxConst_ne_top hc hQ' hk S) (ENNReal.ofReal_pos.mpr (primProd_pos hc hQ' hk S hS)).ne'

include hk in
theorem coneConst_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) : coneConst hc hQ' S ≠ 0 :=
  ENNReal.div_ne_zero.mpr ⟨boxConst_ne_zero hc hQ' hk S, ENNReal.ofReal_ne_top⟩

open Classical in
theorem coneMeasure_Xset
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) :
    coneMeasure hc hQ' hk (Xset AR S K) =
      coneConst hc hQ' S * ConeAdelic.boxMass QC hQ S K * ∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w) := by
  have h := coneMeasure_Xset_mul hc hQ' hk hAR S hS hK hQ
  have hP := primProd_pos hc hQ' hk S hS
  rw [coneConst, ENNReal.div_eq_inv_mul]
  rw [mul_comm, ← ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr hP).ne' ENNReal.ofReal_ne_top] at h
  rw [h, ENNReal.div_eq_inv_mul]
  ring

open Classical in
/-- **The archimedean pushforward of $\sigma_C|_Y$** is $\kappa(S)\,\mathrm{boxMass}(S,K)\prod_w\sigma_{C,w}$. -/
theorem map_restrict_coneMeasure (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) (hfin : ConeAdelic.boxMass QC hQ S K ≠ ⊤) :
    ((coneMeasure hc hQ' hk).restrict (Yset S K)).map archPt =
      (coneConst hc hQ' S * ConeAdelic.boxMass QC hQ S K) •
        Measure.pi fun w => ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w) := by
  have hσ : ∀ w : {w : InfinitePlace F // w.IsReal}, SigmaFinite (ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) :=
    fun w => sigmaFinite_sigCone (cRe_ne hc w) (gramDetR_QRe' hQ' w) (by omega)
  set ν := ((coneMeasure hc hQ' hk).restrict (Yset S K)).map archPt
  set c := coneConst hc hQ' S * ConeAdelic.boxMass QC hQ S K
  have hrect : ∀ AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)),
      (∀ w, MeasurableSet (AR w)) → ν (univ.pi AR) = c * ∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w) := by
    intro AR hAR
    rw [Measure.map_apply measurable_archPt (MeasurableSet.univ_pi hAR), Measure.restrict_apply
      (measurable_archPt (MeasurableSet.univ_pi hAR))]
    have : archPt ⁻¹' univ.pi AR ∩ Yset S K = Xset AR S K := by
      ext x; simp [Xset, Yset, archPt]
    rw [this, coneMeasure_Xset hc hQ' hk hAR S hS hK hQ]
  have hc_top : c ≠ ⊤ := ENNReal.mul_ne_top (coneConst_ne_top hc hQ' hk S hS) hfin
  by_cases hc0 : c = 0
  · have : ν = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ, hrect _ fun _ => MeasurableSet.univ, hc0, zero_mul]
    rw [this, hc0, zero_smul]
  · have h := Measure.pi_eq (μ := fun w => ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) (μ' := c⁻¹ • ν)
      fun AR hAR => by rw [Measure.smul_apply, hrect AR hAR, smul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hc0 hc_top, one_mul]
    rw [h, smul_smul, ENNReal.mul_inv_cancel hc0 hc_top, one_smul]

open Classical in
/-- **The adelic cone integral of a product test function** ($F$ totally real, $k\ge3$, $S\supseteq$ `badCone`):
$$\int\mathbf 1_Y(x)\prod_w\varphi_w(x_w)\,d\sigma_C =
  \kappa(S)\,\mathrm{boxMass}(S,K)\prod_w\int\varphi_w\,d\sigma_{C,w}.$$ -/
@[kb "weil1982" "§2.3, p. 21; §4.5, p. 108 (the cone integral as a product of local integrals) [unverified page]"]
theorem lintegral_coneMeasure_prod (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) (hfin : ConeAdelic.boxMass QC hQ S K ≠ ⊤)
    {φ : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w) → ℝ≥0∞} (hφ : ∀ w, Measurable (φ w)) :
    ∫⁻ x, (Yset S K).indicator (fun x => ∏ w, φ w (coneRpt x w)) x ∂coneMeasure hc hQ' hk =
      coneConst hc hQ' S * ConeAdelic.boxMass QC hQ S K *
        ∏ w, ∫⁻ z, φ w z ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w) := by
  have hσ : ∀ w : {w : InfinitePlace F // w.IsReal}, SigmaFinite (ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) :=
    fun w => sigmaFinite_sigCone (cRe_ne hc w) (gramDetR_QRe' hQ' w) (by omega)
  have hG : Measurable fun y : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w) =>
      ∏ w, φ w (y w) := Finset.measurable_prod _ fun w _ => (hφ w).comp (measurable_pi_apply w)
  rw [lintegral_indicator (measurableSet_Yset hK)]
  change ∫⁻ x in Yset S K, (fun y => ∏ w, φ w (y w)) (archPt x) ∂coneMeasure hc hQ' hk = _
  rw [← lintegral_map hG measurable_archPt, map_restrict_coneMeasure hc hQ' hk S hS hK hQ hfin,
    lintegral_smul_measure, lintegral_pi_prod _ _ hφ, smul_eq_mul]

end Product

end QuadFormsKB.Tamagawa.Measure.Weil

end
