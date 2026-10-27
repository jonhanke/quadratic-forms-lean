import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerArch
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropicGauss
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoIsotropic

/-!
# `AdelicConeEuler` for the Gaussian test function

$F$ totally real, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$). On the adelic cone the
Gaussian test function $\Phi$ = `gaussTest` is $\mathbf 1_{\prod_v L_v}(x_f)\prod_w e^{-\pi|x_w|^2}$
(`gaussTest_cone`), so `lintegral_coneMeasure_prod` gives
$I_C(\Phi) = \kappa\,\mathrm{boxMass}(S,L)\prod_w\int e^{-\pi|z|^2}d\sigma_{C,w}$ (`lintegral_gaussTest_cone`), and
**`adelicConeEuler_gaussTest`** proves `AdelicConeEuler` for it.

*Update:* `AdelicConeEuler` is existential in the archimedean factors
$\Phi_w$, so the constant $\kappa = M(S)/P(S)$ of the box formula is absorbed into $\Phi_{w_0}$ at one real place
$w_0$; the input fixes $I_C(\Phi)$ only up to this constant. What `tamagawaNumberTwoAdelic_cone` uses from it is the
finiteness $I_C(\Phi) < \infty$ (`AdelicConeEuler.lt_top`), which does not depend on $\kappa$.
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

/-! ### Generic facts -/

theorem isBounded_latL {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Bornology.IsBounded (LocalZeta.latL v n) := by
  refine (Metric.isBounded_closedBall (x := (0 : Fin n → v.adicCompletion F)) (r := 1)).subset fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  have h : ‖x i‖ ≤ ‖(1 : v.adicCompletion F)‖ := Valued.toNormedField.norm_le_iff.mpr (by rw [map_one]; exact hx i)
  rwa [norm_one] at h

/-- $\|z\|_\infty^2\le\sum_iz_i^2$. -/
theorem sq_norm_le_sum_sq {n : ℕ} (z : Fin n → ℝ) : ‖z‖ ^ 2 ≤ ∑ i, z i ^ 2 := by
  have hs : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖z‖ ≤ Real.sqrt (∑ i, z i ^ 2) := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => by
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ i, z i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, z i ^ 2 := Real.sq_sqrt hs

/-- A real place, when $F$ has no complex places. -/
def realPlace₀ (F : Type) [Field F] [NumberField F] [IsEmpty {w : InfinitePlace F // w.IsComplex}] :
    {w : InfinitePlace F // w.IsReal} :=
  ⟨Classical.arbitrary _, (isReal_or_isComplex _).resolve_right fun h => isEmptyElim (⟨_, h⟩ : {w // IsComplex w})⟩

/-! ### The Gaussian on the cone -/

variable {F : Type} [Field F] [NumberField F]

/-- The Gaussian $e^{-\pi\sum_iz_i^2}$ at a real place. -/
def gaussRe {n : ℕ} (z : Fin n → ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-Real.pi * ∑ i, z i ^ 2))

theorem measurable_gaussRe {n : ℕ} : Measurable (gaussRe (n := n)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)))

theorem gaussRe_le {n : ℕ} (z : Fin n → ℝ) : gaussRe z ≤ ENNReal.ofReal (Real.exp (-(Real.pi * ‖z‖ ^ 2))) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have := sq_norm_le_sum_sq z
  nlinarith [Real.pi_pos]

open Classical in
/-- With no complex places, the archimedean Gaussian factors over the real places. -/
theorem ofReal_gV_fst [IsEmpty {w : InfinitePlace F // w.IsComplex}] {n : ℕ} (y : AdeleSpace F (Fin n)) :
    ENNReal.ofReal (gV fun i => (y i).1) = ∏ w, gaussRe (adR y w) := by
  simp only [gaussRe, gV, gR]
  simp only [Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.sum_empty, mul_zero, add_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_sum]
  congr 2
  simp only [adR]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mem_OHatVec_iff {n : ℕ} (y : AdeleSpace F (Fin n)) :
    (fun i => (y i).2) ∈ OHatVec ↔ ∀ v, adV y v ∈ LocalZeta.latL v n := by
  simp only [OHatVec, OHat, mem_univ_pi, mem_setOf_eq, adV, LocalZeta.latL,
    HeightOneSpectrum.mem_adicCompletionIntegers]
  exact forall_comm

variable {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

open Classical in
/-- **The Gaussian test function on the adelic cone**: $\Phi(x) = \mathbf 1_Y(x)\prod_w e^{-\pi|x_w|^2}$ with $Y$ the
lattice conditions at every finite place (any $S$). -/
theorem gaussTest_cone [IsEmpty {w : InfinitePlace F // w.IsComplex}] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : adelicCone QC) :
    gaussTest F (k + 1 + 1) x.1 =
      (Yset S fun v => LocalZeta.latL v (k + 1 + 1)).indicator (fun x => ∏ w, gaussRe (coneRpt x w).1) x := by
  have hY : x ∈ Yset S (fun v => LocalZeta.latL v (k + 1 + 1)) ↔ ∀ v, adV x.1 v ∈ LocalZeta.latL v (k + 1 + 1) := by
    simp only [Yset, mem_setOf_eq]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [boxSet_of_mem hv]
    · rw [boxSet_of_not_mem hv]
  rw [gaussTest, ofReal_gV_fst]
  by_cases h : ∀ v, adV x.1 v ∈ LocalZeta.latL v (k + 1 + 1)
  · rw [indicator_of_mem ((mem_OHatVec_iff _).mpr h), indicator_of_mem (hY.mpr h), one_mul]
    rfl
  · rw [indicator_of_notMem (fun h' => h ((mem_OHatVec_iff _).mp h')),
      indicator_of_notMem (fun h' => h (hY.mp h')), zero_mul]

section Euler

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

open Classical in
/-- **The cone integral of the Gaussian**: $I_C(\Phi) = \kappa(S)\,\mathrm{boxMass}(S,L)\prod_w\int e^{-\pi|z|^2}
d\sigma_{C,w}$. -/
theorem lintegral_gaussTest_cone (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) :
    ∫⁻ x, gaussTest F (k + 1 + 1) x.1 ∂coneMeasure hc hQ' hk =
      coneConst hc hQ' S * ConeAdelic.boxMass QC hQ S (fun v => LocalZeta.latL v (k + 1 + 1)) *
        ∏ w, ∫⁻ z, gaussRe z.1 ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w) := by
  have hfin : ConeAdelic.boxMass QC hQ S (fun v => LocalZeta.latL v (k + 1 + 1)) ≠ ⊤ := by
    unfold ConeAdelic.boxMass
    refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun v _ => ?_) ENNReal.ofReal_ne_top
    rw [ConeAdelic.coneMeas_latL QC hQ (by omega) v]; exact ENNReal.ofReal_ne_top
  rw [lintegral_congr fun x => gaussTest_cone S x]
  exact lintegral_coneMeasure_prod hc hQ' hk S hS (fun v _ => LocalZeta.measurableSet_latL v) hQ hfin
    (φ := fun w z => gaussRe z.1) fun w => measurable_gaussRe.comp measurable_subtype_coe

open Classical in
/-- **`AdelicConeEuler` from the cone integral of a product test function** ($F$ totally real): if
$I_C(\Phi) = \kappa\cdot\mathrm{boxMass}(S,K)\prod_w\int\varphi_w\,d\sigma_{C,w}$ with $\kappa<\infty$, the $\varphi_w$
Gaussian-bounded and the $K_v$ ($v\in S$) bounded, then `AdelicConeEuler` holds ($\kappa$ is absorbed into
$\varphi_{w_0}$). -/
theorem adelicConeEuler_of_prod (hQ : (coneFormO c₀ Q₀').Nondegenerate) {Φ : AdeleSpace F (Fin (k + 1 + 1)) → ℝ≥0∞}
    (κ : ℝ≥0∞) (hκ : κ ≠ ⊤) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) (hK : ∀ v ∈ S, Bornology.IsBounded (K v))
    (φ : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w) → ℝ≥0∞) (hφm : ∀ w, Measurable (φ w))
    (a C : {w : InfinitePlace F // w.IsReal} → ℝ) (ha : ∀ w, 0 < a w) (hC : ∀ w, 0 ≤ C w)
    (hφ : ∀ w z, φ w z ≤ ENNReal.ofReal (C w * Real.exp (-(a w * ‖(z : Fin (k + 1 + 1) → ℝ)‖ ^ 2))))
    (heq : ∫⁻ x, Φ x.1 ∂coneMeasure hc hQ' hk =
      κ * ConeAdelic.boxMass QC hQ S K * ∏ w, ∫⁻ z, φ w z ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) :
    AdelicConeEuler hc Q₀' hQ (coneData hc hQ' hk).σ Φ := by
  set w₀ := realPlace₀ F
  refine ⟨⟨fun w z => (if w = w₀ then κ else 1) * φ w z, fun _ _ => 0, a,
    fun w => (if w = w₀ then κ.toReal else 1) * C w, fun _ => 1, fun _ => 0, S, K, ha, fun w => ?_, fun w z => ?_,
    fun _ => one_pos, fun _ => le_refl 0, fun _ _ => bot_le, hK, ?_⟩⟩
  · exact mul_nonneg (by split_ifs; exacts [ENNReal.toReal_nonneg, zero_le_one]) (hC w)
  · rw [mul_assoc, ENNReal.ofReal_mul (by split_ifs; exacts [ENNReal.toReal_nonneg, zero_le_one])]
    refine mul_le_mul' (le_of_eq ?_) (hφ w z)
    split_ifs
    · exact (ENNReal.ofReal_toReal hκ).symm
    · exact ENNReal.ofReal_one.symm
  · show ∫⁻ x, Φ x.1 ∂coneMeasure hc hQ' hk = _
    rw [heq, ConeAdelic.coneIntegral, ConeAdelic.coneBoxMeasure_univ, ConeAdelic.coneIntegralArch]
    have hprod : ∏ w : {w : InfinitePlace F // w.IsReal},
        ∫⁻ z, (if w = w₀ then κ else 1) * φ w z ∂ConeReal.sigCone (Q' := QRe Q₀' w) (ConeAdelic.cRe_ne_zero hc w) =
        κ * ∏ w, ∫⁻ z, φ w z ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w) := by
      simp only [lintegral_const_mul _ (hφm _), Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
        if_true]
    rw [hprod, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty, mul_one]
    ring

open Classical in
/-- **`AdelicConeEuler` for the Gaussian test function** ($F$ totally real, $k\ge3$). -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral of the Gaussian as a product of local factors) [unverified page]"]
theorem adelicConeEuler_gaussTest (hQ : (coneFormO c₀ Q₀').Nondegenerate) :
    AdelicConeEuler hc Q₀' hQ (coneData hc hQ' hk).σ (gaussTest F (k + 1 + 1)) :=
  adelicConeEuler_of_prod hc hQ' hk hQ (coneConst hc hQ' (badCone hc hQ' hk))
    (coneConst_ne_top hc hQ' hk _ subset_rfl) (badCone hc hQ' hk) (fun v => LocalZeta.latL v (k + 1 + 1))
    (fun v _ => isBounded_latL v _) (fun w z => gaussRe z.1)
    (fun w => measurable_gaussRe.comp measurable_subtype_coe) (fun _ => Real.pi) (fun _ => 1)
    (fun _ => Real.pi_pos) (fun _ => zero_le_one) (fun w z => by rw [one_mul]; exact gaussRe_le _)
    (lintegral_gaussTest_cone hc hQ' hk _ subset_rfl hQ)

end Euler

end QuadFormsKB.Tamagawa.Measure.Weil

end
