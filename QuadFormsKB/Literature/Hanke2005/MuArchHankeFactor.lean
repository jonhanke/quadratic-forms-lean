import QuadFormsKB.Literature.Hanke2005.MassFormula
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchGlobal
import QuadFormsKB.Citation

open MeasureTheory Measure NumberField IsDedekindDomain NumberField.InfinitePlace
open scoped ENNReal Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.LerayArch

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

/-- **Factorization of Hanke's archimedean measure.** With $N = n(n-1)/2$ (natural-number division),
$$\tau_a = \prod_{w\ \mathrm{real}}2^{N}\,\mu^{\mathrm{Leray}}_{Q^{\sigma_w}}\ \times\
\prod_{w\ \mathrm{complex}}2^{3N}\,\mu^{\mathrm{Leray}}_{Q^{\tau_w}},$$
i.e. the product over the infinite places of the Leray measures of the archimedean forms, with the constant
$2^{N}$ (from Gram coordinates) at each real place and $2^{3N}$ (Gram coordinates and Weil's $|dz\wedge d\bar z|
= 2\,dx\,dy$) at each complex place. -/
@[kb "hanke2005crelle" "§2, p. 5 (τ_a = ∏ ω̃_G)"]
theorem muArchHanke_eq :
    muArchHanke Q₀ hQ =
      (Measure.pi fun w : {w : InfinitePlace F // w.IsReal} =>
          ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2)) •
            lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)).prod
        (Measure.pi fun w : {w : InfinitePlace F // w.IsComplex} =>
          ENNReal.ofReal ((2 : ℝ) ^ (3 * (n * (n - 1) / 2))) •
            lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w)) := by
  have hd : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have hc : 0 < cF F n := by unfold cF; positivity
  have hconst : archHankeConst F n * (cF F n * cxWeil F n) =
      (∏ _w : {w : InfinitePlace F // w.IsReal}, (2 : ℝ) ^ (n * (n - 1) / 2)) *
        ∏ _w : {w : InfinitePlace F // w.IsComplex}, (2 : ℝ) ^ (3 * (n * (n - 1) / 2)) := by
    rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ]
    unfold archHankeConst cxWeil
    rw [← card_add_two_mul_card_eq_rank F]
    have e1 : Fintype.card {w : InfinitePlace F // w.IsReal} = nrRealPlaces F := rfl
    have e2 : Fintype.card {w : InfinitePlace F // w.IsComplex} = nrComplexPlaces F := rfl
    rw [e1, e2]
    field_simp
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  unfold muArchHanke muArchTamSO muArchNF muArchLeray
  rw [smul_smul, ← ENNReal.ofReal_mul (archHankeConst_pos (F := F) (n := n)).le, hconst]
  rw [sim_pi_smul (fun w : {w : InfinitePlace F // w.IsReal} =>
      lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w))
      (fun _ => (2 : ℝ) ^ (n * (n - 1) / 2)) (fun _ => by positivity),
    sim_pi_smul (fun w : {w : InfinitePlace F // w.IsComplex} =>
      lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w))
      (fun _ => (2 : ℝ) ^ (3 * (n * (n - 1) / 2))) (fun _ => by positivity),
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity)]

theorem hess_det_map {S : Type*} [CommRing S] (σ : F →+* S) :
    ((Q₀.map (algebraMap (𝓞 F) F)).map σ).hessian.det = σ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) := by
  rw [hessian_map_NF σ (Q₀.map (algebraMap (𝓞 F) F)), ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- **The volume factor at a real place:** $|x|_w$ for $x = \det(H_{Q_0})/2^n$ equals $|\det(\tfrac12H(Q^{\sigma_w}))|$,
where $|x|_w = |x|^{m_w}$ with $m_w = 1$. -/
theorem volFactor_real (w : {w : InfinitePlace F // w.IsReal}) :
    (w.1 ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n)) ^ w.1.mult = |gramDetR (QRe Q₀ w)| := by
  rw [mult_isReal, pow_one, gramDetR, hess_det_map, ← norm_embedding_of_isReal w.2, Real.norm_eq_abs,
    map_div₀, map_pow, map_ofNat]

/-- **The volume factor at a complex place:** $|x|_w = |x|^2$ for $x = \det(H_{Q_0})/2^n$ equals
$\|\det(\tfrac12H(Q^{\tau_w}))\|^2$ ($m_w = 2$). -/
theorem volFactor_complex (w : {w : InfinitePlace F // w.IsComplex}) :
    (w.1 ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det / 2 ^ n)) ^ w.1.mult = ‖gramDetC (QCx Q₀ w)‖ ^ 2 := by
  rw [mult_isComplex, gramDetC, gramC, Matrix.det_smul, Fintype.card_fin]
  have : (QCx Q₀ w).hessian.det = w.1.embedding ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) :=
    hess_det_map Q₀ _
  rw [this, ← norm_embedding_eq w.1, map_div₀, map_pow, map_ofNat]
  congr 2
  rw [one_div, inv_pow]; ring

/-- $r_w$ at a real place is the Witt index of the real form $Q^{\sigma_w}$. -/
theorem rAt_eq_wittIndex (w : {w : InfinitePlace F // w.IsReal}) :
    rAt Q₀ w.1 = QuadraticForm.wittIndex (QuadForm.toQuadraticForm (QRe Q₀ w)) := by
  classical
  unfold rAt
  rw [dif_pos w.2]
  rfl

end QuadFormsKB.Hanke2005
