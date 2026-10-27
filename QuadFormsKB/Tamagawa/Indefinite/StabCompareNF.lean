/-
# The stabilizer measures of the sphere fibration from frame data at infinity

**Layer:** number fields, archimedean places. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = k + 1$
variables (any signature), $m\in F$, $m\ne0$, $\xi\in F^N$, $D$ frame data at infinity for $\xi$ (`SplitDataInf`:
$g = [\xi\mid C]$, $Q''$, $\iota$; StabCompare.lean).

**Proves** (unconditional, standard axioms only)
* `archFibrationNF_μH_unfold`: the stabilizer measure of the sphere fibration at $y$ is the product over the places of `realStabMeasure` and of
  $2^{k(k-1)/2}\cdot$`complexStabMeasure` (definitional);
* **`archFibrationNF_μH_eq`**: for every $a\in G_\infty$,
  $$\mu_{H_{a\xi_\infty}}\ (\text{of `archFibrationNF`}) = (h\mapsto a\,\iota(h)\,a^{-1})_*\bigl(\lambda\,\mu^{\mathrm{Tam}}_{Q''}\bigr),
  \qquad\lambda = \prod_{w\ \mathrm{real}}|\sigma_w\det g|^{N}\prod_{w\ \mathrm{complex}}\|\sigma_w\det g\|^{2N}/c_F(k)$$
  ($\lambda$ = `SplitDataInf.lam`, $\mu^{\mathrm{Tam}}_{Q''}$ = `muArchTamSO`, with $c_F(k)$ and Weil's factor $2^{k(k-1)/2}$ at each
  complex place). Place by place this is `realStabMeasure_eq_splitFrame` / `complexStabMeasure_eq_splitFrame` for the
  split frame $P_w = a_wg_w$ ($|\det P_w| = |\sigma_w\det g|$, `det_frameR`, `det_frameC`); the constants $c_F(k)$ cancel and
  `cxWeil` is the product of the complex factors $2^{k(k-1)/2}$. `archFibrationNF_μH_eq_at`: the same at $y$ given with
  $a\,\xi_\infty = y$.
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompare

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

theorem archFibrationNF_μH_unfold (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) {m : F} (hm : m ≠ 0)
    (hk : 1 ≤ k) (y : VInf F (k + 1)) :
    (archFibrationNF Q₀ hQ hm hk).μH y =
      (((Measure.pi fun w => realStabMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (mR_ne_zero hm w) (y.1 w)).map
          (stabPiME y.1).symm).prod
        ((Measure.pi fun w => ((2 : ℝ≥0∞) ^ (k * (k - 1) / 2)) •
          complexStabMeasure (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (mC_ne_zero hm w) (y.2 w)).map
          (stabPiME y.2).symm)).map (stabProdME y).symm := rfl

namespace SplitDataInf

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {m : F} {ξ : Fin (k + 1) → F} (D : SplitDataInf Q₀ m ξ)

theorem det_frameR (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsReal}) :
    |((D.frameR a w).P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).det| =
      |σR w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det| := by
  show |((ArchSO.incl _ (a.1 w) * D.gR w : GL (Fin (k + 1)) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).det| = _
  rw [Units.val_mul, Matrix.det_mul, ((mem_soReal_iff _ _).mp (ArchSOInst.incl_mem _ (a.1 w))).2, one_mul]
  simp [gR, Matrix.GeneralLinearGroup.map, RingHom.map_det]

theorem det_frameC (a : GInfSO Q₀) (w : {w : InfinitePlace F // w.IsComplex}) :
    ‖((D.frameC a w).P : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ =
      ‖σC w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det‖ := by
  show ‖((ArchSOC.incl _ (a.2 w) * D.gC w : GL (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ = _
  rw [Units.val_mul, Matrix.det_mul, ((mem_soC_iff _ _).mp (ArchSOC.incl_mem _ (a.2 w))).2, one_mul]
  simp [gC, Matrix.GeneralLinearGroup.map, RingHom.map_det]

end SplitDataInf

/-- **The stabilizer measure of the sphere fibration at $a\,\xi_\infty$ from frame data** (every number field): the
measure $\mu_{H_y}$ of
`archFibrationNF` at $y = a\,\xi_\infty$ is the image of $\lambda\,\mu^{\mathrm{Tam}}_{Q''}$ under
$h\mapsto a\,\iota(h)\,a^{-1}$, $\lambda$ = `SplitDataInf.lam`. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, Theorem 2.4.3, p. 25 (the measure on H is the quotient measure; independent of the coordinates) [unverified page]"]
theorem archFibrationNF_μH_eq (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) {m : F} (hm : m ≠ 0)
    (hk : 1 ≤ k) {ξ : Fin (k + 1) → F} (D : SplitDataInf Q₀ m ξ) (a : GInfSO Q₀) :
    (archFibrationNF Q₀ hQ hm hk).μH (a • ξInf ξ) =
      (D.lam • muArchTamSO D.Q'' D.hQ'').map (D.conjHom a) := by
  rw [archFibrationNF_μH_unfold]
  set y := a • ξInf ξ with hy
  -- the local measures
  set φ : ∀ w : {w : InfinitePlace F // w.IsReal}, ArchSO (QRe D.Q'' w) →* stabilizer (ArchSO (QRe Q₀ w)) (y.1 w) :=
    fun w => (D.frameR a w).stabHom with hφ
  set ψ : ∀ w : {w : InfinitePlace F // w.IsComplex}, ArchSOC (QCx D.Q'' w) →* stabilizer (ArchSOC (QCx Q₀ w)) (y.2 w) :=
    fun w => (D.frameC a w).stabHom (mC_ne_zero hm w) with hψ
  set L : ∀ w : {w : InfinitePlace F // w.IsReal}, Measure (ArchSO (QRe D.Q'' w)) :=
    fun w => lerayMeasure (QRe D.Q'' w) (gramDetR_QRe_ne_zero D.Q'' D.hQ'' w) with hL
  set LC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Measure (ArchSOC (QCx D.Q'' w)) :=
    fun w => lerayMeasureC (QCx D.Q'' w) (gramDetC_QCx_ne_zero D.Q'' D.hQ'' w) with hLC
  set cR : {w : InfinitePlace F // w.IsReal} → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (|σR w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det| ^ (k + 1)) with hcR
  set cC : {w : InfinitePlace F // w.IsComplex} → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (‖σC w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det‖ ^ (2 * (k + 1))) with hcC
  have hR : ∀ w, realStabMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (mR_ne_zero hm w) (y.1 w) =
      cR w • (L w).map (φ w) := fun w => by
    rw [realStabMeasure_eq_splitFrame hk _ _ (D.frameR a w), D.det_frameR]; rfl
  have hC : ∀ w, complexStabMeasure (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (mC_ne_zero hm w) (y.2 w) =
      cC w • (LC w).map (ψ w) := fun w => by
    rw [complexStabMeasure_eq_splitFrame hk _ _ (D.frameC a w), D.det_frameC]; rfl
  have hcR0 : ∀ w, cR w ≠ 0 := fun w => (ENNReal.ofReal_pos.2 (pow_pos (abs_pos.2 ((map_ne_zero _).2
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit D.g)).ne_zero)) _)).ne'
  have hcC0 : ∀ w, cC w ≠ 0 := fun w => (ENNReal.ofReal_pos.2 (pow_pos (norm_pos_iff.2 ((map_ne_zero _).2
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit D.g)).ne_zero)) _)).ne'
  -- σ-finiteness of the local images
  haveI hsR : ∀ w, SigmaFinite ((L w).map (φ w)) := fun w => by
    have h := (realArchFibration (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (mR_ne_zero hm w) hk).sigmaFinite (y.1 w)
    change SigmaFinite (realStabMeasure (QRe Q₀ w) _ (mR_ne_zero hm w) (y.1 w)) at h
    rw [hR] at h
    have e : (L w).map (φ w) = (cR w)⁻¹ • (cR w • (L w).map (φ w)) := by
      rw [smul_smul, ENNReal.inv_mul_cancel (hcR0 w) ENNReal.ofReal_ne_top, one_smul]
    rw [e]
    exact sigmaFinite_smul _ (ENNReal.inv_ne_top.2 (hcR0 w))
  haveI hsC : ∀ w, SigmaFinite ((LC w).map (ψ w)) := fun w => by
    have h := (complexArchFibration (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (mC_ne_zero hm w) hk).sigmaFinite
      (y.2 w)
    change SigmaFinite (complexStabMeasure (QCx Q₀ w) _ (mC_ne_zero hm w) (y.2 w)) at h
    rw [hC] at h
    have e : (LC w).map (ψ w) = (cC w)⁻¹ • (cC w • (LC w).map (ψ w)) := by
      rw [smul_smul, ENNReal.inv_mul_cancel (hcC0 w) ENNReal.ofReal_ne_top, one_smul]
    rw [e]
    exact sigmaFinite_smul _ (ENNReal.inv_ne_top.2 (hcC0 w))
  have hmφ : ∀ w, Measurable (φ w) := fun w => (D.frameR a w).measurable_stabHom
  have hmψ : ∀ w, Measurable (ψ w) := fun w => (D.frameC a w).measurable_stabHom (mC_ne_zero hm w)
  -- the left side
  have eL := congrArg (fun μ => Measure.pi μ) (funext hR)
  have eC := congrArg (fun μ => Measure.pi μ) (funext fun w => (congrArg (fun ν => ((2 : ℝ≥0∞) ^ (k * (k - 1) / 2)) • ν) (hC w)).trans (smul_smul _ _ _))
  erw [eL, eC]
  rw [pi_smul _ _ (fun w => ENNReal.ofReal_ne_top),
    pi_smul _ _ (fun w => ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top),
    Measure.map_smul, Measure.map_smul, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul]
  -- the right side
  have hconj : (D.conjHom a : GInfSO D.Q'' → stabilizer (GInfSO Q₀) y) =
      (stabProdME y).symm ∘ Prod.map ((stabPiME y.1).symm ∘ fun h w => φ w (h w))
        ((stabPiME y.2).symm ∘ fun h w => ψ w (h w)) := funext fun h => D.conjHom_eq hm a h
  have hmu : muArchTamSO D.Q'' D.hQ'' =
      ENNReal.ofReal (cF F k * cxWeil F k) • (Measure.pi L).prod (Measure.pi LC) := rfl
  have hm1 : Measurable fun (h : ∀ w, ArchSO (QRe D.Q'' w)) w => φ w (h w) :=
    measurable_pi_iff.2 fun w => (hmφ w).comp (measurable_pi_apply w)
  have hm2 : Measurable fun (h : ∀ w, ArchSOC (QCx D.Q'' w)) w => ψ w (h w) :=
    measurable_pi_iff.2 fun w => (hmψ w).comp (measurable_pi_apply w)
  rw [hmu, smul_smul, Measure.map_smul, hconj,
    ← Measure.map_map (stabProdME y).symm.measurable
      (((stabPiME y.1).symm.measurable.comp hm1).prodMap ((stabPiME y.2).symm.measurable.comp hm2)),
    ← Measure.map_prod_map _ _ ((stabPiME y.1).symm.measurable.comp hm1)
      ((stabPiME y.2).symm.measurable.comp hm2),
    ← Measure.map_map (stabPiME y.1).symm.measurable hm1, ← Measure.map_map (stabPiME y.2).symm.measurable hm2,
    pi_map_pi (fun w => (hmφ w).aemeasurable), pi_map_pi (fun w => (hmψ w).aemeasurable)]
  congr 1
  · -- the constants
    have hc := cF_pos' (F := F) k
    have hR0 : 0 ≤ ∏ w : {w : InfinitePlace F // w.IsReal},
        |σR w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det| ^ (k + 1) := by positivity
    have hC0 : 0 ≤ ∏ w : {w : InfinitePlace F // w.IsComplex},
        ‖σC w (D.g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det‖ ^ (2 * (k + 1)) := by positivity
    rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),
      ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity), ← ofReal_cxWeil_eq_prod F k,
      SplitDataInf.lam, ← ENNReal.ofReal_mul cxWeil_pos.le, ← ENNReal.ofReal_mul hR0,
      ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hR0 hC0) hc.le)]
    congr 1
    field_simp
  all_goals first
    | exact (D.measurable_conjHom a).aemeasurable
    | exact (MeasurableEquiv.measurable _).aemeasurable

/-- `archFibrationNF_μH_eq` at a point $y$ given with $a\,\xi_\infty = y$. -/
theorem archFibrationNF_μH_eq_at (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) {m : F} (hm : m ≠ 0)
    (hk : 1 ≤ k) {ξ : Fin (k + 1) → F} (D : SplitDataInf Q₀ m ξ) (a : GInfSO Q₀) {y : VInf F (k + 1)}
    (hy : a • ξInf ξ = y) :
    (archFibrationNF Q₀ hQ hm hk).μH y = (D.lam • muArchTamSO D.Q'' D.hQ'').map (D.conjHomAt a hy) := by
  subst hy; exact archFibrationNF_μH_eq Q₀ hQ hm hk D a

end QuadFormsKB.Tamagawa.Indefinite
