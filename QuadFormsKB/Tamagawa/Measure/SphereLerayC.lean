import QuadFormsKB.Tamagawa.Measure.LerayComplex

/-!
# Leray measures on the complex spheres $\{Q = c\}$

For a complex quadratic form $Q$ in $n$ variables and $c \in \mathbb C^\times$, let
$S_c = \{x \in \mathbb C^n : Q(x) = c\}$ (`SphC Q c`). The **polar map** $(\beta, x) \mapsto \beta x$,
$\mathbb C^\times \times S_c \to \mathbb C^n$ (`polC`), is two-to-one onto $\{Q \ne 0\}$ (its fibres are
$\{(\beta, x), (-\beta, -x)\}$) and locally injective. We pull back Lebesgue measure by **counting fibres**
(`Leray.fibreCount`), obtaining $M_c$ on $\mathbb C^\times \times S_c$, and prove:

* `fibreCount_polC`: **polar coordinates**, $M_c = |\beta|^{2n-2}\,d^2\beta \otimes \nu_c$. The proof uses the
  naturality of fibre counting under $\beta \mapsto a\beta$ ($a \in \mathbb C^\times$), so that for every bounded
  $A \subseteq S_c$ the measure $R \mapsto |\beta|^{-2n}M_c(R \times A)$ is a Haar measure on the group
  $\mathbb C^\times$; Haar uniqueness on $\mathbb C^\times$ identifies it with a multiple of $d^2\beta/|\beta|^2$.
  The **cone measure** $\nu_c$ (`nuC`) is normalized on the fixed sector $R_0 = \{\operatorname{Re}\beta > 0,
  |\beta| < 1\}$: $\nu_c(A) = \mathrm{Leb}(R_0\cdot A)/\int_{R_0}|\beta|^{2n-2}d^2\beta$ (`nuC_apply`).
* `sigC`: **the Leray measure** $\sigma_c = \nu_c/|2c|_{\mathbb C}$ with $|z|_{\mathbb C} = |z|^2$.
* `lintegral_polC_half`: polar coordinates on the half plane $\operatorname{Re}\beta > 0$, where $\mathrm{pol}$ is
  injective; `lintegral_fibration`: **the Leray fibration** $dy = \sigma_t \otimes dt$, written with $t = c\beta^2$
  ($dt = |2c\beta|^2 d^2\beta$), $\int_{\{\beta x\}} f\,dy = \int_{\operatorname{Re}\beta > 0} |2c\beta|^2
  \int_{S_{\beta^2c}} f\,d\sigma_{\beta^2 c}\,d^2\beta$.
* `map_sphMapC_sigC`: $\sigma_c$ is invariant under every $g$ with $g^{\mathsf T}Ag = A$, $|\det g| = 1$ (in particular
  under $SO(Q)(\mathbb C)$).
* `sigC_scale`: **homogeneity**, $\sigma_{a^2c} = |a|^{2(n-2)}\,(x \mapsto ax)_*\sigma_c$ for $a \in \mathbb C^\times$.
-/

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Matrix Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.SphereLerayC

open QuadFormsKB Matrix

variable {n : ℕ}

/-! ### $\mathbb C^\times$ as a measure space; Haar measures on $\mathbb C^\times$ -/

theorem isEmbedding_val : IsEmbedding (Units.val : ℂˣ → ℂ) := Units.isEmbedding_val₀

instance : BorelSpace ℂˣ := ⟨by
  rw [isEmbedding_val.eq_induced, borel_comap]
  rfl⟩

theorem range_val : range (Units.val : ℂˣ → ℂ) = {z | z ≠ 0} := by
  ext z
  simp only [mem_range, mem_ofPred_eq]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hz => ⟨Units.mk0 z hz, rfl⟩⟩

instance : PolishSpace ℂˣ := by
  have : PolishSpace {g : ℂ // g ≠ 0} := (isOpen_ne : IsOpen {g : ℂ | g ≠ 0}).polishSpace
  exact (unitsHomeomorphNeZero (G₀ := ℂ)).isClosedEmbedding.polishSpace

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : ℂˣ → ℂ) :=
  isEmbedding_val.measurableEmbedding (by rw [range_val]; exact (isOpen_ne).measurableSet)

instance : MeasurableMul₂ ℂˣ := ContinuousMul.measurableMul₂

/-- Lebesgue measure on $\mathbb C$, restricted to $\mathbb C^\times$. -/
def volU : Measure ℂˣ := Measure.comap Units.val volume

theorem volU_apply {R : Set ℂˣ} (hR : MeasurableSet R) : volU R = volume (Units.val '' R) :=
  measurableEmbedding_val.comap_apply volume R

/-- The weight $|\beta|^k$ on $\mathbb C^\times$ ($k \in \mathbb Z$). -/
def wt (k : ℤ) (β : ℂˣ) : ℝ≥0∞ := ((‖(β : ℂ)‖₊ ^ k : ℝ≥0) : ℝ≥0∞)

theorem nnnorm_ne_zero (β : ℂˣ) : ‖(β : ℂ)‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr β.ne_zero

theorem continuous_wt_nn (k : ℤ) : Continuous fun β : ℂˣ => ‖(β : ℂ)‖₊ ^ k :=
  (continuous_nnnorm.comp Units.continuous_val).zpow₀ k fun β => Or.inl (nnnorm_ne_zero β)

theorem measurable_wt (k : ℤ) : Measurable (wt k) :=
  (continuous_wt_nn k).measurable.coe_nnreal_ennreal

theorem wt_mul_wt (k l : ℤ) (β : ℂˣ) : wt k β * wt l β = wt (k + l) β := by
  rw [wt, wt, wt, ← ENNReal.coe_mul, zpow_add₀ (nnnorm_ne_zero β)]

theorem wt_zero (β : ℂˣ) : wt 0 β = 1 := by simp [wt]

theorem wt_mul (k : ℤ) (a β : ℂˣ) : wt k (a * β) = wt k a * wt k β := by
  rw [wt, wt, wt, ← ENNReal.coe_mul, Units.val_mul, nnnorm_mul, mul_zpow]

theorem wt_ne_zero (k : ℤ) (β : ℂˣ) : wt k β ≠ 0 := by
  rw [wt, ENNReal.coe_ne_zero]; exact zpow_ne_zero _ (nnnorm_ne_zero β)

theorem wt_ne_top (k : ℤ) (β : ℂˣ) : wt k β ≠ ⊤ := ENNReal.coe_ne_top

/-- **Scaling a weighted measure**: if $\rho$ scales by $|a|^{-k}$ under $\beta \mapsto a\beta$, then
$|\beta|^{-k}\rho$ is left invariant on $\mathbb C^\times$. -/
theorem isMulLeftInvariant_withDensity (ρ : Measure ℂˣ) (k : ℤ)
    (h : ∀ a : ℂˣ, ρ.map (a * ·) = wt (-k) a • ρ) : (ρ.withDensity (wt (-k))).IsMulLeftInvariant := by
  refine ⟨fun a => ?_⟩
  ext R hR
  have hm : Measurable (a * · : ℂˣ → ℂˣ) := measurable_const_mul a
  rw [map_apply hm hR, withDensity_apply _ (hm hR), withDensity_apply _ hR]
  have e : ∫⁻ β in (a * ·) ⁻¹' R, wt (-k) β ∂ρ =
      ∫⁻ β in (a * ·) ⁻¹' R, (fun γ => wt k a * wt (-k) γ) (a * β) ∂ρ := by
    refine lintegral_congr fun β => ?_
    simp only
    rw [wt_mul, ← mul_assoc, wt_mul_wt, add_neg_cancel, wt_zero, one_mul]
  rw [e, ← setLIntegral_map (f := fun γ => wt k a * wt (-k) γ) hR (measurable_const.mul (measurable_wt _)) hm, h,
    setLIntegral_smul_measure, lintegral_const_mul _ (measurable_wt _), smul_eq_mul, ← mul_assoc, wt_mul_wt,
    neg_add_cancel, wt_zero, one_mul]

theorem map_mul_volume (a : ℂˣ) : (volume : Measure ℂ).map ((a : ℂ) * ·) = wt (-2) a • volume := by
  have hdet : LinearMap.det ((a : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) = a := by
    rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]
  have h := LerayComplex.map_clm_addHaar (volume : Measure ℂ) ((a : ℂ) • LinearMap.id) (by rw [hdet]; exact a.ne_zero)
  rw [hdet] at h
  rw [show ((a : ℂ) * ·) = ⇑((a : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) from rfl, h, wt]
  congr 2

theorem image_val_preimage_mul (a : ℂˣ) (R : Set ℂˣ) :
    Units.val '' ((a * ·) ⁻¹' R) = ((a : ℂ) * ·) ⁻¹' (Units.val '' R) := by
  ext z
  constructor
  · rintro ⟨β, hβ, rfl⟩; exact ⟨a * β, hβ, by simp⟩
  · rintro ⟨γ, hγ, hz⟩
    refine ⟨a⁻¹ * γ, by simpa using hγ, ?_⟩
    simp only [Units.val_mul, hz]
    rw [← mul_assoc]
    simp

theorem map_mul_volU (a : ℂˣ) : volU.map (a * ·) = wt (-2) a • volU := by
  ext R hR
  have hm : Measurable (a * · : ℂˣ → ℂˣ) := measurable_const_mul a
  have hR' := measurableEmbedding_val.measurableSet_image' hR
  rw [map_apply hm hR, Measure.smul_apply, volU_apply (hm hR), volU_apply hR, smul_eq_mul,
    image_val_preimage_mul, ← map_apply (measurable_const_mul _) hR', map_mul_volume, Measure.smul_apply,
    smul_eq_mul]

theorem volU_compact_lt_top {K : Set ℂˣ} (hK : IsCompact K) : volU K < ⊤ := by
  rw [volU_apply hK.measurableSet]
  exact (hK.image Units.continuous_val).measure_lt_top

/-- A weighted measure with continuous weight on a measure finite on compacts is finite on compacts. -/
theorem withDensity_isFiniteMeasureOnCompacts (ρ : Measure ℂˣ) [IsFiniteMeasureOnCompacts ρ] (k : ℤ) :
    IsFiniteMeasureOnCompacts (ρ.withDensity (wt k)) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (NNReal.continuous_coe.comp (continuous_wt_nn k)).continuousOn
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ β in K, wt k β ∂ρ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂ρ := by
        refine setLIntegral_mono measurable_const fun β hβ => ?_
        rw [wt, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (by simpa using hC β hβ)
    _ = ENNReal.ofReal C * ρ K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

instance : IsFiniteMeasureOnCompacts volU := ⟨fun _ hK => volU_compact_lt_top hK⟩

/-- **The reference Haar measure** $d^2\beta/|\beta|^2$ on $\mathbb C^\times$. -/
def haarU : Measure ℂˣ := volU.withDensity (wt (-2))

instance : haarU.IsMulLeftInvariant := isMulLeftInvariant_withDensity volU 2 map_mul_volU

instance : IsFiniteMeasureOnCompacts haarU := withDensity_isFiniteMeasureOnCompacts _ _

theorem withDensity_wt_pos {U : Set ℂˣ} (hU : IsOpen U) (hne : U.Nonempty) (k : ℤ) :
    0 < volU.withDensity (wt k) U := by
  rw [pos_iff_ne_zero, Ne, withDensity_apply_eq_zero (measurable_wt k)]
  have : {x | wt k x ≠ 0} ∩ U = U := by
    ext x; simp [wt_ne_zero]
  rw [this, volU_apply hU.measurableSet]
  exact (Units.isOpenMap_val U hU).measure_ne_zero volume (hne.image _)

instance : IsOpenPosMeasure haarU := ⟨fun U hU hne => (withDensity_wt_pos hU hne (-2)).ne'⟩

instance : haarU.IsHaarMeasure := ⟨⟩


/-! ### The sphere and the polar map -/

theorem eval_eq_coeff (Q : QuadForm ℂ n) (x : Fin n → ℂ) : Q.eval x = x ⬝ᵥ (Q.coeff *ᵥ x) := by
  rw [QuadForm.eval, QuadForm.evalIn_eq_dotProduct]
  rfl

theorem eval_eq_gramC (Q : QuadForm ℂ n) (x : Fin n → ℂ) : Q.eval x = x ⬝ᵥ (LerayComplex.gramC Q *ᵥ x) := by
  have ht : x ⬝ᵥ (Q.coeffᵀ *ᵥ x) = x ⬝ᵥ (Q.coeff *ᵥ x) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  rw [LerayComplex.gramC, QuadForm.hessian, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add, ht,
    ← eval_eq_coeff, smul_eq_mul]
  ring

theorem continuous_evalC (Q : QuadForm ℂ n) : Continuous fun x : Fin n → ℂ => Q.eval x := by
  simp_rw [eval_eq_coeff]
  exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem eval_smulC (Q : QuadForm ℂ n) (a : ℂ) (x : Fin n → ℂ) : Q.eval (a • x) = a ^ 2 * Q.eval x := by
  rw [eval_eq_coeff, eval_eq_coeff, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- **The complex sphere** $S_c = \{x \in \mathbb C^n : Q(x) = c\}$. -/
def sphC (Q : QuadForm ℂ n) (c : ℂ) : Set (Fin n → ℂ) := {x | Q.eval x = c}

/-- $S_c$ as a type (closed subspace of $\mathbb C^n$, Borel structure). -/
abbrev SphC (Q : QuadForm ℂ n) (c : ℂ) : Type := ↥(sphC Q c)

theorem isClosed_sphC (Q : QuadForm ℂ n) (c : ℂ) : IsClosed (sphC Q c) :=
  isClosed_eq (continuous_evalC Q) continuous_const

instance (Q : QuadForm ℂ n) (c : ℂ) : PolishSpace (SphC Q c) := (isClosed_sphC Q c).polishSpace

/-- **The polar map** $(\beta, x) \mapsto \beta x$, $\mathbb C^\times \times S_c \to \mathbb C^n$. -/
def polC (Q : QuadForm ℂ n) (c : ℂ) (p : ℂˣ × SphC Q c) : Fin n → ℂ := (p.1 : ℂ) • (p.2 : Fin n → ℂ)

theorem continuous_polC (Q : QuadForm ℂ n) (c : ℂ) : Continuous (polC Q c) :=
  (Units.continuous_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)

theorem eval_polC (Q : QuadForm ℂ n) (c : ℂ) (p : ℂˣ × SphC Q c) :
    Q.eval (polC Q c p) = (p.1 : ℂ) ^ 2 * c := by
  rw [polC, eval_smulC, p.2.2]

theorem polC_eq_imp {Q : QuadForm ℂ n} {c : ℂ} (hc : c ≠ 0) {p q : ℂˣ × SphC Q c} (h : polC Q c p = polC Q c q) :
    (q.1 : ℂ) = p.1 ∨ (q.1 : ℂ) = -p.1 := by
  have h1 := congrArg Q.eval h
  rw [eval_polC, eval_polC] at h1
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (mul_right_cancel₀ hc h1).symm

theorem polC_eq_of_fst_eq {Q : QuadForm ℂ n} {c : ℂ} {p q : ℂˣ × SphC Q c} (h : polC Q c p = polC Q c q)
    (h1 : (q.1 : ℂ) = p.1) : p = q := by
  have e1 : p.1 = q.1 := Units.ext h1.symm
  have e2 : (p.2 : Fin n → ℂ) = q.2 := by
    have h' : (p.1 : ℂ) • (p.2 : Fin n → ℂ) = (p.1 : ℂ) • (q.2 : Fin n → ℂ) := by
      have h2 := h
      simp only [polC] at h2
      rw [h2, h1]
    exact smul_right_injective _ p.1.ne_zero h'
  exact Prod.ext e1 (Subtype.ext e2)

/-- The polar map is injective on $\{\operatorname{Re}(\beta/\beta_0) > 0\} \times S_c$. -/
theorem injOn_polC {Q : QuadForm ℂ n} {c : ℂ} (hc : c ≠ 0) (β₀ : ℂˣ) :
    InjOn (polC Q c) ({β : ℂˣ | 0 < ((β : ℂ) / β₀).re} ×ˢ univ) := by
  rintro p ⟨hp, -⟩ q ⟨hq, -⟩ h
  rcases polC_eq_imp hc h with h1 | h1
  · exact polC_eq_of_fst_eq h h1
  · exfalso
    simp only [mem_setOf_eq] at hp hq
    rw [h1, neg_div, Complex.neg_re] at hq
    linarith

theorem isOpen_halfPlane (β₀ : ℂˣ) : IsOpen {β : ℂˣ | 0 < ((β : ℂ) / β₀).re} :=
  isOpen_lt continuous_const (Complex.continuous_re.comp (Units.continuous_val.div_const _))

theorem isLocInj_polC {Q : QuadForm ℂ n} {c : ℂ} (hc : c ≠ 0) : Leray.IsLocInj (polC Q c) := by
  rintro ⟨β₀, x₀⟩
  refine ⟨{β : ℂˣ | 0 < ((β : ℂ) / β₀).re} ×ˢ univ, (isOpen_halfPlane β₀).prod isOpen_univ, ⟨?_, mem_univ _⟩,
    injOn_polC hc β₀⟩
  show 0 < ((β₀ : ℂ) / β₀).re
  rw [div_self β₀.ne_zero, Complex.one_re]; exact one_pos

/-- **The half plane** $\{\operatorname{Re}\beta > 0\} \subset \mathbb C^\times$, on which the polar map is injective. -/
def halfU : Set ℂˣ := {β | 0 < (β : ℂ).re}

theorem halfU_eq : halfU = {β : ℂˣ | 0 < ((β : ℂ) / (1 : ℂˣ)).re} := by
  ext β; simp [halfU]

theorem isOpen_halfU : IsOpen halfU := by rw [halfU_eq]; exact isOpen_halfPlane 1

theorem injOn_polC_halfU {Q : QuadForm ℂ n} {c : ℂ} (hc : c ≠ 0) : InjOn (polC Q c) (halfU ×ˢ univ) := by
  rw [halfU_eq]; exact injOn_polC hc 1

/-! ### The fibre-counting pull-back of Lebesgue measure along the polar map -/

/-- $M_c = \mathrm{pol}^\#(dy)$ on $\mathbb C^\times \times S_c$ (fibre counting). -/
def MC (Q : QuadForm ℂ n) (c : ℂ) : Measure (ℂˣ × SphC Q c) := Leray.fibreCount (polC Q c) volume

variable {Q : QuadForm ℂ n} {c : ℂ}

theorem MC_apply_of_subset (hc : c ≠ 0) {S : Set (ℂˣ × SphC Q c)} (hS : MeasurableSet S)
    (hS' : S ⊆ halfU ×ˢ univ) : MC Q c S = volume (polC Q c '' S) :=
  Leray.fibreCount_apply_of_injOn (continuous_polC Q c) (isLocInj_polC hc) volume hS
    ((injOn_polC_halfU hc).mono hS')

theorem isFiniteMeasureOnCompacts_MC (hc : c ≠ 0) : IsFiniteMeasureOnCompacts (MC Q c) :=
  Leray.fibreCount_isFiniteMeasureOnCompacts (continuous_polC Q c) (isLocInj_polC hc) volume

/-- Scaling $\beta \mapsto a\beta$ on $\mathbb C^\times \times S_c$. -/
def scT (a : ℂˣ) : (ℂˣ × SphC Q c) ≃ᵐ (ℂˣ × SphC Q c) :=
  (Homeomorph.prodCongr (Homeomorph.mulLeft a) (Homeomorph.refl _)).toMeasurableEquiv

theorem scT_apply (a : ℂˣ) (p : ℂˣ × SphC Q c) : scT a p = (a * p.1, p.2) := rfl

/-- Scaling $y \mapsto ay$ on $\mathbb C^n$. -/
def scV (n : ℕ) (a : ℂˣ) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  LerayComplex.linMEquiv ((a : ℂ) • LinearMap.id) (((a⁻¹ : ℂˣ) : ℂ) • LinearMap.id)
    (fun x => by simp [smul_smul]) (fun x => by simp [smul_smul])

theorem scV_apply (a : ℂˣ) (y : Fin n → ℂ) : scV n a y = (a : ℂ) • y := rfl

theorem det_smul_id (a : ℂ) : LinearMap.det (a • (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) = a ^ n := by
  rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_fin_fun, mul_one]

theorem wt_two_mul (a : ℂˣ) : wt (-(2 * n : ℕ)) a = (((‖LinearMap.det ((a : ℂ) •
    (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [det_smul_id, wt, nnnorm_pow, ← pow_mul, mul_comm n 2, _root_.zpow_neg, zpow_natCast]

theorem map_scV_volume (a : ℂˣ) : (volume : Measure (Fin n → ℂ)).map (scV n a) = wt (-(2 * n : ℕ)) a • volume := by
  rw [show ⇑(scV n a) = ⇑((a : ℂ) • (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) from rfl,
    LerayComplex.map_clm_addHaar _ _ (by rw [det_smul_id]; exact pow_ne_zero _ a.ne_zero), wt_two_mul]

theorem map_scT_MC (hc : c ≠ 0) (a : ℂˣ) : (MC Q c).map (scT a) = wt (-(2 * n : ℕ)) a • MC Q c := by
  rw [MC, Leray.fibreCount_map (continuous_polC Q c) (isLocInj_polC hc) volume (scT a) (scV n a)
    (fun p => by simp [scT_apply, scV_apply, polC, smul_smul]), map_scV_volume,
    Leray.fibreCount_smul (continuous_polC Q c) (isLocInj_polC hc)]

/-- $\lambda_A(R) = M_c(R \times A)$, a measure on $\mathbb C^\times$. -/
def lamA (Q : QuadForm ℂ n) (c : ℂ) (A : Set (SphC Q c)) : Measure ℂˣ :=
  ((MC Q c).restrict (univ ×ˢ A)).map Prod.fst

theorem lamA_apply {A : Set (SphC Q c)} {R : Set ℂˣ} (hR : MeasurableSet R) : lamA Q c A R = MC Q c (R ×ˢ A) := by
  rw [lamA, map_apply measurable_fst hR, restrict_apply (measurable_fst hR)]
  congr 1
  ext p; simp [and_comm]

theorem map_mul_lamA (hc : c ≠ 0) {A : Set (SphC Q c)} (a : ℂˣ) :
    (lamA Q c A).map (a * ·) = wt (-(2 * n : ℕ)) a • lamA Q c A := by
  have h1 : (fun β : ℂˣ => a * β) ∘ Prod.fst = Prod.fst ∘ (scT (Q := Q) (c := c) a) := rfl
  have hpre : (scT (Q := Q) (c := c) a) ⁻¹' (univ ×ˢ A) = univ ×ˢ A := by ext p; simp [scT_apply]
  rw [lamA, Measure.map_map (measurable_const_mul a) measurable_fst, h1,
    ← Measure.map_map measurable_fst (scT a).measurable, ← hpre, ← MeasurableEquiv.restrict_map, map_scT_MC hc,
    Measure.restrict_smul, Measure.map_smul, hpre]
  exact measurable_fst.aemeasurable

/-- The bounded parts of $S_c$. -/
def ballS (Q : QuadForm ℂ n) (c : ℂ) (k : ℝ) : Set (SphC Q c) := {x | ‖(x : Fin n → ℂ)‖ ≤ k}

theorem isCompact_ballS (k : ℝ) : IsCompact (ballS Q c k) := by
  have h := (isClosed_sphC Q c).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_closedBall (0 : Fin n → ℂ) k)
  convert h using 1
  ext x; simp [ballS]

theorem measurableSet_ballS (k : ℝ) : MeasurableSet (ballS Q c k) := (isCompact_ballS k).measurableSet

theorem iUnion_ballS : (⋃ k : ℕ, ballS Q c k) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ?_
  obtain ⟨k, hk⟩ := exists_nat_ge ‖(x : Fin n → ℂ)‖
  exact ⟨k, hk⟩

theorem monotone_ballS : Monotone fun k : ℕ => ballS Q c k := fun k l hkl x hx => by
  show ‖(x : Fin n → ℂ)‖ ≤ (l : ℝ)
  exact le_trans hx (by exact_mod_cast hkl)

theorem lamA_isFiniteMeasureOnCompacts (hc : c ≠ 0) {A : Set (SphC Q c)} {k : ℝ} (hA : A ⊆ ballS Q c k) :
    IsFiniteMeasureOnCompacts (lamA Q c A) := by
  have := isFiniteMeasureOnCompacts_MC (Q := Q) hc
  refine ⟨fun K hK => ?_⟩
  rw [lamA_apply hK.measurableSet]
  exact lt_of_le_of_lt (measure_mono (prod_mono subset_rfl hA)) (hK.prod (isCompact_ballS k)).measure_lt_top

/-- **The radial measure** $|\beta|^{2n-2}\,d^2\beta$ on $\mathbb C^\times$. -/
def lamU (n : ℕ) : Measure ℂˣ := volU.withDensity (wt (2 * n - 2))

instance : IsFiniteMeasureOnCompacts (lamU n) := withDensity_isFiniteMeasureOnCompacts _ _

theorem haarU_withDensity : haarU.withDensity (wt (2 * n)) = lamU n := by
  rw [haarU, ← withDensity_mul _ (measurable_wt _) (measurable_wt _), lamU]
  congr 1
  funext β
  simp only [Pi.mul_apply, wt_mul_wt]
  rw [show (-2 : ℤ) + 2 * n = 2 * n - 2 by ring]

/-- **The fixed sector** $R_0 = \{\operatorname{Re}\beta > 0, |\beta| < 1\}$ normalizing the cone measure. -/
def R0 : Set ℂˣ := {β | 0 < (β : ℂ).re ∧ ‖(β : ℂ)‖ < 1}

theorem isOpen_R0 : IsOpen R0 :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp Units.continuous_val)).inter
    (isOpen_lt (continuous_norm.comp Units.continuous_val) continuous_const)

theorem R0_subset_halfU : R0 ⊆ halfU := fun _ h => h.1

theorem lamU_R0_pos : 0 < lamU n R0 := by
  refine withDensity_wt_pos isOpen_R0 ⟨Units.mk0 (1 / 2) (by norm_num), ?_, ?_⟩ _
  · simp
  · simp only [Units.val_mk0]; rw [norm_div, norm_one, Complex.norm_ofNat]; norm_num

theorem lamU_R0_lt_top (hn : 1 ≤ n) : lamU n R0 < ⊤ := by
  rw [lamU, withDensity_apply _ isOpen_R0.measurableSet]
  calc ∫⁻ β in R0, wt (2 * n - 2) β ∂volU ≤ ∫⁻ _ in R0, 1 ∂volU := by
        refine setLIntegral_mono measurable_const fun β hβ => ?_
        rw [wt, ENNReal.coe_le_one_iff]
        have h1 : ‖(β : ℂ)‖₊ ≤ 1 := by
          rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]; exact hβ.2.le
        exact zpow_le_one₀ (pos_iff_ne_zero.mpr (nnnorm_ne_zero β)) h1 (by omega)
    _ = volU R0 := by rw [setLIntegral_const, one_mul]
    _ < ⊤ := by
        rw [volU_apply isOpen_R0.measurableSet]
        refine lt_of_le_of_lt (measure_mono ?_) (measure_ball_lt_top (x := (0 : ℂ)) (r := 1))
        rintro _ ⟨β, hβ, rfl⟩
        rw [Metric.mem_ball, dist_zero_right]; exact hβ.2

/-- **The cone measure** $\nu_c(A) = M_c(R_0 \times A)/\lambda(R_0)$ (`nuC_apply`). -/
def nuC (Q : QuadForm ℂ n) (c : ℂ) : Measure (SphC Q c) :=
  (lamU n R0)⁻¹ • ((MC Q c).restrict (R0 ×ˢ univ)).map Prod.snd

theorem nuC_apply {A : Set (SphC Q c)} (hA : MeasurableSet A) : nuC Q c A = (lamU n R0)⁻¹ * MC Q c (R0 ×ˢ A) := by
  rw [nuC, Measure.smul_apply, map_apply measurable_snd hA, restrict_apply (measurable_snd hA), smul_eq_mul]
  congr 2
  ext p; simp [and_comm]

/-- On the half plane the cone measure is a volume: $\nu_c(A) = \mathrm{Leb}(R_0\cdot A)/\lambda(R_0)$. -/
theorem nuC_apply_volume (hc : c ≠ 0) {A : Set (SphC Q c)} (hA : MeasurableSet A) :
    nuC Q c A = (lamU n R0)⁻¹ * volume (polC Q c '' (R0 ×ˢ A)) := by
  rw [nuC_apply hA, MC_apply_of_subset hc (isOpen_R0.measurableSet.prod hA)
    (prod_mono R0_subset_halfU (subset_univ _))]

/-- **The product formula on bounded sets** (Haar uniqueness on $\mathbb C^\times$). -/
theorem MC_prod_of_bounded (hc : c ≠ 0) (hn : 1 ≤ n) {A : Set (SphC Q c)} (hAm : MeasurableSet A) {k : ℝ}
    (hA : A ⊆ ballS Q c k) : ∃ κ : ℝ≥0, nuC Q c A = κ ∧ ∀ R, MeasurableSet R → MC Q c (R ×ˢ A) = lamU n R * κ := by
  have := lamA_isFiniteMeasureOnCompacts hc hA
  set ξ := (lamA Q c A).withDensity (wt (-(2 * n : ℕ)))
  have hξ : ξ.IsMulLeftInvariant := isMulLeftInvariant_withDensity _ _ (map_mul_lamA hc)
  have : IsFiniteMeasureOnCompacts ξ := withDensity_isFiniteMeasureOnCompacts _ _
  have hH := isMulLeftInvariant_eq_smul ξ haarU
  set κ := haarScalarFactor ξ haarU
  have hlam : lamA Q c A = (κ : ℝ≥0∞) • lamU n := by
    have e : lamA Q c A = ξ.withDensity (wt (2 * n)) := by
      rw [← withDensity_mul _ (measurable_wt _) (measurable_wt _)]
      have : wt (-(2 * n : ℕ)) * wt (2 * n) = 1 := by
        funext β; simp only [Pi.mul_apply, Pi.one_apply, wt_mul_wt]; push_cast; rw [neg_add_cancel, wt_zero]
      rw [this, withDensity_one]
    rw [e, hH, ENNReal.smul_def, withDensity_smul_measure, haarU_withDensity]
  have hR : ∀ R, MeasurableSet R → MC Q c (R ×ˢ A) = lamU n R * κ := fun R hR => by
    rw [← lamA_apply hR, hlam, Measure.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨κ, ?_, hR⟩
  rw [nuC_apply hAm, hR R0 isOpen_R0.measurableSet, ← mul_assoc, ENNReal.inv_mul_cancel lamU_R0_pos.ne'
    (lamU_R0_lt_top hn).ne, one_mul]

theorem MC_prod (hc : c ≠ 0) (hn : 1 ≤ n) {A : Set (SphC Q c)} (hA : MeasurableSet A) {R : Set ℂˣ}
    (hR : MeasurableSet R) : MC Q c (R ×ˢ A) = lamU n R * nuC Q c A := by
  have hmono : Monotone fun k : ℕ => A ∩ ballS Q c k := fun k l hkl => inter_subset_inter_right _ (monotone_ballS hkl)
  have hU : (⋃ k : ℕ, A ∩ ballS Q c k) = A := by rw [← inter_iUnion, iUnion_ballS, inter_univ]
  have hk : ∀ k : ℕ, MC Q c (R ×ˢ (A ∩ ballS Q c k)) = lamU n R * nuC Q c (A ∩ ballS Q c k) := by
    intro k
    obtain ⟨κ, h1, h2⟩ := MC_prod_of_bounded hc hn (hA.inter (measurableSet_ballS k)) inter_subset_right
    rw [h1, h2 R hR]
  have hmono' : Monotone fun k : ℕ => R ×ˢ (A ∩ ballS Q c k) := fun k l hkl => prod_mono subset_rfl (hmono hkl)
  conv_lhs => rw [← hU, prod_iUnion, hmono'.measure_iUnion]
  conv_rhs => rw [← hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  simp_rw [hk]

theorem nuC_ballS_lt_top (hc : c ≠ 0) (hn : 1 ≤ n) (k : ℝ) : nuC Q c (ballS Q c k) < ⊤ := by
  obtain ⟨κ, h1, -⟩ := MC_prod_of_bounded hc hn (measurableSet_ballS k) subset_rfl
  rw [h1]; exact ENNReal.coe_lt_top

theorem sigmaFinite_nuC (hc : c ≠ 0) (hn : 1 ≤ n) : SigmaFinite (nuC Q c) :=
  ⟨⟨⟨fun k : ℕ => ballS Q c k, fun _ => mem_univ _, fun k => nuC_ballS_lt_top hc hn k, iUnion_ballS⟩⟩⟩

/-- **Polar coordinates on $\mathbb C^\times \times S_c$**: the fibre-counting pull-back of Lebesgue measure along
$(\beta, x) \mapsto \beta x$ is $|\beta|^{2n-2}\,d^2\beta \otimes \nu_c$ ($c \ne 0$, $n \ge 1$). -/
@[kb "weil1982" "§2.2 (gauge forms; polar decomposition dy = |β|^{2n-2}dβ ∧ ω_c) [unverified]"]
theorem fibreCount_polC (hc : c ≠ 0) (hn : 1 ≤ n) :
    Leray.fibreCount (polC Q c) volume = (lamU n).prod (nuC Q c) := by
  have := sigmaFinite_nuC (Q := Q) hc hn
  exact (Measure.prod_eq fun R A hR hA => MC_prod hc hn hA hR).symm


/-- **Polar coordinates on the half plane** $\operatorname{Re}\beta > 0$ (where $\mathrm{pol}$ is injective): for
$f \ge 0$ measurable, $\int_{\{\beta x : \operatorname{Re}\beta > 0\}} f\,dy =
\int_{\operatorname{Re}\beta > 0}\int_{S_c} f(\beta x)\,d\nu_c(x)\,|\beta|^{2n-2}d^2\beta$. -/
@[kb "weil1982" "§2.2 (gauge forms; polar decomposition) [unverified]"]
theorem lintegral_polC_half (hc : c ≠ 0) (hn : 1 ≤ n) {f : (Fin n → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in polC Q c '' (halfU ×ˢ univ), f y =
      ∫⁻ β in halfU, ∫⁻ x, f ((β : ℂ) • (x : Fin n → ℂ)) ∂nuC Q c ∂lamU n := by
  have := sigmaFinite_nuC (Q := Q) hc hn
  have hS : MeasurableSet (halfU ×ˢ (univ : Set (SphC Q c))) := isOpen_halfU.measurableSet.prod MeasurableSet.univ
  have hmap := Leray.map_restrict_fibreCount (continuous_polC Q c) (isLocInj_polC hc) volume hS
    (injOn_polC_halfU hc)
  have e : ((lamU n).prod (nuC Q c)).restrict (halfU ×ˢ univ) = ((lamU n).restrict halfU).prod (nuC Q c) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [← hmap, lintegral_map hf (continuous_polC Q c).measurable, fibreCount_polC hc hn, e,
    lintegral_prod (f := fun p => f (polC Q c p)) (hf.comp (continuous_polC Q c).measurable).aemeasurable]
  rfl

/-- **The Leray measure** $\sigma_c = \nu_c/|2c|_{\mathbb C}$ on $S_c$ ($|z|_{\mathbb C} = |z|^2$; Weil's $|dx/dQ|$,
`lintegral_fibrationC`). -/
@[kb "weil1982" "§2.2 (gauge forms; the form dx/dQ on a level set) [unverified]"]
def sigC (Q : QuadForm ℂ n) (c : ℂ) : Measure (SphC Q c) := (((‖2 * c‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) • nuC Q c

theorem nuC_eq_smul_sigC (hc : c ≠ 0) : nuC Q c = (((‖2 * c‖₊ ^ 2 : ℝ≥0)) : ℝ≥0∞) • sigC Q c := by
  have h2c : ‖2 * c‖₊ ^ 2 ≠ 0 := pow_ne_zero _ (nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hc))
  rw [sigC, smul_smul, ← ENNReal.coe_mul, mul_inv_cancel₀ h2c, ENNReal.coe_one, one_smul]

theorem sigmaFinite_sigC (hc : c ≠ 0) (hn : 1 ≤ n) : SigmaFinite (sigC Q c) := by
  have := sigmaFinite_nuC (Q := Q) hc hn
  show SigmaFinite (((‖2 * c‖₊ ^ 2)⁻¹ : ℝ≥0) • nuC Q c)
  infer_instance

/-! ### Invariance under $SO(Q)(\mathbb C)$ -/

theorem eval_mulVec_of_isometryC {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᵀ * LerayComplex.gramC Q * g = LerayComplex.gramC Q) (x : Fin n → ℂ) : Q.eval (g *ᵥ x) = Q.eval x := by
  rw [eval_eq_gramC, eval_eq_gramC]
  conv_rhs => rw [← hg]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x gᵀ, vecMul_transpose]

/-- **The action of an isometry on $S_c$**: $x \mapsto gx$. -/
def sphMapC (Q : QuadForm ℂ n) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * LerayComplex.gramC Q * g = LerayComplex.gramC Q) (x : SphC Q c) : SphC Q c :=
  ⟨g *ᵥ (x : Fin n → ℂ), by show Q.eval _ = c; rw [eval_mulVec_of_isometryC hg]; exact x.2⟩

theorem continuous_sphMapC (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * LerayComplex.gramC Q * g = LerayComplex.gramC Q) : Continuous (sphMapC Q c g hg) :=
  ((Matrix.toLin' g).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

theorem volume_image_toLin' (g : Matrix (Fin n) (Fin n) ℂ) (hdet : ‖g.det‖ = 1) (E : Set (Fin n → ℂ)) :
    volume (Matrix.toLin' g '' E) = volume E := by
  rw [show ⇑(Matrix.toLin' g) = ⇑((Matrix.toLin' g).restrictScalars ℝ) from rfl, addHaar_image_linearMap,
    LerayComplex.det_restrictScalars_complex, LinearMap.det_toLin', Complex.normSq_eq_norm_sq, hdet]
  simp

/-- **Invariance of the cone measure** under every isometry $g$ with $|\det g| = 1$. -/
theorem map_sphMapC_nuC (hc : c ≠ 0) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * LerayComplex.gramC Q * g = LerayComplex.gramC Q) (hdet : ‖g.det‖ = 1) :
    (nuC Q c).map (sphMapC Q c g hg) = nuC Q c := by
  ext A hA
  have hm := (continuous_sphMapC (c := c) g hg).measurable
  rw [Measure.map_apply hm hA, nuC_apply_volume hc (hm hA), nuC_apply_volume hc hA]
  congr 1
  have h0 : g.det ≠ 0 := by intro h; rw [h, norm_zero] at hdet; exact zero_ne_one hdet
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.mpr h0)
  have hgi' : (g⁻¹)ᵀ * LerayComplex.gramC Q * g⁻¹ = LerayComplex.gramC Q := by
    have : (g⁻¹)ᵀ * (gᵀ * LerayComplex.gramC Q * g) * g⁻¹ = LerayComplex.gramC Q := by
      rw [show (g⁻¹)ᵀ * (gᵀ * LerayComplex.gramC Q * g) * g⁻¹ = (g * g⁻¹)ᵀ * LerayComplex.gramC Q * (g * g⁻¹) by
        rw [transpose_mul]; simp only [Matrix.mul_assoc], hgi, transpose_one, Matrix.one_mul, Matrix.mul_one]
    rwa [hg] at this
  have himg : Matrix.toLin' g '' (polC Q c '' (R0 ×ˢ (sphMapC Q c g hg ⁻¹' A))) = polC Q c '' (R0 ×ˢ A) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩, rfl⟩
      exact ⟨(β, sphMapC Q c g hg x), ⟨hβ, hx⟩, by simp [polC, sphMapC]⟩
    · rintro ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩
      refine ⟨polC Q c (β, sphMapC Q c g⁻¹ hgi' x), ⟨(β, sphMapC Q c g⁻¹ hgi' x), ⟨hβ, ?_⟩, rfl⟩, ?_⟩
      · show sphMapC Q c g hg (sphMapC Q c g⁻¹ hgi' x) ∈ A
        have : sphMapC Q c g hg (sphMapC Q c g⁻¹ hgi' x) = x := by
          apply Subtype.ext; simp [sphMapC, mulVec_mulVec, hgi]
        rw [this]; exact hx
      · simp [polC, sphMapC, mulVec_mulVec, hgi]
  rw [← himg, volume_image_toLin' g hdet]

/-- **$\sigma_c$ is $SO(Q)(\mathbb C)$-invariant** (more generally invariant under isometries with $|\det| = 1$). -/
@[kb "weil1982" "§2.2 (invariant gauge form on a homogeneous space) [unverified]"]
theorem map_sphMapC_sigC (hc : c ≠ 0) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᵀ * LerayComplex.gramC Q * g = LerayComplex.gramC Q) (hdet : ‖g.det‖ = 1) :
    (sigC Q c).map (sphMapC Q c g hg) = sigC Q c := by
  rw [sigC, Measure.map_smul, map_sphMapC_nuC hc g hg hdet]
  exact (continuous_sphMapC g hg).measurable.aemeasurable

/-! ### Homogeneity -/

/-- The scaling $S_c \to S_{a^2c}$, $x \mapsto ax$. -/
def sphScaleC (Q : QuadForm ℂ n) (c : ℂ) (a : ℂ) (x : SphC Q c) : SphC Q (a ^ 2 * c) :=
  ⟨a • (x : Fin n → ℂ), by show Q.eval _ = _; rw [eval_smulC, x.2]⟩

theorem continuous_sphScaleC (a : ℂ) : Continuous (sphScaleC Q c a) :=
  Continuous.subtype_mk (by fun_prop : Continuous fun x : SphC Q c => a • (x : Fin n → ℂ)) _

theorem volume_smul_image (a : ℂ) (E : Set (Fin n → ℂ)) :
    volume ((a • (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) '' E) = ((‖a‖₊ ^ (2 * n) : ℝ≥0) : ℝ≥0∞) * volume E := by
  rw [show ⇑(a • (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) =
      ⇑((a • (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))).restrictScalars ℝ) from rfl, addHaar_image_linearMap,
    LerayComplex.det_restrictScalars_complex, det_smul_id, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
    ← ENNReal.ofReal_coe_nnreal]
  congr 2
  push_cast
  rw [norm_pow, ← pow_mul, mul_comm]

theorem nuC_scale (hc : c ≠ 0) {a : ℂ} (ha : a ≠ 0) :
    nuC Q (a ^ 2 * c) = ((‖a‖₊ ^ (2 * n) : ℝ≥0) : ℝ≥0∞) • (nuC Q c).map (sphScaleC Q c a) := by
  have hc' : a ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) hc
  ext A hA
  have hm := (continuous_sphScaleC (Q := Q) (c := c) a).measurable
  rw [Measure.smul_apply, Measure.map_apply hm hA, nuC_apply_volume hc' hA, nuC_apply_volume hc (hm hA),
    smul_eq_mul, mul_left_comm]
  congr 1
  have himg : polC Q (a ^ 2 * c) '' (R0 ×ˢ A) =
      (a • (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) '' (polC Q c '' (R0 ×ˢ (sphScaleC Q c a ⁻¹' A))) := by
    ext y
    constructor
    · rintro ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩
      have hx' : Q.eval (a⁻¹ • (x : Fin n → ℂ)) = c := by
        rw [eval_smulC, x.2, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha), one_mul]
      refine ⟨polC Q c (β, ⟨_, hx'⟩), ⟨(β, ⟨_, hx'⟩), ⟨hβ, ?_⟩, rfl⟩, ?_⟩
      · show sphScaleC Q c a ⟨_, hx'⟩ ∈ A
        have : sphScaleC Q c a ⟨_, hx'⟩ = x := by
          apply Subtype.ext; simp [sphScaleC, smul_smul, mul_inv_cancel₀ ha]
        rw [this]; exact hx
      · simp only [polC, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
        rw [mul_comm a, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    · rintro ⟨_, ⟨⟨β, x⟩, ⟨hβ, hx⟩, rfl⟩, rfl⟩
      exact ⟨(β, sphScaleC Q c a x), ⟨hβ, hx⟩, by
        simp only [polC, sphScaleC, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_comm]⟩
  rw [himg, volume_smul_image]

/-- **Homogeneity of the complex Leray measure**: $\sigma_{a^2c} = |a|^{2(n-2)}\,(x \mapsto ax)_*\sigma_c$ for
$a \ne 0$, $n \ge 2$ (with $t = a^2$: the factor $|t|_{\mathbb C}^{n/2-1}$). -/
@[kb "weil1982" "§2.2 (gauge forms; homogeneity of dx/dQ) [unverified]"]
theorem sigC_scale (hc : c ≠ 0) {a : ℂ} (ha : a ≠ 0) (hn : 2 ≤ n) :
    sigC Q (a ^ 2 * c) = ((‖a‖₊ ^ (2 * (n - 2)) : ℝ≥0) : ℝ≥0∞) • (sigC Q c).map (sphScaleC Q c a) := by
  rw [sigC, sigC, nuC_scale hc ha, Measure.map_smul, smul_smul, smul_smul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
  congr 2
  have ha' : ‖a‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr ha
  have h2c : ‖2 * c‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hc)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k - 2 = k by omega, show 2 * (2 + k) = 2 * k + 4 by ring, pow_add,
    show (2 : ℂ) * (a ^ 2 * c) = a ^ 2 * (2 * c) by ring, nnnorm_mul, nnnorm_pow, mul_pow, mul_inv]
  field_simp
  exact (continuous_sphScaleC a).measurable.aemeasurable

/-! ### The Leray fibration $dy = \sigma_t \otimes dt$ -/

theorem lintegral_sigC_scale (hc : c ≠ 0) {a : ℂ} (ha : a ≠ 0) (hn : 2 ≤ n) {f : (Fin n → ℂ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f (y : Fin n → ℂ) ∂sigC Q (a ^ 2 * c) =
      ((‖a‖₊ ^ (2 * (n - 2)) : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, f (a • (x : Fin n → ℂ)) ∂sigC Q c := by
  rw [sigC_scale hc ha hn, lintegral_smul_measure,
    lintegral_map (f := fun y : SphC Q (a ^ 2 * c) => f (y : Fin n → ℂ)) (hf.comp measurable_subtype_coe)
    (continuous_sphScaleC a).measurable, smul_eq_mul]
  rfl

/-- **The Leray fibration** at a complex place ($c \ne 0$, $n \ge 2$): for $f \ge 0$ measurable,
$$\int_{\{\beta x\,:\,\operatorname{Re}\beta > 0,\ x \in S_c\}} f\,dy =
\int_{\operatorname{Re}\beta > 0} |2c\beta|^2 \int_{S_{\beta^2c}} f\,d\sigma_{\beta^2c}\,d^2\beta.$$
With $t = c\beta^2$ (a bijection of the half plane onto $\mathbb C \setminus c\,\mathbb R_{\le 0}$, real Jacobian
$|2c\beta|^2$), this is $dy = \sigma_t \otimes dt$: $\sigma_c$ is the Leray measure $dy/dQ$ on $S_c$. -/
@[kb "weil1982" "§2.2 (gauge forms; dy = ω_t ∧ dQ on the fibres of Q) [unverified]"]
theorem lintegral_fibrationC (hc : c ≠ 0) (hn : 2 ≤ n) {f : (Fin n → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in polC Q c '' (halfU ×ˢ univ), f y =
      ∫⁻ β in halfU, ((‖2 * c * β‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) *
        ∫⁻ y, f (y : Fin n → ℂ) ∂sigC Q ((β : ℂ) ^ 2 * c) ∂volU := by
  rw [lintegral_polC_half hc (by omega) hf, lamU, setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_wt _)
    _ isOpen_halfU.measurableSet]
  · refine setLIntegral_congr_fun isOpen_halfU.measurableSet fun β _ => ?_
    rw [Pi.mul_apply, lintegral_sigC_scale hc β.ne_zero hn hf, nuC_eq_smul_sigC hc, lintegral_smul_measure,
      smul_eq_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [wt, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    congr 1
    have hβ := nnnorm_ne_zero β
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show (2 * ((2 + k : ℕ) : ℤ) - 2) = ((2 * k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      show 2 + k - 2 = k by omega]
    simp only [nnnorm_mul, mul_pow, pow_add]
    ring
  · have := sigmaFinite_nuC (Q := Q) hc (by omega)
    exact Measurable.lintegral_prod_right' (f := fun p : ℂˣ × SphC Q c => f ((p.1 : ℂ) • (p.2 : Fin n → ℂ)))
      (hf.comp (continuous_polC Q c).measurable)

end QuadFormsKB.Tamagawa.Measure.SphereLerayC
