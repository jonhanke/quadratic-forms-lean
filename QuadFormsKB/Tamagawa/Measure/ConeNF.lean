import QuadFormsKB.Tamagawa.Measure.ConeComplexOrbit

/-!
# The archimedean cone identities at the infinite places of a number field

Packaging of `ConeReal.lerayMeasure_cone_orbital` and `ConeComplex.lerayMeasureC_cone_orbital` for a global isotropic
form $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ over a number field $F$ (`coneForm c₀ Q₀'`): at an infinite
place $w$ with embedding $\sigma_w$ the local form is $Q_0^{\sigma_w} = $ `coneForm (σ_w c₀) (Q₀'.map σ_w)`
(`map_coneForm`), and
$$\mu_{Q_0^{\sigma_w}} = |2c_0|_w^{-2(k+1)}\cdot\Psi_*(\sigma_C \otimes \mu_P)$$
with the normalized absolute value $|x|_w = w(x)$ (real) or $w(x)^2$ (complex). The local constant is the $w$-component
of the idele $(2c_0)^{-2(k+1)}$, so the archimedean constants are $\prod_{w\mid\infty}|2c_0|_w^{-2(k+1)}$; the product over
all places of $|2c_0|_v^{-2(k+1)}$ is $1$ (product formula).
-/

open MeasureTheory Measure Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeNF

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.ConeAlgebra
open NumberField NumberField.InfinitePlace

variable {k : ℕ}

/-- The local form of a global cone form: $(\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0')^\sigma =
\langle\sigma c_0\rangle\perp\langle -\sigma c_0\rangle\perp Q_0'^\sigma$. -/
theorem map_coneForm {R S : Type*} [Field R] [Field S] (f : R →+* S) (c₀ : R) (Q₀' : QuadForm R k) :
    (coneForm c₀ Q₀').map f = coneForm (f c₀) (Q₀'.map f) := by
  rw [coneForm, coneForm, map_splitForm, map_splitForm, map_neg]

/-- **The cone orbital identity at a real place of a number field**: the constant is $|2c_0|_w^{-2(k+1)}$,
$|x|_w = w(x)$. -/
@[kb "weil1982" "§2.4 Theorem 2.4.3; §4.5 (local factors at the infinite places, cone orbit) [unverified]"]
theorem lerayMeasure_cone_orbital_realPlace {F : Type*} [Field F] [NumberField F]
    (w : {w : InfinitePlace F // w.IsReal}) {c₀ : F} (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm F k)
    (hQ' : gramDetR (Q₀'.map (embedding_of_isReal w.2)) ≠ 0)
    (s' : OrbitalReal.SphSection (-(embedding_of_isReal w.2 c₀)) (Q₀'.map (embedding_of_isReal w.2))) :
    LerayReal.lerayMeasure (coneForm (embedding_of_isReal w.2 c₀) (Q₀'.map (embedding_of_isReal w.2)))
        (ConeReal.gramDetR_cone ((map_ne_zero _).mpr hc₀) hQ') =
      ENNReal.ofReal ((w.1 (2 * c₀) ^ (2 * k + 2))⁻¹) •
        (ConeReal.coneOrbitSection ((map_ne_zero _).mpr hc₀) hQ' s').fibMeasure
          (ConeReal.sigCone ((map_ne_zero _).mpr hc₀)) (ConeReal.muP ((map_ne_zero _).mpr hc₀) hQ') := by
  rw [ConeReal.lerayMeasure_cone_orbital ((map_ne_zero _).mpr hc₀) hQ' s', ← norm_embedding_of_isReal w.2,
    map_mul, map_ofNat, Real.norm_eq_abs]

/-- **The cone orbital identity at a complex place of a number field**: the constant is $|2c_0|_w^{-2(k+1)}$ for
the normalized $|x|_w = w(x)^2$. -/
@[kb "weil1982" "§2.4 Theorem 2.4.3; §4.5 (local factors at the infinite places, cone orbit) [unverified]"]
theorem lerayMeasureC_cone_orbital_complexPlace {F : Type*} [Field F] [NumberField F]
    (w : {w : InfinitePlace F // w.IsComplex}) {c₀ : F} (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm F k)
    (hQ' : LerayComplex.gramDetC (Q₀'.map w.1.embedding) ≠ 0)
    (s' : OrbitalComplex.SphSectionC (-(w.1.embedding c₀)) (Q₀'.map w.1.embedding)) :
    LerayComplex.lerayMeasureC (coneForm (w.1.embedding c₀) (Q₀'.map w.1.embedding))
        (ConeComplex.gramDetC_cone ((map_ne_zero _).mpr hc₀) hQ') =
      ENNReal.ofReal (((w.1 (2 * c₀) ^ 2) ^ (2 * k + 2))⁻¹) •
        (ConeComplex.coneOrbitSection ((map_ne_zero _).mpr hc₀) hQ' s').fibMeasure
          (ConeComplex.sigCone ((map_ne_zero _).mpr hc₀)) (ConeComplex.muP ((map_ne_zero _).mpr hc₀) hQ') := by
  rw [ConeComplex.lerayMeasureC_cone_orbital ((map_ne_zero _).mpr hc₀) hQ' s', ← norm_embedding_eq, map_mul,
    map_ofNat, ← ENNReal.ofReal_coe_nnreal]
  congr 2
  push_cast
  rw [← pow_mul]


/-! ### Consistency: $\sigma_C$ is the Leray measure $dx/dQ$ of the cone -/

section Slice

open QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Tamagawa.Measure.ConeReal

variable {c : ℝ} {Q' : QuadForm ℝ k}

theorem neg_one_isometry {n : ℕ} (Q : QuadForm ℝ n) :
    (-1 : Matrix (Fin n) (Fin n) ℝ)ᵀ * gramMatrixR Q * (-1) = gramMatrixR Q := by
  simp

/-- **$\sigma_C = dx_0 \otimes \sigma'_{-cx_0^2}$** (real places, $k \ge 1$): in the slicing
$Q(x_0, x') = cx_0^2 + Q_m(x')$, $Q_m = \langle -c\rangle\perp Q'$, the cone measure is $dx_0$ times the Leray measure
$\sigma'_{t}$ of the slice $\{Q_m = t\}$, $t = -cx_0^2$. Since $\sigma'_t$ is $dx'/dQ_m$ (the Leray fibration), this
says $\sigma_C = dx/dQ$ on $C^\circ$: the same normalization (Leray measure of $Q$ itself) as the finite-place cone
measure $\sigma_0 = \lim \mathrm{vol}\{Q \in \mathfrak p^j\}/\nu(\mathfrak p^j)$. -/
@[kb "weil1982" "§2.2 (the Leray form on the cone in a slice chart) [unverified]"]
theorem lintegral_sigCone_slice (hc : c ≠ 0) (hk : 1 ≤ k) {F : (Fin (k + 1 + 1) → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ z, F z ∂sigCone (Q' := Q') hc =
      ∫⁻ x₀, ∫⁻ x, F (Fin.cons x₀ (x : Fin (k + 1) → ℝ)) ∂sig (Qm c Q') (x₀ ^ 2 * -c) := by
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  rw [lintegral_sigCone (Q' := Q') hc (F := fun z => F (z : Fin (k + 1 + 1) → ℝ)) (hF.comp measurable_subtype_coe)]
  have hae : ∀ᵐ q : ℝ, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq
  have hq0 : 0 < |q| := abs_pos.mpr hq
  have hn : 2 ≤ k + 1 := by omega
  rw [← sq_abs q, sig_scale hc' hq0 hn, lintegral_smul_measure,
    lintegral_map (f := fun x : Sph (Qm c Q') (|q| ^ 2 * -c) => F (Fin.cons q (x : Fin (k + 1) → ℝ)))
      (hF.comp ((continuous_const.finCons continuous_subtype_val).measurable))
      (continuous_sphScale _ _ _).measurable]
  have hρ : rhoK k q = ENNReal.ofReal (|q| ^ (k + 1 - 2)) := by
    rw [rhoK, show k + 1 - 2 = k - 1 by omega]
    congr 1
    rw [div_eq_iff hq0.ne', ← pow_succ, Nat.sub_add_cancel hk]
  rw [hρ, smul_eq_mul]
  congr 1
  have e1 : ∀ y : Sph (Qm c Q') (-c), (coneMap hc (q, y) : Fin (k + 1 + 1) → ℝ) =
      Fin.cons q (q • (y : Fin (k + 1) → ℝ)) := by
    intro y
    rw [coe_coneMap hc hq, coneVec]
    ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  simp_rw [e1]
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · have habs : |q| = -q := abs_of_neg hneg
    have hinv := map_sphMap_sig (Q := Qm c Q') hc' (-1) (neg_one_isometry _) (by
      rw [det_neg, det_one, mul_one, abs_pow, abs_neg, abs_one, one_pow])
    conv_lhs => rw [← hinv]
    rw [lintegral_map (f := fun y : Sph (Qm c Q') (-c) => F (Fin.cons q (q • (y : Fin (k + 1) → ℝ))))
      (hF.comp ((continuous_const.finCons ((continuous_const_smul q).comp
      continuous_subtype_val)).measurable)) (continuous_sphMap _ _ _ _).measurable]
    refine lintegral_congr fun y => ?_
    show F (Fin.cons q (q • ((-1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *ᵥ (y : Fin (k + 1) → ℝ)))) =
      F (Fin.cons q (|q| • (y : Fin (k + 1) → ℝ)))
    rw [habs, neg_mulVec, one_mulVec, smul_neg, neg_smul]
  · rw [abs_of_pos hpos]
    rfl

end Slice


section SliceC

open QuadFormsKB.Tamagawa.Measure.SphereLerayC QuadFormsKB.Tamagawa.Measure.ConeComplex

variable {c : ℂ} {Q' : QuadForm ℂ k}

/-- **$\sigma_C = d^2x_0 \otimes \sigma'_{-cx_0^2}$** at a complex place ($k \ge 1$): the complex cone measure is the
Leray measure $dx/dQ$ in the slicing $Q = cx_0^2 + Q_m(x')$ (the homogeneity `sigC_scale`). -/
@[kb "weil1982" "§2.2 (the Leray form on the cone in a slice chart, complex place) [unverified]"]
theorem lintegral_sigConeC_slice (hc : c ≠ 0) (hk : 1 ≤ k) {F : (Fin (k + 1 + 1) → ℂ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ z, F z ∂sigCone (Q' := Q') hc =
      ∫⁻ x₀, ∫⁻ x, F (Fin.cons x₀ (x : Fin (k + 1) → ℂ)) ∂sigC (QmC c Q') (x₀ ^ 2 * -c) := by
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  rw [lintegral_sigCone (Q' := Q') hc (F := fun z => F (z : Fin (k + 1 + 1) → ℂ)) (hF.comp measurable_subtype_coe)]
  have hae : ∀ᵐ q : ℂ, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq
  have hn : 2 ≤ k + 1 := by omega
  rw [sigC_scale hc' hq hn, lintegral_smul_measure,
    lintegral_map (f := fun x : SphC (QmC c Q') (q ^ 2 * -c) => F (Fin.cons q (x : Fin (k + 1) → ℂ)))
      (hF.comp ((continuous_const.finCons continuous_subtype_val).measurable))
      (continuous_sphScaleC _).measurable]
  have hq0 : ‖q‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hq
  have hρ : rhoK k q = ((‖q‖₊ ^ (2 * (k + 1 - 2)) : ℝ≥0) : ℝ≥0∞) := by
    rw [rhoK]
    congr 1
    rw [show 2 * (k + 1 - 2) = 2 * k - 2 by omega, ← pow_sub₀ _ hq0 (by omega)]
  rw [hρ, smul_eq_mul]
  congr 1
  refine lintegral_congr fun y => ?_
  show F ((coneMap hc (q, y) : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) =
    F (Fin.cons q (q • (y : Fin (k + 1) → ℂ)))
  rw [coe_coneMap hc hq, coneVec]
  congr 1
  ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp

end SliceC

end QuadFormsKB.Tamagawa.Measure.ConeNF
