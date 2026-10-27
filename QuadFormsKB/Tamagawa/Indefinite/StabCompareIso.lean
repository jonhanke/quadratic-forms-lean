/-
# The norm-one stabilizer measures: independence of $a$, and the normalization of the numbers headline

**Layer:** number fields. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $r + 2$ variables (any signature),
$T_0$ nondegenerate of rank $r$, $\Xi$ a rational frame, the complement $\Xi^\perp$ isotropic (`hiso`), the frame data
`isoTower`, isotropic vector `isoVec`, scale `isoFrameLam`, shell `isoShellInf` (IsoMeasures.lean).

The isotropic rank-2 construction defines the norm-one stabilizer measure at $X = a\,\Xi_\infty$ as the image of
$\lambda\,\mu^{\mathrm{Tam}}_{Q''}|_{\text{shell}}$
under $h\mapsto a\,\iota_\infty(h)\,a^{-1}$, with a *chosen* $a$ (`isoStabAt`, `isoStabMeasure`).

**Defines**
* `isoConj a hX`: $h\mapsto a\,\iota_\infty(h)\,a^{-1}$, $SO(Q'')(F_\infty)\to H_X$ ($a\,\Xi_\infty = X$);
* **`isoShellFrame X`**: the norm-one shell in $H_X$, $\{a\,\iota_\infty(h)\,a^{-1} : h\in\text{shell}\}$ ($\emptyset$
  off the orbit of
  $\Xi_\infty$).

**Proves** (unconditional)
* **`isoStabAt_indep`** (part of the choice independence): `isoStabAt a hX` does not depend on $a$ with
  $a\,\Xi_\infty = X$
  ($a' = a\,\iota_\infty(h_0)$ and $SO(Q'')(F_\infty)$ is commutative); likewise `isoConj` and the shell;
* for $r = 1$, ternary $Q_0$, $T_0 = \langle m\rangle$: **`isoStabMeasure_unary_eq`**: the norm-one stabilizer measure
  at $X$
  is the stabilizer measure of `archFibrationNF` at $X_0$ (`archFibrationNF`, carried to $H_X = H_{X_0}$) restricted
  to the shell;
  hence **`repMeasureIso_unary_eq`** and the ternary isotropic headline with the stabilizer measures of
  `archFibrationNF`,
  **`siegelIndefinite_ternary_isotropic_sphere_uncond`**.
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompareTernary
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernaryIso

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

/-! ### Independence of $a$ (every rank $r$) -/

section General

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
  (Ξ : RatFrame Q₀ T₀)

/-- $h\mapsto a\,\iota_\infty(h)\,a^{-1}$, $SO(Q'')(F_\infty)\to H_X$, for $a\,\Xi_\infty = X$. -/
def isoConj (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X)
    (h : GInfSO (isoTower Q₀ hQ T₀ hT Ξ).Q'') : stabilizer (GInfSO Q₀) X :=
  ⟨a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * a⁻¹, by
    show (a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * a⁻¹) • X = X
    rw [← hX, mul_smul, mul_smul, inv_smul_smul, FrameTowerAlg.ιInf_smul_ratAT]⟩

theorem coe_isoConj (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X)
    (h : GInfSO (isoTower Q₀ hQ T₀ hT Ξ).Q'') :
    (isoConj Q₀ hQ T₀ hT Ξ a hX h : GInfSO Q₀) = a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * a⁻¹ := rfl

theorem measurable_isoConj (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    Measurable (isoConj Q₀ hQ T₀ hT Ξ a hX) :=
  (((measurable_const_mul a).comp (isoTower Q₀ hQ T₀ hT Ξ).measurable_ιInf).mul_const _).subtype_mk

/-- `isoStabAt` is the image of `isoStabBase` under `isoConj`. -/
theorem isoStabAt_eq (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    isoStabAt Q₀ hQ T₀ hT hiso Ξ a hX = (isoStabBase Q₀ hQ T₀ hT hiso Ξ).map (isoConj Q₀ hQ T₀ hT Ξ a hX) := by
  subst hX
  rfl

include hiso in
/-- **`isoConj` does not depend on $a$**: if $a\,\Xi_\infty = a'\,\Xi_\infty$ then $a' = a\,\iota_\infty(h_0)$, and
$SO(Q'')(F_\infty)$ is commutative ($Q''$ isotropic binary: a split torus). -/
theorem isoConj_indep (a a' : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X)
    (hX' : a' • ratAT Q₀ T₀ Ξ = X) : isoConj Q₀ hQ T₀ hT Ξ a hX = isoConj Q₀ hQ T₀ hT Ξ a' hX' := by
  obtain ⟨h₀, hh₀⟩ := FrameTowerAlg.stab_ιInf Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) (a⁻¹ * a')
    (by rw [mul_smul, hX', ← hX, inv_smul_smul])
  have ha' : a' = a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h₀ := by rw [hh₀, mul_inv_cancel_left]
  funext h
  apply Subtype.ext
  rw [coe_isoConj, coe_isoConj, ha', _root_.mul_inv_rev, ← map_inv]
  have hc := mul_comm_GInfSO_iso (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ''
    (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ) h₀ h
  calc a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * a⁻¹
      = a * ((isoTower Q₀ hQ T₀ hT Ξ).ιInf (h₀ * h * h₀⁻¹)) * a⁻¹ := by
        rw [hc, mul_inv_cancel_right]
    _ = a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h₀ * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h *
          ((isoTower Q₀ hQ T₀ hT Ξ).ιInf h₀⁻¹ * a⁻¹) := by
        simp only [map_mul, mul_assoc]

/-- **The norm-one stabilizer measure does not depend on $a$** with $a\,\Xi_\infty = X$ (the `isoStabMeasure` uses a
chosen one). -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (the measure of representations is independent of the choices) [unverified]"]
theorem isoStabAt_indep (a a' : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X)
    (hX' : a' • ratAT Q₀ T₀ Ξ = X) : isoStabAt Q₀ hQ T₀ hT hiso Ξ a hX = isoStabAt Q₀ hQ T₀ hT hiso Ξ a' hX' := by
  rw [isoStabAt_eq, isoStabAt_eq, isoConj_indep Q₀ hQ T₀ hT hiso Ξ a a' hX hX']

theorem isoStabMeasure_eq (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    isoStabMeasure Q₀ hQ T₀ hT hiso Ξ X = isoStabAt Q₀ hQ T₀ hT hiso Ξ a hX := by
  have hX' : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X := ⟨a, hX⟩
  rw [isoStabMeasure, dite_eq_left_of_eq_true (eq_true hX')]
  exact isoStabAt_indep Q₀ hQ T₀ hT hiso Ξ _ _ _ _

open Classical in
/-- **The norm-one shell in $H_X$**: $\{a\,\iota_\infty(h)\,a^{-1} : 0\le\log|\chi(h)|_\infty<1\}$ for
$a\,\Xi_\infty = X$
(independent of $a$, `isoConj_indep`); empty off the orbit of $\Xi_\infty$. -/
def isoShellFrame (X : Fin r → VInf F (r + 2)) : Set (stabilizer (GInfSO Q₀) X) :=
  if hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X then
    Subtype.val ⁻¹' ((fun h => hX.choose * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * hX.choose⁻¹) ''
      isoShellInf (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'' (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ))
  else ∅

theorem isoShellFrame_eq (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    isoShellFrame Q₀ hQ T₀ hT hiso Ξ X = Subtype.val ⁻¹' ((fun h => a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * a⁻¹) ''
      isoShellInf (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'' (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ)) := by
  have hX' : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X := ⟨a, hX⟩
  rw [isoShellFrame, dite_eq_left_of_eq_true (eq_true hX')]
  have e : (fun h => hX'.choose * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * hX'.choose⁻¹) =
      fun h => a * (isoTower Q₀ hQ T₀ hT Ξ).ιInf h * a⁻¹ := funext fun h =>
    congrArg Subtype.val (congrFun (isoConj_indep Q₀ hQ T₀ hT hiso Ξ _ _ hX'.choose_spec hX) h)
  rw [e]

theorem measurableSet_isoShellFrame (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    MeasurableSet (isoShellFrame Q₀ hQ T₀ hT hiso Ξ X) := by
  rw [isoShellFrame_eq Q₀ hQ T₀ hT hiso Ξ a hX]
  refine measurable_subtype_coe ?_
  have h1 := (FrameTowerAlg.measurableEmbedding_ιInf Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ)).measurableSet_image'
    (measurableSet_isoShellInf (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'' (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ))
  have h2 := ((MeasurableEquiv.mulLeft a).trans (MeasurableEquiv.mulRight a⁻¹)).measurableSet_image.2 h1
  rw [← Set.image_comp] at h2
  exact h2

theorem preimage_isoShellFrame (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    isoConj Q₀ hQ T₀ hT Ξ a hX ⁻¹' isoShellFrame Q₀ hQ T₀ hT hiso Ξ X =
      isoShellInf (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'' (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ) := by
  rw [isoShellFrame_eq Q₀ hQ T₀ hT hiso Ξ a hX]
  ext h
  simp only [Set.mem_preimage, coe_isoConj, Set.mem_image]
  constructor
  · rintro ⟨h', hh', e⟩
    have e' : (isoTower Q₀ hQ T₀ hT Ξ).ιInf h' = (isoTower Q₀ hQ T₀ hT Ξ).ιInf h := by
      simpa using e
    rwa [← FrameTowerAlg.ιInf_injective Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) e']
  · intro hh
    exact ⟨h, hh, rfl⟩

end General

/-! ### The ternary case: the measures in the normalization of `archFibrationNF` -/

section Ternary

variable {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
  (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
  (ξ : RatSphere Q₀ (m : F))

/-- The frame data at infinity for $\xi$. -/
abbrev isoTernData : SplitDataInf (k := 2) Q₀ (m : F) (cols (ternFrame Q₀ ξ).1 0) :=
  (isoTower Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ)).toSplitDataInf hm (eval_ternFrame Q₀ ξ)

/-- The scale $\lambda$ = `isoFrameLam` is the scale of the frame data at infinity. -/
theorem isoFrameLam_eq_lam :
    isoFrameLam Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) = (isoTernData Q₀ hQ hm ξ).lam := by
  have hg : ((IsoAlg.towerAdapted Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ)
      (isoTower Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ)) (unary_nondegenerate hm)).g :
      Matrix (Fin (1 + 2)) (Fin (1 + 2)) F) = ((isoTernData Q₀ hQ hm ξ).g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) := by
    rw [IsoAlg.towerAdapted_g_val, IsoAlg.adaptedMat_eq, FrameTowerAlg.toSplitDataInf_g, wittG_eq_splitMat_three]
  unfold isoFrameLam SplitDataInf.lam
  rw [hg]

/-- **The norm-one stabilizer measure in the normalization of `archFibrationNF`** (ternary $Q_0$,
$T_0 = \langle m\rangle$, $m^\perp$ isotropic):
at every $X = a\,\Xi_\infty$, `isoStabMeasure X` is the stabilizer measure of `archFibrationNF` at $X_0$
(`archFibrationNF`, carried to
$H_X = H_{X_0}$) restricted to the norm-one shell `isoShellFrame X`. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (norm-one stabilizers; the frame and sphere normalizations agree) [unverified]"]
theorem isoStabMeasure_unary_eq (X : Fin 1 → VInf F (1 + 2))
    (hX : X ∈ Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ (DVR.unary m) (ternFrame Q₀ ξ)) :
    isoStabMeasure Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso) (ternFrame Q₀ ξ) X =
      (((archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0)).map (stabFrameVecME X).symm).restrict
        (isoShellFrame Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso)
          (ternFrame Q₀ ξ) X) := by
  obtain ⟨a, ha⟩ := hX
  have hy : a • ξInf (cols (ternFrame Q₀ ξ).1 0) = X 0 := by
    rw [← ratAT_zero_eq_ξInf]; exact congrFun ha 0
  have hf : (fun h => (stabFrameVecME X).symm ((isoTernData Q₀ hQ hm ξ).conjHomAt a hy h)) =
      isoConj Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) a ha :=
    funext fun h => Subtype.ext ((isoTernData Q₀ hQ hm ξ).conjHomAt_apply a hy h)
  have hm1 : Measurable fun h => (stabFrameVecME X).symm ((isoTernData Q₀ hQ hm ξ).conjHomAt a hy h) :=
    (stabFrameVecME X).symm.measurable.comp ((isoTernData Q₀ hQ hm ξ).measurable_conjHomAt a hy)
  rw [isoStabMeasure_eq Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso) _ a ha,
    isoStabAt_eq, archFibrationNF_μH_eq_at Q₀ hQ hm _ (isoTernData Q₀ hQ hm ξ) a hy,
    Measure.map_map (stabFrameVecME X).symm.measurable ((isoTernData Q₀ hQ hm ξ).measurable_conjHomAt a hy)]
  have hmc := measurable_isoConj Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) a ha
  have e2 : (⇑(stabFrameVecME X).symm ∘ ⇑((isoTernData Q₀ hQ hm ξ).conjHomAt a hy)) =
      isoConj Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) a ha := hf
  rw [e2, isoStabBase, isoFrameLam_eq_lam Q₀ hQ hm ξ, Measure.map_smul _ hmc.aemeasurable]
  erw [Measure.map_smul _ hmc.aemeasurable]
  rw [Measure.restrict_smul]
  congr 1
  refine ((Measure.restrict_map hmc (measurableSet_isoShellFrame Q₀ hQ (DVR.unary m)
      (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso) (ternFrame Q₀ ξ) a ha)).trans ?_).symm
  exact congrArg (fun s => Measure.map _ (Measure.restrict _ s)) (preimage_isoShellFrame Q₀ hQ (DVR.unary m)
    (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso) (ternFrame Q₀ ξ) a ha)

/-- **The norm-one measure of representations of $\langle m\rangle$ in the normalization of `archFibrationNF`**, class
by class: the sum
over the $\Gamma_i$-orbits of representations $X$ (rational vectors $X_0$ of value $m$ in $M_i$) of
$\operatorname{vol}(\Gamma_{i,X}\backslash H_X)$ for the stabilizer measure of `archFibrationNF` restricted to the
norm-one shell. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (the excluded case, norm-one stabilizers; sphere normalization) [unverified]"]
theorem repMeasureIso_unary_eq (i : DC Q₀) :
    repMeasureIso Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso)
        ((ratFrameEquivRatSphere Q₀ m).symm ξ) i =
      repMeasureOf (unitGroup Q₀ i) (repsT Q₀ (DVR.unary m) i) fun X =>
        (((archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0)).map (stabFrameVecME X).symm).restrict
          (isoShellFrame Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso)
            (ternFrame Q₀ ξ) X) := by
  unfold repMeasureIso repMeasureOf
  refine tsum_congr fun q => ?_
  congr 1
  refine isoStabMeasure_unary_eq Q₀ hQ hm hiso ξ _ ?_
  obtain ⟨Ξ', hΞ'⟩ := exists_ratFrame_of_mem_repsT Q₀ m i (q.out : repsT Q₀ (DVR.unary m) i)
  obtain ⟨γ, hγ⟩ := FrameTowerAlg.exists_smul_eq_ratFrame Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ)
    (isoTower Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ)) (unary_nondegenerate hm) (by norm_num) Ξ'
  exact ⟨(γ : SOAdele Q₀).1, by rw [← hΞ', ← hγ, ratAT_smul]⟩

include hiso ξ in
/-- **The ternary isotropic numbers headline with the stabilizer measures of `archFibrationNF`** (every number field;
Siegel's excluded
case, $m^\perp$ isotropic): for a nondegenerate ternary $Q_0$ over $\mathcal O_F$ (any signature), $m\in\mathcal O_F\setminus0$
with a rational point $\xi$ on $Q_0 = m$ and $-2m\det H_{Q_0}$ a square in $F$,
$$2\,c_\infty(m)\sum_i\rho^1(M_i, m) = |d_F|^{-1}\,\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac1{N\mathfrak p}\Bigr)
  \cdot\sum_iv(M_i),$$
where $\rho^1(M_i, m) = \sum_{X}\operatorname{vol}(\Gamma_{i,X}\backslash H^1_X)$ is computed with the stabilizer
measures of `archFibrationNF`
(`archFibrationNF`) restricted to the norm-one shells (`repMeasureIso_unary_eq`). Derived from the forms headline at
$r = 1$ (via `siegelIndefinite_ternary_isotropic_uncond`). **Unconditional.** -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms; ternary forms, m⊥ isotropic (excluded case), regularized; sphere normalization [unverified]"]
theorem siegelIndefinite_ternary_isotropic_sphere_uncond :
    2 * (cInfNF (k := 2) (m : F) * ∑' i, repMeasureOf (unitGroup Q₀ i) (repsT Q₀ (DVR.unary m) i) fun X =>
        (((archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0)).map (stabFrameVecME X).symm).restrict
          (isoShellFrame Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (isSquare_deltaForms_unary hiso)
            (ternFrame Q₀ ξ) X)) =
      ENNReal.ofReal (ternaryIsoDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  rw [← siegelIndefinite_ternary_isotropic_uncond Q₀ hQ hm hiso ξ]
  simp only [repMeasureIso_unary_eq Q₀ hQ hm hiso ξ]

end Ternary

end QuadFormsKB.Tamagawa.Indefinite
