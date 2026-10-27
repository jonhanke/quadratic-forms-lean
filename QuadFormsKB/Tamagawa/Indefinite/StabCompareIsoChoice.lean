/-
# The norm-one stabilizer measures for arbitrary frame data

**Layer:** number fields. As in `IsoMeasures.lean` ($F$ a number field, $Q_0$ in $r + 2$ variables, $T_0$ of rank $r$, $\Xi$ a
rational frame, $\Xi^\perp$ isotropic), but with **arbitrary** algebraic frame data `D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)` and an
arbitrary isotropic vector $v$ of `D.Q''`, where the earlier development uses the chosen `isoTower` and `isoVec`.

**Defines**
* `isoFrameLamOf D` $=\prod_{w\mid\infty}|\det g_D|_w^{3}/c_F(2)$, `isoStabBaseOf D hv` $=\lambda_D\,\mu^{\mathrm{Tam}}_{Q''_D}|_{\text{shell}(v)}$,
  `isoStabMeasureOf D hv X` (its transport to $H_X$ by $h\mapsto a\,\iota_D(h)\,a^{-1}$, $a$ chosen), **`repMeasureIsoOf D hv i`**
  (the corresponding $\rho^1(M_i, T_0)$), and the shell `isoShellFrameOf D hv X` $\subseteq H_X$;
* for `isoTower`, `isoVec` these are the earlier definitions (`repMeasureIsoOf_isoTower`).

**Proves** (unconditional) for $r = 1$, ternary $Q_0$, $T_0 = \langle m\rangle$: **`isoStabMeasureOf_unary_eq`**: for every frame data
`D` and isotropic vector $v$, `isoStabMeasureOf D hv X` is the sphere-fibration stabilizer measure at $X_0$ (independent of `D` and $v$)
restricted to `isoShellFrameOf D hv X`. So the measures, hence the terms of $\rho^1$, depend on $(D, v)$ only through the
shell (`isoStabMeasureOf_unary_congr`).
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompareIso

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

/-! ### The definitions with explicit frame data -/

section Of

variable {F : Type} [Field F] [NumberField F] {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate)
  (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) (D : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1))
  {v : Fin 2 → F} (hv : IsIsoVec D.Q'' v)

open Classical in
/-- The scale $\lambda_D = \prod_{w\mid\infty}|\det g_D|_w^{3}/c_F(2)$ ($g_D = [\Xi\mid C_D]$), as `isoFrameLam`. -/
def isoFrameLamOf : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det| ^ (2 + 1)) *
    (∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖σC w (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det‖ ^ (2 * (2 + 1))) / cF F 2)

/-- The norm-one stabilizer measure at $\Xi$ for the frame data `D` and the isotropic vector $v$:
$\lambda_D\,\mu^{\mathrm{Tam}}_{Q''_D}$ restricted to $\{0\le\log|\chi_v|_\infty<1\}$, as `isoStabBase`. -/
def isoStabBaseOf : Measure (GInfSO D.Q'') :=
  isoFrameLamOf Q₀ hQ T₀ hT Ξ D • (muArchTamSO D.Q'' D.hQ'').restrict (isoShellInf D.Q'' D.hQ'' hv)

/-- $h\mapsto a\,\iota_D(h)\,a^{-1}$ into $H_X$, $a\,\Xi_\infty = X$. -/
def isoConjOf (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) (h : GInfSO D.Q'') :
    stabilizer (GInfSO Q₀) X :=
  ⟨a * D.ιInf h * a⁻¹, by
    show (a * D.ιInf h * a⁻¹) • X = X
    rw [← hX, mul_smul, mul_smul, inv_smul_smul, FrameTowerAlg.ιInf_smul_ratAT]⟩

theorem measurable_isoConjOf (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    Measurable (isoConjOf Q₀ hQ T₀ Ξ D a hX) :=
  (((measurable_const_mul a).comp D.measurable_ιInf).mul_const _).subtype_mk

open Classical in
/-- **The norm-one stabilizer measure for the frame data `D` and the isotropic vector $v$** at $X$ in the orbit of
$\Xi_\infty$ ($0$ elsewhere), as `isoStabMeasure`. -/
def isoStabMeasureOf (X : Fin r → VInf F (r + 2)) : Measure (stabilizer (GInfSO Q₀) X) :=
  if hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X then
    (isoStabBaseOf Q₀ hQ T₀ hT Ξ D hv).map (isoConjOf Q₀ hQ T₀ Ξ D hX.choose hX.choose_spec)
  else 0

/-- **Siegel's measure of representations, regularized, for the frame data `D` and the isotropic vector $v$**, as
`repMeasureIso`. -/
def repMeasureIsoOf (i : DC Q₀) : ℝ≥0∞ :=
  repMeasureOf (unitGroup Q₀ i) (repsT Q₀ T₀ i) (isoStabMeasureOf Q₀ hQ T₀ hT Ξ D hv)

open Classical in
/-- The norm-one shell in $H_X$ for `D` and $v$: $\{a\,\iota_D(h)\,a^{-1} : 0\le\log|\chi_v(h)|_\infty<1\}$ ($a$ chosen), $\emptyset$ off
the orbit of $\Xi_\infty$. -/
def isoShellFrameOf (X : Fin r → VInf F (r + 2)) : Set (stabilizer (GInfSO Q₀) X) :=
  if hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X then
    Subtype.val ⁻¹' ((fun h => hX.choose * D.ιInf h * hX.choose⁻¹) '' isoShellInf D.Q'' D.hQ'' hv)
  else ∅

/-- For the chosen frame data and isotropic vector these are the earlier definitions. -/
theorem repMeasureIsoOf_isoTower (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (i : DC Q₀) :
    repMeasureIsoOf Q₀ hQ T₀ hT Ξ (isoTower Q₀ hQ T₀ hT Ξ) (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ) i =
      repMeasureIso Q₀ hQ T₀ hT hiso Ξ i := by
  unfold repMeasureIsoOf repMeasureIso
  congr 1
  funext X
  unfold isoStabMeasureOf isoStabMeasure
  split_ifs with hX
  · exact (isoStabAt_eq Q₀ hQ T₀ hT hiso Ξ _ _).symm
  · rfl

theorem isoShellFrameOf_eq {X : Fin r → VInf F (r + 2)} (hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X) :
    isoShellFrameOf Q₀ hQ T₀ Ξ D hv X =
      Subtype.val ⁻¹' ((fun h => hX.choose * D.ιInf h * hX.choose⁻¹) '' isoShellInf D.Q'' D.hQ'' hv) := by
  rw [isoShellFrameOf, dite_eq_left_of_eq_true (eq_true hX)]

theorem measurableSet_isoShellFrameOf {X : Fin r → VInf F (r + 2)} (hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X) :
    MeasurableSet (isoShellFrameOf Q₀ hQ T₀ Ξ D hv X) := by
  rw [isoShellFrameOf_eq Q₀ hQ T₀ Ξ D hv hX]
  refine measurable_subtype_coe ?_
  have h1 := (FrameTowerAlg.measurableEmbedding_ιInf Q₀ hQ T₀ Ξ D).measurableSet_image'
    (measurableSet_isoShellInf D.Q'' D.hQ'' hv)
  have h2 := ((MeasurableEquiv.mulLeft hX.choose).trans (MeasurableEquiv.mulRight hX.choose⁻¹)).measurableSet_image.2 h1
  rw [← Set.image_comp] at h2
  exact h2

theorem preimage_isoShellFrameOf {X : Fin r → VInf F (r + 2)} (hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X) :
    isoConjOf Q₀ hQ T₀ Ξ D hX.choose hX.choose_spec ⁻¹' isoShellFrameOf Q₀ hQ T₀ Ξ D hv X =
      isoShellInf D.Q'' D.hQ'' hv := by
  rw [isoShellFrameOf_eq Q₀ hQ T₀ Ξ D hv hX]
  ext h
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨h', hh', e⟩
    have e' : D.ιInf h' = D.ιInf h := by
      have : hX.choose * D.ιInf h' * hX.choose⁻¹ = hX.choose * D.ιInf h * hX.choose⁻¹ := e
      simpa using this
    rwa [← FrameTowerAlg.ιInf_injective Q₀ hQ T₀ Ξ D e']
  · intro hh
    exact ⟨h, hh, rfl⟩

end Of

/-! ### Ternary forms: the measures do not depend on the frame data -/

section Ternary

variable {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
  (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) (D : FrameTowerAlg Q₀ hQ 2 (cols (ternFrame Q₀ ξ).1))
  {v : Fin 2 → F} (hv : IsIsoVec D.Q'' v)

theorem isoFrameLamOf_eq_lam :
    isoFrameLamOf Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) D =
      (D.toSplitDataInf hm (eval_ternFrame Q₀ ξ)).lam := by
  have hg : ((IsoAlg.towerAdapted Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D (unary_nondegenerate hm)).g :
      Matrix (Fin (1 + 2)) (Fin (1 + 2)) F) =
      ((D.toSplitDataInf hm (eval_ternFrame Q₀ ξ)).g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) := by
    rw [IsoAlg.towerAdapted_g_val, IsoAlg.adaptedMat_eq, FrameTowerAlg.toSplitDataInf_g, wittG_eq_splitMat_three]
  unfold isoFrameLamOf SplitDataInf.lam
  rw [hg]

/-- **The norm-one stabilizer measures do not depend on the frame data, up to the shell** (ternary $Q_0$,
$T_0 = \langle m\rangle$): for **every** algebraic frame data `D` of $\Xi$ and every isotropic vector $v$ of `D.Q''`, at every
$X$ in the orbit of $\Xi_\infty$, `isoStabMeasureOf D hv X` is the sphere-fibration stabilizer measure at $X_0$ (which involves neither `D`
nor $v$), carried to $H_X$, restricted to the shell `isoShellFrameOf D hv X`. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (norm-one stabilizers; independence of the frame data) [unverified]"]
theorem isoStabMeasureOf_unary_eq (X : Fin 1 → VInf F (1 + 2))
    (hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ (DVR.unary m) (ternFrame Q₀ ξ) = X) :
    isoStabMeasureOf Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) D hv X =
      (((archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0)).map (stabFrameVecME X).symm).restrict
        (isoShellFrameOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hv X) := by
  have ha := hX.choose_spec
  have hy : hX.choose • ξInf (cols (ternFrame Q₀ ξ).1 0) = X 0 := by
    rw [← ratAT_zero_eq_ξInf]; exact congrFun ha 0
  have hmc := measurable_isoConjOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hX.choose ha
  have e2 : (⇑(stabFrameVecME X).symm ∘ ⇑((D.toSplitDataInf hm (eval_ternFrame Q₀ ξ)).conjHomAt hX.choose hy)) =
      isoConjOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hX.choose ha :=
    funext fun h => Subtype.ext ((D.toSplitDataInf hm (eval_ternFrame Q₀ ξ)).conjHomAt_apply hX.choose hy h)
  rw [isoStabMeasureOf, dite_eq_left_of_eq_true (eq_true hX),
    archFibrationNF_μH_eq_at Q₀ hQ hm _ (D.toSplitDataInf hm (eval_ternFrame Q₀ ξ)) hX.choose hy,
    Measure.map_map (stabFrameVecME X).symm.measurable
      ((D.toSplitDataInf hm (eval_ternFrame Q₀ ξ)).measurable_conjHomAt hX.choose hy),
    e2, isoStabBaseOf, isoFrameLamOf_eq_lam Q₀ hQ hm ξ D, Measure.map_smul _ hmc.aemeasurable]
  erw [Measure.map_smul _ hmc.aemeasurable]
  rw [Measure.restrict_smul]
  congr 1
  refine ((Measure.restrict_map hmc (measurableSet_isoShellFrameOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hv
    hX)).trans ?_).symm
  exact congrArg (fun s => Measure.map _ (Measure.restrict _ s))
    (preimage_isoShellFrameOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hv hX)

/-- Consequently, two choices of frame data and isotropic vector with the same shell at $X$ give the same norm-one
stabilizer measure at $X$. -/
theorem isoStabMeasureOf_unary_congr (D' : FrameTowerAlg Q₀ hQ 2 (cols (ternFrame Q₀ ξ).1)) {v' : Fin 2 → F}
    (hv' : IsIsoVec D'.Q'' v') (X : Fin 1 → VInf F (1 + 2))
    (hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ (DVR.unary m) (ternFrame Q₀ ξ) = X)
    (hS : isoShellFrameOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D hv X =
      isoShellFrameOf Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) D' hv' X) :
    isoStabMeasureOf Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) D hv X =
      isoStabMeasureOf Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (ternFrame Q₀ ξ) D' hv' X := by
  rw [isoStabMeasureOf_unary_eq Q₀ hQ hm ξ D hv X hX, isoStabMeasureOf_unary_eq Q₀ hQ hm ξ D' hv' X hX, hS]

end Ternary

end QuadFormsKB.Tamagawa.Indefinite
