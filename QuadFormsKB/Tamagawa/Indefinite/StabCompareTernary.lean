/-
# Ternary forms: the two measures of representations agree, class by class

**Layer:** number fields. $F$ a number field, $Q_0$ a nondegenerate ternary form over $\mathcal O_F$ (any signature),
$m\in\mathcal O_F$, $m\ne0$, represented by $Q_0$ over $F$ (a rational point $\xi$), $m^\perp$ anisotropic
($-2m\det H_{Q_0}$ not a square in $F$). The ternary numbers headline `siegelIndefinite_ternary_uncond` measures the
representations of $m$ as $1$-frames with the stabilizer measures of the frame fibration `frameArchFibrationRank2`; the
other numbers headlines use the sphere fibration `archFibrationNF`.

**Proves** (unconditional)
* `stabMeasureAt_eq_map_of`, `covolume_stabArith_conj`: generic facts on the stabilizer measures at $a\,y_0$ and on the
  terms of a measure of representations;
* `map_frameArchFibrationRank2_μH`: at every $X = a\,\Xi_\infty$ in the orbit of $\Xi_\infty$, the frame-fibration stabilizer measure is
  the sphere-fibration one at $X_0$ (via $H_X = H_{X_0}$), by `archFibrationNF_μH_eq` with the frame data
  (`toSplitDataInf`);
* **`repMeasureT_frameArchFibrationRank2_unary`**: the frame-fibration $\rho(M_i,\langle m\rangle)$ = the
  sphere-fibration
  $\rho(M_i, m)$ for every class $i$;
* **`siegelIndefinite_ternary_sphere_uncond`**: the ternary headline with the sphere-fibration measures of
  representations,
  $$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-1}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac{\chi(\mathfrak p)}{N\mathfrak p}\Bigr)
    \cdot\sum_iv(M_i),$$
  derived from the forms headline `siegelIndefiniteForms_rank2_uncond` at $r = 1$.
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompareFrames
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernary

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil LocalDensity

/-! ### Generic facts -/

section Generic

variable {A H : Type*} [Group A] [Group H] [MeasurableSpace A] [MeasurableSpace H] [MeasurableMul A]
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T] {ι : H →* A} {τ : T → Y} {y₀ : Y}

/-- The stabilizer measure at $y = a\,y_0$ is the image of $\mu'$ under any map with values $a\,\iota(h)\,a^{-1}$. -/
theorem stabMeasureAt_eq_map_of [MeasurableInv A] (C : OrbitCoord ι τ y₀)
    (hst : ∀ g : A, g • y₀ = y₀ → ∃ h, ι h = g) (hι : MeasurableEmbedding ι) (μ' : Measure H) (a : A) {y : Y}
    (hy : a • y₀ = y) (f : H → stabilizer A y) (hf : ∀ h, (f h : A) = a * ι h * a⁻¹) :
    stabMeasureAt C hst hι μ' a hy = μ'.map f := by
  subst hy
  have : (conjStabME C hst hι a : H → stabilizer A (a • y₀)) = f :=
    funext fun h => Subtype.ext ((conjStabME_apply C hst hι a h).trans (hf h).symm)
  rw [stabMeasureAt, this]

end Generic

section Covol

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] [MeasurableInv A]
  {Y Y' : Type*} [MulAction A Y] [MulAction A Y']

/-- **The terms of a measure of representations under conjugation**: if $\varphi : H_y\cong H_{y'}$ is
$s\mapsto\gamma s\gamma^{-1}$ with $\gamma\in\Gamma'$ (e.g. $\gamma = 1$ and $H_y = H_{y'}$) and carries $\mu$ to $\mu'$, then
$\operatorname{vol}(\Gamma'_y\backslash H_y,\mu) = \operatorname{vol}(\Gamma'_{y'}\backslash H_{y'},\mu')$. -/
theorem covolume_stabArith_conj (Γ' : Subgroup A) [Countable Γ'] (y : Y) (y' : Y') (γ : A) (hγ : γ ∈ Γ')
    (φ : stabilizer A y ≃* stabilizer A y') (hφ : ∀ s, (φ s : A) = γ * s * γ⁻¹)
    (μ : Measure (stabilizer A y)) (μ' : Measure (stabilizer A y'))
    [SMulInvariantMeasure (stabArith Γ' y) (stabilizer A y) μ]
    [SMulInvariantMeasure (stabArith Γ' y') (stabilizer A y') μ'] (hμ : μ.map φ = μ') :
    covolume (stabArith Γ' y) (stabilizer A y) μ = covolume (stabArith Γ' y') (stabilizer A y') μ' := by
  have hc : ∀ (z : Y) , Countable (stabArith Γ' z) := fun z =>
    Function.Injective.countable (f := fun s : stabArith Γ' z => (⟨((s : stabilizer A z) : A), s.2⟩ : Γ'))
      fun s t hst => Subtype.ext (Subtype.ext (congrArg (fun u : Γ' => (u : A)) hst))
  have hc' : ∀ (z : Y') , Countable (stabArith Γ' z) := fun z =>
    Function.Injective.countable (f := fun s : stabArith Γ' z => (⟨((s : stabilizer A z) : A), s.2⟩ : Γ'))
      fun s t hst => Subtype.ext (Subtype.ext (congrArg (fun u : Γ' => (u : A)) hst))
  haveI := hc y
  haveI := hc' y'
  have hφs : ∀ s, (φ.symm s : A) = γ⁻¹ * s * γ := fun s => by
    have h := hφ (φ.symm s)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]; group
  have hm : Measurable φ := by
    have e : (φ : stabilizer A y → stabilizer A y') = fun s => ⟨(φ s : A), (φ s).2⟩ := rfl
    rw [e]
    refine Measurable.subtype_mk ?_
    have e' : (fun s : stabilizer A y => (φ s : A)) = fun s : stabilizer A y => γ * (s : A) * γ⁻¹ := funext hφ
    rw [e']
    exact ((measurable_const_mul γ).comp measurable_subtype_coe).mul_const _
  have hm' : Measurable φ.symm := by
    have e : (φ.symm : stabilizer A y' → stabilizer A y) = fun s => ⟨(φ.symm s : A), (φ.symm s).2⟩ := rfl
    rw [e]
    refine Measurable.subtype_mk ?_
    have e' : (fun s : stabilizer A y' => (φ.symm s : A)) = fun s : stabilizer A y' => γ⁻¹ * (s : A) * γ := funext hφs
    rw [e']
    exact ((measurable_const_mul γ⁻¹).comp measurable_subtype_coe).mul_const _
  haveI := measurableMul_subgroup (stabilizer A y)
  haveI := measurableMul_subgroup (stabilizer A y')
  refine covolume_restrict_eq_of_map _ _ φ hm hm' ?_ μ μ' hμ
  ext t
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [hφ]
    exact Γ'.mul_mem (Γ'.mul_mem hγ hs) (Γ'.inv_mem hγ)
  · intro ht
    refine ⟨φ.symm t, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [hφs]
    exact Γ'.mul_mem (Γ'.mul_mem (Γ'.inv_mem hγ) ht) hγ

/-- Conjugation by $\gamma$: $H_y\cong H_{\gamma y}$, $s\mapsto\gamma s\gamma^{-1}$. -/
def stabConj (γ : A) (y : Y) : stabilizer A y ≃* stabilizer A (γ • y) where
  toFun s := ⟨γ * s * γ⁻¹, by
    show (γ * s * γ⁻¹) • γ • y = γ • y
    rw [mul_smul, mul_smul, inv_smul_smul, s.2]⟩
  invFun s := ⟨γ⁻¹ * s * γ, by
    show (γ⁻¹ * s * γ) • y = y
    rw [mul_smul, mul_smul, s.2, inv_smul_smul]⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem coe_stabConj (γ : A) (y : Y) (s : stabilizer A y) : (stabConj γ y s : A) = γ * s * γ⁻¹ := rfl

theorem measurable_stabConj (γ : A) (y : Y) : Measurable (stabConj γ y) :=
  (((measurable_const_mul γ).comp measurable_subtype_coe).mul_const _).subtype_mk

end Covol

/-! ### The ternary anisotropic case -/

section Ternary

variable {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
  (hm : (m : F) ≠ 0) (hW : ¬ IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
  (ξ : RatSphere Q₀ (m : F))

/-- The rational $1$-frame of $\xi$. -/
abbrev ternFrame : RatFrame Q₀ (DVR.unary m) := (ratFrameEquivRatSphere Q₀ m).symm ξ

/-- The chosen frame data for the $1$-frame of $\xi$. -/
abbrev ternTower : FrameTower Q₀ hQ 2 (cols (ternFrame Q₀ ξ).1) :=
  chosenTowerRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW) (ternFrame Q₀ ξ)

theorem eval_ternFrame : (Q₀.map (algebraMap (𝓞 F) F)).eval (cols (ternFrame Q₀ ξ).1 0) = (m : F) := by
  exact ξ.2

/-- The frame data at infinity for $\xi$. -/
abbrev ternData : SplitDataInf (k := 2) Q₀ (m : F) (cols (ternFrame Q₀ ξ).1 0) :=
  (ternTower Q₀ hQ hm hW ξ).toAlg.toSplitDataInf hm (eval_ternFrame Q₀ ξ)

/-- The scale $\lambda$ = `frameLamRank2` is the scale of the frame data at infinity. -/
theorem frameLamRank2_eq_lam :
    frameLamRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW) (ternFrame Q₀ ξ) =
      (ternData Q₀ hQ hm hW ξ).lam := by
  have hg : ((towerAdapted Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) (ternTower Q₀ hQ hm hW ξ) (unary_nondegenerate hm)).g :
      Matrix (Fin (1 + 2)) (Fin (1 + 2)) F) = ((ternData Q₀ hQ hm hW ξ).g : Matrix (Fin (2 + 1)) (Fin (2 + 1)) F) := by
    rw [towerAdapted_g_val, adaptedMat_eq, FrameTowerAlg.toSplitDataInf_g, wittG_eq_splitMat_three]
    rfl
  unfold frameLamRank2 SplitDataInf.lam
  rw [hg]

/-- **The frame-fibration stabilizer measure is the sphere-fibration one**: at every $X = a\,\Xi_\infty$, transported
by $H_X = H_{X_0}$. -/
theorem map_frameArchFibrationRank2_μH (X : Fin 1 → VInf F (1 + 2))
    (hX : X ∈ Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ (DVR.unary m) (ternFrame Q₀ ξ)) :
    ((frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
        (ternFrame Q₀ ξ)).μH X).map (stabFrameVecME X) =
      (archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)).μH (X 0) := by
  have ha := hX.choose_spec
  set a := hX.choose
  have hy : a • ξInf (cols (ternFrame Q₀ ξ).1 0) = X 0 := by
    rw [← ratAT_zero_eq_ξInf]; exact congrFun ha 0
  have hf : ∀ h, (((stabFrameVecME X).symm ((ternData Q₀ hQ hm hW ξ).conjHomAt a hy h) : stabilizer (GInfSO Q₀) X) : GInfSO Q₀) =
      a * (ternTower Q₀ hQ hm hW ξ).ιInf h * a⁻¹ := fun h => (ternData Q₀ hQ hm hW ξ).conjHomAt_apply a hy h
  have h1 : (frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
        (ternFrame Q₀ ξ)).μH X =
      frameLamRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
        (ternFrame Q₀ ξ) • (muArchTamSO (ternTower Q₀ hQ hm hW ξ).Q'' (ternTower Q₀ hQ hm hW ξ).hQ'').map
          (fun h => (stabFrameVecME X).symm ((ternData Q₀ hQ hm hW ξ).conjHomAt a hy h)) := by
    haveI := sigmaFinite_frameσA Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) (ternTower Q₀ hQ hm hW ξ)
    show _ • (frameArchFibTam Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ) (ternTower Q₀ hQ hm hW ξ)).μH X = _
    rw [frameArchFibTam, archFibrationOfCoord_μH _ _ _ _ _ _ _ hX]
    exact congrArg _ (stabMeasureAt_eq_map_of _ _ _ _ _ _ _ hf)
  have hm1 : Measurable fun h => (stabFrameVecME X).symm ((ternData Q₀ hQ hm hW ξ).conjHomAt a hy h) :=
    (stabFrameVecME X).symm.measurable.comp ((ternData Q₀ hQ hm hW ξ).measurable_conjHomAt a hy)
  rw [h1, Measure.map_smul, archFibrationNF_μH_eq_at Q₀ hQ hm _ (ternData Q₀ hQ hm hW ξ) a hy, Measure.map_smul,
    frameLamRank2_eq_lam]
  congr 1
  refine (Measure.map_map (stabFrameVecME X).measurable hm1).trans ?_
  · exact congrArg (fun f => Measure.map f _) (funext fun h => (stabFrameVecME X).apply_symm_apply _)
  all_goals first
    | exact hm
    | exact hW
    | exact ((ternData Q₀ hQ hm hW ξ).measurable_conjHomAt a hy).aemeasurable
    | exact (stabFrameVecME X).measurable.aemeasurable

include hQ hm hW in
/-- Every representation of $\langle m\rangle$ lies in the $G_\infty$-orbit of $\Xi_\infty$ (Witt's theorem over $F$). -/
theorem mem_orbit_ternFrame (i : DC Q₀) (X : repsT Q₀ (DVR.unary m) i) :
    (X : Fin 1 → VInf F (1 + 2)) ∈ Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ (DVR.unary m) (ternFrame Q₀ ξ) := by
  obtain ⟨Ξ', hΞ'⟩ := exists_ratFrame_of_mem_repsT Q₀ m i X
  obtain ⟨γ, hγ⟩ := FrameTowerAlg.exists_smul_eq_ratFrame Q₀ hQ (DVR.unary m) (ternFrame Q₀ ξ)
    (ternTower Q₀ hQ hm hW ξ).toAlg (unary_nondegenerate hm) (by norm_num) Ξ'
  exact ⟨(γ : SOAdele Q₀).1, by rw [← hΞ', ← hγ, ratAT_smul]⟩

/-- **The ternary measures of representations for the two fibrations agree, class by class**: for every class $i$,
$\rho(M_i,\langle m\rangle)$ for `frameArchFibrationRank2` (representations of $m$ as $1$-frames) equals $\rho(M_i, m)$ for
the sphere fibration `archFibrationNF`. -/
@[kb "siegel1936" "Indefinite quadratische Formen; Darstellungsmaß (ternary forms; the frame and sphere normalizations agree) [unverified]"]
theorem repMeasureT_frameArchFibrationRank2_unary (i : DC Q₀) :
    repMeasureT Q₀ (DVR.unary m) hQ (frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
        (not_isSquare_deltaForms_unary hW) ((ratFrameEquivRatSphere Q₀ m).symm ξ)) i =
      repMeasure Q₀ hQ (m : F) (archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)) i := by
  set 𝔉T := frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
    (ternFrame Q₀ ξ)
  set 𝔉S := archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)
  have := countable_GammaSOAdele Q₀
  haveI : Countable (unitGroup Q₀ i) := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  unfold repMeasureT repMeasure
  refine repMeasureOf_congr _ _ _ (repsFrameVec Q₀ m i) (repsFrameVec_smul Q₀ m i) _ _ ?_ ?_
  · intro X
    have hX := mem_orbit_ternFrame Q₀ hQ hm hW ξ i X
    have key : ∀ y' (h : (X : Fin 1 → VInf F (1 + 2)) 0 = y'),
        covolume (stabArith (unitGroup Q₀ i) (X : Fin 1 → VInf F (1 + 2)))
          (stabilizer (GInfSO Q₀) (X : Fin 1 → VInf F (1 + 2))) (𝔉T.μH X) =
        covolume (stabArith (unitGroup Q₀ i) y') (stabilizer (GInfSO Q₀) y') (𝔉S.μH y') := by
      rintro _ rfl
      haveI := 𝔉T.leftInv (X : Fin 1 → VInf F (1 + 2))
      haveI := 𝔉S.leftInv ((X : Fin 1 → VInf F (1 + 2)) 0)
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₀ i) (X : Fin 1 → VInf F (1 + 2)))
        (𝔉T.μH X)
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₀ i) ((X : Fin 1 → VInf F (1 + 2)) 0))
        (𝔉S.μH ((X : Fin 1 → VInf F (1 + 2)) 0))
      exact covolume_stabArith_conj _ _ _ 1 (Subgroup.one_mem _) (stabFrameVec (X : Fin 1 → VInf F (1 + 2)))
        (fun s => by simp [coe_stabFrameVec]) _ _ (map_frameArchFibrationRank2_μH Q₀ hQ hm hW ξ _ hX)
    exact key _ (repsFrameVec_apply Q₀ m i X).symm
  · intro y γ
    obtain ⟨a, ha⟩ : ∃ a : GInfSO Q₀, a • ξInf (cols (ternFrame Q₀ ξ).1 0) = (y : VInf F (1 + 2)) := by
      obtain ⟨a, ha⟩ := mem_orbit_ternFrame Q₀ hQ hm hW ξ i ((repsFrameVec Q₀ m i).symm y)
      refine ⟨a, ?_⟩
      have h1 := congrFun ha 0
      have h2 := repsFrameVec_apply Q₀ m i ((repsFrameVec Q₀ m i).symm y)
      rw [Equiv.apply_symm_apply] at h2
      rw [← ratAT_zero_eq_ξInf, h2]
      exact h1
    have key : ∀ y'' (h : (γ : GInfSO Q₀) • (y : VInf F (1 + 2)) = y''),
        covolume (stabArith (unitGroup Q₀ i) y'') (stabilizer (GInfSO Q₀) y'') (𝔉S.μH y'') =
        covolume (stabArith (unitGroup Q₀ i) (y : VInf F (1 + 2))) (stabilizer (GInfSO Q₀) (y : VInf F (1 + 2)))
          (𝔉S.μH y) := by
      rintro _ rfl
      haveI := 𝔉S.leftInv (y : VInf F (1 + 2))
      haveI := 𝔉S.leftInv ((γ : GInfSO Q₀) • (y : VInf F (1 + 2)))
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₀ i) (y : VInf F (1 + 2))) (𝔉S.μH y)
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₀ i) ((γ : GInfSO Q₀) • (y : VInf F (1 + 2))))
        (𝔉S.μH ((γ : GInfSO Q₀) • (y : VInf F (1 + 2))))
      have hγa : ((γ : GInfSO Q₀) * a) • ξInf (cols (ternFrame Q₀ ξ).1 0) = (γ : GInfSO Q₀) • (y : VInf F (1 + 2)) := by
        rw [mul_smul, ha]
      refine (covolume_stabArith_conj _ _ _ (γ : GInfSO Q₀) γ.2 (stabConj (γ : GInfSO Q₀) (y : VInf F (1 + 2)))
        (coe_stabConj _ _) _ _ ?_).symm
      rw [archFibrationNF_μH_eq_at Q₀ hQ hm _ (ternData Q₀ hQ hm hW ξ) a ha,
        archFibrationNF_μH_eq_at Q₀ hQ hm _ (ternData Q₀ hQ hm hW ξ) _ hγa, Measure.map_smul, Measure.map_smul,
        Measure.map_map (measurable_stabConj _ _) ((ternData Q₀ hQ hm hW ξ).measurable_conjHomAt a ha)]
      refine Eq.trans ?_ (Measure.map_smul _ ((ternData Q₀ hQ hm hW ξ).measurable_conjHomAt _ hγa).aemeasurable).symm
      refine congrArg (fun ν => (ternData Q₀ hQ hm hW ξ).lam • ν) (congrArg (fun f => Measure.map f _) ?_)
      funext h
      apply Subtype.ext
      · simp only [Function.comp_apply, coe_stabConj, SplitDataInf.conjHomAt_apply, mul_assoc, _root_.mul_inv_rev]
      · exact (measurable_stabConj _ _).aemeasurable
      · exact ((ternData Q₀ hQ hm hW ξ).measurable_conjHomAt a ha).aemeasurable
    exact key _ rfl

include hW ξ in
/-- **The ternary numbers headline in the sphere normalization** (every number field; $m^\perp$ anisotropic): for a
nondegenerate ternary $Q_0$ over $\mathcal O_F$ (any signature), $m\in\mathcal O_F\setminus0$ with a rational point $\xi$
on $Q_0 = m$, and $-2m\det H_{Q_0}$ not a square in $F$,
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-1}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac{\chi(\mathfrak p)}{N\mathfrak p}\Bigr)
  \cdot\sum_iv(M_i),$$
$c_\infty(m)$ = `cInfNF m`, $\rho(M_i, m)$ = `repMeasure` for the sphere fibration `archFibrationNF` (the stabilizer
measures of the numbers headlines `siegelIndefinite_uncond`), $\chi(\mathfrak p) = (-2m\det H_{Q_0}/\mathfrak p)$. Derived from
the forms headline at $r = 1$ (`siegelIndefiniteForms_rank2_uncond`, via `siegelIndefinite_ternary_uncond`) and
`repMeasureT_frameArchFibrationRank2_unary`. **Unconditional.** -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; ternary forms, numbers, sphere normalization; every number field) [unverified]"]
theorem siegelIndefinite_ternary_sphere_uncond :
    cInfNF (k := 2) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (archFibrationNF (k := 2) Q₀ hQ hm (by norm_num)) i =
      ENNReal.ofReal (ternaryDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  rw [← siegelIndefinite_ternary_uncond Q₀ hQ hm hW ξ]
  simp only [repMeasureT_frameArchFibrationRank2_unary Q₀ hQ hm hW ξ]

end Ternary

end QuadFormsKB.Tamagawa.Indefinite
