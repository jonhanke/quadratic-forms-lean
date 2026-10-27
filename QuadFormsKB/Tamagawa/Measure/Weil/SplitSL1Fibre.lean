import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Measure

/-!
# The fibres of $\operatorname{nrd}$ over a box, for split $D$

**Layer:** $F$ a number field, $a, b\in F^\times$, $x, y\in F$ with $x^2 - ay^2 = b$; $\Phi$ = `quatAdeleMatEquiv`,
$\psi$ = `sl1SplitEquiv`.

* `matUnitsEquiv`: $\Phi$ on units, $(D\otimes\mathbb A)^\times\cong\mathrm{GL}_2(\mathbb A_F)$.
* `sigmaA q` $=\operatorname{diag}(1, q)$, a section of $\det$; `nrdPos_sigmaQ`: $\operatorname{nrd}(\Phi^{-1}\sigma(q)) = q$.
* `boxM W` $=\{g : g_f, g_f^{-1}\in M_2(\hat{\mathcal O}),\ g_\infty\in W\}$.
* **`fibre_boxM`**: for $h\in\mathrm{SL}_2(\mathbb A_F)$, $\sigma(q)h\in$ `boxM W` iff $q_f\in\hat{\mathcal O}^\times$,
  $h_f\in\mathrm{SL}_2(\hat{\mathcal O})$ and $\sigma(q_\infty)h_\infty\in W$.
-/

open MeasureTheory Measure Set NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### $\Phi$ on units and the section $\sigma$ -/

section Phi

variable {a b x y : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b)

/-- $\Phi$ on units: $(D\otimes\mathbb A)^\times\cong\mathrm{GL}_2(\mathbb A_F)$. -/
def matUnitsEquiv : (QuatAdele a b)ˣ ≃ₜ* (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ :=
  unitsContinuousMulEquiv (quatAdeleMatEquiv ha0 hb0 h).toRingEquiv (continuous_quatAdeleMatEquiv ha0 hb0 h)
    (continuous_quatAdeleMatEquiv_symm ha0 hb0 h)

@[simp] theorem coe_matUnitsEquiv (u : (QuatAdele a b)ˣ) :
    ((matUnitsEquiv ha0 hb0 h u : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) : Matrix (Fin 2) (Fin 2) (Adeles F)) =
      quatAdeleMatEquiv ha0 hb0 h (u : QuatAdele a b) := rfl

theorem nrdUnit_eq_det (u : (QuatAdele a b)ˣ) :
    ((nrdUnit u : (Adeles F)ˣ) : Adeles F) =
      ((matUnitsEquiv ha0 hb0 h u : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) : Matrix (Fin 2) (Fin 2) (Adeles F)).det := by
  rw [coe_matUnitsEquiv, det_quatAdeleMatEquiv, nrdUnit_val]

end Phi

/-- The section $\sigma(q) = \operatorname{diag}(1, q)$ of $\det : \mathrm{GL}_2(\mathbb A_F)\to\mathbb A_F^\times$. -/
def sigmaA (q : (Adeles F)ˣ) : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ where
  val := !![1, 0; 0, (q : Adeles F)]
  inv := !![1, 0; 0, ((q⁻¹ : (Adeles F)ˣ) : Adeles F)]
  val_inv := by
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_sigmaA (q : (Adeles F)ˣ) :
    ((sigmaA q : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) : Matrix (Fin 2) (Fin 2) (Adeles F)).det = q := by
  simp [sigmaA, Matrix.det_fin_two_of]

section Phi2

variable {a b x y : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b)

/-- The lift $\Phi^{-1}\sigma(q)$ of $q\in A_+$ to $(D\otimes\mathbb A)^\times$. -/
def sigmaQ (q : (Adeles F)ˣ) : (QuatAdele a b)ˣ := (matUnitsEquiv ha0 hb0 h).symm (sigmaA q)

theorem nrdUnit_sigmaQ (q : (Adeles F)ˣ) : nrdUnit (sigmaQ ha0 hb0 h q : (QuatAdele a b)ˣ) = q := by
  apply Units.ext
  rw [nrdUnit_eq_det ha0 hb0 h, sigmaQ, ContinuousMulEquiv.apply_symm_apply, det_sigmaA]

theorem nrdPos_sigmaQ (q : posA a b) : nrdPos a b (sigmaQ ha0 hb0 h (q : (Adeles F)ˣ)) = q :=
  Subtype.ext (nrdUnit_sigmaQ ha0 hb0 h q)

end Phi2

/-! ### The box and its fibres -/

/-- $g\in M_2(\mathbb A_F)$ has finite part in $M_2(\hat{\mathcal O})$. -/
def FinInt (g : Matrix (Fin 2) (Fin 2) (Adeles F)) : Prop := ∀ i j, (g i j).2 ∈ OHat

/-- The archimedean part of $g\in M_2(\mathbb A_F)$. -/
def archM (g : Matrix (Fin 2) (Fin 2) (Adeles F)) : Matrix (Fin 2) (Fin 2) (mixedSpace F) := g.map Prod.fst

theorem archM_mul (g g' : Matrix (Fin 2) (Fin 2) (Adeles F)) : archM (g * g') = archM g * archM g' :=
  (RingHom.mapMatrix (RingHom.fst (mixedSpace F) AF)).map_mul g g'

/-- **The box** $\{g\in\mathrm{GL}_2(\mathbb A_F) : g_f, g_f^{-1}\in M_2(\hat{\mathcal O}),\ g_\infty\in W\}$. -/
def boxM (W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) : Set (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ :=
  {g | FinInt (g : Matrix (Fin 2) (Fin 2) (Adeles F)) ∧ FinInt ((g⁻¹ : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) :
    Matrix (Fin 2) (Fin 2) (Adeles F)) ∧ archM (g : Matrix (Fin 2) (Fin 2) (Adeles F)) ∈ W}

theorem OHat_mul {u w : AF} (hu : u ∈ OHat) (hw : w ∈ OHat) : u * w ∈ OHat := fun v => mul_mem (hu v) (hw v)
theorem OHat_add {u w : AF} (hu : u ∈ OHat) (hw : w ∈ OHat) : u + w ∈ OHat := fun v => add_mem (hu v) (hw v)
theorem OHat_neg {u : AF} (hu : u ∈ OHat) : -u ∈ OHat := fun v => neg_mem (hu v)
theorem OHat_sub {u w : AF} (hu : u ∈ OHat) (hw : w ∈ OHat) : u - w ∈ OHat := fun v => sub_mem (hu v) (hw v)

/-- $\sigma(q)$ as a matrix. -/
theorem coe_sigmaA (q : (Adeles F)ˣ) :
    ((sigmaA q : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) : Matrix (Fin 2) (Fin 2) (Adeles F)) =
      !![1, 0; 0, (q : Adeles F)] := rfl

theorem coe_sigmaA_inv (q : (Adeles F)ˣ) :
    (((sigmaA q)⁻¹ : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) : Matrix (Fin 2) (Fin 2) (Adeles F)) =
      !![1, 0; 0, ((q⁻¹ : (Adeles F)ˣ) : Adeles F)] := rfl

/-- **The fibre of the box over $q$**: $\sigma(q)h\in$ `boxM W` iff $q_f\in\hat{\mathcal O}^\times$,
$h_f\in\mathrm{SL}_2(\hat{\mathcal O})$ and $\sigma(q_\infty)h_\infty\in W$. -/
theorem sigmaA_mul_mem_boxM_iff (W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) (q : (Adeles F)ˣ)
    (g : SL2A F) :
    sigmaA q * Matrix.SpecialLinearGroup.toGL g ∈ boxM W ↔
      finPart q ∈ OHatUnits F ∧ g ∈ intFin F ∧ !![1, 0; 0, (q : Adeles F).1] * archPart g ∈ W := by
  set G : Matrix (Fin 2) (Fin 2) (Adeles F) := (g : Matrix (Fin 2) (Fin 2) (Adeles F))
  have hdet : G.det = 1 := g.2
  have hval : ((sigmaA q * Matrix.SpecialLinearGroup.toGL g : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) :
      Matrix (Fin 2) (Fin 2) (Adeles F)) = !![1, 0; 0, (q : Adeles F)] * G := rfl
  have hinv : (((sigmaA q * Matrix.SpecialLinearGroup.toGL g)⁻¹ : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) :
      Matrix (Fin 2) (Fin 2) (Adeles F)) = G.adjugate * !![1, 0; 0, ((q⁻¹ : (Adeles F)ˣ) : Adeles F)] := by
    rw [mul_inv_rev, Units.val_mul, coe_sigmaA_inv]
    rfl
  have harch : archM (!![1, 0; 0, (q : Adeles F)] * G) = !![1, 0; 0, (q : Adeles F).1] * archPart g := by
    rw [archM_mul]
    congr 1
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hP : !![1, 0; 0, (q : Adeles F)] * G = !![G 0 0, G 0 1; (q : Adeles F) * G 1 0, (q : Adeles F) * G 1 1] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hPi : G.adjugate * !![1, 0; 0, ((q⁻¹ : (Adeles F)ˣ) : Adeles F)] =
      !![G 1 1, -G 0 1 * ((q⁻¹ : (Adeles F)ˣ) : Adeles F); -G 1 0, G 0 0 * ((q⁻¹ : (Adeles F)ˣ) : Adeles F)] := by
    rw [Matrix.adjugate_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hP] at harch
  simp only [boxM, Set.mem_ofPred_eq, hval, hinv, hP, hPi, harch, FinInt, Fin.forall_fin_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Fin.isValue, Prod.snd_mul, Prod.snd_neg]
  have hq : ((q : Adeles F) * ((q⁻¹ : (Adeles F)ˣ) : Adeles F)) = 1 := q.mul_inv
  have hq2 : (q : Adeles F).2 * ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2 = 1 := by
    rw [← Prod.snd_mul, hq, Prod.snd_one]
  have hdet2 : (G 0 0).2 * (G 1 1).2 - (G 0 1).2 * (G 1 0).2 = 1 := by
    rw [← Prod.snd_mul, ← Prod.snd_mul, ← Prod.snd_sub, ← Matrix.det_fin_two, hdet, Prod.snd_one]
  have hfin : finPart q ∈ OHatUnits F ↔ (q : Adeles F).2 ∈ OHat ∧ ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2 ∈ OHat :=
    Iff.rfl
  rw [hfin]
  constructor
  · rintro ⟨⟨⟨h00, h01⟩, h10, h11⟩, ⟨⟨k00, k01⟩, k10, k11⟩, h3⟩
    have hqf : (q : Adeles F).2 ∈ OHat := by
      have := OHat_sub (OHat_mul h00 h11) (OHat_mul h01 h10)
      have e : (G 0 0).2 * ((q : Adeles F).2 * (G 1 1).2) - (G 0 1).2 * ((q : Adeles F).2 * (G 1 0).2) =
          (q : Adeles F).2 := by linear_combination (q : Adeles F).2 * hdet2
      rwa [e] at this
    have hqi : ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2 ∈ OHat := by
      have := OHat_sub (OHat_mul k00 k11) (OHat_mul k01 k10)
      have e : (G 1 1).2 * ((G 0 0).2 * ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2) -
          (-(G 0 1).2 * ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2) * (-(G 1 0).2) =
          ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2 := by linear_combination ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2 * hdet2
      rwa [e] at this
    refine ⟨⟨hqf, hqi⟩, fun i j => ?_, h3⟩
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · have := OHat_mul hqi h10
      rwa [← mul_assoc, mul_comm ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2, hq2, one_mul] at this
    · have := OHat_mul hqi h11
      rwa [← mul_assoc, mul_comm ((q⁻¹ : (Adeles F)ˣ) : Adeles F).2, hq2, one_mul] at this
  · rintro ⟨⟨hqf, hqi⟩, hg, h3⟩
    exact ⟨⟨⟨hg 0 0, hg 0 1⟩, OHat_mul hqf (hg 1 0), OHat_mul hqf (hg 1 1)⟩,
      ⟨⟨hg 1 1, OHat_mul (OHat_neg (hg 0 1)) hqi⟩, OHat_neg (hg 1 0), OHat_mul (hg 0 0) hqi⟩, h3⟩

/-! ### The fibred measure of the box -/

section FibMeas

variable {a b x y : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b)

/-- The box $\Phi^{-1}(\text{`boxM W`})\subseteq(D\otimes\mathbb A)^\times$. -/
def quatBoxX (W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) : Set (QuatAdele a b)ˣ :=
  matUnitsEquiv ha0 hb0 h ⁻¹' boxM W

theorem matUnitsEquiv_kerPos (g : SL2A F) :
    matUnitsEquiv ha0 hb0 h (((kerPosEquiv a b).symm ((sl1SplitEquiv ha0 hb0 h).symm g) : (nrdPos a b).ker) :
      (QuatAdele a b)ˣ) = Matrix.SpecialLinearGroup.toGL g := by
  apply Units.ext
  rw [coe_matUnitsEquiv, coe_kerPosEquiv_symm, ← coe_sl1SplitEquiv, ContinuousMulEquiv.apply_symm_apply]
  rfl

theorem measurableSet_boxM_preimage {W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hW : MeasurableSet W) :
    MeasurableSet (quatBoxX ha0 hb0 h W) := by
  set Φ := matUnitsEquiv ha0 hb0 h
  have hc : Continuous fun u : (QuatAdele a b)ˣ => ((Φ u : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) :
      Matrix (Fin 2) (Fin 2) (Adeles F)) := Units.continuous_val.comp (map_continuous Φ)
  have hci : Continuous fun u : (QuatAdele a b)ˣ => (((Φ u)⁻¹ : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) :
      Matrix (Fin 2) (Fin 2) (Adeles F)) := Units.continuous_coe_inv.comp (map_continuous Φ)
  have hent : ∀ {f : (QuatAdele a b)ˣ → Matrix (Fin 2) (Fin 2) (Adeles F)}, Continuous f →
      MeasurableSet {u | FinInt (f u)} := by
    intro f hf
    have : {u | FinInt (f u)} = ⋂ i, ⋂ j, (fun u => (f u i j).2) ⁻¹' OHat := by
      ext u; simp [FinInt, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      (continuous_snd.comp ((continuous_apply j).comp ((continuous_apply i).comp hf))).measurable
        measurableSet_OHat
  have harch : Measurable fun u : (QuatAdele a b)ˣ => archM ((Φ u : (Matrix (Fin 2) (Fin 2) (Adeles F))ˣ) :
      Matrix (Fin 2) (Fin 2) (Adeles F)) := by
    refine Continuous.measurable ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_fst.comp ((continuous_apply j).comp ((continuous_apply i).comp hc))
  exact (hent hc).inter ((hent hci).inter (harch hW))

/-- **The fibre measure over $q\in A_+$**: $\mu_T\{h : \Phi^{-1}\sigma(q)\,\psi^{-1}(h)\in X\} =
\mathbf 1_{\hat{\mathcal O}^\times}(q_f)\cdot|\omega|_\infty\{Y : \sigma(q_\infty)Y\in W\}\cdot\prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))$. -/
theorem kern_quatBoxX {W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hW : MeasurableSet W) (q : posA a b) :
    NormalFib.kern (nrdPos a b) (nrdPos_surjective ha0 hb0) (muTP ha0 hb0 h) q (quatBoxX ha0 hb0 h W) =
      (OHatUnits F : Set AFˣ).indicator (fun _ => 1) (finPart (q : (Adeles F)ˣ)) *
        (muGaugeInf F {Y | !![1, 0; 0, ((q : (Adeles F)ˣ) : Adeles F).1] * Y ∈ W} * finFactorSL2 F) := by
  have := isHaarMeasure_muTP ha0 hb0 h
  have hX := measurableSet_boxM_preimage ha0 hb0 h hW
  have hq : nrdPos a b (sigmaQ ha0 hb0 h (q : (Adeles F)ˣ)) = q := nrdPos_sigmaQ ha0 hb0 h q
  conv_lhs => rw [← hq]
  rw [NormalFib.kern_apply_N, NormalFib.fibK_apply _ _ _ hX, muTP,
    Measure.map_map (map_continuous (kerPosEquiv a b).symm).measurable
      (map_continuous (sl1SplitEquiv ha0 hb0 h).symm).measurable,
    Measure.map_apply ((map_continuous (kerPosEquiv a b).symm).measurable.comp
      (map_continuous (sl1SplitEquiv ha0 hb0 h).symm).measurable) ((NormalFib.measurable_mul_val _ _) hX)]
  set U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F)) :=
    {Y | !![1, 0; 0, ((q : (Adeles F)ˣ) : Adeles F).1] * Y ∈ W}
  have hUm : MeasurableSet U := hW.preimage (continuous_const.matrix_mul continuous_id).measurable
  have hset : (((kerPosEquiv a b).symm ∘ (sl1SplitEquiv ha0 hb0 h).symm) ⁻¹' ((fun k : (nrdPos a b).ker =>
      sigmaQ ha0 hb0 h (q : (Adeles F)ˣ) * (k : (QuatAdele a b)ˣ)) ⁻¹' quatBoxX ha0 hb0 h W)) =
      {g : SL2A F | finPart (q : (Adeles F)ˣ) ∈ OHatUnits F} ∩ (intFin F ∩ archPart ⁻¹' U) := by
    ext g
    simp only [Set.mem_preimage, Function.comp_apply, quatBoxX, map_mul, sigmaQ,
      ContinuousMulEquiv.apply_symm_apply, matUnitsEquiv_kerPos, sigmaA_mul_mem_boxM_iff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, U]
  rw [hset]
  by_cases hf : finPart (q : (Adeles F)ˣ) ∈ OHatUnits F
  · rw [Set.indicator_of_mem hf, one_mul, show {g : SL2A F | finPart (q : (Adeles F)ˣ) ∈ OHatUnits F} = univ
      from Set.eq_univ_of_forall fun _ => hf, Set.univ_inter, muT_box_gauge hUm]
  · rw [Set.indicator_of_notMem hf, zero_mul, show {g : SL2A F | finPart (q : (Adeles F)ˣ) ∈ OHatUnits F} = ∅
      from Set.eq_empty_of_forall_notMem fun _ => hf, Set.empty_inter, measure_empty]

include h in
/-- A split $D$ ($b = x^2 - ay^2$) ramifies at no real place. -/
theorem not_isRamifiedReal_of_split (w : InfinitePlace F) (hw : w.IsReal) :
    ¬ QuadFormsKB.Quat.IsRamifiedReal a b w hw := by
  rintro ⟨ha, hb⟩
  have e := congrArg (InfinitePlace.embedding_of_isReal hw) h
  simp only [map_sub, map_mul, map_pow] at e
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw x), sq_nonneg (InfinitePlace.embedding_of_isReal hw y)]

include h in
/-- For split $D$, $A_+$ is all of $\mathbb A_F^\times$. -/
theorem mem_posA_of_split (u : (Adeles F)ˣ) : u ∈ posA a b :=
  fun w hw hram => absurd hram (not_isRamifiedReal_of_split h w hw)

instance : SFinite (muGaugeInf F) := by unfold muGaugeInf; infer_instance

set_option maxHeartbeats 1000000 in
/-- **The fibred measure of the box** (split $D$):
$\int_{\mathbb A^\times}\mu_T\{h : \sigma(q)h\in X\}\,dq = \mu_f(\hat{\mathcal O}^\times)\cdot
\prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))\cdot\int_{F_\infty^\times}|\omega|_\infty\{Y : \sigma(t)Y\in W\}\,d^\times t$. -/
theorem fibMeas_quatBoxX {W : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hW : MeasurableSet W) :
    NormalFib.fibMeas (nrdPos a b) (nrdPos_surjective ha0 hb0) (muPosA a b) (muTP ha0 hb0 h)
        (quatBoxX ha0 hb0 h W) =
      muFinUnits F (OHatUnits F) * finFactorSL2 F *
        ∫⁻ t, muGaugeInf F {Y | !![1, 0; 0, ((t : (mixedSpace F)ˣ) : mixedSpace F)] * Y ∈ W} ∂omegaInf F := by
  have := isHaarMeasure_muTP ha0 hb0 h
  have hX := measurableSet_boxM_preimage ha0 hb0 h hW
  -- the integrand on all ideles
  set G : (mixedSpace F) → ℝ≥0∞ := fun t => muGaugeInf F {Y | !![1, 0; 0, t] * Y ∈ W} with hG
  have hGm : Measurable G := by
    have hS : MeasurableSet {p : mixedSpace F × Matrix (Fin 2) (Fin 2) (mixedSpace F) |
        !![1, 0; 0, p.1] * p.2 ∈ W} := by
      refine hW.preimage (Continuous.measurable ?_)
      refine Continuous.matrix_mul ?_ continuous_snd
      refine continuous_pi fun i => continuous_pi fun j => ?_
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] <;>
        first | exact continuous_const | exact continuous_fst
    exact measurable_measure_prodMk_left hS
  set f : (Adeles F)ˣ → ℝ≥0∞ := fun u =>
    (OHatUnits F : Set AFˣ).indicator (fun _ => 1) (finPart u) * (G (u : Adeles F).1 * finFactorSL2 F) with hf
  have hfm : Measurable f := by
    refine Measurable.mul ?_ ((hGm.comp (measurable_fst.comp Units.continuous_val.measurable)).mul_const _)
    exact (measurable_const.indicator (isOpen_OHatUnits.measurableSet)).comp continuous_finPart.measurable
  rw [NormalFib.fibMeas_apply _ _ measurable_nrdPos _ _ hX]
  have hk : ∀ q : posA a b, NormalFib.kern (nrdPos a b) (nrdPos_surjective ha0 hb0) (muTP ha0 hb0 h) q
      (quatBoxX ha0 hb0 h W) = f q := fun q => kern_quatBoxX ha0 hb0 h hW q
  simp_rw [hk]
  -- from `muPosA` to `tamIdeles`
  have hemb := measurableEmbedding_posA (a := a) (b := b)
  have h1 : ∫⁻ q : posA a b, f q ∂muPosA a b = ∫⁻ u, f u ∂tamIdeles F := by
    rw [muPosA, ← hemb.lintegral_map, hemb.map_comap]
    have : Set.range (Subtype.val : posA a b → (Adeles F)ˣ) = univ :=
      Set.eq_univ_of_forall fun u => ⟨⟨u, mem_posA_of_split h u⟩, rfl⟩
    rw [this, Measure.restrict_univ]
  have he : ((idelesEquiv F).symm : _ → (Adeles F)ˣ) = (idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [h1, tamIdeles, he, lintegral_map_equiv]
  have hfe : Measurable fun p : (mixedSpace F)ˣ × AFˣ => f ((idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv p) :=
    hfm.comp (MeasurableEquiv.measurable _)
  rw [lintegral_prod _ hfe.aemeasurable]
  have hinner : ∀ t : (mixedSpace F)ˣ, ∫⁻ s, f ((idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv (t, s))
      ∂muFinUnits F = muFinUnits F (OHatUnits F) * finFactorSL2 F * G (t : mixedSpace F) := by
    intro t
    have hval : ∀ s : AFˣ, f ((idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv (t, s)) =
        (OHatUnits F : Set AFˣ).indicator (fun _ => 1) s * (G (t : mixedSpace F) * finFactorSL2 F) := fun s => rfl
    simp_rw [hval]
    rw [lintegral_mul_const _ (measurable_const.indicator isOpen_OHatUnits.measurableSet),
      lintegral_indicator_const isOpen_OHatUnits.measurableSet, one_mul]
    ring
  simp_rw [hinner]
  exact lintegral_const_mul _ (hGm.comp Units.continuous_val.measurable)

end FibMeas

end QuadFormsKB.Tamagawa.Measure.Weil
