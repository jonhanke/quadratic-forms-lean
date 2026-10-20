import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures

/-!
# The chart lemma for the Tamagawa measure on $\mathbb A_f^\times$

For a finite set $S$ of finite places and sets $U_v\subseteq F_v^\times$ ($v\in S$), the **box**
$\operatorname{box}(S, U) = \prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v^\times\subseteq\mathbb A_f^\times$ (`ideleBox`).

* **`muFinUnits_ideleBox`**: if each $U_v$ ($v\in S$) is measurable with $\omega_v(U_v) < \infty$, then
  $\mu_f(\operatorname{box}(S,U)) = \mu_f(\hat{\mathcal O}^\times)\cdot\prod_{v\in S}\omega_v(U_v)/\omega_v(\mathcal O_v^\times)$.
* **`muFinUnits_ideleBox_weil`** (Weil's form, AAG §2.3, p. 21): $\mu_f(\operatorname{box}(S,U))\cdot\prod_{v\in S}
  \operatorname{vol}(\mathcal O_v) = |d_F|^{-1/2}\prod_{v\in S}\lambda_v^{-1}\omega_v(U_v)$, i.e.
  $\mu_f = \prod_{v\in S}\lambda_v^{-1}\omega_v\times\prod_{v\notin S}\lambda_v^{-1}\omega_v|_{\mathcal O_v^\times}$ on the chart
  (with $\prod_v\operatorname{vol}(\mathcal O_v) = |d_F|^{-1/2}$ and $\lambda_v^{-1}\omega_v(\mathcal O_v^\times) =
  \operatorname{vol}(\mathcal O_v)$).

Proof: induction on $S$. For $w\notin S$, the image of $\mu_f$ restricted to the other constraints under $g\mapsto g_w$
is invariant under $F_w^\times$ (translation by the single-place idele `mulSingleAt w x`) and finite on compacts
(a compact set is covered by finitely many cosets of the open subgroup $\mathcal O_w^\times$), hence a multiple of
$\omega_w$ (uniqueness of Haar measure); the multiple is read off on $\mathcal O_w^\times$ (as `muFin_boxSO_haar`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Pointwise Classical

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

instance (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
  (isOpenEmbedding_val_adic v).locallyCompactSpace

instance (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (v.adicCompletion F)ˣ :=
  (isOpenEmbedding_val_adic v).isEmbedding.secondCountableTopology

theorem continuous_unitAt (v : HeightOneSpectrum (𝓞 F)) : Continuous fun g : AFˣ => unitAt g v :=
  Units.continuous_iff.mpr ⟨(RestrictedProduct.continuous_eval v).comp Units.continuous_val,
    (RestrictedProduct.continuous_eval v).comp Units.continuous_coe_inv⟩

theorem measurable_unitAt (v : HeightOneSpectrum (𝓞 F)) : Measurable fun g : AFˣ => unitAt g v :=
  (continuous_unitAt v).measurable

theorem isOpen_unitsVSub (v : HeightOneSpectrum (𝓞 F)) : IsOpen (unitsVSub v) := by
  have h : unitsVSub v = {u : (v.adicCompletion F)ˣ | (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F} := by
    ext u
    simp only [unitsVSub, mem_ofPred_eq, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val,
      map_inv₀]
    constructor
    · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩
    · rintro ⟨h1, h2⟩
      have h0 : Valued.v (u : v.adicCompletion F) ≠ 0 := by simp
      have := mul_le_mul' (le_refl (Valued.v (u : v.adicCompletion F))) h2
      rw [mul_inv_cancel₀ h0, mul_one] at this
      exact le_antisymm h1 this
  rw [h]
  exact ((isOpen_adicCompletionIntegers v).preimage Units.continuous_val).inter
    ((isOpen_adicCompletionIntegers v).preimage Units.continuous_coe_inv)

theorem one_mem_unitsVSub (v : HeightOneSpectrum (𝓞 F)) : (1 : (v.adicCompletion F)ˣ) ∈ unitsVSub v := by
  simp [unitsVSub]

theorem mul_mem_unitsVSub {v : HeightOneSpectrum (𝓞 F)} {x y : (v.adicCompletion F)ˣ} (hx : x ∈ unitsVSub v)
    (hy : y ∈ unitsVSub v) : x * y ∈ unitsVSub v := by
  simp only [unitsVSub, mem_ofPred_eq, Units.val_mul, map_mul] at hx hy ⊢
  rw [hx, hy, one_mul]

theorem inv_mem_unitsVSub {v : HeightOneSpectrum (𝓞 F)} {x : (v.adicCompletion F)ˣ} (hx : x ∈ unitsVSub v) :
    x⁻¹ ∈ unitsVSub v := by
  simp only [unitsVSub, mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
  rw [hx, inv_one]

/-- The box $\prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v^\times\subseteq\mathbb A_f^\times$. -/
def ideleBox (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) :
    Set AFˣ :=
  {g | ∀ v, unitAt g v ∈ (if v ∈ S then U v else unitsVSub v)}

theorem measurableSet_ideleBox (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    MeasurableSet (ideleBox S U) := by
  have : ideleBox S U = ⋂ v, (fun g : AFˣ => unitAt g v) ⁻¹' (if v ∈ S then U v else unitsVSub v) := by
    ext g; simp [ideleBox]
  rw [this]
  refine MeasurableSet.iInter fun v => measurable_unitAt v ?_
  split_ifs with h
  · exact hU v h
  · exact measurableSet_unitsVSub v

theorem unitAt_one (v : HeightOneSpectrum (𝓞 F)) : unitAt (1 : AFˣ) v = 1 := Units.ext rfl

theorem unitAt_mulSingleAt (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    unitAt (mulSingleAt w x) w = x :=
  Units.ext (by change Pi.mulSingle w (x : w.adicCompletion F) w = x; simp)

theorem unitAt_mulSingleAt_of_ne {w v : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : (w.adicCompletion F)ˣ) :
    unitAt (mulSingleAt w x) v = 1 :=
  Units.ext (by change Pi.mulSingle w (x : w.adicCompletion F) v = 1; simp [Pi.mulSingle_eq_of_ne h])

theorem ideleBox_empty (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) :
    ideleBox ∅ U = (OHatUnits F : Set AFˣ) := by
  ext g
  simp only [ideleBox, Finset.notMem_empty, ite_false, mem_ofPred_eq, SetLike.mem_coe, mem_OHatUnits]
  constructor
  · intro h
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have := h v
      simp only [unitsVSub, mem_ofPred_eq, unitAt_val] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr this.le
    · have := inv_mem_unitsVSub (h v)
      have h' : unitAt g⁻¹ v = (unitAt g v)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← unitAt_mul, inv_mul_cancel, unitAt_one]
      rw [← h'] at this
      simp only [unitsVSub, mem_ofPred_eq, unitAt_val] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr this.le
  · rintro ⟨h1, h2⟩ v
    have := distribHaarChar_eq_one_of_mem (unitAt g v) (h1 v) (h2 v)
    have hv1 : Valued.v ((g : AF) v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h1 v)
    have hv2 : Valued.v (((g⁻¹ : AFˣ) : AF) v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h2 v)
    have hprod : Valued.v ((g : AF) v) * Valued.v (((g⁻¹ : AFˣ) : AF) v) = 1 := by
      rw [← map_mul]
      have : (g : AF) v * ((g⁻¹ : AFˣ) : AF) v = 1 := congrArg (fun x : AF => x v) g.mul_inv
      rw [this, map_one]
    change Valued.v ((g : AF) v) = 1
    refine le_antisymm hv1 ?_
    by_contra hlt
    push Not at hlt
    have : Valued.v ((g : AF) v) * Valued.v (((g⁻¹ : AFˣ) : AF) v) < 1 :=
      mul_lt_one_of_lt_of_le hlt hv2
    rw [hprod] at this
    exact lt_irrefl _ this

/-! ### The induction step -/

/-- The constraint set away from $w$. -/
def ideleBoxAway (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (w : HeightOneSpectrum (𝓞 F)) : Set AFˣ :=
  {g | ∀ v, v ≠ w → unitAt g v ∈ (if v ∈ S then U v else unitsVSub v)}

theorem measurableSet_ideleBoxAway (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (w : HeightOneSpectrum (𝓞 F))
    (hU : ∀ v ∈ S, MeasurableSet (U v)) : MeasurableSet (ideleBoxAway S U w) := by
  have : ideleBoxAway S U w =
      ⋂ v, ⋂ (_ : v ≠ w), (fun g : AFˣ => unitAt g v) ⁻¹' (if v ∈ S then U v else unitsVSub v) := by
    ext g; simp [ideleBoxAway]
  rw [this]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => measurable_unitAt v ?_
  split_ifs with h
  · exact hU v h
  · exact measurableSet_unitsVSub v

theorem ideleBox_eq_away {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    ideleBox S U = ideleBoxAway S U w ∩ (fun g : AFˣ => unitAt g w) ⁻¹' unitsVSub w := by
  ext g
  simp only [ideleBox, ideleBoxAway, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · intro h; exact ⟨fun v _ => h v, by simpa [hw] using h w⟩
  · rintro ⟨h, hw'⟩ v
    by_cases hv : v = w
    · subst hv; simpa [hw] using hw'
    · exact h v hv

theorem ideleBox_insert_eq_away {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    ideleBox (insert w S) U = ideleBoxAway S U w ∩ (fun g : AFˣ => unitAt g w) ⁻¹' U w := by
  ext g
  simp only [ideleBox, ideleBoxAway, mem_inter_iff, mem_ofPred_eq, mem_preimage, Finset.mem_insert]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, by simpa using h w⟩
    have := h v
    simpa [hv] using this
  · rintro ⟨h, hw'⟩ v
    by_cases hv : v = w
    · subst hv; simpa using hw'
    · simpa [hv] using h v hv

theorem mulSingleAt_mul_mem_away_iff {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)}
    (x : (w.adicCompletion F)ˣ) (g : AFˣ) :
    mulSingleAt w x * g ∈ ideleBoxAway S U w ↔ g ∈ ideleBoxAway S U w := by
  simp only [ideleBoxAway, mem_ofPred_eq]
  refine forall_congr' fun v => forall_congr' fun hv => ?_
  rw [unitAt_mul, unitAt_mulSingleAt_of_ne hv, one_mul]

/-- The image of $\mu_f$ restricted to the constraints away from $w$, under $g\mapsto g_w$. -/
def boxMarginal (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    Measure (w.adicCompletion F)ˣ :=
  ((muFinUnits F).restrict (ideleBoxAway S U w)).map fun g => unitAt g w

theorem boxMarginal_apply {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)}
    {A : Set (w.adicCompletion F)ˣ} (hA : MeasurableSet A) :
    boxMarginal S U w A = muFinUnits F (ideleBoxAway S U w ∩ (fun g : AFˣ => unitAt g w) ⁻¹' A) := by
  rw [boxMarginal, Measure.map_apply (measurable_unitAt w) hA, Measure.restrict_apply (measurable_unitAt w hA),
    inter_comm]

theorem map_mul_boxMarginal {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)}
    (x : (w.adicCompletion F)ˣ) :
    (boxMarginal S U w).map (x * ·) = boxMarginal S U w := by
  ext A hA
  rw [Measure.map_apply (measurable_const_mul x) hA, boxMarginal_apply (hA.preimage (measurable_const_mul x)),
    boxMarginal_apply hA]
  have hset : ideleBoxAway S U w ∩ (fun g : AFˣ => unitAt g w) ⁻¹' ((x * ·) ⁻¹' A) =
      (mulSingleAt w x * ·) ⁻¹' (ideleBoxAway S U w ∩ (fun g : AFˣ => unitAt g w) ⁻¹' A) := by
    ext g
    simp only [mem_inter_iff, mem_preimage, mulSingleAt_mul_mem_away_iff, unitAt_mul, unitAt_mulSingleAt]
  rw [hset, measure_preimage_mul]

theorem boxMarginal_unitsVSub {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∉ S) :
    boxMarginal S U w (unitsVSub w) = muFinUnits F (ideleBox S U) := by
  rw [boxMarginal_apply (measurableSet_unitsVSub w), ideleBox_eq_away hw]

theorem boxMarginal_U {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)}
    (hUw : MeasurableSet (U w)) (hw : w ∉ S) :
    boxMarginal S U w (U w) = muFinUnits F (ideleBox (insert w S) U) := by
  rw [boxMarginal_apply hUw, ideleBox_insert_eq_away hw]

theorem isFiniteMeasureOnCompacts_boxMarginal {S : Finset (HeightOneSpectrum (𝓞 F))}
    {U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ} {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∉ S) (hfin : muFinUnits F (ideleBox S U) ≠ ⊤) :
    IsFiniteMeasureOnCompacts (boxMarginal S U w) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => (x : (w.adicCompletion F)ˣ) • unitsVSub w)
    (fun x => (isOpen_unitsVSub w).smul _) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, 1, one_mem_unitsVSub w, mul_one x⟩)
  have hinv : ∀ y : (w.adicCompletion F)ˣ, boxMarginal S U w (y • unitsVSub w) = boxMarginal S U w (unitsVSub w) := by
    intro y
    have := congrArg (fun m : Measure (w.adicCompletion F)ˣ => m (y • unitsVSub w)) (map_mul_boxMarginal (S := S) (U := U) y)
    rw [← this, Measure.map_apply (measurable_const_mul _) ((measurableSet_unitsVSub w).const_smul y)]
    congr 1
    ext z
    simp only [mem_preimage, mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel_left]
  calc boxMarginal S U w K ≤ boxMarginal S U w (⋃ x ∈ t, (x : (w.adicCompletion F)ˣ) • unitsVSub w) :=
        measure_mono ht
    _ ≤ ∑ x ∈ t, boxMarginal S U w ((x : (w.adicCompletion F)ˣ) • unitsVSub w) := measure_biUnion_finset_le _ _
    _ = ∑ _x ∈ t, muFinUnits F (ideleBox S U) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hinv, boxMarginal_unitsVSub hw]
    _ < ⊤ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin.lt_top

theorem omegaV_unitsVSub_ne_zero (v : HeightOneSpectrum (𝓞 F)) : omegaV v (unitsVSub v) ≠ 0 :=
  (isOpen_unitsVSub v).measure_ne_zero _ ⟨1, one_mem_unitsVSub v⟩

theorem omegaV_unitsVSub_ne_top (v : HeightOneSpectrum (𝓞 F)) : omegaV v (unitsVSub v) ≠ ⊤ := by
  rw [omegaV_unitsVSub]
  exact ne_top_of_le_ne_top (b := Analysis.selfDualV v (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (volO_ne_top v)
    (measure_mono fun x hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (le_of_eq hx))

/-- **The chart lemma on $\mathbb A_f^\times$**: for $U_v\subseteq F_v^\times$ ($v\in S$) measurable with
$\omega_v(U_v) < \infty$, $\mu_f(\prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v^\times) =
\mu_f(\hat{\mathcal O}^\times)\prod_{v\in S}\omega_v(U_v)/\omega_v(\mathcal O_v^\times)$. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem muFinUnits_ideleBox (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v))
    (hUf : ∀ v ∈ S, omegaV v (U v) ≠ ⊤) :
    muFinUnits F (ideleBox S U) =
      muFinUnits F (OHatUnits F) * ∏ v ∈ S, omegaV v (U v) / omegaV v (unitsVSub v) := by
  induction S using Finset.induction_on with
  | empty => rw [ideleBox_empty, Finset.prod_empty, mul_one]
  | insert w S hw ih =>
    have hU' : ∀ v ∈ S, MeasurableSet (U v) := fun v hv => hU v (Finset.mem_insert_of_mem hv)
    have hUf' : ∀ v ∈ S, omegaV v (U v) ≠ ⊤ := fun v hv => hUf v (Finset.mem_insert_of_mem hv)
    have ih' := ih hU' hUf'
    have hfin : muFinUnits F (ideleBox S U) ≠ ⊤ := by
      rw [ih']
      refine ENNReal.mul_ne_top (by rw [muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top) ?_
      exact ENNReal.prod_ne_top fun v hv => ENNReal.div_ne_top (hUf' v hv) (omegaV_unitsVSub_ne_zero v)
    have := isFiniteMeasureOnCompacts_boxMarginal hw hfin
    have : (boxMarginal S U w).IsMulLeftInvariant := ⟨fun x => map_mul_boxMarginal (S := S) (U := U) x⟩
    have hsmul := Measure.isMulLeftInvariant_eq_smul (boxMarginal S U w) (omegaV w)
    set c := Measure.haarScalarFactor (boxMarginal S U w) (omegaV w)
    have hO := congrArg (fun m : Measure (w.adicCompletion F)ˣ => m (unitsVSub w)) hsmul
    have hUw := congrArg (fun m : Measure (w.adicCompletion F)ˣ => m (U w)) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hO hUw
    rw [boxMarginal_unitsVSub hw] at hO
    rw [boxMarginal_U (hU w (Finset.mem_insert_self w S)) hw] at hUw
    rw [hUw, Finset.prod_insert hw, mul_left_comm, ← ih', hO, mul_comm (c : ℝ≥0∞) (omegaV w (unitsVSub w)),
      ← mul_assoc, ENNReal.div_mul_cancel (omegaV_unitsVSub_ne_zero w) (omegaV_unitsVSub_ne_top w), mul_comm]

/-- **Weil's form of the chart lemma**: $\mu_f(\prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v^\times)\cdot
\prod_{v\in S}\operatorname{vol}(\mathcal O_v) = |d_F|^{-1/2}\prod_{v\in S}\lambda_v^{-1}\omega_v(U_v)$, i.e. on the chart
$\mu_f = \prod_{v\in S}\lambda_v^{-1}\omega_v\times\prod_{v\notin S}\lambda_v^{-1}\omega_v|_{\mathcal O_v^\times}$
(since $\lambda_v^{-1}\omega_v(\mathcal O_v^\times) = \operatorname{vol}(\mathcal O_v)$ and $\prod_v\operatorname{vol}(\mathcal O_v)
= |d_F|^{-1/2}$). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem muFinUnits_ideleBox_weil (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v))
    (hUf : ∀ v ∈ S, omegaV v (U v) ≠ ⊤) :
    muFinUnits F (ideleBox S U) * ∏ v ∈ S, volO v =
      ENNReal.ofReal (ohatVol F) * ∏ v ∈ S, ENNReal.ofReal (lamV v)⁻¹ * omegaV v (U v) := by
  rw [muFinUnits_ideleBox S U hU hUf, muFinUnits_OHatUnits, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← lamV_inv_mul_omegaV_unitsVSub, mul_left_comm,
    ENNReal.div_mul_cancel (omegaV_unitsVSub_ne_zero v) (omegaV_unitsVSub_ne_top v)]

end

end QuadFormsKB.Tamagawa.Measure.Weil
