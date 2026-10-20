import Mathlib
import QuadFormsKB.Citation

/-!
# The abstract chart lemma for Haar measures on restricted products

**Generic (Mathlib-only hypotheses).** $G$ is a topological group with a Haar measure $\mu$, $(G_i)_{i\in\iota}$
($\iota$ countable) locally compact second countable groups with Haar measures $\omega_i$, $p_i : G\to G_i$ continuous
homomorphisms and $s_i : G_i\to G$ homomorphisms with $p_i\circ s_i = \mathrm{id}$ and $p_j\circ s_i = 1$ ($j\ne i$)
(single-place elements), and $K_i\subseteq G_i$ open sets containing $1$ with $\omega_i(K_i) < \infty$. The **box**
$\operatorname{box}(S, U) = \{g : p_i(g)\in U_i\ (i\in S),\ p_i(g)\in K_i\ (i\notin S)\}$ (`chartBox`).

* **`measure_chartBox`**: if $\mu(\operatorname{box}(\emptyset)) < \infty$ and $U_i$ ($i\in S$) is measurable with
  $\omega_i(U_i) < \infty$, then $\mu(\operatorname{box}(S,U)) = \mu(\operatorname{box}(\emptyset))\cdot
  \prod_{i\in S}\omega_i(U_i)/\omega_i(K_i)$.

This is the proof of `muFinUnits_ideleBox` (`IdeleChart.lean`) with the idelic data abstracted: induction on
$S$; for $w\notin S$ the image of $\mu$ restricted to the constraints away from $w$ under $p_w$ is $G_w$-invariant
(translate by $s_w(x)$) and finite on compacts (a compact set is covered by finitely many translates of $K_w$), hence
a multiple of $\omega_w$, the multiple being read off on $K_w$. It is used for $(\mathbb H\otimes\mathbb A_f)^\times$
(`QuatTamagawa.lean`).
-/

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-- $(\sup_nf_n)(\sup_ng_n) = \sup_n f_ng_n$ for monotone $f, g : \mathbb N\to[0,\infty]$. -/
theorem ENNReal_iSup_mul_iSup_of_monotone {f g : ℕ → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ n, f n) * (⨆ n, g n) = ⨆ n, f n * g n := by
  refine le_antisymm ?_ (iSup_le fun n => mul_le_mul' (le_iSup f n) (le_iSup g n))
  rw [ENNReal.iSup_mul]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  exact (mul_le_mul' (hf (le_max_left m n)) (hg (le_max_right m n))).trans (le_iSup (fun k => f k * g k) _)

/-- $\sup_n\prod_{i\in S}f_i(n) = \prod_{i\in S}\sup_nf_i(n)$ for monotone $f_i : \mathbb N\to[0,\infty]$. -/
theorem iSup_prod_of_monotone {ι : Type*} (S : Finset ι) {f : ι → ℕ → ℝ≥0∞} (hf : ∀ i, Monotone (f i)) :
    ⨆ n, ∏ i ∈ S, f i n = ∏ i ∈ S, ⨆ n, f i n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert w S hw ih =>
    simp_rw [Finset.prod_insert hw]
    rw [← ih, ENNReal_iSup_mul_iSup_of_monotone (hf w)
      (fun m n hmn => Finset.prod_le_prod fun i _ => hf i hmn)]

/-- **Chart data** on a group $G$: local factors $G_i$, projections $p_i$, single-place sections $s_i$ and the
standard local sets $K_i$ (open, containing $1$). -/
structure ChartData (G : Type*) [Group G] (ι : Type*) (H : ι → Type*) [∀ i, Group (H i)]
    [∀ i, TopologicalSpace (H i)] where
  /-- the projection to the $i$-th factor -/
  p : ∀ i, G →* H i
  /-- the single-place section at $i$ -/
  s : ∀ i, H i →* G
  /-- the standard open set at $i$ -/
  K : ∀ i, Set (H i)
  p_s_self : ∀ i x, p i (s i x) = x
  p_s_of_ne : ∀ i j, j ≠ i → ∀ x, p j (s i x) = 1
  isOpen_K : ∀ i, IsOpen (K i)
  one_mem_K : ∀ i, (1 : H i) ∈ K i

namespace ChartData

variable {G : Type*} [Group G] {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  (D : ChartData G ι H)

/-- The box $\{g : p_i(g)\in U_i\ (i\in S),\ p_i(g)\in K_i\ (i\notin S)\}$. -/
def chartBox (S : Finset ι) (U : ∀ i, Set (H i)) : Set G := {g | ∀ i, D.p i g ∈ (if i ∈ S then U i else D.K i)}

/-- The constraints away from $w$. -/
def chartAway (S : Finset ι) (U : ∀ i, Set (H i)) (w : ι) : Set G :=
  {g | ∀ i, i ≠ w → D.p i g ∈ (if i ∈ S then U i else D.K i)}

theorem chartBox_eq_away {S : Finset ι} {U : ∀ i, Set (H i)} {w : ι} (hw : w ∉ S) :
    D.chartBox S U = D.chartAway S U w ∩ D.p w ⁻¹' D.K w := by
  ext g
  simp only [chartBox, chartAway, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · intro h; exact ⟨fun v _ => h v, by simpa [hw] using h w⟩
  · rintro ⟨h, hw'⟩ v
    by_cases hv : v = w
    · subst hv; simpa [hw] using hw'
    · exact h v hv

theorem chartBox_insert_eq_away {S : Finset ι} {U : ∀ i, Set (H i)} {w : ι} (hw : w ∉ S) :
    D.chartBox (insert w S) U = D.chartAway S U w ∩ D.p w ⁻¹' U w := by
  ext g
  simp only [chartBox, chartAway, mem_inter_iff, mem_ofPred_eq, mem_preimage, Finset.mem_insert]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, by simpa using h w⟩
    have := h v
    simpa [hv] using this
  · rintro ⟨h, hw'⟩ v
    by_cases hv : v = w
    · subst hv; simpa using hw'
    · simpa [hv] using h v hv

theorem s_mul_mem_away_iff {S : Finset ι} {U : ∀ i, Set (H i)} {w : ι} (x : H w) (g : G) :
    D.s w x * g ∈ D.chartAway S U w ↔ g ∈ D.chartAway S U w := by
  simp only [chartAway, mem_ofPred_eq]
  refine forall_congr' fun v => forall_congr' fun hv => ?_
  rw [map_mul, D.p_s_of_ne w v hv, one_mul]

variable [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [∀ i, MeasurableSpace (H i)]
  [∀ i, BorelSpace (H i)] [Countable ι]

theorem measurableSet_chartBox (hp : ∀ i, Continuous (D.p i)) (S : Finset ι) (U : ∀ i, Set (H i))
    (hU : ∀ i ∈ S, MeasurableSet (U i)) : MeasurableSet (D.chartBox S U) := by
  have : D.chartBox S U = ⋂ i, D.p i ⁻¹' (if i ∈ S then U i else D.K i) := by
    ext g; simp [chartBox]
  rw [this]
  refine MeasurableSet.iInter fun i => (hp i).measurable ?_
  split_ifs with h
  · exact hU i h
  · exact (D.isOpen_K i).measurableSet

theorem measurableSet_chartAway (hp : ∀ i, Continuous (D.p i)) (S : Finset ι) (U : ∀ i, Set (H i)) (w : ι)
    (hU : ∀ i ∈ S, MeasurableSet (U i)) : MeasurableSet (D.chartAway S U w) := by
  have : D.chartAway S U w = ⋂ i, ⋂ (_ : i ≠ w), D.p i ⁻¹' (if i ∈ S then U i else D.K i) := by
    ext g; simp [chartAway]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (hp i).measurable ?_
  split_ifs with h
  · exact hU i h
  · exact (D.isOpen_K i).measurableSet

/-- The image of $\mu$ restricted to the constraints away from $w$ under $p_w$. -/
def chartMarginal (μ : Measure G) (S : Finset ι) (U : ∀ i, Set (H i)) (w : ι) : Measure (H w) :=
  (μ.restrict (D.chartAway S U w)).map (D.p w)

variable {D}

theorem chartMarginal_apply (hp : ∀ i, Continuous (D.p i)) (μ : Measure G) {S : Finset ι} {U : ∀ i, Set (H i)}
    {w : ι} {A : Set (H w)} (hA : MeasurableSet A) :
    D.chartMarginal μ S U w A = μ (D.chartAway S U w ∩ D.p w ⁻¹' A) := by
  rw [chartMarginal, Measure.map_apply (hp w).measurable hA, Measure.restrict_apply ((hp w).measurable hA),
    inter_comm]

variable [IsTopologicalGroup G] [∀ i, IsTopologicalGroup (H i)]

theorem map_mul_chartMarginal (hp : ∀ i, Continuous (D.p i)) (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Finset ι} {U : ∀ i, Set (H i)} {w : ι} (x : H w) :
    (D.chartMarginal μ S U w).map (x * ·) = D.chartMarginal μ S U w := by
  ext A hA
  rw [Measure.map_apply (measurable_const_mul x) hA,
    chartMarginal_apply hp μ (hA.preimage (measurable_const_mul x)), chartMarginal_apply hp μ hA]
  have hset : D.chartAway S U w ∩ D.p w ⁻¹' ((x * ·) ⁻¹' A) =
      (D.s w x * ·) ⁻¹' (D.chartAway S U w ∩ D.p w ⁻¹' A) := by
    ext g
    simp only [mem_inter_iff, mem_preimage, D.s_mul_mem_away_iff, map_mul, D.p_s_self]
  rw [hset, measure_preimage_mul]

theorem chartMarginal_K (hp : ∀ i, Continuous (D.p i)) (μ : Measure G) {S : Finset ι} {U : ∀ i, Set (H i)}
    {w : ι} (hw : w ∉ S) : D.chartMarginal μ S U w (D.K w) = μ (D.chartBox S U) := by
  rw [chartMarginal_apply hp μ (D.isOpen_K w).measurableSet, D.chartBox_eq_away hw]

theorem chartMarginal_U (hp : ∀ i, Continuous (D.p i)) (μ : Measure G) {S : Finset ι} {U : ∀ i, Set (H i)}
    {w : ι} (hUw : MeasurableSet (U w)) (hw : w ∉ S) :
    D.chartMarginal μ S U w (U w) = μ (D.chartBox (insert w S) U) := by
  rw [chartMarginal_apply hp μ hUw, D.chartBox_insert_eq_away hw]

theorem isFiniteMeasureOnCompacts_chartMarginal (hp : ∀ i, Continuous (D.p i)) (μ : Measure G)
    [μ.IsMulLeftInvariant] {S : Finset ι} {U : ∀ i, Set (H i)} {w : ι} (hw : w ∉ S)
    (hfin : μ (D.chartBox S U) ≠ ⊤) : IsFiniteMeasureOnCompacts (D.chartMarginal μ S U w) := by
  refine ⟨fun C hC => ?_⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => (x : H w) • D.K w)
    (fun x => (D.isOpen_K w).smul _) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, 1, D.one_mem_K w, mul_one x⟩)
  have hinv : ∀ y : H w, D.chartMarginal μ S U w (y • D.K w) = D.chartMarginal μ S U w (D.K w) := by
    intro y
    have := congrArg (fun m : Measure (H w) => m (y • D.K w)) (map_mul_chartMarginal hp μ (S := S) (U := U) y)
    rw [← this, Measure.map_apply (measurable_const_mul _) ((D.isOpen_K w).measurableSet.const_smul y)]
    congr 1
    ext z
    simp only [mem_preimage, mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel_left]
  calc D.chartMarginal μ S U w C ≤ D.chartMarginal μ S U w (⋃ x ∈ t, (x : H w) • D.K w) := measure_mono ht
    _ ≤ ∑ x ∈ t, D.chartMarginal μ S U w ((x : H w) • D.K w) := measure_biUnion_finset_le _ _
    _ = ∑ _x ∈ t, μ (D.chartBox S U) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hinv, chartMarginal_K hp μ hw]
    _ < ⊤ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin.lt_top

variable [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)]

/-- **The abstract chart lemma**: $\mu(\operatorname{box}(S,U)) = \mu(\operatorname{box}(\emptyset))\cdot
\prod_{i\in S}\omega_i(U_i)/\omega_i(K_i)$, for $U_i$ measurable with $\omega_i(U_i) < \infty$, provided
$\mu(\operatorname{box}(\emptyset)) < \infty$ and $\omega_i(K_i) < \infty$. -/
@[kb "weil1982" "§2.3, p. 21 (the measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem measure_chartBox (hp : ∀ i, Continuous (D.p i)) (μ : Measure G) [μ.IsMulLeftInvariant]
    (ω : ∀ i, Measure (H i)) [∀ i, (ω i).IsHaarMeasure] (hωK : ∀ i, ω i (D.K i) ≠ ⊤)
    (h0 : μ (D.chartBox ∅ (fun i => D.K i)) ≠ ⊤) (S : Finset ι) (U : ∀ i, Set (H i))
    (hU : ∀ i ∈ S, MeasurableSet (U i)) (hUf : ∀ i ∈ S, ω i (U i) ≠ ⊤) :
    μ (D.chartBox S U) = μ (D.chartBox ∅ (fun i => D.K i)) * ∏ i ∈ S, ω i (U i) / ω i (D.K i) := by
  have hK0 : ∀ i, ω i (D.K i) ≠ 0 := fun i => (D.isOpen_K i).measure_ne_zero _ ⟨1, D.one_mem_K i⟩
  have hbox0 : ∀ U' : ∀ i, Set (H i), D.chartBox ∅ U' = D.chartBox ∅ (fun i => D.K i) := by
    intro U'; ext g; simp [chartBox]
  induction S using Finset.induction_on with
  | empty => rw [hbox0, Finset.prod_empty, mul_one]
  | insert w S hw ih =>
    have hU' : ∀ v ∈ S, MeasurableSet (U v) := fun v hv => hU v (Finset.mem_insert_of_mem hv)
    have hUf' : ∀ v ∈ S, ω v (U v) ≠ ⊤ := fun v hv => hUf v (Finset.mem_insert_of_mem hv)
    have ih' := ih hU' hUf'
    have hfin : μ (D.chartBox S U) ≠ ⊤ := by
      rw [ih']
      exact ENNReal.mul_ne_top h0 (ENNReal.prod_ne_top fun v hv => ENNReal.div_ne_top (hUf' v hv) (hK0 v))
    have := isFiniteMeasureOnCompacts_chartMarginal hp μ hw hfin
    have : (D.chartMarginal μ S U w).IsMulLeftInvariant :=
      ⟨fun x => map_mul_chartMarginal hp μ (S := S) (U := U) x⟩
    have hsmul := Measure.isMulLeftInvariant_eq_smul (D.chartMarginal μ S U w) (ω w)
    set c := Measure.haarScalarFactor (D.chartMarginal μ S U w) (ω w)
    have hO := congrArg (fun m : Measure (H w) => m (D.K w)) hsmul
    have hUw := congrArg (fun m : Measure (H w) => m (U w)) hsmul
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hO hUw
    rw [chartMarginal_K hp μ hw] at hO
    rw [chartMarginal_U hp μ (hU w (Finset.mem_insert_self w S)) hw] at hUw
    rw [hUw, Finset.prod_insert hw, mul_left_comm, ← ih', hO, mul_comm (c : ℝ≥0∞) (ω w (D.K w)),
      ← mul_assoc, ENNReal.div_mul_cancel (hK0 w) (hωK w), mul_comm]

omit [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)] in
theorem chartBox_mono {S : Finset ι} {U V : ∀ i, Set (H i)} (h : ∀ i ∈ S, U i ⊆ V i) :
    D.chartBox S U ⊆ D.chartBox S V := by
  intro g hg i
  have := hg i
  split_ifs at this ⊢ with hi
  · exact h i hi this
  · exact this

/-- **The abstract chart lemma without finiteness hypotheses** on the $U_i$ (monotone exhaustion of each $U_i$ by
compact sets, from the finite case `measure_chartBox`). -/
@[kb "weil1982" "§2.3, p. 21 (the measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem measure_chartBox_of_measurable (hp : ∀ i, Continuous (D.p i)) (μ : Measure G) [μ.IsMulLeftInvariant]
    (ω : ∀ i, Measure (H i)) [∀ i, (ω i).IsHaarMeasure] (hωK : ∀ i, ω i (D.K i) ≠ ⊤)
    (h0 : μ (D.chartBox ∅ (fun i => D.K i)) ≠ ⊤) (S : Finset ι) (U : ∀ i, Set (H i))
    (hU : ∀ i ∈ S, MeasurableSet (U i)) :
    μ (D.chartBox S U) = μ (D.chartBox ∅ (fun i => D.K i)) * ∏ i ∈ S, ω i (U i) / ω i (D.K i) := by
  -- compact exhaustions of the factors
  let C : ∀ i, CompactExhaustion (H i) := fun i => CompactExhaustion.choice (H i)
  let Un : ℕ → ∀ i, Set (H i) := fun n i => U i ∩ interior (C i (n + 1))
  have hUn : ∀ n, ∀ i ∈ S, MeasurableSet (Un n i) := fun n i hi =>
    (hU i hi).inter isOpen_interior.measurableSet
  have hUnf : ∀ n, ∀ i ∈ S, ω i (Un n i) ≠ ⊤ := fun n i _ =>
    ne_top_of_le_ne_top ((C i).isCompact (n + 1)).measure_lt_top.ne
      (measure_mono (inter_subset_right.trans interior_subset))
  have hmonoU : ∀ i, Monotone fun n => Un n i := fun i m n hmn =>
    inter_subset_inter_right _ (interior_mono ((C i).subset (Nat.succ_le_succ hmn)))
  -- the boxes increase to the box of U
  have hmonoB : Monotone fun n => D.chartBox S (Un n) := fun m n hmn =>
    D.chartBox_mono fun i _ => hmonoU i hmn
  have hunion : ⋃ n, D.chartBox S (Un n) = D.chartBox S U := by
    refine Subset.antisymm (iUnion_subset fun n => D.chartBox_mono fun i _ => inter_subset_left) fun g hg => ?_
    have hex : ∀ i ∈ S, ∃ n, D.p i g ∈ C i n := fun i _ => (C i).exists_mem (D.p i g)
    choose! N hN using hex
    refine mem_iUnion.mpr ⟨S.sup N, fun i => ?_⟩
    have := hg i
    split_ifs at this ⊢ with hi
    · exact ⟨this, (C i).subset_interior_succ _ ((C i).subset (Finset.le_sup hi) (hN i hi))⟩
    · exact this
  have hlimB : μ (D.chartBox S U) = ⨆ n, μ (D.chartBox S (Un n)) := by
    rw [← hunion, hmonoB.measure_iUnion]
  -- the factors increase to ω(U_i)
  have hlimU : ∀ i, ω i (U i) / ω i (D.K i) = ⨆ n, ω i (Un n i) / ω i (D.K i) := by
    intro i
    have hu : ⋃ n, Un n i = U i := by
      rw [← inter_iUnion]
      refine inter_eq_left.mpr fun x _ => mem_iUnion.mpr ?_
      obtain ⟨n, hn⟩ := (C i).exists_mem x
      exact ⟨n, (C i).subset_interior_succ n hn⟩
    rw [← ENNReal.iSup_div, ← (hmonoU i).measure_iUnion, hu]
  have hmonoF : ∀ i, Monotone fun n => ω i (Un n i) / ω i (D.K i) := fun i m n hmn =>
    ENNReal.div_le_div_right (measure_mono (hmonoU i hmn)) _
  rw [hlimB]
  simp_rw [D.measure_chartBox hp μ ω hωK h0 S _ (hUn _) (hUnf _)]
  rw [← ENNReal.mul_iSup]
  congr 1
  simp_rw [hlimU]
  exact iSup_prod_of_monotone S hmonoF

omit [∀ i, LocallyCompactSpace (H i)] [∀ i, SecondCountableTopology (H i)] [IsTopologicalGroup G]
  [∀ i, IsTopologicalGroup (H i)] in
theorem measurableSet_chartAwaySet (hp : ∀ i, Continuous (D.p i)) (S : Finset ι) :
    MeasurableSet {g : G | ∀ i, i ∉ S → D.p i g ∈ D.K i} := by
  have : {g : G | ∀ i, i ∉ S → D.p i g ∈ D.K i} = ⋂ i, ⋂ (_ : i ∉ S), D.p i ⁻¹' D.K i := by
    ext g; simp
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (hp i).measurable (D.isOpen_K i).measurableSet

/-- **The chart lemma as an equality of measures** (π-λ, via `Measure.pi_eq`): on
$\{g : p_i(g)\in K_i\ (i\notin S)\}$, the image of $\mu$ under $(p_i)_{i\in S}$ is
$\mu(\operatorname{box}(\emptyset))\cdot\bigotimes_{i\in S}\omega_i(K_i)^{-1}\omega_i$. -/
@[kb "weil1982" "§2.3, p. 21 (the measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem map_restrict_chart_eq_pi (hp : ∀ i, Continuous (D.p i)) (μ : Measure G) [μ.IsMulLeftInvariant]
    (ω : ∀ i, Measure (H i)) [∀ i, (ω i).IsHaarMeasure] (hωK : ∀ i, ω i (D.K i) ≠ ⊤)
    (h0 : μ (D.chartBox ∅ (fun i => D.K i)) ≠ ⊤) (h0' : μ (D.chartBox ∅ (fun i => D.K i)) ≠ 0)
    (S : Finset ι) :
    (μ.restrict {g : G | ∀ i, i ∉ S → D.p i g ∈ D.K i}).map (fun g (i : S) => D.p i g) =
      μ (D.chartBox ∅ (fun i => D.K i)) •
        Measure.pi (fun i : S => ((ω i (D.K i)).toNNReal)⁻¹ • ω i) := by
  set c := μ (D.chartBox ∅ (fun i => D.K i))
  have hK0 : ∀ i, ω i (D.K i) ≠ 0 := fun i => (D.isOpen_K i).measure_ne_zero _ ⟨1, D.one_mem_K i⟩
  have hproj : Measurable fun (g : G) (i : S) => D.p i g :=
    measurable_pi_iff.mpr fun i => (hp i).measurable
  have key : Measure.pi (fun i : S => ((ω i (D.K i)).toNNReal)⁻¹ • ω i) =
      c⁻¹ • (μ.restrict {g : G | ∀ i, i ∉ S → D.p i g ∈ D.K i}).map (fun g (i : S) => D.p i g) := by
    refine Measure.pi_eq fun s hs => ?_
    set U : ∀ i, Set (H i) := fun i => if h : i ∈ S then s ⟨i, h⟩ else univ
    have hU : ∀ i ∈ S, MeasurableSet (U i) := fun i hi => by simp only [U, hi, dite_true]; exact hs _
    have hset : {g : G | ∀ i, i ∉ S → D.p i g ∈ D.K i} ∩ (fun g (i : S) => D.p i g) ⁻¹' Set.pi univ s =
        D.chartBox S U := by
      ext g
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_imp_iff,
        ChartData.chartBox, U]
      constructor
      · rintro ⟨h1, h2⟩ i
        by_cases hi : i ∈ S
        · simp only [hi, ite_true, dite_true]; exact h2 ⟨i, hi⟩
        · simp only [hi, ite_false]; exact h1 i hi
      · intro h
        refine ⟨fun i hi => by simpa [hi] using h i, fun i => ?_⟩
        have := h i
        simpa [i.2] using this
    rw [Measure.smul_apply, Measure.map_apply hproj (MeasurableSet.univ_pi hs),
      Measure.restrict_apply (hproj (MeasurableSet.univ_pi hs)), inter_comm, hset,
      D.measure_chartBox_of_measurable hp μ ω hωK h0 S U hU, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel h0' h0, one_mul, ← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv ((ENNReal.toNNReal_ne_zero).mpr ⟨hK0 i, hωK i⟩),
      ENNReal.coe_toNNReal (hωK i), div_eq_mul_inv, mul_comm]
    simp only [U, i.2, dite_true]
  rw [key, smul_smul, ENNReal.mul_inv_cancel h0' h0, one_smul]

end ChartData

end

end QuadFormsKB.Tamagawa.Measure.Weil
