import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerBox
import QuadFormsKB.Tamagawa.Measure.Weil.LintegralPiProd

/-!
# The adelic cone measure as a product of local cone measures

$F$ totally real, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$). From the box formula
(`coneMeasure_coneBox`, primitive points outside $S$):

* **`muLocSO_soStab_good`**: at a good place $\mu_v(SO(L_v)) = \sigma_{C,v}(C^\circ_v\cap L_v^{\mathrm{prim}})\,\mu'_v(SO(L'_v))$;
* **`boxConst_insert`**: $M(S) = \sigma_{C,v}(L_v^{\mathrm{prim}})\,M(S\cup\{v\})$ for a good place $v\notin S$;
* positivity and finiteness of $M(S)$.
-/

open MeasureTheory Set Matrix Filter Topology
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra QuadFormsKB.Tamagawa.Measure.LerayReal

variable {F : Type} [Field F] [NumberField F] {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k}
  (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-! ### Products modified at finitely many places -/

theorem multipliable_ite {ι : Type*} [DecidableEq ι] {a : ι → ℝ} (ha : Multipliable a) (S : Finset ι)
    (hS : ∀ v ∈ S, a v ≠ 0) : Multipliable fun v => if v ∈ S then 1 else a v := by
  set c : ι → ℝ := fun v => if v ∈ S then (a v)⁻¹ else 1
  have hc : HasProd c (∏ v ∈ S, (a v)⁻¹) := by
    have h1 : HasProd c (∏ v ∈ S, c v) := hasProd_prod_of_ne_finset_one fun v hv => by simp [c, hv]
    rwa [Finset.prod_congr rfl fun v hv => (show c v = (a v)⁻¹ by simp [c, hv])] at h1
  convert (ha.hasProd.mul hc).multipliable using 1
  funext v
  by_cases hv : v ∈ S
  · simp [c, hv, hS v hv]
  · simp [c, hv]

/-- Splitting off one more place: $\prod'_{v\notin S}a_v = a_{v_0}\prod'_{v\notin S\cup\{v_0\}}a_v$. -/
theorem tprod_ite_insert {ι : Type*} [DecidableEq ι] {a : ι → ℝ} (ha : Multipliable a) (S : Finset ι)
    (hS : ∀ v, a v ≠ 0) {v₀ : ι} (hv₀ : v₀ ∉ S) :
    (∏' v, if v ∈ S then 1 else a v) = a v₀ * ∏' v, if v ∈ insert v₀ S then 1 else a v := by
  have hm := multipliable_ite ha S fun v _ => hS v
  have h := tprod_eq_prod_mul_tprod_ite (fun v => if v ∈ S then 1 else a v) hm {v₀}
    (fun v hv => by rw [Finset.mem_singleton] at hv; subst hv; simp [hv₀, hS])
  rw [h, Finset.prod_singleton, if_neg hv₀]
  congr 1
  refine tprod_congr fun v => ?_
  by_cases h1 : v = v₀
  · subst h1; simp
  · by_cases h2 : v ∈ S
    · simp [h1, h2]
    · simp [h1, h2]

/-! ### Good places -/

theorem norm_eq_one_of_valued {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    ‖x‖ = 1 := by
  have h1 : ‖x‖ ≤ ‖(1 : v.adicCompletion F)‖ := Valued.toNormedField.norm_le_iff.mpr (by rw [hx, map_one])
  have h2 : ‖(1 : v.adicCompletion F)‖ ≤ ‖x‖ := Valued.toNormedField.norm_le_iff.mpr (by rw [hx, map_one])
  rw [norm_one] at h1 h2
  exact le_antisymm h1 h2

theorem cVv_good {v : HeightOneSpectrum (𝓞 F)} (h2c : Valued.v (cAt c₀ (σV v) * 2) = 1) : cVv c₀ k v = 1 := by
  have h : absTwoM v c₀ = 1 := by
    rw [ConeFinite.absTwoM_eq_norm, mul_comm]
    exact norm_eq_one_of_valued h2c
  simp [cVv, h]

theorem measurableSet_primCone (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet {z : ConeFinite.ConeTV v QC | PrimV v z.1} :=
  measurable_subtype_coe (measurableSet_primVec v)

/-- **At a good place** $\mu_v(SO(L_v)) = \sigma_{C,v}(L_v^{\mathrm{prim}})\,\mu'_v(SO(L'_v))$. -/
theorem muLocSO_soStab_good {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badCone hc hQ' hk) :
    muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC)) =
      ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') {z | PrimV v z.1} *
        muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀')) := by
  have hg := good_of_not_mem_badCone hc hQ' hk hv
  rw [← ofCoordV_image_good hc hQ' hk v hg.1 hg.2,
    muLocSO_ofCoordV_image hc hQ' hk v (measurableSet_primCone v) (measurableSet_BfinV hc hQ' hk v),
    muPV_BfinV hc hQ' hk v]
  rw [show (absTwoM v c₀ ^ (2 * k + 2))⁻¹ = cVv c₀ k v from rfl, cVv_good hg.2, ENNReal.ofReal_one, one_mul]

theorem sigConeV_prim_ne_zero {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badCone hc hQ' hk) :
    ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') {z | PrimV v z.1} ≠ 0 := by
  intro h0
  have h := muLocSO_soStab_good hc hQ' hk hv
  rw [h0, zero_mul] at h
  exact (muLocSO_soStabSO_pos QC (nondeg_QC hc hQ') v one_pos) h

theorem sigConeV_prim_ne_top {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badCone hc hQ' hk) :
    ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') {z | PrimV v z.1} ≠ ⊤ := by
  intro ht
  have h := muLocSO_soStab_good hc hQ' hk hv
  rw [ht, ENNReal.top_mul (muLocSO_soStabSO_pos Q₀' hQ' v one_pos)] at h
  rw [muLocSO_soStabSO] at h
  exact ENNReal.ofReal_ne_top h

/-! ### Changing $S$ -/

open Classical in
/-- **$M(S) = \sigma_{C,v_0}(L_{v_0}^{\mathrm{prim}})\,M(S\cup\{v_0\})$** for a place $v_0\notin S$ ($S\supseteq$ `badCone`). -/
theorem boxConst_insert [IsEmpty {w : InfinitePlace F // w.IsComplex}] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : badCone hc hQ' hk ⊆ S) {v₀ : HeightOneSpectrum (𝓞 F)} (hv₀ : v₀ ∉ S) :
    boxConst hc hQ' S =
      ConeFinite.sigConeV v₀ QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') {z | PrimV v₀ z.1} *
        boxConst hc hQ' (insert v₀ S) := by
  have hbad : v₀ ∉ badCone hc hQ' hk := fun h => hv₀ (hS h)
  have hg := good_of_not_mem_badCone hc hQ' hk hbad
  have hmult := multipliable_muLocSO_one QC (nondeg_QC hc hQ') (by omega : k + 1 + 1 ≠ 0) (by omega : k + 1 + 1 ≠ 2)
  have hpos : ∀ v, (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal ≠ 0 := fun v =>
    (ENNReal.toReal_pos (muLocSO_soStabSO_pos QC (nondeg_QC hc hQ') v one_pos)
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)).ne'
  have hsplit := tprod_ite_insert hmult S hpos hv₀
  have hfin : muLocSO v₀ QC 1 (soStabSO v₀ QC : Set (SOv v₀ QC)) ≠ ⊤ := by
    rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top
  have hnn : 0 ≤ ∏' v, (if v ∈ insert v₀ S then 1 else (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal) :=
    tprod_nonneg fun v => by split_ifs; exacts [zero_le_one, ENNReal.toReal_nonneg]
  unfold boxConst
  rw [hsplit, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin, muLocSO_soStab_good hc hQ' hk hbad,
    Finset.prod_insert hv₀, cVv_good hg.2, ENNReal.ofReal_one, one_mul]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  ring


/-! ### Positivity of $M(S)$ and the iterated relation -/

section Iterate

include hc in
theorem cRw_pos (w : {w : InfinitePlace F // w.IsReal}) : 0 < cRw c₀ k w := by
  have : 0 < |2 * ConeAdelic.cRe c₀ w| := abs_pos.mpr (mul_ne_zero two_ne_zero (ConeAdelic.cRe_ne_zero hc w))
  exact inv_pos.mpr (pow_pos this _)

include hc in
theorem cVv_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < cVv c₀ k v :=
  inv_pos.mpr (pow_pos (absTwoM_pos v hc) _)

open Classical in
include hc hQ' hk in
theorem tprod_ite_muLocSO_pos (S : Finset (HeightOneSpectrum (𝓞 F))) :
    0 < ∏' v, (if v ∈ S then 1 else (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal) := by
  have hmult := multipliable_muLocSO_one QC (nondeg_QC hc hQ') (by omega : k + 1 + 1 ≠ 0) (by omega : k + 1 + 1 ≠ 2)
  have hpos : ∀ v, 0 < (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal := fun v =>
    ENNReal.toReal_pos (muLocSO_soStabSO_pos QC (nondeg_QC hc hQ') v one_pos)
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have h := tprod_eq_prod_mul_tprod_ite _ hmult S fun v _ => (hpos v).ne'
  have htot : 0 < ∏' v, (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal := by
    have := tprod_siegelDensity_pos (by omega : 3 ≤ k + 1 + 1) QC (nondeg_QC hc hQ')
    rw [← finFactor_one QC (nondeg_QC hc hQ')] at this
    exact this
  have hS : 0 < ∏ v ∈ S, (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal :=
    Finset.prod_pos fun v _ => hpos v
  rw [h] at htot
  exact pos_of_mul_pos_right htot hS.le

include hk in
theorem boxConst_ne_zero [IsEmpty {w : InfinitePlace F // w.IsComplex}] (S : Finset (HeightOneSpectrum (𝓞 F))) : boxConst hc hQ' S ≠ 0 := by
  classical
  unfold boxConst
  refine ENNReal.div_ne_zero.mpr ⟨?_, coneMuP_Bbox_ne_top hc hQ'⟩
  refine mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr cF_pos').ne' ?_) (mul_ne_zero ?_ ?_)
  · refine Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero (ENNReal.ofReal_pos.mpr (cRw_pos hc w)).ne'
      (mul_ne_zero (by rw [volume_W₀]; exact one_ne_zero) (V₀_spec hQ' w).2.1)
  · exact Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero (ENNReal.ofReal_pos.mpr (cVv_pos hc v)).ne'
      (muLocSO_soStabSO_pos Q₀' hQ' v one_pos)
  · exact (ENNReal.ofReal_pos.mpr (tprod_ite_muLocSO_pos hc hQ' hk S)).ne'

include hk in
theorem boxConst_ne_top [IsEmpty {w : InfinitePlace F // w.IsComplex}] (S : Finset (HeightOneSpectrum (𝓞 F))) : boxConst hc hQ' S ≠ ⊤ := by
  classical
  unfold boxConst
  refine ENNReal.div_ne_top ?_ (coneMuP_Bbox_ne_zero hc hQ' hk)
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
    (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
  · exact ENNReal.prod_ne_top fun w _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by rw [volume_W₀]; exact ENNReal.one_ne_top) (V₀_spec hQ' w).2.2)
  · exact ENNReal.prod_ne_top fun v _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)

open Classical in
/-- **$M(S) = \prod_{v\in T\smallsetminus S}\sigma_{C,v}(L_v^{\mathrm{prim}})\cdot M(S\cup T)$.** -/
theorem boxConst_union [IsEmpty {w : InfinitePlace F // w.IsComplex}] (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), badCone hc hQ' hk ⊆ S →
      boxConst hc hQ' S = (∏ v ∈ T \ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ')
        {z | PrimV v z.1}) * boxConst hc hQ' (S ∪ T) := by
  induction T using Finset.induction_on with
  | empty => intro S _; simp
  | insert a T ha ih =>
    intro S hS
    rw [ih S hS]
    by_cases haS : a ∈ S
    · have h1 : insert a T \ S = T \ S := by
        ext v; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h | h, h'⟩
          · exact absurd (h ▸ haS) h'
          · exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨Or.inr h, h'⟩
      have h2 : S ∪ insert a T = S ∪ T := by
        ext v; simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (h ▸ haS)
          · exact Or.inr h
        · rintro (h | h); exacts [Or.inl h, Or.inr (Or.inr h)]
      rw [h1, h2]
    · have h1 : insert a T \ S = insert a (T \ S) := by
        ext v; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h | h, h'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, h'⟩
        · rintro (h | ⟨h, h'⟩)
          · exact ⟨Or.inl h, h ▸ haS⟩
          · exact ⟨Or.inr h, h'⟩
      have h2 : S ∪ insert a T = insert a (S ∪ T) := by
        ext v; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      have haST : a ∉ S ∪ T := by simp [haS, ha]
      have haTS : a ∉ T \ S := by simp [ha]
      rw [h1, h2, Finset.prod_insert haTS,
        boxConst_insert hc hQ' hk (S ∪ T) (hS.trans Finset.subset_union_left) haST]
      ring

end Iterate

/-! ### Cone measures of lattice sets -/

section Lattice

theorem sigConeV_preimage {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate)
    {K : Set (Fin N → v.adicCompletion F)} (hK : MeasurableSet K) :
    ConeFinite.sigConeV v Q hQ (Subtype.val ⁻¹' K) = ConeAdelic.coneMeas Q hQ v K := by
  have hemb := MeasurableEmbedding.subtype_coe (ConeFinite.measurableSet_coneSetV v Q)
  rw [ConeFinite.sigConeV, hemb.comap_apply, Subtype.image_preimage_coe]
  set μ := LerayFinite.lerayMeasure v (Analysis.haarV v) (LocalDensity.NF.Qp v Q) (LocalDensity.NF.nondegenerate_Qp v hQ) 0
  have hnull : μ (ConeFinite.coneSetV v Q)ᶜ = 0 := by
    refine measure_mono_null (t := {x | LerayFinite.Qv v (LocalDensity.NF.Qp v Q) x ≠ 0} ∪ {0}) ?_ ?_
    · intro x hx
      by_cases h : LerayFinite.Qv v (LocalDensity.NF.Qp v Q) x = 0
      · right
        simp only [Set.mem_compl_iff, ConeFinite.coneSetV, Set.mem_ofPred_eq, not_and, not_not] at hx
        exact hx h
      · left; exact h
    · exact measure_union_null (ConeFinite.lerayMeasure_compl_level v (Analysis.haarV v) (LocalDensity.NF.Qp v Q)
        (LocalDensity.NF.nondegenerate_Qp v hQ) 0) (LerayFinite.lerayMeasure_singleton_zero v _ _ _ 0)
  show μ (ConeFinite.coneSetV v Q ∩ K) = μ K
  rw [inter_comm]
  exact measure_inter_conull' (measure_mono_null (fun x hx => hx.2) hnull)

end Lattice


/-! ### The convergent products -/

section Products

/-- $\sigma_{C,v}(C^\circ_v\cap L_v^{\mathrm{prim}})$. -/
abbrev sigPrim (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0∞ :=
  ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') {z | PrimV v z.1}

open Classical in
/-- $P(S) = \prod'_{v\notin S}\sigma_{C,v}(L_v^{\mathrm{prim}})$, a positive convergent product. -/
theorem hasProd_sigPrim (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) :
    ∃ P, 0 < P ∧ HasProd (fun v => if v ∈ S then 1 else (sigPrim hc hQ' v).toReal) P := by
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀'))).toReal
  have hαm := multipliable_muLocSO_one QC (nondeg_QC hc hQ') (by omega : k + 1 + 1 ≠ 0) (by omega : k + 1 + 1 ≠ 2)
  have hβm := multipliable_muLocSO_one Q₀' hQ' (by omega : k ≠ 0) (by omega : k ≠ 2)
  have hαpos : ∀ v, 0 < α v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos QC (nondeg_QC hc hQ') v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hβpos : ∀ v, 0 < β v := fun v => ENNReal.toReal_pos (muLocSO_soStabSO_pos Q₀' hQ' v one_pos)
    (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hB : 0 < ∏' v, β v := by
    have := tprod_siegelDensity_pos hk Q₀' hQ'
    rw [← finFactor_one Q₀' hQ'] at this
    exact this
  have hA : 0 < ∏' v, α v := by
    have := tprod_siegelDensity_pos (by omega : 3 ≤ k + 1 + 1) QC (nondeg_QC hc hQ')
    rw [← finFactor_one QC (nondeg_QC hc hQ')] at this
    exact this
  have hoff : ∀ v ∉ S, α v = (if v ∈ S then 1 else (sigPrim hc hQ' v).toReal) * β v := fun v hv => by
    rw [if_neg hv]
    simp only [α, β]
    rw [muLocSO_soStab_good hc hQ' hk (fun h => hv (hS h)), ENNReal.toReal_mul]
  have h := hasProd_of_ratio S hαm.hasProd hβm.hasProd hB.ne' hβpos hαpos hoff
  refine ⟨_, ?_, h⟩
  refine mul_pos (div_pos hA hB) (Finset.prod_pos fun v hv => ?_)
  rw [if_pos hv, one_mul]
  exact div_pos (hβpos v) (hαpos v)

/-- The value $P(S)$. -/
def primProd (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ :=
  open Classical in ∏' v, if v ∈ S then 1 else (sigPrim hc hQ' v).toReal

theorem primProd_pos (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) :
    0 < primProd hc hQ' S := by
  classical
  obtain ⟨P, hP, h⟩ := hasProd_sigPrim hc hQ' hk S hS
  rw [primProd, h.tprod_eq]; exact hP

theorem hasProd_primProd (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) :
    open Classical in HasProd (fun v => if v ∈ S then 1 else (sigPrim hc hQ' v).toReal) (primProd hc hQ' S) := by
  classical
  obtain ⟨P, -, h⟩ := hasProd_sigPrim hc hQ' hk S hS
  rw [primProd, h.tprod_eq]; exact h

include hk in
/-- $\sigma_{C,v}(C^\circ_v\cap L_v)$ = `coneTotal` ($n\ge3$). -/
theorem sigConeV_latL (v : HeightOneSpectrum (𝓞 F)) :
    ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (Subtype.val ⁻¹' LocalZeta.latL v (k + 1 + 1)) =
      ENNReal.ofReal (LerayCone.coneTotal QC v) := by
  rw [sigConeV_preimage v QC _ (LocalZeta.measurableSet_latL v), ConeAdelic.coneMeas_latL QC _ (by omega) v]

theorem prim_subset_latL (v : HeightOneSpectrum (𝓞 F)) :
    {z : ConeFinite.ConeTV v QC | PrimV v z.1} ⊆ Subtype.val ⁻¹' LocalZeta.latL v (k + 1 + 1) :=
  fun _ hz => hz.1

include hk in
theorem sigPrim_le_coneTotal (v : HeightOneSpectrum (𝓞 F)) :
    sigPrim hc hQ' v ≤ ENNReal.ofReal (LerayCone.coneTotal QC v) := by
  rw [← sigConeV_latL hc hQ' hk v]; exact measure_mono (prim_subset_latL v)

end Products

end QuadFormsKB.Tamagawa.Measure.Weil

end
