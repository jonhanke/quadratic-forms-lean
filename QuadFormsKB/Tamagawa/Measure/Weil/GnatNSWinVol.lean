/-
# The lattice index $[\mathfrak L : \mathfrak L_N]$ by volumes

**Layer:** as in `GnatNSWinIndex`: a number field $F$, $K = F(\delta)$, a finite place $v$, levels $M_w$, $N$.

* **`measure_addSubgroup_eq_relIndex_mul`**: additive coset counting (the additive form of `measure_subgroup_eq_relIndex_mul`).
* In the coordinates $E^3\cong(F_v^2)^3$ (`toE`): $\mathfrak L = \prod_l\Phi^{-1}(\prod_{w\mid v}\mathfrak p_w^{k_{l,w}})$ with
  $k_{0,w} = k_{1,w} = M_w - s_w$, $k_{2,w} = M_w - s_w - \min(e_\alpha(w),e_\beta(w))$, so
  **`vol_Lc`**: $\mathrm{vol}(\mathfrak L) = c_v^3\prod_{l,w}\mathrm{vol}(\mathfrak p_w^{k_{l,w}})$; and **`vol_Lwc`**:
  $\mathrm{vol}(\mathfrak L_N) = \mathrm{vol}(\mathfrak p_v^{N-s})^5\,\mathrm{vol}(\mathfrak p_v^{N-s-\min(e_a,e_b)})$.

Source: Weil 1982, §2.2 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinConst
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinCover

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic LocalDensity

section AddCount

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]

/-- **Additive coset counting:** for open additive subgroups $B\le A$ of finite index and an additive-left-invariant
measure, $\mu(A) = [A:B]\,\mu(B)$. -/
theorem measure_addSubgroup_eq_relIndex_mul (μ : Measure G) [μ.IsAddLeftInvariant] {A B : AddSubgroup G}
    (hB : IsOpen (B : Set G)) (hBA : B ≤ A) (hfin : B.relIndex A ≠ 0) :
    μ (A : Set G) = (B.relIndex A : ℝ≥0∞) * μ (B : Set G) := by
  classical
  set B' := B.addSubgroupOf A
  have : B'.FiniteIndex := ⟨hfin⟩
  have : Finite (A ⧸ B') := AddSubgroup.finite_quotient_of_finiteIndex
  have : Fintype (A ⧸ B') := Fintype.ofFinite _
  let r : A ⧸ B' → G := fun q => ((Quotient.out q : A) : G)
  have hU : (A : Set G) = ⋃ q, r q +ᵥ (B : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_vadd_set, vadd_eq_add, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨(QuotientAddGroup.mk ⟨x, hx⟩ : A ⧸ B'), ?_⟩
      obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add B' ⟨x, hx⟩
      refine ⟨-((h : A) : G), B.neg_mem (AddSubgroup.mem_addSubgroupOf.mp h.2), ?_⟩
      simp only [r, hh, AddSubgroup.coe_add, add_neg_cancel_right]
    · rintro ⟨q, b, hb, rfl⟩
      exact A.add_mem (Quotient.out q).2 (hBA hb)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => r q +ᵥ (B : Set G)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ ⟨b', hb', he⟩
    apply hqq'
    have hrel : -(r q) + r q' = b + -b' := by
      rw [eq_add_neg_iff_add_eq, add_assoc]
      change -(r q) + (r q' + b') = b
      rw [show r q' + b' = r q + b from he, neg_add_cancel_left]
    have : (QuotientAddGroup.mk (Quotient.out q) : A ⧸ B') = QuotientAddGroup.mk (Quotient.out q') := by
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      change -(r q) + r q' ∈ B
      rw [hrel]; exact B.add_mem hb (B.neg_mem hb')
    simpa only [QuotientAddGroup.out_eq'] using this
  rw [hU, measure_iUnion hdisj (fun q => (hB.vadd (r q)).measurableSet), tsum_fintype]
  simp only [measure_vadd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem addRelIndex_ne_zero_of_isOpen {H K : AddSubgroup G} (hK : IsCompact (K : Set G)) (hH : IsOpen (H : Set G)) :
    H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hU : IsOpen ((H.addSubgroupOf K : AddSubgroup K) : Set K) := hH.preimage continuous_subtype_val
  have : DiscreteTopology (K ⧸ H.addSubgroupOf K) := QuotientAddGroup.discreteTopology hU
  have : Finite (K ⧸ H.addSubgroupOf K) := finite_of_compact_of_discrete
  exact AddSubgroup.index_ne_zero_of_finite

end AddCount

section Coords

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (v : HeightOneSpectrum (𝓞 F))
  (M : HeightOneSpectrum (𝓞 K) → ℕ)

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

variable (d) in
/-- The coordinates $(F_v^2)^3\cong E^3$. -/
def toE : (Fin 3 → Fin 2 → Fv) →+ (Fin 3 → E) where
  toFun c l := ⟨c l 0, c l 1⟩
  map_zero' := by funext l; rfl
  map_add' c c' := by funext l; rfl

theorem toE_surjective : Function.Surjective (toE d v) := fun η =>
  ⟨fun l => ![(η l).re, (η l).im], by funext l; rfl⟩

/-- The local box $\prod_{w\mid v}B_{l,w}$ of $\mathfrak L$ in the coordinate $l$. -/
def boxL (l : Fin 3) (w : PlaceSet (K := K) v) : Set (w.1.adicCompletion K) :=
  if l = 2 then latTwoAB w.1 (M w.1) (algebraMap K (w.1.adicCompletion K) (α : K))
    (algebraMap K (w.1.adicCompletion K) (β : K)) else latTwo w.1 (M w.1)

/-- The measure on the coordinates. -/
abbrev volC : Measure (Fin 3 → Fin 2 → Fv) := Measure.pi fun _ : Fin 3 => volVN (ι := Fin 2) v

include hb₀ in
theorem coe_Lc :
    (((LSub hb₁ α β v M).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) : Set (Fin 3 → Fin 2 → Fv)) =
      Set.pi Set.univ fun l => localPiCLE bK v ⁻¹' Set.pi Set.univ (boxL v M (α := α) (β := β) l) := by
  ext c
  simp only [SetLike.mem_coe, AddSubgroup.mem_comap, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage]
  have hq : ∀ (w : PlaceSet (K := K) v) (l : Fin 3), qlh hb₁ v w ((toE d v c) l) = localPiCLE bK v (c l) w := by
    intro w l
    rw [qlh_apply, quadLocalHom_eq_localPi hb₀ hb₁, localPiCLE_apply]
    have : (![((toE d v) c l).re, ((toE d v) c l).im] : Fin 2 → Fv) = c l := by
      funext i; fin_cases i <;> rfl
    rw [this]
  constructor
  · intro h l w
    have := h w
    simp only [hq] at this
    obtain ⟨p0, p1, p2, p3⟩ := this
    fin_cases l
    · simpa [boxL, latTwo] using p0
    · simpa [boxL, latTwo] using p1
    · simpa [boxL, latTwoAB] using And.intro p2 p3
  · intro h w
    show (fun l => qlh hb₁ v w ((toE d v c) l)) ∈ _
    simp only [hq]
    have h0 := h 0 w
    have h1 := h 1 w
    have h2 := h 2 w
    simp only [boxL, latTwo, latTwoAB] at h0 h1 h2
    exact ⟨by simpa using h0, by simpa using h1, by simpa using h2.1, by simpa using h2.2⟩

variable (a b) in
/-- The box of $\mathfrak L_N$ in the real part of coordinate $l$. -/
def boxW (N : ℕ) (l : Fin 3) : Set Fv := if l = 2 then latTwoAB v N Av Bv else latTwo v N

theorem coe_Lwc (N : ℕ) :
    (((LwinSub a b d v N).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) : Set (Fin 3 → Fin 2 → Fv)) =
      Set.pi Set.univ fun l => Set.pi Set.univ ![boxW a b v N l, latTwo v N] := by
  ext c
  simp only [SetLike.mem_coe, AddSubgroup.mem_comap, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨⟨p0, p1, p2, p3⟩, q⟩ l i
    fin_cases l <;> fin_cases i
    · exact p0
    · exact q 0
    · exact p1
    · exact q 1
    · exact ⟨p2, p3⟩
    · exact q 2
  · intro h
    refine ⟨⟨h 0 0, h 1 0, (h 2 0).1, (h 2 0).2⟩, fun l => ?_⟩
    fin_cases l
    · exact h 0 1
    · exact h 1 1
    · exact h 2 1

theorem latTwo_eq' {k : Type} [Field k] [NumberField k] (u : HeightOneSpectrum (𝓞 k)) {m : ℕ} (h : sExp u ≤ m) :
    latTwo u m = (Analysis.latticeV u ((m - sExp u : ℕ) : ℤ) : Set (u.adicCompletion k)) :=
  latTwo_eq (valued_two_eq u) h

theorem latTwoAB_eq' {k : Type} [Field k] [NumberField k] (u : HeightOneSpectrum (𝓞 k)) {x y : 𝓞 k} (hx : x ≠ 0)
    (hy : y ≠ 0) {m : ℕ} (h : sExp u + min (eExp x hx u) (eExp y hy u) ≤ m) :
    latTwoAB u m (algebraMap k (u.adicCompletion k) (x : k)) (algebraMap k (u.adicCompletion k) (y : k)) =
      (Analysis.latticeV u ((m - sExp u - min (eExp x hx u) (eExp y hy u) : ℕ) : ℤ) : Set (u.adicCompletion k)) :=
  latTwoAB_eq (valued_two_eq u) (valued_eExp x hx u) (valued_eExp y hy u) h

theorem boxL_eq (hMd : ∀ w, nsLevK hα0 hβ0 w ≤ M w) (l : Fin 3) (w : PlaceSet (K := K) v) :
    boxL v M (α := α) (β := β) l w = (Analysis.latticeV w.1 ((M w.1 - sExp w.1 -
      (if l = 2 then min (eExp α hα0 w.1) (eExp β hβ0 w.1) else 0) : ℕ) : ℤ) : Set _) := by
  have hm := hMd w.1
  unfold nsLevK at hm
  unfold boxL
  split_ifs
  · exact latTwoAB_eq' w.1 hα0 hβ0 (by omega)
  · rw [Nat.sub_zero]; exact latTwo_eq' w.1 (by omega)

include hb₀ in
/-- **$\mathrm{vol}(\mathfrak L) = \prod_l c_v\prod_{w\mid v}\mathrm{vol}(B_{l,w})$.** -/
theorem vol_Lc : volC v (((LSub hb₁ α β v M).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) :
      Set (Fin 3 → Fin 2 → Fv)) =
    ∏ l : Fin 3, ((localConst bK v : ℝ≥0∞) * ∏ w : PlaceSet (K := K) v,
      Analysis.selfDualV w.1 (boxL v M (α := α) (β := β) l w)) := by
  rw [coe_Lc hb₀ hb₁ v M, volC, Measure.pi_pi]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [volVN_preimage_localPi (bK := bK) v, placeMeasure, Measure.pi_pi]
  refine MeasurableSet.univ_pi fun w => ?_
  unfold boxL; split_ifs
  · exact measurableSet_latTwoAB _ _ _
  · exact measurableSet_latTwo _

/-- **$\mathrm{vol}(\mathfrak L_N) = \prod_l\mathrm{vol}(B'_l)\,\mathrm{vol}(\{|2x|\le q^{-N}\})$.** -/
theorem vol_Lwc (N : ℕ) : volC v (((LwinSub a b d v N).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) :
      Set (Fin 3 → Fin 2 → Fv)) =
    ∏ l : Fin 3, (Analysis.selfDualV v (boxW a b v N l) * Analysis.selfDualV v (latTwo v N)) := by
  rw [coe_Lwc, volC, Measure.pi_pi]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [volVN, Measure.pi_pi, Fin.prod_univ_two]
  rfl

theorem isOpen_latticeV' {k : Type} [Field k] [NumberField k] (u : HeightOneSpectrum (𝓞 k)) (j : ℤ) :
    IsOpen (Analysis.latticeV u j : Set (u.adicCompletion k)) := by
  rw [QuadFormsKB.Analysis.coe_latticeV]
  refine IsUltrametricDist.isOpen_closedBall _ ?_
  rw [Ne, norm_eq_zero]; exact zpow_ne_zero _ (QuadFormsKB.HN.ϖ_ne_zero u)

include hb₀ in
/-- **$[\mathfrak L : \mathfrak L_N]\cdot\mathrm{vol}(\mathfrak L_N) = \mathrm{vol}(\mathfrak L)$.** -/
theorem relIndex_L_mul_vol (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hMd : ∀ w, nsLevK hα0 hβ0 w ≤ M w) {N : ℕ}
    (hN : sExp v + min (eExp a ha0 v) (eExp b hb0 v) ≤ N)
    (hMN : ∀ w : PlaceSet (K := K) v,
      (M w.1 : ℤ) ≤ ramE v w.1 * ((N : ℤ) - sExp v - eExp a ha0 v)) :
    ((LwinSub a b d v N).relIndex (LSub hb₁ α β v M) : ℝ≥0∞) *
        volC v (((LwinSub a b d v N).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) : Set _) =
      volC v (((LSub hb₁ α β v M).comap (toE d v) : AddSubgroup (Fin 3 → Fin 2 → Fv)) : Set _) := by
  set Lc := (LSub hb₁ α β v M).comap (toE d v)
  set Lwc := (LwinSub a b d v N).comap (toE d v)
  have hle : Lwc ≤ Lc := AddSubgroup.comap_mono (lwin_le_L hb₀ hb₁ v M ha0 hMN)
  have hidx : Lwc.relIndex Lc = (LwinSub a b d v N).relIndex (LSub hb₁ α β v M) := by
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (toE_surjective v)]
  have hopen : IsOpen (Lwc : Set (Fin 3 → Fin 2 → Fv)) := by
    rw [coe_Lwc]
    refine isOpen_set_pi Set.finite_univ fun l _ => isOpen_set_pi Set.finite_univ fun i _ => ?_
    have h1 : IsOpen (latTwo v N) := by rw [latTwo_eq' v (by omega)]; exact isOpen_latticeV' v _
    fin_cases i
    · unfold boxW; split_ifs
      · rw [latTwoAB_eq' v ha0 hb0 hN]; exact isOpen_latticeV' v _
      · exact h1
    · exact h1
  have hcpt : IsCompact (Lc : Set (Fin 3 → Fin 2 → Fv)) := by
    rw [coe_Lc hb₀ hb₁ v M]
    refine isCompact_univ_pi fun l => ?_
    refine (localPiCLE bK v).toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun w => ?_)
    rw [boxL_eq hα0 hβ0 v M hMd]
    exact QuadFormsKB.Analysis.isCompact_latticeV w.1 _
  rw [← hidx, measure_addSubgroup_eq_relIndex_mul (volC v) hopen hle (addRelIndex_ne_zero_of_isOpen hcpt hopen)]

end Coords

end QuadFormsKB.Tamagawa.Measure.Weil
