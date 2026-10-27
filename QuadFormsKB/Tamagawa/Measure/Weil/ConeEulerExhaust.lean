import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerProd

/-!
# The adelic cone measure of a lattice box

$F$ totally real, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$), $S\supseteq$ `badCone` a finite
set of finite places, $K_v$ ($v\in S$) measurable. The set
$$X = \{x\in C^\circ(\mathbb A) : x_w\in A_w\ (w\mid\infty),\ x_v\in K_v\ (v\in S),\ x_v\in L_v\ (v\notin S)\}$$
is the increasing union over finite sets $T$ of finite places of the boxes with primitive points outside $S\cup T$
(`Xset_eq_iUnion`). The box formula and $M(S) = \prod_{v\in T\smallsetminus S}\sigma_{C,v}(L_v^{\mathrm{prim}})\,M(S\cup T)$
give, in the limit (**`coneMeasure_Xset`**),
$$\sigma_C(X)\cdot P(S) = M(S)\prod_w\sigma_{C,w}(A_w)\cdot\prod_{v\in S}\sigma_{C,v}(K_v)\prod_{v\notin S}\sigma_{C,v}(L_v),$$
with $P(S) = \prod_{v\notin S}\sigma_{C,v}(L_v^{\mathrm{prim}})\in(0,\infty)$ (`primProd`). The right-hand finite part
is `ConeAdelic.boxMass`.
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

/-- **The lattice box** $\{x : x_w\in A_w,\ x_v\in K_v\ (v\in S),\ x_v\in L_v\ (v\notin S)\}$ in $C^\circ(\mathbb A)$. -/
def Xset (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) :
    Set (adelicCone QC) :=
  {x | (∀ w, coneRpt x w ∈ AR w) ∧ ∀ v, adV x.1 v ∈ ConeAdelic.boxSet S K v}

open Classical in
/-- The approximating boxes: primitive points outside $S\cup T$. -/
def XT (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F))
    (T : Finset (HeightOneSpectrum (𝓞 F))) : Set (adelicCone QC) :=
  coneBox AR (S ∪ T) fun v => Subtype.val ⁻¹' ConeAdelic.boxSet S K v

theorem boxSet_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 F))}
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) : ConeAdelic.boxSet S K v = LocalZeta.latL v (k + 1 + 1) := by
  classical
  simp only [ConeAdelic.boxSet]; convert if_neg hv

theorem boxSet_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))}
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∈ S) : ConeAdelic.boxSet S K v = K v := by
  classical
  simp only [ConeAdelic.boxSet]; convert if_pos hv

theorem measurableSet_boxSet {S : Finset (HeightOneSpectrum (𝓞 F))}
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (ConeAdelic.boxSet S K v) := by
  by_cases hv : v ∈ S
  · rw [boxSet_of_mem hv]; exact hK v hv
  · rw [boxSet_of_not_mem hv]; exact LocalZeta.measurableSet_latL v

open Classical in
theorem XT_mono (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) :
    Monotone (XT AR S K) := by
  intro T T' hTT' x ⟨hR, hV, hP⟩
  refine ⟨hR, fun v hv => ?_, fun v hv => hP v fun h => hv (Finset.union_subset_union (le_refl S) hTT' h)⟩
  by_cases hv' : v ∈ S ∪ T
  · exact hV v hv'
  · have hS : v ∉ S := fun h => hv' (Finset.mem_union_left _ h)
    show adV x.1 v ∈ ConeAdelic.boxSet S K v
    rw [boxSet_of_not_mem hS]
    exact (hP v hv').1

open Classical in
theorem Xset_eq_iUnion (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) :
    Xset AR S K = ⋃ T, XT AR S K T := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨hR, hV⟩
    have hfin : {v | ¬ PrimV v (adV x.1 v)}.Finite := x.2.2.2.2
    refine ⟨hfin.toFinset, hR, fun v _ => hV v, fun v hv => ?_⟩
    by_contra h
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h))
  · rintro ⟨T, hR, hV, hP⟩
    refine ⟨hR, fun v => ?_⟩
    by_cases hv : v ∈ S ∪ T
    · exact hV v hv
    · have hS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
      rw [boxSet_of_not_mem hS]
      exact (hP v hv).1

section Limit

variable [IsEmpty {w : InfinitePlace F // w.IsComplex}]

open Classical in
/-- **The approximating boxes, multiplied out**:
$\sigma_C(X_T)\prod_{v\in T\smallsetminus S}\sigma_{C,v}(L_v^{\mathrm{prim}}) =
  M(S)\prod_w\sigma_{C,w}(A_w)\prod_{v\in S}\sigma_{C,v}(K_v)\prod_{v\in T\smallsetminus S}\sigma_{C,v}(L_v)$. -/
theorem coneMeasure_XT_mul
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    coneMeasure hc hQ' hk (XT AR S K T) * ∏ v ∈ T \ S, sigPrim hc hQ' v =
      boxConst hc hQ' S * (∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
        ((∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (Subtype.val ⁻¹' K v)) *
          ∏ v ∈ T \ S, ENNReal.ofReal (LerayCone.coneTotal QC v)) := by
  classical
  have hAV : ∀ v, MeasurableSet (Subtype.val ⁻¹' ConeAdelic.boxSet S K v : Set (ConeFinite.ConeTV v QC)) :=
    fun v => measurable_subtype_coe (measurableSet_boxSet hK v)
  rw [XT, coneMeasure_coneBox hc hQ' hk hAR (S ∪ T) (hS.trans Finset.subset_union_left) hAV,
    boxConst_union hc hQ' hk T S hS]
  have hsplit : S ∪ T = S ∪ (T \ S) := by simp
  have hdisj : Disjoint S (T \ S) := Finset.disjoint_sdiff
  rw [hsplit, Finset.prod_union hdisj]
  have h1 : ∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ')
      (Subtype.val ⁻¹' ConeAdelic.boxSet S K v) =
      ∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (Subtype.val ⁻¹' K v) :=
    Finset.prod_congr rfl fun v hv => by rw [boxSet_of_mem (K := K) hv]
  have h2 : ∏ v ∈ T \ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ')
      (Subtype.val ⁻¹' ConeAdelic.boxSet S K v) = ∏ v ∈ T \ S, ENNReal.ofReal (LerayCone.coneTotal QC v) :=
    Finset.prod_congr rfl fun v hv => by
      rw [boxSet_of_not_mem (K := K) (Finset.mem_sdiff.mp hv).2, sigConeV_latL hc hQ' hk v]
  rw [h1, h2]
  ring

open Classical in
/-- **The cone measure of a lattice box** ($F$ totally real, $k\ge3$, $S\supseteq$ `badCone`):
$$\sigma_C(X)\cdot P(S) = M(S)\prod_w\sigma_{C,w}(A_w)\cdot\prod_{v\in S}\sigma_{C,v}(K_v)
  \prod_{v\notin S}\sigma_{C,v}(L_v),$$
the finite part being `ConeAdelic.boxMass`. -/
@[kb "weil1982" "§2.3, p. 21; §4.5, p. 108 (the cone measure is the product of the local cone measures) [unverified page]"]
theorem coneMeasure_Xset_mul
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) :
    coneMeasure hc hQ' hk (Xset AR S K) * ENNReal.ofReal (primProd hc hQ' S) =
      boxConst hc hQ' S * (∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) * ConeAdelic.boxMass QC hQ S K := by
  classical
  -- the two products over `T \ S`, as products over `T` of functions modified on `S`
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if v ∈ S then 1 else (sigPrim hc hQ' v).toReal
  set b : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if v ∈ S then 1 else LerayCone.coneTotal QC v
  have hb : Multipliable b := ConeAdelic.multipliable_coneTotal_off QC hQ (by omega) S
  have hprod_a : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∏ v ∈ T \ S, sigPrim hc hQ' v = ENNReal.ofReal (∏ v ∈ T, a v) := by
    intro T
    rw [← Finset.prod_sdiff (Finset.inter_subset_left : T ∩ S ⊆ T) (f := a),
      Finset.prod_eq_one (s := T ∩ S) (fun v hv => by simp [a, (Finset.mem_inter.mp hv).2]), mul_one,
      Finset.sdiff_inter_self_left, ENNReal.ofReal_prod_of_nonneg fun v _ => by
        simp only [a]; split_ifs; exacts [zero_le_one, ENNReal.toReal_nonneg]]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [show a v = (sigPrim hc hQ' v).toReal by simp [a, (Finset.mem_sdiff.mp hv).2], ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (sigPrim_le_coneTotal hc hQ' hk v)
  have hprod_b : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∏ v ∈ T \ S, ENNReal.ofReal (LerayCone.coneTotal QC v) = ENNReal.ofReal (∏ v ∈ T, b v) := by
    intro T
    rw [← Finset.prod_sdiff (Finset.inter_subset_left : T ∩ S ⊆ T) (f := b),
      Finset.prod_eq_one (s := T ∩ S) (fun v hv => by simp [b, (Finset.mem_inter.mp hv).2]), mul_one,
      Finset.sdiff_inter_self_left, ENNReal.ofReal_prod_of_nonneg fun v _ => by
        simp only [b]; split_ifs; exacts [zero_le_one, ConeAdelic.coneTotal_nonneg QC hQ (by omega) v]]
    exact Finset.prod_congr rfl fun v hv => by simp [b, (Finset.mem_sdiff.mp hv).2]
  -- limits
  have hlimX : Tendsto (fun T => coneMeasure hc hQ' hk (XT AR S K T)) atTop
      (𝓝 (coneMeasure hc hQ' hk (Xset AR S K))) := by
    rw [Xset_eq_iUnion]
    exact tendsto_measure_iUnion_atTop (XT_mono AR S K)
  have hlimA : Tendsto (fun T => ENNReal.ofReal (∏ v ∈ T, a v)) atTop (𝓝 (ENNReal.ofReal (primProd hc hQ' S))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hasProd_primProd hc hQ' hk S hS)
  have hlimB : Tendsto (fun T => ENNReal.ofReal (∏ v ∈ T, b v)) atTop (𝓝 (ENNReal.ofReal (∏' v, b v))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hb.hasProd
  have hP := primProd_pos hc hQ' hk S hS
  -- `P(S) ≤ ∏' b`, so the right-hand limit is not `0 · ∞`
  have hPB : primProd hc hQ' S ≤ ∏' v, b v := by
    refine le_of_tendsto_of_tendsto' (hasProd_primProd hc hQ' hk S hS) hb.hasProd fun T => ?_
    refine Finset.prod_le_prod₀ (fun v _ => ?_) fun v _ => ?_
    · split_ifs; exacts [zero_le_one, ENNReal.toReal_nonneg]
    · simp only [b]; split_ifs
      · exact le_refl _
      · exact ENNReal.toReal_le_of_le_ofReal (ConeAdelic.coneTotal_nonneg QC hQ (by omega) v)
          (sigPrim_le_coneTotal hc hQ' hk v)
  have hBpos : ENNReal.ofReal (∏' v, b v) ≠ 0 := (ENNReal.ofReal_pos.mpr (hP.trans_le hPB)).ne'
  have hL : Tendsto (fun T => coneMeasure hc hQ' hk (XT AR S K T) * ENNReal.ofReal (∏ v ∈ T, a v)) atTop
      (𝓝 (coneMeasure hc hQ' hk (Xset AR S K) * ENNReal.ofReal (primProd hc hQ' S))) :=
    ENNReal.Tendsto.mul hlimX (Or.inr ENNReal.ofReal_ne_top) hlimA (Or.inl (ENNReal.ofReal_pos.mpr hP).ne')
  set R := boxConst hc hQ' S * (∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
    ∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (Subtype.val ⁻¹' K v)
  have hR : Tendsto (fun T => R * ENNReal.ofReal (∏ v ∈ T, b v)) atTop (𝓝 (R * ENNReal.ofReal (∏' v, b v))) :=
    ENNReal.Tendsto.const_mul hlimB (Or.inl hBpos)
  have heq : (fun T => coneMeasure hc hQ' hk (XT AR S K T) * ENNReal.ofReal (∏ v ∈ T, a v)) =
      fun T => R * ENNReal.ofReal (∏ v ∈ T, b v) := by
    funext T
    rw [← hprod_a, ← hprod_b, coneMeasure_XT_mul hc hQ' hk hAR S hS hK T]
    simp only [R]; ring
  rw [heq] at hL
  rw [tendsto_nhds_unique hL hR]
  simp only [R, ConeAdelic.boxMass]
  rw [Finset.prod_congr rfl fun v hv => sigConeV_preimage v QC _ (hK v hv)]
  ring

end Limit

end QuadFormsKB.Tamagawa.Measure.Weil

end
