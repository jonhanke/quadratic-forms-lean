import QuadFormsKB.Tamagawa.Measure.Weil.ConeBoxNF
import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerGaussHat
import QuadFormsKB.Tamagawa.Measure.Weil.SphereBoxNF
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerIdeleNF
import QuadFormsKB.Tamagawa.Measure.Weil.SphereEulerHat

/-!
# The cone Euler identifications over every number field
$F$ any number field, $Q_0 = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$ ($k\ge3$), $\sigma_C$ = `coneMeasure`. From
the box formula `coneMeasure_coneBoxNF`, the same steps as for totally real $F$ with the complex places:

* $M(S) = \sigma_{C,v}(L_v^{\mathrm{prim}})\,M(S\cup\{v\})$ (**`boxConstNF'_insert`**), positivity and finiteness;
* lattice boxes by exhaustion (**`coneMeasure_XsetNF_mul`**);
* the archimedean pushforward and **`lintegral_coneMeasure_prodNF`**:
  $\int\mathbf 1_Y\prod_w\varphi_w\,d\sigma_C = \kappa(S)\,\mathrm{boxMass}(S,K)\prod_{w\ \mathrm{real}}\int\varphi_w\,d\sigma_{C,w}
  \prod_{w\ \mathrm{complex}}\int\psi_w\,d\sigma_{C,w}$;
* **`adelicConeEuler_gaussTestNF`**, **`adelicConeEuler_gaussTestHatNF`**: `AdelicConeEuler` for $\Phi$ = `gaussTest` and
  $\hat\Phi$ = `gaussTestHat` over every number field.
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

/-- **The complex cone measure is σ-finite** ($k\ge1$): the closed balls have finite measure. -/
theorem sigmaFinite_sigConeC {k : ℕ} {c : ℂ} {Q' : QuadForm ℂ k} (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0)
    (hk : 1 ≤ k) : SigmaFinite (ConeComplex.sigCone (Q' := Q') hc) :=
  ⟨⟨{ set := fun n : ℕ => {z | ‖(z : Fin (k + 1 + 1) → ℂ)‖ ≤ n}
      set_mem := fun _ => trivial
      finite := fun n => ConeComplex.sigCone_closedBall_lt_top hc hQ' hk n
      spanning := by
        refine eq_univ_of_forall fun z => mem_iUnion.mpr ?_
        obtain ⟨n, hn⟩ := exists_nat_ge ‖(z : Fin (k + 1 + 1) → ℂ)‖
        exact ⟨n, hn⟩ }⟩⟩

variable {F : Type} [Field F] [NumberField F] {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k}
  (hc : c₀ ≠ 0) (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k)

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-! ### The constant $M(S)$ -/

section Const

open Classical in
/-- **$M(S) = \sigma_{C,v_0}(L_{v_0}^{\mathrm{prim}})\,M(S\cup\{v_0\})$** for a place $v_0\notin S$ ($S\supseteq$ `badCone`;
every number field). -/
theorem boxConstNF'_insert (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {v₀ : HeightOneSpectrum (𝓞 F)} (hv₀ : v₀ ∉ S) :
    boxConstNF' hc hQ' S = sigPrim hc hQ' v₀ * boxConstNF' hc hQ' (insert v₀ S) := by
  have hbad : v₀ ∉ badCone hc hQ' hk := fun h => hv₀ (hS h)
  have hg := good_of_not_mem_badCone hc hQ' hk hbad
  have hmult := multipliable_muLocSO_one QC (nondeg_QC hc hQ') (by omega : k + 1 + 1 ≠ 0) (by omega : k + 1 + 1 ≠ 2)
  have hpos : ∀ v, (muLocSO v QC 1 (soStabSO v QC : Set (SOv v QC))).toReal ≠ 0 := fun v =>
    (ENNReal.toReal_pos (muLocSO_soStabSO_pos QC (nondeg_QC hc hQ') v one_pos)
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)).ne'
  have hsplit := tprod_ite_insert hmult S hpos hv₀
  have hfin : muLocSO v₀ QC 1 (soStabSO v₀ QC : Set (SOv v₀ QC)) ≠ ⊤ := by
    rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top
  unfold boxConstNF'
  rw [hsplit, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin, muLocSO_soStab_good hc hQ' hk hbad,
    Finset.prod_insert hv₀, cVv_good hg.2, ENNReal.ofReal_one, one_mul]
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  ring

include hk in
theorem boxConstNF'_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) : boxConstNF' hc hQ' S ≠ 0 := by
  classical
  unfold boxConstNF'
  refine ENNReal.div_ne_zero.mpr ⟨?_, coneMuP_BboxNF_ne_top hc hQ'⟩
  refine mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr (mul_pos cF_pos' cxWeil_pos)).ne'
    (mul_ne_zero ?_ ?_)) (mul_ne_zero ?_ ?_)
  · refine Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero (ENNReal.ofReal_pos.mpr (cRw_pos hc w)).ne'
      (mul_ne_zero (by rw [volume_W₀]; exact one_ne_zero) (V₀_spec hQ' w).2.1)
  · refine Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero (ENNReal.coe_ne_zero.mpr (inv_ne_zero (pow_ne_zero _
      (nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero (cCx_ne hc w))))))
      (mul_ne_zero volume_W₀C_ne_zero (V₀C_spec hQ' w).2.1)
  · exact Finset.prod_ne_zero_iff.mpr fun v _ => mul_ne_zero (ENNReal.ofReal_pos.mpr (cVv_pos hc v)).ne'
      (muLocSO_soStabSO_pos Q₀' hQ' v one_pos)
  · exact (ENNReal.ofReal_pos.mpr (tprod_ite_muLocSO_pos hc hQ' hk S)).ne'

include hk in
theorem boxConstNF'_ne_top (S : Finset (HeightOneSpectrum (𝓞 F))) : boxConstNF' hc hQ' S ≠ ⊤ := by
  classical
  unfold boxConstNF'
  refine ENNReal.div_ne_top ?_ (coneMuP_BboxNF_ne_zero hc hQ' hk)
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ?_))
    (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
  · exact ENNReal.prod_ne_top fun w _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by rw [volume_W₀]; exact ENNReal.one_ne_top) (V₀_spec hQ' w).2.2)
  · exact ENNReal.prod_ne_top fun w _ => ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top volume_W₀C_ne_top (V₀C_spec hQ' w).2.2)
  · exact ENNReal.prod_ne_top fun v _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)

open Classical in
/-- **$M(S) = \prod_{v\in T\smallsetminus S}\sigma_{C,v}(L_v^{\mathrm{prim}})\cdot M(S\cup T)$** (every number field). -/
theorem boxConstNF'_union (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), badCone hc hQ' hk ⊆ S →
      boxConstNF' hc hQ' S = (∏ v ∈ T \ S, sigPrim hc hQ' v) * boxConstNF' hc hQ' (S ∪ T) := by
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
        boxConstNF'_insert hc hQ' hk (S ∪ T) (hS.trans Finset.subset_union_left) haST]
      ring

end Const

/-! ### Lattice boxes -/

section Exhaust

/-- **The lattice box** $\{x : x_w\in A_w,\ x_v\in K_v\ (v\in S),\ x_v\in L_v\ (v\notin S)\}$, real and complex places. -/
def XsetNF (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) :
    Set (adelicCone QC) :=
  {x | (∀ w, coneRpt x w ∈ AR w) ∧ (∀ w, coneCpt x w ∈ AC w) ∧ ∀ v, adV x.1 v ∈ ConeAdelic.boxSet S K v}

open Classical in
/-- The approximating boxes: primitive points outside $S\cup T$. -/
def XTNF (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F))
    (T : Finset (HeightOneSpectrum (𝓞 F))) : Set (adelicCone QC) :=
  coneBoxNF AR AC (S ∪ T) fun v => Subtype.val ⁻¹' ConeAdelic.boxSet S K v

open Classical in
theorem XTNF_mono (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) :
    Monotone (XTNF AR AC S K) := by
  intro T T' hTT' x ⟨hR, hC, hV, hP⟩
  refine ⟨hR, hC, fun v hv => ?_, fun v hv => hP v fun h => hv (Finset.union_subset_union (le_refl S) hTT' h)⟩
  by_cases hv' : v ∈ S ∪ T
  · exact hV v hv'
  · have hS : v ∉ S := fun h => hv' (Finset.mem_union_left _ h)
    show adV x.1 v ∈ ConeAdelic.boxSet S K v
    rw [boxSet_of_not_mem hS]
    exact (hP v hv').1

open Classical in
theorem XsetNF_eq_iUnion (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w)))
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) :
    XsetNF AR AC S K = ⋃ T, XTNF AR AC S K T := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨hR, hC, hV⟩
    have hfin : {v | ¬ PrimV v (adV x.1 v)}.Finite := x.2.2.2.2
    refine ⟨hfin.toFinset, hR, hC, fun v _ => hV v, fun v hv => ?_⟩
    by_contra h
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.mpr h))
  · rintro ⟨T, hR, hC, hV, hP⟩
    refine ⟨hR, hC, fun v => ?_⟩
    by_cases hv : v ∈ S ∪ T
    · exact hV v hv
    · have hS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
      rw [boxSet_of_not_mem hS]
      exact (hP v hv).1

open Classical in
theorem coneMeasure_XTNF_mul
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    {AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w))}
    (hAC : ∀ w, MeasurableSet (AC w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    coneMeasure hc hQ' hk (XTNF AR AC S K T) * ∏ v ∈ T \ S, sigPrim hc hQ' v =
      boxConstNF' hc hQ' S * ((∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
        ∏ w, ConeComplex.sigCone (cCx_ne hc w) (AC w)) *
        ((∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (Subtype.val ⁻¹' K v)) *
          ∏ v ∈ T \ S, ENNReal.ofReal (LerayCone.coneTotal QC v)) := by
  classical
  have hAV : ∀ v, MeasurableSet (Subtype.val ⁻¹' ConeAdelic.boxSet S K v : Set (ConeFinite.ConeTV v QC)) :=
    fun v => measurable_subtype_coe (measurableSet_boxSet hK v)
  rw [XTNF, coneMeasure_coneBoxNF hc hQ' hk hAR hAC (S ∪ T) (hS.trans Finset.subset_union_left) hAV,
    boxConstNF'_union hc hQ' hk T S hS]
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
/-- **The cone measure of a lattice box over every number field** ($k\ge3$, $S\supseteq$ `badCone`):
$\sigma_C(X)\cdot P(S) = M(S)\prod_{w\mid\infty}\sigma_{C,w}(A_w)\cdot\mathrm{boxMass}(S,K)$. -/
theorem coneMeasure_XsetNF_mul
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    {AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w))}
    (hAC : ∀ w, MeasurableSet (AC w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) :
    coneMeasure hc hQ' hk (XsetNF AR AC S K) * ENNReal.ofReal (primProd hc hQ' S) =
      boxConstNF' hc hQ' S * ((∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
        ∏ w, ConeComplex.sigCone (cCx_ne hc w) (AC w)) * ConeAdelic.boxMass QC hQ S K := by
  classical
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
  have hlimX : Tendsto (fun T => coneMeasure hc hQ' hk (XTNF AR AC S K T)) atTop
      (𝓝 (coneMeasure hc hQ' hk (XsetNF AR AC S K))) := by
    rw [XsetNF_eq_iUnion]
    exact tendsto_measure_iUnion_atTop (XTNF_mono AR AC S K)
  have hlimA : Tendsto (fun T => ENNReal.ofReal (∏ v ∈ T, a v)) atTop (𝓝 (ENNReal.ofReal (primProd hc hQ' S))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hasProd_primProd hc hQ' hk S hS)
  have hlimB : Tendsto (fun T => ENNReal.ofReal (∏ v ∈ T, b v)) atTop (𝓝 (ENNReal.ofReal (∏' v, b v))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hb.hasProd
  have hP := primProd_pos hc hQ' hk S hS
  have hPB : primProd hc hQ' S ≤ ∏' v, b v := by
    refine le_of_tendsto_of_tendsto' (hasProd_primProd hc hQ' hk S hS) hb.hasProd fun T => ?_
    refine Finset.prod_le_prod₀ (fun v _ => ?_) fun v _ => ?_
    · split_ifs; exacts [zero_le_one, ENNReal.toReal_nonneg]
    · simp only [b]; split_ifs
      · exact le_refl _
      · exact ENNReal.toReal_le_of_le_ofReal (ConeAdelic.coneTotal_nonneg QC hQ (by omega) v)
          (sigPrim_le_coneTotal hc hQ' hk v)
  have hBpos : ENNReal.ofReal (∏' v, b v) ≠ 0 := (ENNReal.ofReal_pos.mpr (hP.trans_le hPB)).ne'
  have hL : Tendsto (fun T => coneMeasure hc hQ' hk (XTNF AR AC S K T) * ENNReal.ofReal (∏ v ∈ T, a v)) atTop
      (𝓝 (coneMeasure hc hQ' hk (XsetNF AR AC S K) * ENNReal.ofReal (primProd hc hQ' S))) :=
    ENNReal.Tendsto.mul hlimX (Or.inr ENNReal.ofReal_ne_top) hlimA (Or.inl (ENNReal.ofReal_pos.mpr hP).ne')
  set R := boxConstNF' hc hQ' S * ((∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
    ∏ w, ConeComplex.sigCone (cCx_ne hc w) (AC w)) *
    ∏ v ∈ S, ConeFinite.sigConeV v QC (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') (Subtype.val ⁻¹' K v)
  have hR : Tendsto (fun T => R * ENNReal.ofReal (∏ v ∈ T, b v)) atTop (𝓝 (R * ENNReal.ofReal (∏' v, b v))) :=
    ENNReal.Tendsto.const_mul hlimB (Or.inl hBpos)
  have heq : (fun T => coneMeasure hc hQ' hk (XTNF AR AC S K T) * ENNReal.ofReal (∏ v ∈ T, a v)) =
      fun T => R * ENNReal.ofReal (∏ v ∈ T, b v) := by
    funext T
    rw [← hprod_a, ← hprod_b, coneMeasure_XTNF_mul hc hQ' hk hAR hAC S hS hK T]
    simp only [R]; ring
  rw [heq] at hL
  rw [tendsto_nhds_unique hL hR]
  simp only [R, ConeAdelic.boxMass]
  rw [Finset.prod_congr rfl fun v hv => sigConeV_preimage v QC _ (hK v hv)]
  ring

end Exhaust

/-! ### The archimedean pushforward and integrals of product functions -/

section Product

/-- **The constant** $\kappa(S) = M(S)/P(S)$ (every number field). -/
def coneConstNF (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ≥0∞ :=
  boxConstNF' hc hQ' S / ENNReal.ofReal (primProd hc hQ' S)

theorem coneConstNF_ne_top (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S) :
    coneConstNF hc hQ' S ≠ ⊤ :=
  ENNReal.div_ne_top (boxConstNF'_ne_top hc hQ' hk S) (ENNReal.ofReal_pos.mpr (primProd_pos hc hQ' hk S hS)).ne'

open Classical in
theorem coneMeasure_XsetNF
    {AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hAR : ∀ w, MeasurableSet (AR w))
    {AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ConeComplex.ConeT (QwC c₀ Q₀' w))}
    (hAC : ∀ w, MeasurableSet (AC w))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) :
    coneMeasure hc hQ' hk (XsetNF AR AC S K) =
      coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S K * ((∏ w, ConeReal.sigCone (cRe_ne hc w) (AR w)) *
        ∏ w, ConeComplex.sigCone (cCx_ne hc w) (AC w)) := by
  have h := coneMeasure_XsetNF_mul hc hQ' hk hAR hAC S hS hK hQ
  have hP := primProd_pos hc hQ' hk S hS
  rw [coneConstNF, ENNReal.div_eq_inv_mul]
  rw [mul_comm, ← ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr hP).ne' ENNReal.ofReal_ne_top] at h
  rw [h, ENNReal.div_eq_inv_mul]
  ring

/-- The archimedean components of a point of the adelic cone (real and complex places). -/
def archPtNF (x : adelicCone QC) : (∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w)) ×
    (∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (QwC c₀ Q₀' w)) :=
  (fun w => coneRpt x w, fun w => coneCpt x w)

theorem measurable_archPtNF : Measurable (archPtNF (c₀ := c₀) (Q₀' := Q₀')) :=
  (measurable_pi_iff.mpr fun w => measurable_coneRpt w).prodMk (measurable_pi_iff.mpr fun w => measurable_coneCpt w)

open Classical in
/-- **The archimedean pushforward of $\sigma_C|_Y$** is $\kappa(S)\,\mathrm{boxMass}(S,K)\prod_w\sigma_{C,w}$ (every
number field). -/
theorem map_restrict_coneMeasureNF (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) (hfin : ConeAdelic.boxMass QC hQ S K ≠ ⊤) :
    ((coneMeasure hc hQ' hk).restrict (Yset S K)).map archPtNF =
      ((coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S K) •
        Measure.pi fun w => ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)).prod
        (Measure.pi fun w => ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne hc w)) := by
  have hσ : ∀ w : {w : InfinitePlace F // w.IsReal}, SigmaFinite (ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) :=
    fun w => sigmaFinite_sigCone (cRe_ne hc w) (gramDetR_QRe' hQ' w) (by omega)
  have hσC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne hc w)) :=
    fun w => sigmaFinite_sigConeC (cCx_ne hc w) (gramDetC_QCx' hQ' w) (by omega)
  set c := coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S K
  have hc_top : c ≠ ⊤ := ENNReal.mul_ne_top (coneConstNF_ne_top hc hQ' hk S hS) hfin
  have h3C := AdelicSphereSetup.finiteSpanningSetsIn_smul
    (Measure.FiniteSpanningSetsIn.pi fun w => (ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)).toFiniteSpanningSetsIn)
    hc_top
  have h3D := Measure.FiniteSpanningSetsIn.pi fun w =>
    (ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne hc w)).toFiniteSpanningSetsIn
  refine (Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi h3C h3D ?_).symm
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  have hs' : ∀ w, MeasurableSet (s w) := fun w => hs w (mem_univ w)
  have ht' : ∀ w, MeasurableSet (t w) := fun w => ht w (mem_univ w)
  have hst : MeasurableSet (univ.pi s ×ˢ univ.pi t) := (MeasurableSet.univ_pi hs').prod (MeasurableSet.univ_pi ht')
  rw [Measure.map_apply measurable_archPtNF hst, Measure.restrict_apply (measurable_archPtNF hst)]
  have : archPtNF ⁻¹' (univ.pi s ×ˢ univ.pi t) ∩ Yset S K = XsetNF s t S K := by
    ext x; simp [XsetNF, Yset, archPtNF, and_assoc]
  rw [this, coneMeasure_XsetNF hc hQ' hk hs' ht' S hS hK hQ, Measure.smul_apply, smul_eq_mul, Measure.pi_pi,
    Measure.pi_pi]
  ring

open Classical in
/-- **The adelic cone integral of a product test function over every number field** ($k\ge3$, $S\supseteq$
`badCone`): $\int\mathbf 1_Y(x)\prod_{w\ \mathrm{real}}\varphi_w(x_w)\prod_{w\ \mathrm{complex}}\psi_w(x_w)\,d\sigma_C =
\kappa(S)\,\mathrm{boxMass}(S,K)\prod_{w\ \mathrm{real}}\int\varphi_w\,d\sigma_{C,w}\prod_{w\ \mathrm{complex}}\int\psi_w\,
d\sigma_{C,w}$. -/
@[kb "weil1982" "§2.3, p. 21; §4.5, p. 108 (the cone integral as a product of local integrals) [unverified page]"]
theorem lintegral_coneMeasure_prodNF (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    {K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)} (hK : ∀ v ∈ S, MeasurableSet (K v))
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) (hfin : ConeAdelic.boxMass QC hQ S K ≠ ⊤)
    {φ : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w) → ℝ≥0∞} (hφ : ∀ w, Measurable (φ w))
    {ψ : ∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (QwC c₀ Q₀' w) → ℝ≥0∞}
    (hψ : ∀ w, Measurable (ψ w)) :
    ∫⁻ x, (Yset S K).indicator (fun x => (∏ w, φ w (coneRpt x w)) * ∏ w, ψ w (coneCpt x w)) x
        ∂coneMeasure hc hQ' hk =
      coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S K *
        ((∏ w, ∫⁻ z, φ w z ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) *
          ∏ w, ∫⁻ z, ψ w z ∂ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne hc w)) := by
  have hσ : ∀ w : {w : InfinitePlace F // w.IsReal}, SigmaFinite (ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) :=
    fun w => sigmaFinite_sigCone (cRe_ne hc w) (gramDetR_QRe' hQ' w) (by omega)
  have hσC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne hc w)) :=
    fun w => sigmaFinite_sigConeC (cCx_ne hc w) (gramDetC_QCx' hQ' w) (by omega)
  have hG : Measurable fun y : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w) =>
      ∏ w, φ w (y w) := Finset.measurable_prod _ fun w _ => (hφ w).comp (measurable_pi_apply w)
  have hH : Measurable fun y : ∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (QwC c₀ Q₀' w) =>
      ∏ w, ψ w (y w) := Finset.measurable_prod _ fun w _ => (hψ w).comp (measurable_pi_apply w)
  have hGH : Measurable fun p : (∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w)) ×
      (∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (QwC c₀ Q₀' w)) =>
      (∏ w, φ w (p.1 w)) * ∏ w, ψ w (p.2 w) := (hG.comp measurable_fst).mul (hH.comp measurable_snd)
  rw [lintegral_indicator (measurableSet_Yset hK)]
  refine (lintegral_map hGH measurable_archPtNF).symm.trans ?_
  have hc_top : coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S K ≠ ⊤ :=
    ENNReal.mul_ne_top (coneConstNF_ne_top hc hQ' hk S hS) hfin
  have hsf : SigmaFinite ((coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S K) •
      Measure.pi fun w => ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) := by
    lift coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S K to NNReal using hc_top with c
    rw [show ((c : ℝ≥0∞) • Measure.pi fun w => ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) =
      c • Measure.pi fun w => ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w) from rfl]
    infer_instance
  rw [map_restrict_coneMeasureNF hc hQ' hk S hS hK hQ hfin, lintegral_prod_mul hG.aemeasurable hH.aemeasurable,
    lintegral_smul_measure, lintegral_pi_prod _ _ hφ, lintegral_pi_prod _ _ hψ, smul_eq_mul, mul_assoc]

end Product

/-! ### The Gaussian test functions -/

section Euler

open Classical in
/-- **The Gaussian test function on the adelic cone, every number field.** -/
theorem gaussTest_coneNF (S : Finset (HeightOneSpectrum (𝓞 F))) (x : adelicCone QC) :
    gaussTest F (k + 1 + 1) x.1 =
      (Yset S fun v => LocalZeta.latL v (k + 1 + 1)).indicator
        (fun x => (∏ w, gaussRe (coneRpt x w).1) * ∏ w, ENNReal.ofReal (gaussFnC (coneCpt x w).1)) x := by
  have hY : x ∈ Yset S (fun v => LocalZeta.latL v (k + 1 + 1)) ↔ ∀ v, adV x.1 v ∈ LocalZeta.latL v (k + 1 + 1) := by
    simp only [Yset, mem_ofPred_eq]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [boxSet_of_mem hv]
    · rw [boxSet_of_not_mem hv]
  rw [gaussTest, ofReal_gV_fstNF]
  by_cases h : ∀ v, adV x.1 v ∈ LocalZeta.latL v (k + 1 + 1)
  · rw [indicator_of_mem ((mem_OHatVec_iff _).mpr h), indicator_of_mem (hY.mpr h), one_mul]
    rfl
  · rw [indicator_of_notMem (fun h' => h ((mem_OHatVec_iff _).mp h')),
      indicator_of_notMem (fun h' => h (hY.mp h')), zero_mul]

theorem gaussFnC_le {n : ℕ} (z : Fin n → ℂ) :
    ENNReal.ofReal (gaussFnC z) ≤ ENNReal.ofReal (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2))) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have := sq_pi_norm_le_sum z
  nlinarith [Real.pi_pos]

open Classical in
/-- **`AdelicConeEuler` from the cone integral of a product test function** (every number field): $\kappa$ is
absorbed into the factor at one infinite place. -/
theorem adelicConeEuler_of_prodNF (hQ : (coneFormO c₀ Q₀').Nondegenerate) {Φ : AdeleSpace F (Fin (k + 1 + 1)) → ℝ≥0∞}
    (κ : ℝ≥0∞) (hκ : κ ≠ ⊤) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (k + 1 + 1) → v.adicCompletion F)) (hK : ∀ v ∈ S, Bornology.IsBounded (K v))
    (φ : ∀ w : {w : InfinitePlace F // w.IsReal}, ConeReal.ConeT (Qw c₀ Q₀' w) → ℝ≥0∞) (hφm : ∀ w, Measurable (φ w))
    (a C : {w : InfinitePlace F // w.IsReal} → ℝ) (ha : ∀ w, 0 < a w) (hC : ∀ w, 0 ≤ C w)
    (hφ : ∀ w z, φ w z ≤ ENNReal.ofReal (C w * Real.exp (-(a w * ‖(z : Fin (k + 1 + 1) → ℝ)‖ ^ 2))))
    (ψ : ∀ w : {w : InfinitePlace F // w.IsComplex}, ConeComplex.ConeT (QwC c₀ Q₀' w) → ℝ≥0∞)
    (hψm : ∀ w, Measurable (ψ w))
    (ac Cc : {w : InfinitePlace F // w.IsComplex} → ℝ) (hac : ∀ w, 0 < ac w) (hCc : ∀ w, 0 ≤ Cc w)
    (hψ : ∀ w z, ψ w z ≤ ENNReal.ofReal (Cc w * Real.exp (-(ac w * ‖(z : Fin (k + 1 + 1) → ℂ)‖ ^ 2))))
    (heq : ∫⁻ x, Φ x.1 ∂coneMeasure hc hQ' hk =
      κ * ConeAdelic.boxMass QC hQ S K * ((∏ w, ∫⁻ z, φ w z ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) *
        ∏ w, ∫⁻ z, ψ w z ∂ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne hc w))) :
    AdelicConeEuler hc Q₀' hQ (coneData hc hQ' hk).σ Φ := by
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hκ1 : ∀ p : Prop, [Decidable p] → ENNReal.ofReal (if p then κ.toReal else 1) = if p then κ else 1 := by
    intro p _; split_ifs
    · exact ENNReal.ofReal_toReal hκ
    · exact ENNReal.ofReal_one
  have hκ0 : ∀ p : Prop, [Decidable p] → 0 ≤ (if p then κ.toReal else 1) := by
    intro p _; split_ifs; exacts [ENNReal.toReal_nonneg, zero_le_one]
  refine ⟨⟨fun w z => (if w.1 = w₀ then κ else 1) * φ w z, fun w z => (if w.1 = w₀ then κ else 1) * ψ w z, a,
    fun w => (if w.1 = w₀ then κ.toReal else 1) * C w, ac, fun w => (if w.1 = w₀ then κ.toReal else 1) * Cc w,
    S, K, ha, fun w => mul_nonneg (hκ0 _) (hC w), fun w z => ?_, hac, fun w => mul_nonneg (hκ0 _) (hCc w),
    fun w z => ?_, hK, ?_⟩⟩
  · rw [mul_assoc, ENNReal.ofReal_mul (hκ0 _), hκ1]
    exact mul_le_mul' le_rfl (hφ w z)
  · rw [mul_assoc, ENNReal.ofReal_mul (hκ0 _), hκ1]
    exact mul_le_mul' le_rfl (hψ w z)
  · show ∫⁻ x, Φ x.1 ∂coneMeasure hc hQ' hk = _
    rw [heq, ConeAdelic.coneIntegral, ConeAdelic.coneBoxMeasure_univ, ConeAdelic.coneIntegralArch]
    simp only [lintegral_const_mul _ (hφm _), lintegral_const_mul _ (hψm _), Finset.prod_mul_distrib]
    have hR : ∏ w : {w : InfinitePlace F // w.IsReal}, (if w.1 = w₀ then κ else 1) = if w₀.IsReal then κ else 1 := by
      by_cases h : w₀.IsReal
      · rw [if_pos h, Finset.prod_eq_single ⟨w₀, h⟩ (fun b _ hb => if_neg fun e : b.1 = w₀ => hb (Subtype.ext e))
          (fun h' => absurd (Finset.mem_univ _) h'), if_pos rfl]
      · rw [if_neg h]; exact Finset.prod_eq_one fun b _ => if_neg fun e : b.1 = w₀ => h (e ▸ b.2)
    have hCx : ∏ w : {w : InfinitePlace F // w.IsComplex}, (if w.1 = w₀ then κ else 1) =
        if w₀.IsReal then 1 else κ := by
      by_cases h : w₀.IsReal
      · rw [if_pos h]; exact Finset.prod_eq_one fun b _ => if_neg fun e : b.1 = w₀ => (not_isReal_iff_isComplex.mpr b.2) (e ▸ h)
      · rw [if_neg h, Finset.prod_eq_single ⟨w₀, not_isReal_iff_isComplex.mp h⟩
          (fun b _ hb => if_neg fun e : b.1 = w₀ => hb (Subtype.ext e)) (fun h' => absurd (Finset.mem_univ _) h'), if_pos rfl]
    rw [hR, hCx]
    by_cases h : w₀.IsReal
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring

open Classical in
/-- **The cone integral of the Gaussian over every number field.** -/
theorem lintegral_gaussTest_coneNF (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : badCone hc hQ' hk ⊆ S)
    (hQ : (ConeFinite.Qcone c₀ Q₀').Nondegenerate) :
    ∫⁻ x, gaussTest F (k + 1 + 1) x.1 ∂coneMeasure hc hQ' hk =
      coneConstNF hc hQ' S * ConeAdelic.boxMass QC hQ S (fun v => LocalZeta.latL v (k + 1 + 1)) *
        ((∏ w, ∫⁻ z, gaussRe z.1 ∂ConeReal.sigCone (Q' := QRe Q₀' w) (cRe_ne hc w)) *
          ∏ w, ∫⁻ z, ENNReal.ofReal (gaussFnC z.1) ∂ConeComplex.sigCone (Q' := QCx Q₀' w) (cCx_ne hc w)) := by
  have hfin : ConeAdelic.boxMass QC hQ S (fun v => LocalZeta.latL v (k + 1 + 1)) ≠ ⊤ := by
    unfold ConeAdelic.boxMass
    refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun v _ => ?_) ENNReal.ofReal_ne_top
    rw [ConeAdelic.coneMeas_latL QC hQ (by omega) v]; exact ENNReal.ofReal_ne_top
  rw [lintegral_congr fun x => gaussTest_coneNF S x]
  exact lintegral_coneMeasure_prodNF hc hQ' hk S hS (fun v _ => LocalZeta.measurableSet_latL v) hQ hfin
    (φ := fun w z => gaussRe z.1) (fun w => measurable_gaussRe.comp measurable_subtype_coe)
    (ψ := fun w z => ENNReal.ofReal (gaussFnC z.1))
    (fun w => (ENNReal.measurable_ofReal.comp measurable_gaussFnC).comp measurable_subtype_coe)

open Classical in
/-- **`AdelicConeEuler` for the Gaussian test function over every number field** ($k\ge3$). -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral of the Gaussian as a product of local factors) [unverified page]"]
theorem adelicConeEuler_gaussTestNF (hQ : (coneFormO c₀ Q₀').Nondegenerate) :
    AdelicConeEuler hc Q₀' hQ (coneData hc hQ' hk).σ (gaussTest F (k + 1 + 1)) :=
  adelicConeEuler_of_prodNF hc hQ' hk hQ (coneConstNF hc hQ' (badCone hc hQ' hk))
    (coneConstNF_ne_top hc hQ' hk _ subset_rfl) (badCone hc hQ' hk) (fun v => LocalZeta.latL v (k + 1 + 1))
    (fun v _ => isBounded_latL v _) (fun w z => gaussRe z.1)
    (fun w => measurable_gaussRe.comp measurable_subtype_coe) (fun _ => Real.pi) (fun _ => 1)
    (fun _ => Real.pi_pos) (fun _ => zero_le_one) (fun w z => by rw [one_mul]; exact gaussRe_le _)
    (fun w z => ENNReal.ofReal (gaussFnC z.1))
    (fun w => (ENNReal.measurable_ofReal.comp measurable_gaussFnC).comp measurable_subtype_coe)
    (fun _ => 2 * Real.pi) (fun _ => 1) (fun _ => by positivity) (fun _ => zero_le_one)
    (fun w z => by rw [one_mul]; exact gaussFnC_le _)
    (lintegral_gaussTest_coneNF hc hQ' hk _ subset_rfl hQ)

open Classical in
/-- **$\hat\Phi$ on the adelic cone, every number field.** -/
theorem gaussTestHat_coneNF (x : adelicCone QC) :
    gaussTestHat QC x.1 = muFinVec F (Fin (k + 1 + 1)) OHatVec *
      (Yset (badHat hc hQ' hk) (KH QC)).indicator
        (fun x => (∏ w, gaussRe (hesAt QC (σR w) *ᵥ (coneRpt x w).1)) *
          ∏ w, ENNReal.ofReal (gaussFnC (hesAt QC (σC w) *ᵥ (coneCpt x w).1))) x := by
  have hY : x ∈ Yset (badHat hc hQ' hk) (KH QC) ↔ ∀ v, adV x.1 v ∈ KH QC v := by
    simp only [Yset, mem_ofPred_eq]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ badHat hc hQ' hk
    · rw [boxSet_of_mem hv]
    · rw [boxSet_of_not_mem hv, KH_eq_latL_of_not_mem hc hQ' hk hv]
  rw [gaussTestHat_apply_gV]
  congr 1
  by_cases h : ∀ v, adV x.1 v ∈ KH QC v
  · rw [indicator_of_mem (show x.1 ∈ {y : AdeleSpace F (Fin (k + 1 + 1)) | ∀ v, adV y v ∈ KH QC v} from h),
      indicator_of_mem (hY.mpr h), ofReal_gV_fstNF]
    simp only [adR_mulVec', hessA_map_projR', adC_mulVec', hessA_map_projC']
    rfl
  · rw [indicator_of_notMem (show x.1 ∉ {y : AdeleSpace F (Fin (k + 1 + 1)) | ∀ v, adV y v ∈ KH QC v} from h),
      indicator_of_notMem (fun h' => h (hY.mp h'))]

include hc hQ' in
theorem hesAt_σR_det_ne_zeroNF (w : {w : InfinitePlace F // w.IsReal}) : (hesAt QC (σR w)).det ≠ 0 := by
  have h := gramDetR_QRe_ne_zero QC (nondeg_QC hc hQ') w
  rw [Siegel.gramDetR, div_ne_zero_iff] at h
  rw [hesAt, ← hessian_map']
  exact h.1

include hc hQ' in
theorem hesAt_σC_det_ne_zero (w : {w : InfinitePlace F // w.IsComplex}) : (hesAt QC (σC w)).det ≠ 0 := by
  rw [hesAt_QCx]
  exact SphericalNF.nondegenerate_cplxForm (nondeg_QC hc hQ') w

/-- A complex Gaussian through an invertible matrix is bounded by a Gaussian. -/
theorem exists_gaussFnC_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ z, ENNReal.ofReal (gaussFnC (M *ᵥ z)) ≤ ENNReal.ofReal (Real.exp (-(a * ‖z‖ ^ 2))) := by
  obtain ⟨b, hb, hbz⟩ := exists_sq_le_mulVec M hM
  refine ⟨2 * Real.pi * b, by positivity, fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)⟩
  have := hbz z
  nlinarith [Real.pi_pos]

/-- **`AdelicConeEuler` for $\hat\Phi$** = `gaussTestHat` over every number field ($k\ge3$). -/
@[kb "weil1982" "§4.5, p. 108 (the cone integral of the Fourier transform of the Gaussian) [unverified page]"]
theorem adelicConeEuler_gaussTestHatNF (hQ : (coneFormO c₀ Q₀').Nondegenerate) :
    AdelicConeEuler hc Q₀' hQ (coneData hc hQ' hk).σ (gaussTestHat (coneFormO c₀ Q₀')) := by
  classical
  set S := badHat hc hQ' hk
  have hS : badCone hc hQ' hk ⊆ S := Finset.subset_union_left
  have hμ : muFinVec F (Fin (k + 1 + 1)) OHatVec ≠ ⊤ := fun h => by
    have := muFinVec_OHatVec_toReal_pos (F := F) (n := k + 1 + 1)
    rw [h, ENNReal.toReal_top] at this
    exact lt_irrefl 0 this
  choose a ha hb using fun w => exists_gaussRe_mulVec_le _ (hesAt_σR_det_ne_zeroNF hc hQ' w)
  choose ac hac hbc using fun w => exists_gaussFnC_mulVec_le _ (hesAt_σC_det_ne_zero hc hQ' w)
  have hfin : ConeAdelic.boxMass QC hQ S (KH QC) ≠ ⊤ :=
    (ConeAdelic.boxMass_lt_top (Q₀ := QC) (hQ := hQ) (by omega) S _ fun v _ => isBounded_KH QC (nondeg_QC hc hQ') v).ne
  have hmR : ∀ w : {w : InfinitePlace F // w.IsReal},
      Measurable fun z : ConeReal.ConeT (Qw c₀ Q₀' w) => gaussRe (hesAt QC (σR w) *ᵥ z.1) := fun w =>
    measurable_gaussRe.comp ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp
      measurable_subtype_coe)
  have hmC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      Measurable fun z : ConeComplex.ConeT (QwC c₀ Q₀' w) => ENNReal.ofReal (gaussFnC (hesAt QC (σC w) *ᵥ z.1)) :=
    fun w => (ENNReal.measurable_ofReal.comp measurable_gaussFnC).comp
      ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp measurable_subtype_coe)
  refine adelicConeEuler_of_prodNF hc hQ' hk hQ (muFinVec F (Fin (k + 1 + 1)) OHatVec * coneConstNF hc hQ' S)
    (ENNReal.mul_ne_top hμ (coneConstNF_ne_top hc hQ' hk S hS)) S (KH QC)
    (fun v _ => isBounded_KH QC (nondeg_QC hc hQ') v) (fun w z => gaussRe (hesAt QC (σR w) *ᵥ z.1)) hmR
    a (fun _ => 1) ha (fun _ => zero_le_one) (fun w z => by rw [one_mul]; exact hb w z.1)
    (fun w z => ENNReal.ofReal (gaussFnC (hesAt QC (σC w) *ᵥ z.1))) hmC
    ac (fun _ => 1) hac (fun _ => zero_le_one) (fun w z => by rw [one_mul]; exact hbc w z.1) ?_
  show ∫⁻ x, gaussTestHat QC x.1 ∂coneMeasure hc hQ' hk = _
  rw [lintegral_congr fun x => gaussTestHat_coneNF hc hQ' hk x, lintegral_const_mul' _ _ hμ,
    lintegral_coneMeasure_prodNF hc hQ' hk S hS (fun v _ => measurableSet_KH QC v) hQ hfin hmR hmC]
  ring

end Euler

end QuadFormsKB.Tamagawa.Measure.Weil

end
