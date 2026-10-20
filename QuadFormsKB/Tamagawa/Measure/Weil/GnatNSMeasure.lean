/-
# Assembly of $\mu_P(\pi(S_0))$ and $\mu_{\mathrm{Tam}}(\Phi(\pi(S_0)))$

**Layer:** $F$ totally real, $K = F(\delta)$ totally real, $-a,-b\gg0$.

* **`nsN`**: $N_v = \{r\in F_v^\times : \varphi_w(r)\in\operatorname{nrd}\Lambda^{(m_w)}_w\ \forall w\mid v\}$; **`tamIdeles_nsXF`**:
  $\mathrm{tamIdeles}_F(X_F) = \omega_\infty(\mathrm{BInf})\cdot\mu_f(\prod_{v\in S}N_v\times\prod_{v\notin S}\mathcal O_v^\times)$.
* **`ns_real_assembly`** (pure algebra): the local-ratio bookkeeping, place by place over $v\in S$ with the places $w\mid v$
  grouped.

Source: Weil 1982, Thm 2.3.1 (∏_v r_v = 1); §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSBox

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace IsDedekindDomain Filter
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat

noncomputable section

/-! ### The $F$-side idele set as a box -/

section FSide

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  {d : 𝓞 F} {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (S : Finset (HeightOneSpectrum (𝓞 F))) (SK : Finset (HeightOneSpectrum (𝓞 K)))
  (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

variable (α β) in
/-- **$N_v = \{r\in F_v^\times : \varphi_w(r)\in\operatorname{nrd}\Lambda^{(m_w)}_w\ \forall w\mid v\}$.** -/
def nsN (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F)ˣ :=
  {r | ∀ (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v),
    Units.map (localRingHom v w h).toMonoidHom r ∈ nL α β mK hmK1 w}

theorem measurableSet_nsN (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (nsN α β mK hmK1 v) := by
  have e : nsN α β mK hmK1 v = ⋂ w : PlaceSet (K := K) v,
      (Units.map (localRingHom v w.1 w.2).toMonoidHom) ⁻¹' nL α β mK hmK1 w.1 := by
    ext r
    simp only [nsN, mem_setOf_eq, mem_iInter, mem_preimage]
    exact ⟨fun h w => h w.1 w.2, fun h w hw => h ⟨w, hw⟩⟩
  rw [e]
  exact MeasurableSet.iInter fun w => (measurableSet_nL mK hmK1 w.1).preimage
    (Continuous.units_map _ (continuous_localRingHom v w.1 w.2)).measurable

include hb₀ hb₁ in
theorem nsN_subset (v : HeightOneSpectrum (𝓞 F)) : nsN α β mK hmK1 v ⊆ unitsVSub v := by
  intro r hr
  obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ v
  have := nL_subset mK hmK1 w (hr w hw)
  exact (valued_localRingHom_eq_one_iff w hw _).1 this

set_option maxHeartbeats 1600000 in
include hb₀ hb₁ in
theorem nsXF_eq_box [IsTotallyReal K] (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hSKg : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1) :
    nsXF F α β SK mK hmK1 = idelesEquiv F ⁻¹' ((BInf (F := F)) ×ˢ ideleBox S (nsN α β mK hmK1)) := by
  rw [nsXF_eq hb₀ hb₁ SK mK hmK1 hSKg]
  ext t
  have hcomp : ∀ (w : HeightOneSpectrum (𝓞 K)),
      unitAt ((idelesEquiv K) (adeleUnitsMap F K t)).2 w = Units.map (localRingHom (underPlace w) w rfl).toMonoidHom
        (unitAt ((idelesEquiv F) t).2 (underPlace w)) := fun w =>
    Units.ext (by
      change ((adeleUnitsMap F K t : Adeles K)).2 w = _
      rw [coe_adeleUnitsMap, adeleMap_snd_apply_over (underPlace w) w rfl]; rfl)
  simp only [mem_inter_iff, mem_preimage, mem_prod]
  constructor
  · rintro ⟨hB, -, hN⟩
    refine ⟨hB.1, fun u => ?_⟩
    split_ifs with hu
    · intro w hw
      subst hw
      have := hN w
      rw [if_pos ((hSK w).2 hu), hcomp] at this
      exact this
    · exact (finPart_mem_OHatUnits_iff t).1 hB.2 u
  · rintro ⟨hinf, hbox⟩
    have hfin : finPart t ∈ OHatUnits F := by
      change (idelesEquiv F t).2 ∈ OHatUnits F
      rw [← SetLike.mem_coe, ← ideleBox_empty (nsN α β mK hmK1)]
      intro u
      have := hbox u
      simp only [Finset.notMem_empty, ite_false]
      split_ifs at this with hu
      · exact nsN_subset hb₀ hb₁ mK hmK1 u this
      · exact this
    refine ⟨⟨hinf, hfin⟩, fun w => ?_, fun w => ?_⟩
    · show ((adeleUnitsMap F K t : Adeles K)).1.1 w ∈ Ico 1 (Real.exp 2)
      rw [adeleUnitsMap_fst_fst]; exact hinf _
    · split_ifs with hw
      · have := hbox (underPlace w)
        rw [if_pos ((hSK w).1 hw)] at this
        rw [hcomp]; exact this w rfl
      · exact (finPart_mem_OHatUnits_iff _).1 ((finPart_adeleUnitsMap_mem_iff hb₀ hb₁ t).2 hfin) w

include hb₀ hb₁ in
/-- **$\mathrm{tamIdeles}_F(X_F) = \omega_\infty(\mathrm{BInf})\,\mu_f(\mathrm{box}(S, N))$.** -/
theorem tamIdeles_nsXF [IsTotallyReal K] (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hSKg : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1) :
    tamIdeles F (nsXF F α β SK mK hmK1) = omegaInf F BInf * muFinUnits F (ideleBox S (nsN α β mK hmK1)) := by
  rw [nsXF_eq_box hb₀ hb₁ S SK mK hmK1 hSK hSKg, tamIdeles_prod]

end FSide

/-! ### The bookkeeping, abstractly -/

/-- **The local-ratio bookkeeping** (pure algebra): the places $w$ of $K$ in $S_K$ are grouped over the places $v\in S$ of
$F$; with the good-place identity, the archimedean identity and the bad-place local ratios, the two box volumes agree. -/
theorem ns_real_assembly {ι κ : Type*} (S : Finset ι) (P : ι → Finset κ) (SK : Finset κ)
    (hreg : ∀ f : κ → ℝ, ∏ w ∈ SK, f w = ∏ v ∈ S, ∏ w ∈ P v, f w) (AK AF fK fF : ℝ) (L3 al nl uk : κ → ℝ) (n u Y α4 r : ι → ℝ)
    (hal : ∀ w, al w ≠ 0) (hnl : ∀ w, nl w ≠ 0) (huk : ∀ w, uk w ≠ 0) (hα4 : ∀ v, α4 v ≠ 0)
    (hgood : fK = fF * ∏ v ∈ S, (∏ w ∈ P v, al w) / α4 v)
    (harch : AK * ∏ v ∈ S, r v = AF)
    (hin : ∀ v ∈ S, (∏ w ∈ P v, L3 w * uk w / nl w) * (n v / u v) = r v * Y v) :
    AK * (fK * ∏ w ∈ SK, L3 w / al w) * (∏ v ∈ S, n v / u v) =
      AF * (fF * ∏ v ∈ S, Y v / α4 v) * (∏ w ∈ SK, nl w / uk w) := by
  rw [hreg, hreg, hgood, ← harch]
  have key : ∀ v ∈ S, (∏ w ∈ P v, al w) / α4 v * (∏ w ∈ P v, L3 w / al w) * (n v / u v) =
      r v * (Y v / α4 v) * (∏ w ∈ P v, nl w / uk w) := by
    intro v hv
    have h := hin v hv
    have hA : (∏ w ∈ P v, al w) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => hal w
    have hC : (∏ w ∈ P v, nl w) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => hnl w
    have hD : (∏ w ∈ P v, uk w) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => huk w
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib] at h
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib,
      show r v * (Y v / α4 v) * ((∏ w ∈ P v, nl w) / ∏ w ∈ P v, uk w) =
        (r v * Y v) * ((∏ w ∈ P v, nl w) / ∏ w ∈ P v, uk w) / α4 v by ring, ← h]
    have := hα4 v
    field_simp
  have hL : (∏ v ∈ S, (∏ w ∈ P v, al w) / α4 v) * (∏ v ∈ S, ∏ w ∈ P v, L3 w / al w) * (∏ v ∈ S, n v / u v) =
      (∏ v ∈ S, r v) * (∏ v ∈ S, Y v / α4 v) * (∏ v ∈ S, ∏ w ∈ P v, nl w / uk w) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl key
  linear_combination AK * fF * hL

end

end QuadFormsKB.Tamagawa.Measure.Weil
