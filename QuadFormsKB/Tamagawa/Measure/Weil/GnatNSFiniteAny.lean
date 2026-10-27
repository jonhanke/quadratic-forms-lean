/-
# The signature-free finite-place identity of the non-square model

**Layer:** an *arbitrary* number field $F$ (no `IsTotallyReal`), $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$ in
$\mathcal O_K$; **no** definiteness or positivity hypotheses on $a, b, d$ (only $a, b, d \ne 0$ and $\alpha,\beta\ne0$, and
non-degeneracy of $\langle1,-ad,-bd,abd\rangle$ up to the printed shape `qNS`).

* **`nsBadPlaceRatio_any`**: the conclusion of `NSBadPlaceRatio.ratio` without the three definiteness binders
  (from `nsBadDeepRatio_any` by `nsBadPlaceRatio_of_deep_at`).
* **`fin_identity_ns`**: the finite-place identity
  $$\mu^{(3)}_f(\mathrm{box}_{S_K})\,\mu_f(N_F)\,\mu_f(\widehat{\mathcal O}_K^\times)
    = \Bigl(\prod_{v\in S} r_v\Bigr)\,\mu^{(4)}_f(\mathrm{box}_S)\,\mu_f(N_H)\,\mu_f(\widehat{\mathcal O}_F^\times)$$
  in $\mathbb R$, i.e. the good-place, bad-place and idele-box bookkeeping of `map_muP_nsPEquiv_of_local` with the
  archimedean factor removed (it is the signature-dependent part, kept separate).

Source: Weil 1982, Thm 2.3.1 (local ratios); §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinFinal

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace IsDedekindDomain Filter
  WithZero
open scoped ENNReal NNReal Quaternion ComplexOrder

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

noncomputable section

section Any

variable {F : Type} [Field F] [NumberField F]

/-- `measurableSet_nsN` without the (unused) total reality instance. -/
theorem measurableSet_nsN_any {K : Type} [Field K] [NumberField K] [Algebra F K] {α β : 𝓞 K}
    (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w) (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (nsN α β mK hmK1 v) := by
  have e : nsN α β mK hmK1 v = ⋂ w : PlaceSet (K := K) v,
      (Units.map (localRingHom v w.1 w.2).toMonoidHom) ⁻¹' nL α β mK hmK1 w.1 := by
    ext r
    simp only [nsN, mem_setOf_eq, mem_iInter, mem_preimage]
    exact ⟨fun h w => h w.1 w.2, fun h w hw => h ⟨w, hw⟩⟩
  rw [e]
  exact MeasurableSet.iInter fun w => (measurableSet_nL mK hmK1 w.1).preimage
    (Continuous.units_map _ (continuous_localRingHom v w.1 w.2)).measurable

/-- `nsRatio_pos` without the (unused) total reality instances. -/
theorem nsRatio_pos_any {K : Type} [Field K] [NumberField K] [Algebra F K] {a b d : 𝓞 F}
    (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    0 < nsRatio K a b d v := by
  have hab : algebraMap F (v.adicCompletion F) ((a : F) * (b : F)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F _).injective]; exact mul_ne_zero ha0 hb0
  have hd : algebraMap F (v.adicCompletion F) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F _).injective]; exact hd0
  unfold nsRatio
  have := relDisc_pos (K := K) v
  have := norm_pos_iff.2 hab
  have := norm_pos_iff.2 hd
  positivity

/-- **The bad-place ratio of the non-square model with no signature hypotheses**: the conclusion of
`NSBadPlaceRatio.ratio` for every number field $F$ and every model (no definiteness or positivity of $a, b, d$). -/
theorem nsBadPlaceRatio_any (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v) :
    (∏ w ∈ placesOver (K := K) v, Measure.muLocSO w (QuatZeta.pureFormO α β) 1
        (congSO3S (a := α) (b := β) (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) w) *
      omegaV w (unitsVSub w) / omegaV w (nL α β (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) w)) *
        (omegaV v (nsN α β (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) v) / omegaV v (unitsVSub v)) =
      ENNReal.ofReal (nsRatio K a b d v) * Measure.muLocSO v (qNS a b d) 1
        (nsU hb₁ hα hβ (ne_zero_of_algebraMap_eq hα hα0) (d_ne_zero_of_basis hb₁) (nsLevK hα0 hβ0)
          (one_le_nsLevK hα0 hβ0) v) :=
  nsBadPlaceRatio_of_deep_at hb₀ hb₁ hα hβ hα0 hβ0 hv (nsBadDeepRatio_any a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 v hv)

variable {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0)

include hb₀ in
set_option maxHeartbeats 6400000 in
/-- **The signature-free finite-place identity of the non-square model.** For every number field $F$ (no total reality,
no positivity of $a, b, d$), with $S$ = `nsBad`, $S_K$ = `nsBadK S`, $m$ = `nsLevK`, in $\mathbb R$:
$$\mu^{(3)}_f(\mathrm{box}_{S_K}(K^{(3)}_m))\cdot\mu_f(\mathrm{box}(S,N))\cdot\mu_f(\widehat{\mathcal O}_K^\times)
  = \Bigl(\prod_{v\in S}r_v\Bigr)\cdot\mu^{(4)}_f(\mathrm{box}_S(U_m))\cdot\mu_f(N_H)\cdot\mu_f(\widehat{\mathcal O}_F^\times),$$
where $r_v$ = `nsRatio`. Proof: the good places (`finFactor_regroup`, `prod_siegelDensity_good`) and the bad places
(`nsBadPlaceRatio_any`) through the abstract bookkeeping `ns_real_assembly` with trivial archimedean factor. -/
theorem fin_identity_ns (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (hQ : (qNS a b d).Nondegenerate) (hint : ∀ i, IsIntegral ℤ (bK i)) :
    (QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO α β) (fun _ => 1)
        (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO α β) (nsBadK (K := K) (nsBad (bK := bK) ha0 hb0 hd0))
          (congSO3S (a := α) (b := β) (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0)))).toReal *
      (muFinUnits F (ideleBox (nsBad (bK := bK) ha0 hb0 hd0)
        (nsN α β (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0)))).toReal *
      (muFinUnits K (OHatUnits K)).toReal =
    (∏ v ∈ nsBad (bK := bK) ha0 hb0 hd0, nsRatio K a b d v) *
      (QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1)
        (Measure.boxSO (qNS a b d) (nsBad (bK := bK) ha0 hb0 hd0)
          (nsU hb₁ hα hβ ha0 hd0 (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0)))).toReal *
      (muFinUnits K (NH α β (nsBadK (K := K) (nsBad (bK := bK) ha0 hb0 hd0))
        (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0))).toReal *
      (muFinUnits F (OHatUnits F)).toReal := by
  classical
  set S := nsBad (bK := bK) ha0 hb0 hd0 with hSdef
  set SK := nsBadK (K := K) S with hSKdef
  set m := nsLevK hα0 hβ0
  have hm1 : ∀ w, 1 ≤ m w := one_le_nsLevK hα0 hβ0
  have hSKiff : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S := fun w => mem_nsBadK
  have hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := fun v hv => nsGood_of_not_mem bK hv
  have hQ3 := nondegenerate_pureFormO α β hα0 hβ0
  have hUo : ∀ v ∈ S, MeasurableSet (nsU hb₁ hα hβ ha0 hd0 m hm1 v) := fun v hv =>
    (isOpen_nsU hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK m hm1 hb0 hint hSKiff hgood hv).measurableSet
  have hU3m : ∀ w ∈ SK, MeasurableSet (congSO3S (a := α) (b := β) m hm1 w) := fun w _ =>
    ((isOpen_congSub w _ (m w) (hm1 w)).preimage continuous_subtype_val).measurableSet
  have hm3 := muFin_boxSO_toReal (QuatZeta.pureFormO α β) hQ3 SK (congSO3S m hm1) hU3m
  have hm4 := muFin_boxSO_toReal (qNS a b d) hQ S (nsU hb₁ hα hβ ha0 hd0 m hm1) hUo
  have hnh : (muFinUnits K (NH α β SK m hm1)).toReal = ohatVol K * ∏ w ∈ SK, (omegaV w (nL α β m hm1 w)).toReal /
      (omegaV w (unitsVSub w)).toReal :=
    muFinUnits_ideleBox_toReal (F := K) SK (nL α β m hm1) (fun w _ => measurableSet_nL m hm1 w)
  have hnf := muFinUnits_ideleBox_toReal S (nsN α β m hm1) (fun v _ => measurableSet_nsN_any m hm1 v)
  have huF : (muFinUnits F (OHatUnits F)).toReal = ohatVol F := by
    rw [muFinUnits_OHatUnits, ENNReal.toReal_ofReal ohatVol_pos.le]
  have huK : (muFinUnits K (OHatUnits K)).toReal = ohatVol K := by
    rw [muFinUnits_OHatUnits, ENNReal.toReal_ofReal ohatVol_pos.le]
  have hreg : ∀ f : HeightOneSpectrum (𝓞 K) → ℝ, ∏ w ∈ SK, f w = ∏ v ∈ S, ∏ w ∈ placesOver (K := K) v, f w :=
    fun f => Finset.prod_biUnion (pairwiseDisjoint_placesOver S)
  have hgoodId := finFactor_regroup hα0 hβ0 hQ S fun v hv =>
    prod_siegelDensity_good hb₀ hb₁ hα hβ (hgood v hv)
  have hinR : ∀ v ∈ S, (∏ w ∈ placesOver (K := K) v,
      (Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) m hm1 w)).toReal *
        (omegaV w (unitsVSub w)).toReal / (omegaV w (nL α β m hm1 w)).toReal) *
          ((omegaV v (nsN α β m hm1 v)).toReal / (omegaV v (unitsVSub v)).toReal) =
        nsRatio K a b d v * (Measure.muLocSO v (qNS a b d) 1 (nsU hb₁ hα hβ ha0 hd0 m hm1 v)).toReal := by
    intro v hv
    have hv' : ¬ NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := (Set.Finite.mem_toFinset _).1 hv
    have h := congrArg ENNReal.toReal
      (nsBadPlaceRatio_any a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 v hv')
    simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (nsRatio_pos_any ha0 hb0 hd0 v).le] at h
    exact h
  have key := ns_real_assembly S (fun v => placesOver (K := K) v) SK hreg (1 : ℝ) (∏ v ∈ S, nsRatio K a b d v)
    _ _ _ _ _ _ _ _ _ _ (nsRatio K a b d)
    (fun w => (siegelDensity_self_pos' _ hQ3 w).ne')
    (fun w => (ENNReal.toReal_pos (omegaV_nL_ne_zero m hm1 hα0 w)
      (ne_of_lt (lt_of_le_of_lt (measure_mono (nL_subset m hm1 w))
        (lt_of_le_of_ne le_top (omegaV_unitsVSub_ne_top w))))).ne')
    (fun w => (ENNReal.toReal_pos (omegaV_unitsVSub_ne_zero w) (omegaV_unitsVSub_ne_top w)).ne')
    (fun v => (siegelDensity_self_pos' _ hQ v).ne') hgoodId (one_mul _) hinR
  rw [hm3, hnf, hm4, hnh, huF, huK]
  linear_combination (ohatVol K * ohatVol F) * key

end Any

end

end QuadFormsKB.Tamagawa.Measure.Weil
