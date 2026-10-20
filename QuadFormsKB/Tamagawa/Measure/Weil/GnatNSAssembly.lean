/-
# $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ from the good-place, archimedean and bad-place identities

**Layer:** $F$ totally real, $K = F(\delta)$ totally real ($\delta^2 = d$), $\alpha = a$, $\beta = b$ with $-a,-b\gg0$.

* **`nsBad`** (finite): the places $v$ of $F$ with $|2abd|_v\ne1$ or $v\mid\operatorname{disc}(1,\delta)$; **`nsBadK`**: the places of $K$
  over them; **`nsLevK`**: levels $m_w = 2(3s_w+2e_\alpha(w)+2e_\beta(w))+1$.
* **`map_muP_nsPEquiv_of_local`**: $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ given (i) the good-place identity of the regularized
  products $\prod'_w\alpha^{(3)}_w = \prod'_v\alpha^{(4)}_v\cdot\prod_{v\in S}\dots$, (ii) the archimedean identity
  $\mu^{(3)}_{K,\infty}(G_\infty)\prod_{v\in S}r_v = \mu^{(4)}_{F,\infty}(G_\infty)$ and (iii) the local ratios at the bad places.

Source: Weil 1982, Thm 2.3.1 (∏_v r_v = 1); §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSMeasure

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace IsDedekindDomain Filter
  WithZero
open scoped ENNReal NNReal Quaternion ComplexOrder

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat LerayPadic

noncomputable section

/-! ### Positivity of $\omega_v(\operatorname{nrd}\Lambda^{(m)}_v)$ -/

section NLPos

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

theorem scalV_mem_lamCong (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 F)) {r : (v.adicCompletion F)ˣ}
    (hr : Valued.v (r : v.adicCompletion F) = 1) : scalV v r ∈ lamCong v a b (m v) (hm1 v) := by
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  refine ⟨?_, ?_⟩
  · show conjOrth _ (hQF a b) (scalV v r) ∈ congSub v _ (m v) (hm1 v)
    rw [(conjOrth_eq_one_iff _ (hQF a b) hA _).2 ⟨r, rfl⟩]
    exact Subgroup.one_mem _
  · show scalV v r ∈ lamLocUnits (a : F) (b : F) v
    rw [mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w),
      nrdLoc_scalV, map_pow, hr, one_pow]
    refine ⟨?_, rfl⟩
    simp only [lamLoc, mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers]
    refine ⟨hr.le, ?_, ?_, ?_⟩ <;> simp [scalV]

/-- $1+\pi^{2s+1}\mathfrak o_v\subseteq\operatorname{nrd}\Lambda^{(m)}_v$ (squares of scalars, Hensel). -/
theorem oneAdd_subset_nL (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    {r : (v.adicCompletion F)ˣ | Valued.v ((r : v.adicCompletion F) - 1) ≤ exp (-((sExp v + 1 + sExp v : ℕ) : ℤ))} ⊆
      nL a b m hm1 v := by
  intro t ht
  obtain ⟨r, hr, hr1⟩ := exists_sq_eq_near_one v (valued_two_eq v) (Nat.lt_succ_self (sExp v)) ht
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, zero_sub, Valuation.map_neg, map_one] at hr1
    exact absurd hr1 (by rw [← exp_zero, exp_le_exp]; omega)
  have hrv : Valued.v r = 1 := valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v (by omega) hr1)
  refine ⟨scalV v (Units.mk0 r hr0), scalV_mem_lamCong m hm1 ha v (by simpa using hrv), Units.ext ?_⟩
  rw [nrdLocUnit_val, nrdLoc_scalV, Units.val_mk0, hr]

theorem omegaV_nL_ne_zero (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : omegaV v (nL a b m hm1 v) ≠ 0 := by
  intro h0
  have hle := measure_mono (μ := omegaV v) (oneAdd_subset_nL (b := b) m hm1 ha v)
  rw [h0, omegaV_oneAdd v (by omega), selfDualV_latticeV_nat] at hle
  have hpos : 0 < (Analysis.selfDualV v).real (Analysis.latticeV v 0) := selfDualV_real_pos v
  have h0' : Analysis.selfDualV v (Analysis.latticeV v 0) ≠ 0 := fun h => by
    rw [Measure.real, h] at hpos; simp at hpos
  exact (ENNReal.div_pos h0' (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne' (nonpos_iff_eq_zero.1 hle)

end NLPos

/-! ### The bad places and the levels -/

section Data

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  (bK : Module.Basis (Fin 2) F K)

theorem eventually_nsGood (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := by
  have h1 := eventually_good_place ha0 hb0
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, v.valuation F (d : F) = 1 := by
    have := finite_valuation_ne_one (k := F) (d : F) hd0
    filter_upwards [this.compl_mem_cofinite] with v hv
    simpa using hv
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, v.valuation F (Algebra.discr F bK) = 1 := by
    have := finite_valuation_ne_one (k := F) (Algebra.discr F bK) (Algebra.discr_not_zero_of_basis F bK)
    filter_upwards [this.compl_mem_cofinite] with v hv
    simpa using hv
  filter_upwards [h1, h2, h3] with v hv hd hdisc
  exact ⟨hv.1, hv.2.1, hv.2.2.1, by rw [valued_algebraMap]; exact hd, hdisc⟩

variable {bK} in
/-- **The bad places** of the non-square model: $|2abd|_v\ne1$ or $v\mid\operatorname{disc}(1,\delta)$. -/
def nsBad (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp (eventually_nsGood bK ha0 hb0 hd0)).toFinset

theorem nsGood_of_not_mem {ha0 : (a : F) ≠ 0} {hb0 : (b : F) ≠ 0} {hd0 : (d : F) ≠ 0} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ nsBad (bK := bK) ha0 hb0 hd0) : NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).mpr h)

open scoped Classical in
/-- The places of $K$ over the bad places. -/
def nsBadK (S : Finset (HeightOneSpectrum (𝓞 F))) : Finset (HeightOneSpectrum (𝓞 K)) :=
  S.biUnion fun v => placesOver (K := K) v

open scoped Classical in
theorem mem_nsBadK {S : Finset (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 K)} :
    w ∈ nsBadK (K := K) S ↔ underPlace (k := F) w ∈ S := by
  classical
  simp only [nsBadK, Finset.mem_biUnion, mem_placesOver]
  exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨_, h, rfl⟩⟩

theorem pairwiseDisjoint_placesOver (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (S : Set (HeightOneSpectrum (𝓞 F))).PairwiseDisjoint fun v => placesOver (K := K) v := by
  intro v _ v' _ hvv'
  rw [Function.onFun, Finset.disjoint_left]
  intro w hw hw'
  rw [mem_placesOver] at hw hw'
  exact hvv' (hw.symm.trans hw')

variable {α β : 𝓞 K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0)

/-- **The levels** $m_w = 2(3s_w+2e_\alpha(w)+2e_\beta(w))+1$. -/
def nsLevK (w : HeightOneSpectrum (𝓞 K)) : ℕ := 2 * (3 * sExp w + 2 * eExp α hα0 w + 2 * eExp β hβ0 w) + 1

theorem one_le_nsLevK (w : HeightOneSpectrum (𝓞 K)) : 1 ≤ nsLevK hα0 hβ0 w := by unfold nsLevK; omega

theorem nsLevK_cond (w : HeightOneSpectrum (𝓞 K)) :
    2 * sExp w < nsLevK hα0 hβ0 w ∧ sExp w + eExp α hα0 w ≤ nsLevK hα0 hβ0 w := by unfold nsLevK; omega

variable {bK} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))

include hα hβ in
/-- Good places of $F$ give good places of $K$. -/
theorem nsGoodK {v : HeightOneSpectrum (𝓞 F)} (hv : NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v)
    (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) :
    Valued.v (2 : w.adicCompletion K) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1 := by
  obtain ⟨h2, ha, hb, -, -⟩ := hv
  have e2 : (2 : w.adicCompletion K) = localRingHom v w h (2 : v.adicCompletion F) := (map_ofNat _ 2).symm
  have ea : algebraMap K (w.adicCompletion K) (α : K) =
      localRingHom v w h (algebraMap F (v.adicCompletion F) (a : F)) := by
    rw [show algebraMap F (v.adicCompletion F) (a : F) = ((a : F) : v.adicCompletion F) from rfl,
      localRingHom_algebraMap, ← hα]; rfl
  have eb : algebraMap K (w.adicCompletion K) (β : K) =
      localRingHom v w h (algebraMap F (v.adicCompletion F) (b : F)) := by
    rw [show algebraMap F (v.adicCompletion F) (b : F) = ((b : F) : v.adicCompletion F) from rfl,
      localRingHom_algebraMap, ← hβ]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e2, valued_localRingHom_eq_one_iff]; exact h2
  · rw [ea, valued_localRingHom_eq_one_iff]; exact ha
  · rw [eb, valued_localRingHom_eq_one_iff]; exact hb

end Data


/-! ### Finiteness of the archimedean mass (definite forms) -/

section ArchFin

open QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

theorem muArchTamSO_univ_ne_top (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF Q₀)) : muArchTamSO Q₀ hQ univ ≠ ∞ := by
  have : ∀ w, Fact (IsPosDefR (QRe Q₀ w)) := fun w => ⟨isPosDefR_QRe Q₀ hQ hpd w⟩
  have : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩
  have : CompactSpace (GInfSO Q₀) := by
    unfold GInfSO QuadFormsKB.Tamagawa.Measure.LerayArch.ArchGroup; infer_instance
  exact isCompact_univ.measure_lt_top.ne

end ArchFin

/-! ### The assembly -/

section Main

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K]
  [Algebra F K] [IsTotallyReal K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0)

local notation "Φ" => nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
  (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁)

set_option maxHeartbeats 6400000 in
/-- **$\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the non-square model from the three local identities** (good places, archimedean
places, bad places; Weil's $\prod_vr_v = 1$). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, ∏_v r_v = 1); §3.7, pp. 64-65 [unverified page]"]
theorem map_muP_nsPEquiv_of_local (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) (hdpos : IsTotallyPos (d : F))
    (hQ : (qNS a b d).Nondegenerate) (hint : ∀ i, IsIntegral ℤ (bK i)) (rv : HeightOneSpectrum (𝓞 F) → ℝ) (hrv : ∀ v, 0 < rv v)
    (hgoodId : finFactor (QuatZeta.pureFormO α β) (fun _ => 1) = finFactor (qNS a b d) (fun _ => 1) *
      ∏ v ∈ nsBad (bK := bK) ha0 hb0 hd0, (∏ w ∈ placesOver (K := K) v,
        LocalDensity.NF.siegelDensity w (QuatZeta.pureFormO α β) (QuatZeta.pureFormO α β)) /
          LocalDensity.NF.siegelDensity v (qNS a b d) (qNS a b d))
    (harch : (muArchTamSO (QuatZeta.pureFormO α β) (nondegenerate_pureFormO α β hα0 hβ0) univ).toReal *
      ∏ v ∈ nsBad (bK := bK) ha0 hb0 hd0, rv v = (muArchTamSO (qNS a b d) hQ univ).toReal)
    (hin : ∀ v ∈ nsBad (bK := bK) ha0 hb0 hd0,
      (∏ w ∈ placesOver (K := K) v, Measure.muLocSO w (QuatZeta.pureFormO α β) 1
          (congSO3S (a := α) (b := β) (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) w) *
        omegaV w (unitsVSub w) / omegaV w (nL α β (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) w)) *
          (omegaV v (nsN α β (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) v) / omegaV v (unitsVSub v)) =
        ENNReal.ofReal (rv v) * Measure.muLocSO v (qNS a b d) 1
          (nsU hb₁ hα hβ ha0 hd0 (nsLevK hα0 hβ0) (one_le_nsLevK hα0 hβ0) v)) :
    ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ = muTam (qNS a b d) hQ (fun _ => 1) := by
  classical
  set S := nsBad (bK := bK) ha0 hb0 hd0 with hSdef
  set SK := nsBadK (K := K) S with hSKdef
  set m := nsLevK hα0 hβ0
  have hm1 : ∀ w, 1 ≤ m w := one_le_nsLevK hα0 hβ0
  have hSKiff : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S := fun w => mem_nsBadK
  have hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := fun v hv => nsGood_of_not_mem bK hv
  have hSKg : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧
        Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1 := fun w hw =>
    nsGoodK hα hβ (hgood _ (fun h => hw ((hSKiff w).2 h))) w rfl
  have hmS : ∀ w ∈ SK, 2 * sExp w < m w ∧ sExp w + eExp α hα0 w ≤ m w := fun w _ => nsLevK_cond hα0 hβ0 w
  have hna' : IsTotallyPos (-(α : K)) := by rw [hα, ← map_neg]; exact isTotallyPos_algebraMap hna
  have hnb' : IsTotallyPos (-(β : K)) := by rw [hβ, ← map_neg]; exact isTotallyPos_algebraMap hnb
  have hdivK := hdiv_of_totallyNeg (F := K) (a := (α : K)) (b := (β : K))
    (fun w hw => emb_neg_of_isTotallyPos_neg hna' w hw) (fun w hw => emb_neg_of_isTotallyPos_neg hnb' w hw)
  have hpd3 := hpd_pureFormO (F := K) hna' hnb'
  have hQ3 := nondegenerate_pureFormO α β hα0 hβ0
  set S₀ := nsS0 hb₀ hα0 hβ0 (HS α β SK m hm1)
  have hHo : IsOpen (HS α β SK m hm1 : Set (QuatAdele (α : K) (β : K))ˣ) :=
    (isOpen_quatCongS SK m hm1).preimage (continuous_quatFinPart α β)
  have hS₀ : IsOpen (S₀ : Set (gnatBCO bK 0 hb₀ hα0 hβ0).G) := isOpen_nsS0 hb₀ hα0 hβ0 hHo
  -- the four measure identities
  have e1 := muP_nsS0_mul hb₀ hb₁ hα hβ hα0 hβ0 SK m hm1 hna hnb hSKg
  rw [tamIdeles_nsXF hb₀ hb₁ S SK m hm1 hSKiff hSKg] at e1
  have e2 := muSL1N_HS_mul (F := K) SK m hm1 hα0 hβ0 hna' hnb' hSKg
  have e3 := muPD_pdMk_HS (F := K) hα0 hβ0 SK m hm1 hQ3 hpd3 hdivK hSKg hmS
  have himg : Φ '' ((gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀) =
      univ ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 m hm1) := by
    rw [Set.image_image]
    exact nsAdele_image_nsS0 hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK m hm1 hb0 hint hSKiff hgood
  have hUo : ∀ v ∈ S, MeasurableSet (nsU hb₁ hα hβ ha0 hd0 m hm1 v) := fun v hv =>
    (isOpen_nsU hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK m hm1 hb0 hint hSKiff hgood hv).measurableSet
  -- names
  set P := (gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0) ((gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀)
  set W := omegaInf F (BInf (F := F))
  set UF := muFinUnits F (OHatUnits F)
  set UK := muFinUnits K (OHatUnits K)
  set NF := muFinUnits F (ideleBox S (nsN α β m hm1))
  set NH := muFinUnits K (NH α β SK m hm1)
  set SL := muSL1N hα0 hβ0 {x : (nrdHom (α : K) (β : K)).ker | (x : (QuatAdele (α : K) (β : K))ˣ) ∈ HS α β SK m hm1}
  set A3 := muArchTamSO (QuatZeta.pureFormO α β) hQ3 univ
  set M3 := QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO α β) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO α β) SK (congSO3S m hm1))
  set A4 := muArchTamSO (qNS a b d) hQ univ
  set M4 := QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1)
    (Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 m hm1))
  have hW0 : W ≠ 0 := omegaInf_BInf_ne_zero
  have hWt : W ≠ ∞ := omegaInf_BInf_ne_top
  have hA : P * UF = SL * NF := (ENNReal.mul_right_inj hW0 hWt).1 (by
    calc W * (P * UF) = P * (W * UF) := by ring
      _ = SL * (W * NF) := e1
      _ = W * (SL * NF) := by ring)
  have hB : P * UF * NH = UK * (A3 * M3) * NF := by rw [hA, mul_right_comm SL, e2, e3]
  -- finiteness and positivity
  have hUF : UF = ENNReal.ofReal (ohatVol F) := muFinUnits_OHatUnits
  have hUK : UK = ENNReal.ofReal (ohatVol K) := muFinUnits_OHatUnits
  have hUF0 : UF ≠ 0 := by rw [hUF]; exact (ENNReal.ofReal_pos.2 ohatVol_pos).ne'
  have hUFt : UF ≠ ∞ := by rw [hUF]; exact ENNReal.ofReal_ne_top
  have hUKt : UK ≠ ∞ := by rw [hUK]; exact ENNReal.ofReal_ne_top
  have hNHt : NH ≠ ∞ := ne_of_lt (lt_of_le_of_lt (measure_mono (NH_subset_OHatUnits SK m hm1))
    (lt_of_le_of_ne le_top hUKt))
  have hNH0 : NH ≠ 0 := by
    rw [show NH = UK * ∏ w ∈ SK, omegaV w (nL α β m hm1 w) / omegaV w (unitsVSub w) from
      muFinUnits_ideleBox_of_measurable SK _ fun w _ => measurableSet_nL m hm1 w]
    refine mul_ne_zero (by rw [hUK]; exact (ENNReal.ofReal_pos.2 ohatVol_pos).ne')
      (Finset.prod_ne_zero_iff.2 fun w _ => ?_)
    exact (ENNReal.div_pos (omegaV_nL_ne_zero m hm1 hα0 w) (omegaV_unitsVSub_ne_top w)).ne'
  have hbox_sub : ideleBox S (nsN α β m hm1) ⊆ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ) := by
    intro g hg
    rw [← ideleBox_empty (nsN α β m hm1)]
    intro v
    have := hg v
    simp only [Finset.notMem_empty, ite_false]
    split_ifs at this with hv
    · exact nsN_subset hb₀ hb₁ m hm1 v this
    · exact this
  have hNFt : NF ≠ ∞ := ne_of_lt (lt_of_le_of_lt (measure_mono hbox_sub) (lt_of_le_of_ne le_top hUFt))
  have hA3t : A3 ≠ ∞ := muArchTamSO_univ_ne_top _ hQ3 hpd3
  have hpd4 : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (qNS a b d)) := by
    rw [qNS]
    refine isTotallyPosDef_formF_diag _ fun i => ?_
    fin_cases i
    · intro σ; show 0 < σ ((1 : 𝓞 F) : F); simp only [algebraMap.coe_one, map_one]
      exact (zero_lt_one : (0 : ℂ) < 1)
    · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hna hdpos
      simpa [neg_mul] using this
    · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hnb hdpos
      simpa [neg_mul] using this
    · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul (QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hna hnb) hdpos
      simpa [neg_mul_neg] using this
  have hA4t : A4 ≠ ∞ := muArchTamSO_univ_ne_top _ hQ hpd4
  have hM3t : M3 ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (by
      rw [QuadFormsKB.Tamagawa.Measure.muFin_KSO]; exact ENNReal.ofReal_lt_top))
    rw [show congSO3S (a := α) (b := β) m hm1 = congSOgen (QuatZeta.pureFormO α β) m hm1 from rfl, ← coe_boxSub]
    exact inf_le_left
  -- finiteness of the bad-place volumes from the local ratios
  have hL3t : ∀ w, Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) m hm1 w) ≠ ∞ := by
    intro w
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun x hx => ?_)) (by
      rw [Measure.muLocSO_soStabSO]; exact ENNReal.ofReal_lt_top))
    exact congSub_le_stdStab w _ (m w) (hm1 w) hx
  have hUvt : ∀ v ∈ S, Measure.muLocSO v (qNS a b d) 1 (nsU hb₁ hα hβ ha0 hd0 m hm1 v) ≠ ∞ := by
    intro v hv
    have h := hin v hv
    have hl : (∏ w ∈ placesOver (K := K) v, Measure.muLocSO w (QuatZeta.pureFormO α β) 1
        (congSO3S (a := α) (b := β) m hm1 w) * omegaV w (unitsVSub w) / omegaV w (nL α β m hm1 w)) *
          (omegaV v (nsN α β m hm1 v) / omegaV v (unitsVSub v)) ≠ ∞ := by
      refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => ENNReal.div_ne_top
        (ENNReal.mul_ne_top (hL3t w) (omegaV_unitsVSub_ne_top w)) (omegaV_nL_ne_zero m hm1 hα0 w))
        (ENNReal.div_ne_top (ne_of_lt (lt_of_le_of_lt (measure_mono (nsN_subset hb₀ hb₁ m hm1 v))
          (lt_of_le_of_ne le_top (omegaV_unitsVSub_ne_top v)))) (omegaV_unitsVSub_ne_zero v))
    rw [h] at hl
    intro htop
    exact hl (by rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (hrv v)).ne'])
  have hM4t : M4 ≠ ∞ := by
    change QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1)
      (Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 m hm1)) ≠ ∞
    rw [QuadFormsKB.Tamagawa.Measure.muFin_boxSO (qNS a b d) hQ (fun _ => one_pos) S _ hUo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun v hv =>
      ENNReal.div_ne_top (hUvt v hv) (Measure.muLocSO_soStabSO_pos (qNS a b d) hQ v one_pos))
  -- the real identity
  have hU3m : ∀ w ∈ SK, MeasurableSet (congSO3S (a := α) (b := β) m hm1 w) := fun w _ =>
    ((isOpen_congSub w _ (m w) (hm1 w)).preimage continuous_subtype_val).measurableSet
  have hm3 := muFin_boxSO_toReal (QuatZeta.pureFormO α β) hQ3 SK (congSO3S m hm1) hU3m
  have hm4 := muFin_boxSO_toReal (qNS a b d) hQ S (nsU hb₁ hα hβ ha0 hd0 m hm1) hUo
  have hnh : NH.toReal = ohatVol K * ∏ w ∈ SK, (omegaV w (nL α β m hm1 w)).toReal /
      (omegaV w (unitsVSub w)).toReal :=
    muFinUnits_ideleBox_toReal (F := K) SK (nL α β m hm1) (fun w _ => measurableSet_nL m hm1 w)
  have hnf := muFinUnits_ideleBox_toReal S (nsN α β m hm1) (fun v _ => measurableSet_nsN m hm1 v)
  have huF : UF.toReal = ohatVol F := by rw [hUF, ENNReal.toReal_ofReal ohatVol_pos.le]
  have huK : UK.toReal = ohatVol K := by rw [hUK, ENNReal.toReal_ofReal ohatVol_pos.le]
  have hreg : ∀ f : HeightOneSpectrum (𝓞 K) → ℝ, ∏ w ∈ SK, f w = ∏ v ∈ S, ∏ w ∈ placesOver (K := K) v, f w :=
    fun f => Finset.prod_biUnion (pairwiseDisjoint_placesOver S)
  have hinR : ∀ v ∈ S, (∏ w ∈ placesOver (K := K) v,
      (Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) m hm1 w)).toReal *
        (omegaV w (unitsVSub w)).toReal / (omegaV w (nL α β m hm1 w)).toReal) *
          ((omegaV v (nsN α β m hm1 v)).toReal / (omegaV v (unitsVSub v)).toReal) =
        rv v * (Measure.muLocSO v (qNS a b d) 1 (nsU hb₁ hα hβ ha0 hd0 m hm1 v)).toReal := by
    intro v hv
    have h := congrArg ENNReal.toReal (hin v hv)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (hrv v).le] at h
    exact h
  have key := ns_real_assembly S (fun v => placesOver (K := K) v) SK hreg A3.toReal A4.toReal _ _ _ _ _ _ _ _ _ _ rv
    (fun w => (siegelDensity_self_pos' _ hQ3 w).ne')
    (fun w => (ENNReal.toReal_pos (omegaV_nL_ne_zero m hm1 hα0 w)
      (ne_of_lt (lt_of_le_of_lt (measure_mono (nL_subset m hm1 w))
        (lt_of_le_of_ne le_top (omegaV_unitsVSub_ne_top w))))).ne')
    (fun w => (ENNReal.toReal_pos (omegaV_unitsVSub_ne_zero w) (omegaV_unitsVSub_ne_top w)).ne')
    (fun v => (siegelDensity_self_pos' _ hQ v).ne') hgoodId harch hinR
  have hreal : (P * UF * NH).toReal = (A4 * M4 * (UF * NH)).toReal := by
    rw [hB]
    simp only [ENNReal.toReal_mul]
    rw [hm3, hnf, hm4, hnh, huF, huK]
    linear_combination (ohatVol K * ohatVol F) * key
  have hfinL : P * UF * NH ≠ ∞ := by
    rw [hB]; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hUKt (ENNReal.mul_ne_top hA3t hM3t)) hNFt
  have hX : P * UF * NH = A4 * M4 * (UF * NH) :=
    (ENNReal.toReal_eq_toReal_iff' hfinL
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA4t hM4t) (ENNReal.mul_ne_top hUFt hNHt))).1 hreal
  have hP : P = A4 * M4 := by
    rw [mul_assoc] at hX
    exact (ENNReal.mul_left_inj (mul_ne_zero hUF0 hNH0) (ENNReal.mul_ne_top hUFt hNHt)).1 hX
  have hPt : P ≠ ∞ := by rw [hP]; exact ENNReal.mul_ne_top hA4t hM4t
  refine map_muP_ns_eq_of_open hb₀ hb₁ hα hβ hα0 hβ0 hQ S₀ hS₀ hPt ?_
  rw [himg, muTam, Measure.prod_prod]
  exact hP

end Main

end

end QuadFormsKB.Tamagawa.Measure.Weil
