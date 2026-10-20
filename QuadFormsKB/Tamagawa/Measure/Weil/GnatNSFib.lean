/-
# $\mu_P(\pi(S_0))$ for $S_0 = \{g\in G^\natural : g_1\in H_S\}$

**Layer:** $F$ totally real, $K = F(\delta)$, $\delta^2 = d\gg0$, $\alpha = a$, $\beta = b$ with $-a,-b\gg0$ (so $K$ is totally real and
$D' = (\alpha,\beta)_K$ totally definite), $G^\natural$ = `gnatBCO`, $H_S$ = `HS` over $K$.

* **`GnatData.muG_S0_eq`** (abstract, along $p$): for an open subgroup $S_0$ and $S = \{g\in S_0 : p(g)\in B\}$,
  $\mu_{G^\natural}(S) = \mu_{\ker p}(S_0\cap\ker p)\cdot\mu_{A_+}(B\cap p(S_0))$.
* **`muP_nsS0_mul`**: for $S_0$ = `nsS0 (HS ..)`,
  $$\mu_P(\pi(S_0))\cdot\omega_\infty(\mathrm{BInf})\,\mu_f(\hat{\mathcal O}_F^\times) =
    \mu_{\mathrm{SL}_1(D')}(H_S\cap\mathrm{SL}_1)\cdot\omega_\infty(\mathrm{BInf})\,\mu_f(N_F),$$
  $N_F = \{t\in\hat{\mathcal O}_F^\times : \iota(t)\in N_H\}$ (the $F$-ideles whose image in $\mathbb A_K$ is a reduced norm from
  $H_S$).

Source: Weil 1982, §2.4, Thm 2.4.4; §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSSL1
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeLocalConst

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

noncomputable section

namespace GnatData

variable {k : Type} [Field k] [NumberField k] {M T : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
  (d : GnatData k M T) (μSν : Measure (d.ν : M →* T).ker) [μSν.IsHaarMeasure]

/-- **Along $p$ for an open subgroup**: $\mu_{G^\natural}(\{g\in S_0 : p(g)\in B\}) = \mu_{\ker p}(S_0\cap\ker p)\,\mu_{A_+}(X)$
with $X = B\cap p(S_0)$. -/
theorem muG_S0_eq (S₀ : Subgroup d.G) (hS₀ : IsOpen (S₀ : Set d.G)) {B : Set (Adeles k)ˣ} (hB : MeasurableSet B)
    (X : Set d.Apos) (hX : MeasurableSet X)
    (hXc : ∀ a : d.Apos, a ∈ X ↔ (a : (Adeles k)ˣ) ∈ B ∧ ∃ g ∈ S₀, d.p g = a) :
    d.muG μSν {g | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} = d.muS μSν {x | (x : d.G) ∈ S₀} * d.muA X := by
  have hS : MeasurableSet {g : d.G | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} :=
    hS₀.measurableSet.inter (hB.preimage (continuous_snd.comp continuous_subtype_val).measurable)
  have hp : ∀ (g : d.G) (x : d.p.ker), (((g * (x : d.G)) : d.G) : M × (Adeles k)ˣ).2 = (g : M × (Adeles k)ˣ).2 := by
    intro g x
    change (g : M × (Adeles k)ˣ).2 * ((x : d.G) : M × (Adeles k)ˣ).2 = _
    rw [d.mem_ker_p.1 x.2, mul_one]
  rw [muG]
  refine fibMeas_apply_of_kern _ _ d.measurable_p _ _ hS hX _ ?_ ?_
  · intro q hq
    obtain ⟨hqB, g, hg, rfl⟩ := (hXc q).1 hq
    refine ⟨g, rfl, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hS]
    congr 1
    ext x
    simp only [mem_preimage, mem_setOf_eq, hp]
    rw [S₀.mul_mem_cancel_left hg]
    exact and_iff_left hqB
  · intro g hg
    rw [NormalFib.fibK_apply _ _ _ hS]
    convert measure_empty (μ := d.muS μSν)
    ext x
    simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false, hp]
    rintro ⟨h1, h2⟩
    apply hg
    refine (hXc _).2 ⟨h2, _, h1, ?_⟩
    apply Subtype.ext
    exact hp g x

/-- `muS` of a set of the form $\{x : x_1\in A\}$. -/
theorem muS_fst (A : Set M) (hA : MeasurableSet A) :
    d.muS μSν {x | ((x : d.G) : M × (Adeles k)ˣ).1 ∈ A} = μSν {m | (m : M) ∈ A} := by
  rw [muS, Measure.map_apply (map_continuous d.kerSEquiv.symm).measurable]
  · rfl
  · exact hA.preimage ((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).measurable

end GnatData

/-! ### Transfer of units and signs along $\mathbb A_F\to\mathbb A_K$ -/

section Transfer

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem isTotallyPos_algebraMap {x : F} (h : IsTotallyPos x) : IsTotallyPos (algebraMap F K x) := by
  intro σ
  have := h (σ.comp (IsScalarTower.toAlgHom ℚ F K))
  simpa using this

variable {v : HeightOneSpectrum (𝓞 F)}

/-- $|\varphi_w(x)|_w = 1\iff|x|_v = 1$ for $w\mid v$. -/
theorem valued_localRingHom_eq_one_iff (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v)
    (x : v.adicCompletion F) : Valued.v (localRingHom v w h x) = 1 ↔ Valued.v x = 1 := by
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    obtain ⟨n, hn⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hx0
    obtain ⟨s, hs⟩ := v.intValuation_exists_uniformizer
    have hsv : Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = WithZero.exp (-1 : ℤ) := by
      rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hs]
    have hs0 : (s : F) ≠ 0 := by
      intro h0; rw [h0, map_zero, map_zero] at hsv; exact WithZero.exp_ne_zero hsv.symm
    set y := x * algebraMap F (v.adicCompletion F) ((s : F) ^ n) with hy
    have hyv : Valued.v y = 1 := by
      rw [hy, map_mul, hn, map_zpow₀, map_zpow₀, hsv, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    have hφy : Valued.v (localRingHom v w h y) = 1 := by
      have hy0 : y ≠ 0 := by rintro h0; rw [h0, map_zero] at hyv; exact zero_ne_one hyv
      refine le_antisymm (localRingHom_valued_le_one v w h y hyv.le) ?_
      have h1 := localRingHom_valued_le_one v w h y⁻¹ (by rw [map_inv₀, hyv, inv_one])
      have h2 : Valued.v (localRingHom v w h y) * Valued.v (localRingHom v w h y⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
      by_contra hlt
      push_neg at hlt
      have := mul_lt_one_of_lt_of_le hlt h1
      rw [h2] at this
      exact lt_irrefl _ this
    have hsw : Valued.v (localRingHom v w h (algebraMap F (v.adicCompletion F) (s : F))) < 1 := by
      rw [show (algebraMap F (v.adicCompletion F) (s : F)) = ((s : F) : v.adicCompletion F) from rfl,
        localRingHom_algebraMap]
      change Valued.v (algebraMap K (w.adicCompletion K) (algebraMap F K (s : F))) < 1
      rw [valued_algebraMap]
      have hmem : (algebraMap (𝓞 F) (𝓞 K) s) ∈ w.asIdeal := by
        have hsm : s ∈ v.asIdeal := by
          rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, hs]
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
        rw [← h] at hsm
        exact hsm
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w _).2 hmem
      convert this using 2
      rfl
    have hsw0 : Valued.v (localRingHom v w h (algebraMap F (v.adicCompletion F) (s : F))) ≠ 0 := by
      rw [Ne, map_eq_zero, map_eq_zero, map_eq_zero]; exact hs0
    have hxy : localRingHom v w h x = localRingHom v w h y *
        (localRingHom v w h (algebraMap F (v.adicCompletion F) (s : F))) ^ (-n) := by
      rw [hy, map_mul, map_zpow₀, map_zpow₀, mul_assoc, ← zpow_add₀ (by
        rw [Ne, map_eq_zero, map_eq_zero]; exact hs0), add_neg_cancel, zpow_zero, mul_one]
    rw [hxy, map_mul, hφy, one_mul, map_zpow₀] at hx
    have hn0 : n = 0 := by
      by_contra hn0
      rcases lt_or_gt_of_ne hn0 with hneg | hpos
      · have : (Valued.v (localRingHom v w h (algebraMap F (v.adicCompletion F) (s : F)))) ^ (-n) < 1 :=
          zpow_lt_one₀ (zero_lt_iff.2 hsw0) hsw (by omega)
        rw [hx] at this; exact lt_irrefl _ this
      · have h3 : 1 < (Valued.v (localRingHom v w h (algebraMap F (v.adicCompletion F) (s : F)))) ^ (-n) := by
          rw [zpow_neg]
          exact one_lt_inv_iff₀.2 ⟨zpow_pos (zero_lt_iff.2 hsw0) _, zpow_lt_one₀ (zero_lt_iff.2 hsw0) hsw hpos⟩
        rw [hx] at h3; exact lt_irrefl _ h3
    rw [hn, hn0, WithZero.exp_zero]
  · intro hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    refine le_antisymm (localRingHom_valued_le_one v w h x hx.le) ?_
    have h1 := localRingHom_valued_le_one v w h x⁻¹ (by rw [map_inv₀, hx, inv_one])
    have h2 : Valued.v (localRingHom v w h x) * Valued.v (localRingHom v w h x⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
    by_contra hlt
    push_neg at hlt
    have := mul_lt_one_of_lt_of_le hlt h1
    rw [h2] at this
    exact lt_irrefl _ this

variable {d : F} {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K d)

include hb₀ hb₁ in
/-- **$\iota(t)_f\in\hat{\mathcal O}_K^\times\iff t_f\in\hat{\mathcal O}_F^\times$.** -/
theorem finPart_adeleUnitsMap_mem_iff (t : (Adeles F)ˣ) :
    finPart (adeleUnitsMap F K t) ∈ OHatUnits K ↔ finPart t ∈ OHatUnits F := by
  rw [finPart_mem_OHatUnits_iff, finPart_mem_OHatUnits_iff]
  constructor
  · intro h u
    obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ u
    have := h w
    rw [coe_adeleUnitsMap, adeleMap_snd_apply_over u w hw] at this
    exact (valued_localRingHom_eq_one_iff w hw _).1 this
  · intro h w
    rw [coe_adeleUnitsMap, adeleMap_snd_apply_over (underPlace w) w rfl]
    exact (valued_localRingHom_eq_one_iff w rfl _).2 (h _)

theorem adeleUnitsMap_fst_fst (t : (Adeles F)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    ((adeleUnitsMap F K t : Adeles K)).1.1 w = (t : Adeles F).1.1 ⟨w.1.comap (algebraMap F K), IsReal.comap _ w.2⟩ := by
  rw [coe_adeleUnitsMap, adeleMap_fst_fst]

include hb₀ hb₁ in
theorem adeleUnitsMap_mem_Bset [IsTotallyReal K] {t : (Adeles F)ˣ} (ht : t ∈ (Bset : Set (Adeles F)ˣ)) :
    adeleUnitsMap F K t ∈ (Bset : Set (Adeles K)ˣ) := by
  refine ⟨fun w => ?_, (finPart_adeleUnitsMap_mem_iff hb₀ hb₁ t).2 ht.2⟩
  show ((adeleUnitsMap F K t : Adeles K)).1.1 w ∈ Ico 1 (Real.exp 2)
  rw [adeleUnitsMap_fst_fst]
  exact ht.1 _

/-- Every real place of $F$ lies under a real place of $K$ (totally real $K$). -/
theorem exists_real_over [IsTotallyReal K] (v : {v : InfinitePlace F // v.IsReal}) :
    ∃ w : {w : InfinitePlace K // w.IsReal}, (⟨w.1.comap (algebraMap F K), IsReal.comap _ w.2⟩ :
      {v : InfinitePlace F // v.IsReal}) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := K) (k := F) v.1
  exact ⟨⟨w, IsTotallyReal.isReal w⟩, Subtype.ext hw⟩

end Transfer

/-! ### The non-square model: $\mu_P(\pi(S_0))$ -/

section NS

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K]
  [Algebra F K] [IsTotallyReal K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
  (SK : Finset (HeightOneSpectrum (𝓞 K))) (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0
local notation "MK" => (QuatAdele (α : K) (β : K))ˣ

variable (F α β) in
/-- $X_F = \{t\in\mathrm{Bset}_F : \iota(t)\in\operatorname{nrd}(H_S)\}$. -/
def nsXF : Set (Adeles F)ˣ :=
  {t | t ∈ (Bset : Set (Adeles F)ˣ) ∧ adeleUnitsMap F K t ∈ nrdUnit '' (HS α β SK mK hmK1 : Set MK)}

include hb₀ hb₁ in
theorem nsXF_eq (hSK : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1) :
    nsXF F α β SK mK hmK1 = (Bset : Set (Adeles F)ˣ) ∩
      adeleUnitsMap F K ⁻¹' (idelesEquiv K ⁻¹' ((BInf (F := K)) ×ˢ NH α β SK mK hmK1)) := by
  ext t
  simp only [nsXF, mem_setOf_eq, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hB, hn⟩
    refine ⟨hB, ?_⟩
    rw [← mem_preimage, ← nrd_image_HS SK mK hmK1 hSK]
    exact ⟨hn, adeleUnitsMap_mem_Bset hb₀ hb₁ hB⟩
  · rintro ⟨hB, hn⟩
    refine ⟨hB, ?_⟩
    have : adeleUnitsMap F K t ∈ idelesEquiv K ⁻¹' ((BInf (F := K)) ×ˢ NH α β SK mK hmK1) := hn
    rw [← nrd_image_HS SK mK hmK1 hSK] at this
    exact this.1

include hb₀ hb₁ in
theorem measurableSet_nsXF (hSK : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1) :
    MeasurableSet (nsXF F α β SK mK hmK1) := by
  rw [nsXF_eq hb₀ hb₁ SK mK hmK1 hSK]
  exact measurableSet_Bset.inter (((measurableSet_BInf.prod (measurableSet_NH SK mK hmK1)).preimage
    (idelesEquiv K).continuous.measurable).preimage continuous_adeleUnitsMap.measurable)

include hα hβ in
theorem ns_nrd_pos (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) (x : MK)
    (w : {w : InfinitePlace K // w.IsReal}) : 0 < ((nrdUnit x : (Adeles K)ˣ) : Adeles K).1.1 w := by
  have hna' : IsTotallyPos (-(α : K)) := by rw [hα, ← map_neg]; exact isTotallyPos_algebraMap hna
  have hnb' : IsTotallyPos (-(β : K)) := by rw [hβ, ← map_neg]; exact isTotallyPos_algebraMap hnb
  exact nrdUnit_pos_of_ramified x w.1 w.2 ⟨emb_neg_of_isTotallyPos_neg hna' w.1 w.2,
    emb_neg_of_isTotallyPos_neg hnb' w.1 w.2⟩

include hα hβ hb₁ in
/-- For $g\in S_0$: $p(g)$ is totally positive and $p(g)_f\in\hat{\mathcal O}_F^\times$. -/
theorem p_nsS0 (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) {g : (dN).G}
    (hg : g ∈ nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)) :
    (∀ v, 0 < ((g : MK × (Adeles F)ˣ).2 : Adeles F).1.1 v) ∧ finPart (g : MK × (Adeles F)ˣ).2 ∈ OHatUnits F := by
  have hν : nrdUnit (g : MK × (Adeles F)ˣ).1 = adeleUnitsMap F K (g : MK × (Adeles F)ˣ).2 := (dN).ν_fst g
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := exists_real_over (K := K) v
    rw [← adeleUnitsMap_fst_fst, ← hν]
    exact ns_nrd_pos hα hβ hna hnb _ w
  · rw [← finPart_adeleUnitsMap_mem_iff hb₀ hb₁, ← hν]
    exact finPart_nrd_mem_OHat _ ((mem_HS α β SK mK hmK1).1 hg).1

set_option maxHeartbeats 1600000 in
include hα hβ hb₁ in
/-- **$\mu_P(\pi(S_0))\cdot\omega_\infty(\mathrm{BInf})\mu_f(\hat{\mathcal O}_F^\times) = \mu_{\mathrm{SL}_1(D')}(H_S\cap\mathrm{SL}_1)\cdot
\mathrm{tamIdeles}_F(X_F)$** for $S_0 = \{g : g_1\in H_S\}$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.7, pp. 64-65 [unverified page]"]
theorem muP_nsS0_mul (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F)))
    (hSK : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧ Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1) :
    (dN).muP (muBC bK 0 hb₀ hα0 hβ0) ((dN).π '' nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)) *
        (omegaInf F BInf * muFinUnits F (OHatUnits F)) =
      muSL1N hα0 hβ0 {x : (nrdHom (α : K) (β : K)).ker | (x : MK) ∈ HS α β SK mK hmK1} *
        tamIdeles F (nsXF F α β SK mK hmK1) := by
  set S₀ := nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)
  have hHo : IsOpen (HS α β SK mK hmK1 : Set MK) :=
    (isOpen_quatCongS SK mK hmK1).preimage (continuous_quatFinPart α β)
  have hS₀ : IsOpen (S₀ : Set (dN).G) := isOpen_nsS0 hb₀ hα0 hβ0 hHo
  -- along π
  have hc : ∀ g ∈ S₀, tamIdeles F {u | (dN).zHom u ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 * u ^ 2 ∈ Bset} =
      omegaInf F BInf * muFinUnits F (OHatUnits F) := by
    intro g hg
    obtain ⟨hpos, hfin⟩ := p_nsS0 hb₀ hb₁ hα hβ hα0 hβ0 SK mK hmK1 hna hnb hg
    have hset : {u | (dN).zHom u ∈ S₀ ∧ (g : MK × (Adeles F)ˣ).2 * u ^ 2 ∈ Bset} =
        {u | finPart u ∈ OHatUnits F ∧ u ^ 2 * (g : MK × (Adeles F)ˣ).2 ∈ Bset} := by
      ext u
      simp only [mem_setOf_eq]
      have hz : (dN).zHom u ∈ S₀ ↔ finPart u ∈ OHatUnits F := by
        change quatScalar (α : K) (β : K) (adeleUnitsMap F K u) ∈ HS α β SK mK hmK1 ↔ _
        rw [quatScalar_mem_HS_iff SK mK hmK1 hα0, finPart_adeleUnitsMap_mem_iff hb₀ hb₁]
      rw [hz, mul_comm]
    rw [hset]
    exact tamIdeles_sq_mem_Bset _ hpos hfin
  have h1 := (dN).muG_eq_mul_muP (muBC bK 0 hb₀ hα0 hβ0) S₀ hS₀ measurableSet_Bset _ hc
  -- along p
  have hXm := measurableSet_nsXF hb₀ hb₁ SK mK hmK1 hSK
  have h2 := (dN).muG_S0_eq (muBC bK 0 hb₀ hα0 hβ0) S₀ hS₀ measurableSet_Bset
    {a | (a : (Adeles F)ˣ) ∈ nsXF F α β SK mK hmK1} (hXm.preimage measurable_subtype_coe) (fun t => by
      constructor
      · rintro ⟨hB, m, hm, hmt⟩
        refine ⟨hB, ⟨⟨(m, t), ?_⟩, hm, rfl⟩⟩
        exact hmt
      · rintro ⟨hB, g, hg, rfl⟩
        exact ⟨hB, _, hg, (dN).ν_fst g⟩)
  have h3 := (dN).muS_fst (muBC bK 0 hb₀ hα0 hβ0) _ hHo.measurableSet
  rw [GnatData.muA_apply] at h2
  have himg : Subtype.val '' {a : (dN).Apos | (a : (Adeles F)ˣ) ∈ nsXF F α β SK mK hmK1} = nsXF F α β SK mK hmK1 := by
    ext t
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro ht
      obtain ⟨-, m, -, hmt⟩ := id ht
      exact ⟨⟨t, (dN).mem_Apos m t hmt⟩, ht, rfl⟩
  rw [himg] at h2
  have h3' : (dN).muS (muBC bK 0 hb₀ hα0 hβ0) {x | (x : (dN).G) ∈ S₀} =
      muSL1N hα0 hβ0 {x : (nrdHom (α : K) (β : K)).ker | (x : MK) ∈ HS α β SK mK hmK1} := h3
  rw [h3'] at h2
  rw [mul_comm, ← h1, h2]

end NS

end

end QuadFormsKB.Tamagawa.Measure.Weil
