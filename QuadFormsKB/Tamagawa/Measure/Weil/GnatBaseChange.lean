import QuadFormsKB.Tamagawa.Measure.Weil.GnatSquare
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChange

/-!
# Non-square discriminant: $G^\natural\subset(D'\otimes\mathbb A_K)^\times$ via base change

**Layer:** a finite extension $K/k$ of number fields with a $k$-basis $b$ of $K$ containing $1$ (`b i₀ = 1`), and a quaternion
**division** algebra $D' = \mathbb H[K,\alpha,\beta]$ over $K$ ($\alpha,\beta\in\mathcal O_K\setminus0$). For $V$ quaternary with non-square
discriminant $d$, one takes $K = E = k(\sqrt d)$ and $D' = D\otimes_kK = D_E$; then $D_E\otimes_k\mathbb A_k\cong D'\otimes_K\mathbb A_K$
and
$$G^\natural(\mathbb A_k) = \{\alpha\in(D'\otimes\mathbb A_K)^\times : \operatorname{nrd}\alpha\in\mathbb A_k^\times\}.$$
Nothing below uses that $K/k$ is quadratic.

* **Base change facts** (from `adeleBaseChange`, with $\Psi(e_{i_0}u) = \iota(u)$): `adeleMap_injective`,
  `isClosedEmbedding_adeleMap`, `adeleUnitsMap` ($\iota$ on ideles, a closed embedding), **`adeleUnitsMap_mem_diag_iff`**
  ($\iota(u)\in K^\times\iff u\in k^\times$, i.e. $K\cap\mathbb A_k = k$ inside $\mathbb A_K$), and at the real places
  **`adeleMap_fst_fst`**: $\iota(t)_w = t_{w|_k}$ (ℝ-linearity of `infMap` and density of $k$ in $k_\infty$).
* **`gnatBC`**: the `GnatData` with $M = (D'\otimes\mathbb A_K)^\times$, $\nu = \operatorname{nrd}$, $\iota = $ `adeleUnitsMap`, $s = $ scalars,
  $A_+ = \iota^{-1}(\operatorname{nrd}(M))$, $\Gamma_M = D'^\times$.
* **`covolume_gnatBC`**: for Weil's quotient measure $\mu_P$ (fibre $\mu_{\mathrm{SL}_1(D')}$ over $\mathbb A_K$, base `tamIdeles` of $k$),
  $$\operatorname{vol}(P(k)\backslash P(\mathbb A_k),\ \mu_P) = 2,$$
  **unconditionally**: $\tau(\mathrm{SL}_1(D')) = 1$ over the number field $K$ (`tamagawa_SL1_division_unconditional` at $K$), the
  rest is `GnatData.covolume_muP`. The Weil restriction $R_{K/k}\mathrm{SL}_1(D')(\mathbb A_k) = \mathrm{SL}_1(D')(\mathbb A_K)$ is used in the
  form "$\ker\nu$ *is* $\mathrm{SL}_1(D')(\mathbb A_K)$" (no measure transport is needed because $\mu_S$ is defined on $\mathbb A_K$).
-/

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ### Base change facts -/

section BaseChangeFacts

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K) (i₀ : ι) (hb₀ : b i₀ = 1)

include hb₀ in
theorem adeleBaseChange_single_eq_adeleMap (u : Adeles k) : adeleBaseChange b (Pi.single i₀ u) = adeleMap k K u := by
  rw [adeleBaseChange_apply, Finset.sum_eq_single i₀]
  · rw [Pi.single_eq_same, hb₀, map_one, one_mul]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i₀) h

include hb₀ in
theorem adeleMap_injective : Injective (adeleMap k K) := fun u v h => by
  have h' : adeleBaseChange b (Pi.single i₀ u) = adeleBaseChange b (Pi.single i₀ v) := by
    rw [adeleBaseChange_single_eq_adeleMap b i₀ hb₀, adeleBaseChange_single_eq_adeleMap b i₀ hb₀, h]
  have := congrFun ((adeleBaseChange b).injective h') i₀
  simpa using this

include hb₀ in
theorem isClosedEmbedding_adeleMap : IsClosedEmbedding (adeleMap k K) := by
  have h : (adeleMap k K : Adeles k → Adeles K) = adeleBaseChange b ∘ fun u => Pi.single i₀ u := by
    funext u; exact (adeleBaseChange_single_eq_adeleMap b i₀ hb₀ u).symm
  have hs : IsClosedEmbedding (fun u : Adeles k => (Pi.single i₀ u : ι → Adeles k)) := by
    have : (fun u : Adeles k => (Pi.single i₀ u : ι → Adeles k)) = Function.update (0 : ι → Adeles k) i₀ := by
      funext u j; rfl
    rw [this]; exact isClosedEmbedding_update _ _
  rw [h]
  exact (adeleBaseChange b).toHomeomorph.isClosedEmbedding.comp hs

variable (k K) in
/-- $\iota$ on ideles: $\mathbb A_k^\times\to\mathbb A_K^\times$. -/
def adeleUnitsMap : (Adeles k)ˣ →* (Adeles K)ˣ := Units.map (adeleMap k K).toMonoidHom

@[simp] theorem coe_adeleUnitsMap (u : (Adeles k)ˣ) :
    ((adeleUnitsMap k K u : (Adeles K)ˣ) : Adeles K) = adeleMap k K u := rfl

theorem continuous_adeleUnitsMap : Continuous (adeleUnitsMap k K) :=
  Units.continuous_iff.2 ⟨continuous_adeleMap.comp Units.continuous_val,
    continuous_adeleMap.comp Units.continuous_coe_inv⟩

include hb₀ in
theorem isClosedEmbedding_adeleUnitsMap : IsClosedEmbedding (adeleUnitsMap k K) :=
  (isClosedEmbedding_adeleMap b i₀ hb₀ (k := k) (K := K)).units_map (f := (adeleMap k K).toMonoidHom)

include hb₀ in
theorem adeleUnitsMap_injective : Injective (adeleUnitsMap k K) :=
  (isClosedEmbedding_adeleUnitsMap b i₀ hb₀).injective

theorem adeleUnitsMap_diagUnits (f : kˣ) :
    adeleUnitsMap k K (diagUnits k f) = diagUnits K (Units.map (algebraMap k K).toMonoidHom f) :=
  Units.ext (by rw [coe_adeleUnitsMap, diagUnits_val, diagUnits_val]; exact adeleMap_diag _)

include hb₀ in
/-- **$K\cap\mathbb A_k = k$ inside $\mathbb A_K$**: $\iota(u)$ is principal iff $u$ is. -/
theorem adeleUnitsMap_mem_diag_iff (u : (Adeles k)ˣ) :
    adeleUnitsMap k K u ∈ diagUnitsSub K ↔ u ∈ diagUnitsSub k := by
  constructor
  · rintro ⟨y, hy⟩
    -- write y in the basis b; compare via Ψ
    have hΨ : adeleBaseChange b (diagVec k ι (b.equivFun (y : K))) = adeleBaseChange b (Pi.single i₀ (u : Adeles k)) := by
      rw [adeleBaseChange_diag, LinearEquiv.symm_apply_apply, adeleBaseChange_single_eq_adeleMap b i₀ hb₀, ← coe_adeleUnitsMap,
        ← hy, diagUnits_val]
    have h1 := (adeleBaseChange b).injective hΨ
    have hu : (u : Adeles k) = diag k (b.equivFun (y : K) i₀) := by
      have := congrFun h1 i₀
      simp only [Pi.single_eq_same, diagVec_apply] at this
      exact this.symm
    have hne : b.equivFun (y : K) i₀ ≠ 0 := by
      intro h0
      have : (u : Adeles k) = 0 := by rw [hu, h0, ← diagRing_apply, map_zero]
      exact u.ne_zero this
    exact ⟨Units.mk0 _ hne, Units.ext (by rw [diagUnits_val, Units.val_mk0, hu])⟩
  · rintro ⟨f, rfl⟩
    exact ⟨_, (adeleUnitsMap_diagUnits f).symm⟩

/-- **The real places**: $\iota(t)_w = t_{w|_k}$. Both sides are $\mathbb R$-linear in $t_\infty$ and agree on $k$, which spans
$k_\infty$ (`span_range_mixedEmbedding`). -/
theorem adeleMap_fst_fst (t : Adeles k) (w : {w : InfinitePlace K // w.IsReal}) :
    (adeleMap k K t).1.1 w = t.1.1 ⟨w.1.comap (algebraMap k K), IsReal.comap _ w.2⟩ := by
  set v : {v : InfinitePlace k // v.IsReal} := ⟨w.1.comap (algebraMap k K), IsReal.comap _ w.2⟩
  let L1 : mixedSpace k →ₗ[ℝ] ℝ := (LinearMap.proj w).comp ((LinearMap.fst ℝ _ _).comp (infMap k K))
  let L2 : mixedSpace k →ₗ[ℝ] ℝ := (LinearMap.proj v).comp (LinearMap.fst ℝ _ _)
  have hL : L1 = L2 := by
    refine LinearMap.ext_on_range (span_range_mixedEmbedding k) fun x => ?_
    simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.fst_apply,
      infMap_mixedEmbedding, mixedEmbedding_apply_isReal]
    apply Complex.ofReal_injective
    rw [embedding_of_isReal_apply, embedding_of_isReal_apply, comap_embedding_of_isReal (algebraMap k K) v.2]
    rfl
  have := LinearMap.congr_fun hL t.1
  simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.fst_apply] at this
  exact this

/-- **Every $k^\times$-orbit in $\mathbb A_k^\times$ meets the totally positive ideles** (weak approximation of signs). -/
theorem exists_diag_mul_pos (x : (Adeles k)ˣ) :
    ∃ f : kˣ, ∀ v : {v : InfinitePlace k // v.IsReal}, 0 < ((diagUnits k f * x : (Adeles k)ˣ) : Adeles k).1.1 v := by
  obtain ⟨c, hc0, hc⟩ := QuadFormsKB.Quat.exists_signs (F := k)
    (fun w hw => 0 < (x : Adeles k).1.1 ⟨w, hw⟩)
  refine ⟨Units.mk0 c hc0, fun ⟨w, hw⟩ => ?_⟩
  rw [idele_mul_fst_fst, diagUnits_val]
  have hσ : (diag k ((Units.mk0 c hc0 : kˣ) : k)).1.1 ⟨w, hw⟩ = embedding_of_isReal hw c := diag_fst_fst c ⟨w, hw⟩
  rw [hσ]
  have hy0 : (x : Adeles k).1.1 ⟨w, hw⟩ ≠ 0 := idele_fst_fst_ne_zero _ _
  have hc0' : embedding_of_isReal hw c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · have : ¬ 0 < embedding_of_isReal hw c := fun h => absurd ((hc w hw).1 h) (not_lt.2 hneg.le)
    exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 this) hc0') hneg
  · exact mul_pos ((hc w hw).2 hpos) hpos

end BaseChangeFacts

/-! ### The data $G^\natural$ for $K/k$ -/

section Data

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K) (i₀ : ι) (hb₀ : b i₀ = 1)
variable {α β : K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0)

/-- `adeleUnitsMap` as a continuous homomorphism. -/
def adeleUnitsCHom : (Adeles k)ˣ →ₜ* (Adeles K)ˣ := ⟨adeleUnitsMap k K, continuous_adeleUnitsMap⟩

include hb₀ hα0 hβ0 in
/-- **The data of $G^\natural = \{g\in(D'\otimes\mathbb A_K)^\times : \operatorname{nrd}g\in\mathbb A_k^\times\}$.** -/
def gnatBC : GnatData k (QuatAdele α β)ˣ (Adeles K)ˣ where
  ν := nrdCHom α β
  ι := adeleUnitsCHom
  s := (quatScalarCHom α β).comp adeleUnitsCHom
  ι_injective := adeleUnitsMap_injective b i₀ hb₀
  s_closedEmbedding := (isClosedEmbedding_quatScalar α β).comp (isClosedEmbedding_adeleUnitsMap b i₀ hb₀)
  s_central u m := quatScalar_comm α β _ m
  ν_s u := by
    change nrdUnit (quatScalar α β (adeleUnitsMap k K u)) = adeleUnitsMap k K (u ^ 2)
    rw [nrdUnit_quatScalar, map_pow]
  Apos := (posA α β).comap (adeleUnitsMap k K)
  isOpen_Apos := (isOpen_posA α β).preimage continuous_adeleUnitsMap
  mem_Apos m u h := by
    change adeleUnitsMap k K u ∈ posA α β
    rw [← show nrdHom α β m = adeleUnitsMap k K u from h]
    exact nrdUnit_pos_of_ramified m
  surj_Apos u hu := (mem_posA_iff_exists_nrd hα0 hβ0 _).1 hu
  ΓM := quatUnitsSub α β

theorem gnatBC_hsΓ (u : (Adeles k)ˣ) :
    (gnatBC b i₀ hb₀ hα0 hβ0).s u ∈ (gnatBC b i₀ hb₀ hα0 hβ0).ΓM ↔ u ∈ diagUnitsSub k := by
  change quatScalar α β (adeleUnitsMap k K u) ∈ quatUnitsSub α β ↔ _
  rw [quatScalar_mem_quatUnitsSub_iff, adeleUnitsMap_mem_diag_iff b i₀ hb₀]

theorem gnatBC_heich (f : kˣ) (hf : diagUnits k f ∈ (gnatBC b i₀ hb₀ hα0 hβ0).Apos) :
    ∃ γ ∈ (gnatBC b i₀ hb₀ hα0 hβ0).ΓM,
      (gnatBC b i₀ hb₀ hα0 hβ0).ν γ = (gnatBC b i₀ hb₀ hα0 hβ0).ι (diagUnits k f) := by
  change adeleUnitsMap k K (diagUnits k f) ∈ posA α β at hf
  rw [adeleUnitsMap_diagUnits] at hf
  obtain ⟨γ, hγ, hνγ⟩ := exists_global_nrd hα0 hβ0 _ hf
  refine ⟨γ, hγ, ?_⟩
  change nrdHom α β γ = adeleUnitsMap k K (diagUnits k f)
  rw [hνγ, adeleUnitsMap_diagUnits]

theorem gnatBC_hsign (x : (Adeles k)ˣ) :
    ∃ f : kˣ, diagUnits k f * x ∈ (gnatBC b i₀ hb₀ hα0 hβ0).Apos := by
  obtain ⟨f, hf⟩ := exists_diag_mul_pos x
  refine ⟨f, fun w hw _ => ?_⟩
  change 0 < (adeleMap k K ((diagUnits k f * x : (Adeles k)ˣ) : Adeles k)).1.1 ⟨w, hw⟩
  rw [adeleMap_fst_fst]
  exact hf _

end Data

/-! ### The theorem -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K) (i₀ : ι) (hb₀ : b i₀ = 1)
variable {α β : 𝓞 K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0)

/-- `gnatBC` for $\alpha,\beta\in\mathcal O_K$. -/
abbrev gnatBCO : GnatData k (QuatAdele (α : K) (β : K))ˣ (Adeles K)ˣ :=
  gnatBC b i₀ hb₀ (α := (α : K)) (β := (β : K)) (by simpa using hα0) (by simpa using hβ0)

instance : DiscreteTopology (gnatBCO b i₀ hb₀ hα0 hβ0).ΓM := discreteTopology_quatUnitsSub (α : K) (β : K)

instance : Countable (gnatBCO b i₀ hb₀ hα0 hβ0).ΓM :=
  inferInstanceAs (Countable (quatUnitsSub (α : K) (β : K)))

/-- The $\mu_{\mathrm{SL}_1(D')}$ on $\ker\nu$ of `gnatBCO` (the same measure as `muSL1N`). -/
def muBC : Measure ((gnatBCO b i₀ hb₀ hα0 hβ0).ν : (QuatAdele (α : K) (β : K))ˣ →* (Adeles K)ˣ).ker :=
  muSL1N hα0 hβ0

instance : (muBC b i₀ hb₀ hα0 hβ0).IsHaarMeasure := inferInstanceAs (muSL1N hα0 hβ0).IsHaarMeasure

/-- **Non-square discriminant (and every finite extension $K/k$): $\operatorname{vol}(P(k)\backslash P(\mathbb A_k)) = 2$** for Weil's
quotient measure on $P = G^\natural/\mathbb G_m$, $G^\natural = \{g\in(D'\otimes\mathbb A_K)^\times : \operatorname{nrd}g\in\mathbb A_k^\times\}$, $\mu_{G^\natural}$ fibred over
`tamIdeles` of $k$ with fibre the $\mu_{\mathrm{SL}_1(D')}$ over $K$, for every quaternion division algebra $D'$ over $K$. Unconditional
(the input $\tau(\mathrm{SL}_1(D')) = 1$ is `tamagawa_SL1_division_unconditional` over the number field $K$). -/
@[kb "weil1982" "§3.7, pp. 64-65 (m = 4, non-square discriminant) [unverified page]; §1.3 (restriction of scalars) [unverified]; §3.2, p. 43"]
theorem covolume_gnatBC (hdiv : ∀ ξ : ℍ[K,(α : K),(β : K)], ξ ≠ 0 → IsUnit ξ) :
    covolume (gnatBCO b i₀ hb₀ hα0 hβ0).gamP (gnatBCO b i₀ hb₀ hα0 hβ0).P
      ((gnatBCO b i₀ hb₀ hα0 hβ0).muP (muBC b i₀ hb₀ hα0 hβ0)) = 2 := by
  have h := (gnatBCO b i₀ hb₀ hα0 hβ0).covolume_muP (muBC b i₀ hb₀ hα0 hβ0) (gnatBC_hsΓ _ _ _ _ _)
    (gnatBC_heich _ _ _ _ _) (gnatBC_hsign _ _ _ _ _) (map_adK_muSL1N hα0 hβ0 hdiv) (covolume_muSL1N hα0 hβ0 hdiv)
  rw [h, mul_one]

end

end QuadFormsKB.Tamagawa.Measure.Weil
