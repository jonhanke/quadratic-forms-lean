/-
# The reduction of `GnatTamagawaComparison` to a measure statement, and the definite consumers


**Layer:** a number field $F$ (totally real for the consumers).

* **`GnatTamagawaComparisonDef F`** (input, the definite part of `GnatTamagawaComparison F`): the same statement for totally
  definite $D$ only ($-a, -b\gg0$, and $d\gg0$ in the non-square case). `GnatTamagawaComparison.toDef`.
* With it: **`quaternaryTamagawaTwo_of_gnatComparisonDef`** ($\tau(SO_4) = 2$, every totally real $F$, any class number),
  **`rankFourUnitSiegel_of_gnatComparisonDef`**, and the all-ranks consumers (the same proofs as the covolume results, which only ever apply the
  input to totally definite quaternion algebras).
* **`GnatMeasureComparison F`** (input, measure only): for the explicit isomorphisms `sqPEquiv` and `nsPEquiv`,
  $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$; the definite version **`GnatMeasureComparisonDef F`**.
* **In this form:** **`gnatTamagawaComparison_of_measure`** (`GnatMeasureComparison F → GnatTamagawaComparison F`) and
  **`gnatTamagawaComparisonDef_of_measure`**: the isomorphism $P\cong SO(V)(\mathbb A)$ and $\Phi(\pi(\Gamma)) = SO(V)(F)$ are now proved
  (`sqPEquiv`, `map_gamP_sqPEquiv`, `nsPEquiv`, `map_gamP_nsPEquiv`); only Weil's local-ratio identity $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$
  (Thm 2.3.1) remains.

*Hypothesis hygiene.* `GnatMeasureComparison` compares two explicit Haar measures on $SO(V)(\mathbb A)$ along an explicit
isomorphism; it mentions no lattice, covolume, Tamagawa number or representation count.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSPoints

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace Matrix
open scoped ENNReal NNReal Quaternion ComplexOrder

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### The definite comparison -/

variable (F) in
/-- **Input (named): Weil's measure comparison for $G^\natural\to SO(V)$, $m = 4$, totally definite $D$** — the fields of `GnatTamagawaComparison F` restricted to $-a, -b$ totally positive (and $d$ totally positive in the non-square case), which is all the
reduction to $\tau(SO_4) = 2$ uses.

Fields: `square`, `nonsquare` as in `GnatTamagawaComparison`, with the extra hypotheses `hna : IsTotallyPos (-(a : F))`,
`hnb : IsTotallyPos (-(b : F))` (and `hdpos : IsTotallyPos (d : F)`). -/
@[kb "weil1982" "Thm 2.3.1 and §3.7, pp. 64-65 [unverified page]"]
structure GnatTamagawaComparisonDef : Prop where
  square : ∀ (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (_hna : IsTotallyPos (-(a : F))) (_hnb : IsTotallyPos (-(b : F)))
    (hQ : (qSq a b).Nondegenerate),
    ∃ Φ : (gnatSqO ha0 hb0).P ≃ₜ* SOAdele (qSq a b),
      (gnatSqO ha0 hb0).gamP.map Φ.toMulEquiv.toMonoidHom = GammaSOAdele (qSq a b) ∧
      ((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map Φ = muTam (qSq a b) hQ (fun _ => 1)
  nonsquare : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (_hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (_hα : (α : K) = algebraMap F K (a : F)) (_hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (_hna : IsTotallyPos (-(a : F))) (_hnb : IsTotallyPos (-(b : F)))
    (_hdpos : IsTotallyPos (d : F)) (hQ : (qNS a b d).Nondegenerate),
    ∃ Φ : (gnatBCO bK 0 hb₀ hα0 hβ0).P ≃ₜ* SOAdele (qNS a b d),
      (gnatBCO bK 0 hb₀ hα0 hβ0).gamP.map Φ.toMulEquiv.toMonoidHom = GammaSOAdele (qNS a b d) ∧
      ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ = muTam (qNS a b d) hQ (fun _ => 1)

theorem GnatTamagawaComparison.toDef (hC : GnatTamagawaComparison F) : GnatTamagawaComparisonDef F :=
  ⟨fun a b ha0 hb0 _ _ hQ => hC.square a b ha0 hb0 hQ,
   fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 _ _ _ hQ => hC.nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ⟩

/-- Weil's adelic $\tau(SO(\langle1,-a,-b,ab\rangle)) = 2$ for totally definite $D$, given the definite input. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_qSq_def (hC : GnatTamagawaComparisonDef F) {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F)))
    (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) (hQ : (qSq a b).Nondegenerate) :
    TamagawaNumberTwoAdelic (qSq a b) hQ := by
  obtain ⟨Φ, hΓ, hμ⟩ := hC.square a b ha0 hb0 hna hnb hQ
  have := (gnatSqO ha0 hb0).isHaarMeasure_muP (muSq ha0 hb0)
  unfold TamagawaNumberTwoAdelic
  rw [covolume_eq_of_continuousMulEquiv _ _ Φ hΓ _ _ hμ, covolume_gnatSq ha0 hb0 hdiv]

/-- Weil's adelic $\tau(SO(\langle1,-ad,-bd,abd\rangle)) = 2$ for totally definite $D'$, given the definite input. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem tamagawaNumberTwoAdelic_qNS_def (hC : GnatTamagawaComparisonDef F) {a b d : 𝓞 F} {K : Type} [Field K]
    [NumberField K] [Algebra F K] (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1)
    (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F)) {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F))
    (hβ : (β : K) = algebraMap F K (b : F)) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) (hdpos : IsTotallyPos (d : F))
    (hdiv : ∀ ξ : ℍ[K,(α : K),(β : K)], ξ ≠ 0 → IsUnit ξ) (hQ : (qNS a b d).Nondegenerate) :
    TamagawaNumberTwoAdelic (qNS a b d) hQ := by
  obtain ⟨Φ, hΓ, hμ⟩ := hC.nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos hQ
  have := (gnatBCO bK 0 hb₀ hα0 hβ0).isHaarMeasure_muP (muBC bK 0 hb₀ hα0 hβ0)
  unfold TamagawaNumberTwoAdelic
  rw [covolume_eq_of_continuousMulEquiv _ _ Φ hΓ _ _ hμ, covolume_gnatBC bK 0 hb₀ hα0 hβ0 hdiv]

section Reduction

open QuadForm LatChange

variable [IsTotallyReal F]

/-- **$\tau(SO_4) = 2$ over every totally real field (any class number), given the definite comparison**: the proof of `quaternaryTamagawaTwo_of_gnatComparison`, which only applies the input to totally definite quaternion algebras. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65"]
theorem quaternaryTamagawaTwo_of_gnatComparisonDef (hC : GnatTamagawaComparisonDef F) : QuaternaryTamagawaTwo F := by
  refine quaternaryTamagawaTwo_of_diag_nf fun c hc hpd => ?_
  set e : Fin 4 → 𝓞 F := Fin.cons 1 c
  have hpos : ∀ i, IsTotallyPos (e i : F) := isTotallyPos_of_diag hpd
  have hp1 : IsTotallyPos (c 0 : F) := hpos 1
  have hp2 : IsTotallyPos (c 1 : F) := hpos 2
  have hp3 : IsTotallyPos (c 2 : F) := hpos 3
  set a' : 𝓞 F := -(c 2 * c 1)
  set b' : 𝓞 F := -(c 2 * c 0)
  set d' : 𝓞 F := c 0 * c 1 * c 2
  have hna : IsTotallyPos (-(a' : F)) := by
    have : (-(a' : F)) = (c 2 : F) * c 1 := by simp only [a']; push_cast; ring
    rw [this]; exact isTotallyPos_mul hp3 hp2
  have hnb : IsTotallyPos (-(b' : F)) := by
    have : (-(b' : F)) = (c 2 : F) * c 0 := by simp only [b']; push_cast; ring
    rw [this]; exact isTotallyPos_mul hp3 hp1
  have hdpos : IsTotallyPos (d' : F) := by
    have : (d' : F) = (c 0 : F) * c 1 * c 2 := by simp only [d']; push_cast; ring
    rw [this]; exact isTotallyPos_mul (isTotallyPos_mul hp1 hp2) hp3
  have ha0 : a' ≠ 0 := neg_ne_zero.2 (mul_ne_zero (hc 2) (hc 1))
  have hb0 : b' ≠ 0 := neg_ne_zero.2 (mul_ne_zero (hc 2) (hc 0))
  -- the change of lattice to `qNS a' b' d'`
  set G : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal ![1, c 1 * c 2, c 0 * c 2, c 0 * c 1 * c 2]
  have hG : G.det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    fin_cases i <;> simp [hc 0, hc 1, hc 2]
  have hqG : (QuadForm.diag e).compMat G = qNS a' b' d' := by
    rw [diag_compMat_diagonal, qNS]
    congr 1
    funext i
    have h1 : (Fin.cons 1 c : Fin 4 → 𝓞 F) 1 = c 0 := rfl
    have h2 : (Fin.cons 1 c : Fin 4 → 𝓞 F) 2 = c 1 := rfl
    have h3 : (Fin.cons 1 c : Fin 4 → 𝓞 F) 3 = c 2 := rfl
    fin_cases i <;> simp [e, a', b', d', h1, h2, h3] <;> ring
  have hQe : (QuadForm.diag e).Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hQns : (qNS a' b' d').Nondegenerate := hqG ▸ nondegenerate_compMat_of_det hQe hG
  have hpdns : IsTotallyPosDef (formF (qNS a' b' d')) := by
    rw [← hqG, formF, ← map_compMat]
    exact isTotallyPosDef_compMat_of_det hpd (det_map_algebraMap_ne_zero_gnat hG)
  apply tamagawaNumberTwo_of_compMat hQe hpd hG
  rw [hqG]
  by_cases hsq : ∃ t : F, t ^ 2 = (d' : F)
  · -- square discriminant: `qNS a' b' d' = qSq a' b' ∘ diag(1,t,t,t)`
    obtain ⟨t, ht⟩ := hsq
    have hti : IsIntegral ℤ t := IsIntegral.of_pow two_pos (by rw [ht]; exact d'.isIntegral_coe)
    set t' : 𝓞 F := ⟨t, hti⟩
    have ht' : t' * t' = d' := RingOfIntegers.coe_injective (by
      change t * t = (d' : F); rw [← ht, sq])
    set H : Matrix (Fin 4) (Fin 4) (𝓞 F) := diagonal ![1, t', t', t']
    have ht0 : t' ≠ 0 := by
      intro h0; rw [h0, mul_zero] at ht'
      exact (mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) (hc 2)) ht'.symm
    have hH : H.det ≠ 0 := by
      rw [det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      fin_cases i <;> simp [ht0]
    have hqH : (qSq a' b').compMat H = qNS a' b' d' := by
      rw [qSq, diag_compMat_diagonal, qNS]
      congr 1
      funext i
      fin_cases i <;> simp <;> rw [← ht'] <;> ring
    have hpdsq : IsTotallyPosDef (formF (qSq a' b')) := by
      rw [← hqH, formF, ← map_compMat] at hpdns
      exact isTotallyPosDef_of_compMat (det_map_algebraMap_ne_zero_gnat hH) hpdns
    have hQsq : (qSq a' b').Nondegenerate := nondegenerate_of_map hpdsq.nondegenerate
    rw [← hqH]
    refine tamagawaNumberTwo_compMat_of hQsq hpdsq hH ?_
    have hdiv := hdiv_of_totallyNeg (F := F) (a := (a' : F)) (b := (b' : F))
      (fun w hw => emb_neg_of_isTotallyPos_neg hna w hw) (fun w hw => emb_neg_of_isTotallyPos_neg hnb w hw)
    exact (tamagawaNumberTwoAdelic_iff (qSq a' b') hQsq (by norm_num) hpdsq (isIntegral_std _)).1
      (tamagawaNumberTwoAdelic_qSq_def hC ha0 hb0 hna hnb hdiv hQsq)
  · -- non-square discriminant: `K = F(√d')`
    push_neg at hsq
    have := fact_irreducible_quadPoly (d' : F) hsq
    have := numberField_quadFieldOf (d' : F) hsq
    have := isTotallyReal_quadFieldOf (d' : F) hdpos
    set K := quadFieldOf (d' : F)
    have hαi : IsIntegral ℤ (algebraMap F K (a' : F)) := a'.isIntegral_coe.algebraMap
    have hβi : IsIntegral ℤ (algebraMap F K (b' : F)) := b'.isIntegral_coe.algebraMap
    set α : 𝓞 K := ⟨algebraMap F K (a' : F), hαi⟩
    set β : 𝓞 K := ⟨algebraMap F K (b' : F), hβi⟩
    have hα0 : α ≠ 0 := fun h => ha0 (RingOfIntegers.coe_injective (by
      have h' : algebraMap F K (a' : F) = 0 := congrArg Subtype.val h
      rw [map_eq_zero] at h'; simpa using h'))
    have hβ0 : β ≠ 0 := fun h => hb0 (RingOfIntegers.coe_injective (by
      have h' : algebraMap F K (b' : F) = 0 := congrArg Subtype.val h
      rw [map_eq_zero] at h'; simpa using h'))
    have hdiv : ∀ ξ : ℍ[K,(α : K),(β : K)], ξ ≠ 0 → IsUnit ξ := by
      refine hdiv_of_totallyNeg (fun w hw => ?_) (fun w hw => ?_)
      · change embedding_of_isReal hw (algebraMap F K (a' : F)) < 0
        rw [embedding_of_isReal_algebraMap]; exact emb_neg_of_isTotallyPos_neg hna _ _
      · change embedding_of_isReal hw (algebraMap F K (b' : F)) < 0
        rw [embedding_of_isReal_algebraMap]; exact emb_neg_of_isTotallyPos_neg hnb _ _
    exact (tamagawaNumberTwoAdelic_iff (qNS a' b' d') hQns (by norm_num) hpdns (isIntegral_std _)).1
      (tamagawaNumberTwoAdelic_qNS_def hC (quadBasis (d' : F)) (quadBasis_zero _) (quadBasis_one_sq _)
        (α := α) (β := β) rfl rfl hα0 hβ0 hna hnb hdpos hdiv hQns)

/-- **`RankFourUnitSiegel F`, every totally real field, given the definite comparison.** -/
@[kb "weil1982" "§4.5, p. 100; §3.7, Thm 3.7.1 (m = 4)"]
theorem rankFourUnitSiegel_of_gnatComparisonDef (hC : GnatTamagawaComparisonDef F) : RankFourUnitSiegel F :=
  rankFourUnitSiegel_of_quaternary (quaternaryTamagawaTwo_of_gnatComparisonDef hC)

end Reduction

/-! ### The comparison reduced to the measure identity -/

/-- $\alpha\ne0$ in $\mathcal O_K$ with $\alpha = \iota(a)$ gives $a\ne0$. -/
theorem ne_zero_of_algebraMap_eq {K : Type} [Field K] [Algebra F K] {a : 𝓞 F} {α : 𝓞 K}
    (hα : (α : K) = algebraMap F K (a : F)) (hα0 : α ≠ 0) : (a : F) ≠ 0 := by
  intro h
  apply hα0
  apply RingOfIntegers.coe_injective
  change (α : K) = ((0 : 𝓞 K) : K)
  rw [hα, h, map_zero]; rfl

theorem coeK_ne_zero {K : Type} [Field K] [NumberField K] {α : 𝓞 K} (hα0 : α ≠ 0) : (α : K) ≠ 0 := by
  simpa using hα0

theorem d_ne_zero_of_basis {K : Type} [Field K] [Algebra F K] {bK : Module.Basis (Fin 2) F K} {d : 𝓞 F}
    (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F)) : (d : F) ≠ 0 := by
  intro h
  rw [h, map_zero] at hb₁
  exact bK.ne_zero 1 (mul_self_eq_zero.1 hb₁)

variable (F) in
/-- **Input (named): Weil's local-ratio identity for the explicit $\Phi$** ($m = 4$, Weil 1982, Thm 2.3.1 [unverified page]).

Fields:
- `square`: for $a, b\in\mathcal O_F\setminus0$: `((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map (sqPEquiv ha0 hb0) = muTam (qSq a b) hQ 1`;
- `nonsquare`: the same for `gnatBCO`, `nsPEquiv` and `qNS a b d`.

*Hypothesis hygiene.* The isomorphism and the global points are proved; this is only the identity of two explicit Haar
measures on $SO(V)(\mathbb A)$ ($\prod_v r_v = 1$). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, ∏ r_v = 1) [unverified page]"]
structure GnatMeasureComparison : Prop where
  square : ∀ (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hQ : (qSq a b).Nondegenerate),
    ((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map (sqPEquiv ha0 hb0) = muTam (qSq a b) hQ (fun _ => 1)
  nonsquare : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hQ : (qNS a b d).Nondegenerate),
    ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map
      (nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
        (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁)) = muTam (qNS a b d) hQ (fun _ => 1)

variable (F) in
/-- **Input (named): the definite part of `GnatMeasureComparison`** ($-a, -b\gg0$; $d\gg0$ in the non-square case). -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
structure GnatMeasureComparisonDef : Prop where
  square : ∀ (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (_hna : IsTotallyPos (-(a : F))) (_hnb : IsTotallyPos (-(b : F)))
    (hQ : (qSq a b).Nondegenerate),
    ((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map (sqPEquiv ha0 hb0) = muTam (qSq a b) hQ (fun _ => 1)
  nonsquare : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (_hna : IsTotallyPos (-(a : F))) (_hnb : IsTotallyPos (-(b : F)))
    (_hdpos : IsTotallyPos (d : F)) (hQ : (qNS a b d).Nondegenerate),
    ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map
      (nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
        (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁)) = muTam (qNS a b d) hQ (fun _ => 1)

theorem GnatMeasureComparison.toDef (hM : GnatMeasureComparison F) : GnatMeasureComparisonDef F :=
  ⟨fun a b ha0 hb0 _ _ hQ => hM.square a b ha0 hb0 hQ,
   fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 _ _ _ hQ => hM.nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ⟩

/-- **`GnatTamagawaComparison F` reduces to the measure identity** (the isomorphism and the global points are proved). -/
@[kb "weil1982" "§3.7, pp. 64-65; Thm 2.3.1 [unverified page]"]
theorem gnatTamagawaComparison_of_measure (hM : GnatMeasureComparison F) : GnatTamagawaComparison F :=
  ⟨fun a b ha0 hb0 hQ => ⟨sqPEquiv ha0 hb0, map_gamP_sqPEquiv ha0 hb0, hM.square a b ha0 hb0 hQ⟩,
   fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ =>
    ⟨nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
        (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁),
      map_gamP_nsPEquiv hb₀ hb₁ hα hβ _ _ _ _ _, hM.nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ⟩⟩

/-- **Definite case: `GnatTamagawaComparisonDef F` reduces to `GnatMeasureComparisonDef F`.** -/
@[kb "weil1982" "§3.7, pp. 64-65; Thm 2.3.1 [unverified page]"]
theorem gnatTamagawaComparisonDef_of_measure (hM : GnatMeasureComparisonDef F) : GnatTamagawaComparisonDef F :=
  ⟨fun a b ha0 hb0 hna hnb hQ => ⟨sqPEquiv ha0 hb0, map_gamP_sqPEquiv ha0 hb0, hM.square a b ha0 hb0 hna hnb hQ⟩,
   fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos hQ =>
    ⟨nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
        (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁),
      map_gamP_nsPEquiv hb₀ hb₁ hα hβ _ _ _ _ _, hM.nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos hQ⟩⟩

section Consumers

variable [IsTotallyReal F]

/-- **$\tau(SO_4) = 2$, every totally real field, any class number, given the definite measure identity.** -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem quaternaryTamagawaTwo_of_measureDef (hM : GnatMeasureComparisonDef F) : QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_gnatComparisonDef (gnatTamagawaComparisonDef_of_measure hM)

/-- **`RankFourUnitSiegel F`, every totally real field, given the definite measure identity.** -/
@[kb "weil1982" "§4.5, p. 100; §3.7; Thm 2.3.1"]
theorem rankFourUnitSiegel_of_measureDef (hM : GnatMeasureComparisonDef F) : RankFourUnitSiegel F :=
  rankFourUnitSiegel_of_gnatComparisonDef (gnatTamagawaComparisonDef_of_measure hM)

/-- **$\tau = 2$ in every rank $N\ge4$, every totally real field, given the definite measure identity.** -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109; Thm 2.3.1; any class number"]
theorem tamagawaNumberTwo_all_ranks_of_measureDef (hM : GnatMeasureComparisonDef F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_nf (rankFourUnitSiegel_of_measureDef hM) hN Q₀ hpd

/-- **The mass formula in every rank $N\ge4$, every totally real field, given the definite measure identity.** -/
@[kb "weil1982" "Thm 4.5.1, p. 109; Thm 2.3.1; any class number"]
theorem massFormula_all_ranks_of_measureDef (hM : GnatMeasureComparisonDef F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_nf (rankFourUnitSiegel_of_measureDef hM) hN Q₀ hpd

/-- **Siegel's formula for numbers in every rank $N\ge5$, every totally real field, given the definite measure identity.** -/
@[kb "weil1982" "§4.5, p. 100; Thm 4.5.1, p. 109; Thm 2.3.1; any class number"]
theorem siegelFormulaAt_all_ranks_of_measureDef (hM : GnatMeasureComparisonDef F) {n : ℕ} (hn : 4 ≤ n)
    (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_all_ranks_nf (rankFourUnitSiegel_of_measureDef hM) hn Q₀ hpd hm

end Consumers

end

end QuadFormsKB.Tamagawa.Measure.Weil
