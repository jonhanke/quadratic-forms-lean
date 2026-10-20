import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.NeatCovolume

/-!
# Generic measure transport for Tamagawa covolumes

**Generic (Mathlib-only hypotheses).** Weil compares Tamagawa numbers of isomorphic groups (e.g. $SO(D^0)\cong PD^\times$,
AAG Thm 2.3.1 and §3.2) by transporting measures: an isomorphism $G \cong G'$ defined over $k$ induces a topological group
isomorphism $\varphi : G(\mathbb A)\to G'(\mathbb A)$ carrying $G(k)$ onto $G'(k)$; at each place the local Tamagawa measures
correspond up to a factor $r_v$, and $\prod_v r_v = 1$ by the product formula. This file proves the abstract statements, so
that the isomorphism $SO(D^0)\cong PD^\times$ and other applications can reuse them.

* `covolume_eq_of_map` : a measurable group isomorphism $\varphi$ with $\varphi(\Gamma) = \Gamma'$ and $\varphi_*\mu = \mu'$
  preserves covolumes: $\mathrm{covol}(\Gamma, G, \mu) = \mathrm{covol}(\Gamma', G', \mu')$.
* `covolume_smul` : $\mathrm{covol}(\Gamma, G, c\mu) = c\cdot\mathrm{covol}(\Gamma, G, \mu)$ for $c \ne 0$.
* `covolume_eq_mul_of_map_eq_smul` : $\varphi_*\mu = c\,\mu'$ ($c\ne0$) gives $\mathrm{covol}(\Gamma,\mu) = c\cdot\mathrm{covol}(\Gamma',\mu')$.
* `map_prodMap_prod` : for $\varphi = \varphi_\infty\times\varphi_f$ on $G_\infty\times G_f$ with $(\varphi_\infty)_*\mu_\infty = r_\infty\mu'_\infty$
  and $(\varphi_f)_*\mu_f = r_f\mu'_f$, $\varphi_*(\mu_\infty\times\mu_f) = r_\infty r_f\,(\mu'_\infty\times\mu'_f)$.
* `map_eq_smul_of_compact_open` : on locally compact groups, a topological isomorphism carries a regular Haar measure to
  $c$ times another one, with $c = \mu(\varphi^{-1}K')/\mu'(K')$ read off on any compact open $K'$ (Haar uniqueness).
* `map_eq_tprod_smul` : the **local-factor form**: if $\mu(\varphi^{-1}K') = \prod'_v a_v$, $\mu'(K') = \prod'_v a'_v$ and
  $a_v = r_v a'_v$ with $(a'_v)$, $(r_v)$ multipliable and $a'_v > 0$, then $\varphi_*\mu = (\prod'_v r_v)\,\mu'$.
* **`covolume_eq_of_localFactors`** (headline): $\varphi = \varphi_\infty\times\varphi_f$ with archimedean ratio $r_\infty$ and
  finite local ratios $r_v$ as above, and $r_\infty\prod'_v r_v = 1$ (Weil's product formula, Thm 2.3.1) $\Rightarrow$
  $\mathrm{covol}(\Gamma, G_\infty\times G_f, \mu_\infty\times\mu_f) = \mathrm{covol}(\Gamma', G'_\infty\times G'_f,
  \mu'_\infty\times\mu'_f)$.

The compact open $K'$ is arbitrary: in applications one takes $K' = \prod_v K'_v$ with $K_v := \varphi_v^{-1}(K'_v)$, so
that $a_v = \mu_v(K_v)$, $a'_v = \mu'_v(K'_v)$, and $r_v = 1$ at almost all $v$ (where both are the "standard"
integral points).
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

section Abstract

variable {G G' : Type*} [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul G]
  [MeasurableMul G']

/-- A fundamental domain of $\Gamma'$ pulls back along a group isomorphism $\varphi$ with $\varphi(\Gamma) = \Gamma'$ and
$\varphi_*\mu = \mu'$ to a fundamental domain of $\Gamma$. -/
theorem isFundamentalDomain_preimage (Γ : Subgroup G) (Γ' : Subgroup G') (φ : G ≃* G') (hφ : Measurable φ)
    (hΓ : Γ.map φ.toMonoidHom = Γ') (μ : Measure G) (μ' : Measure G') (hμ : μ.map φ = μ') {s : Set G'}
    (hs : IsFundamentalDomain Γ' s μ') : IsFundamentalDomain Γ (φ ⁻¹' s) μ := by
  have hqmp : QuasiMeasurePreserving φ μ μ' := ⟨hφ, by rw [hμ]⟩
  let e : Γ' → Γ := fun g => ⟨φ.symm g, by
    have : (g : G') ∈ Γ.map φ.toMonoidHom := hΓ ▸ g.2
    obtain ⟨x, hx, hxg⟩ := this
    have : φ.symm g = x := by rw [← hxg]; simp
    rw [this]; exact hx⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (φ.symm.injective (congrArg Subtype.val h)), fun g => ?_⟩
    refine ⟨⟨φ g, hΓ ▸ ⟨g, g.2, rfl⟩⟩, Subtype.ext ?_⟩
    simp [e]
  refine hs.preimage_of_equiv hqmp he fun g x => ?_
  show φ ((e g : G) * x) = (g : G') * φ x
  simp [e]

/-- **Covolumes are preserved by measure-preserving group isomorphisms** carrying $\Gamma$ onto $\Gamma'$. -/
@[kb "weil1982" "§2.3 (transport of Tamagawa measures along k-isomorphisms) [unverified]"]
theorem covolume_eq_of_map (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] (φ : G ≃* G') (hφ : Measurable φ)
    (hφ' : Measurable φ.symm) (hΓ : Γ.map φ.toMonoidHom = Γ') (μ : Measure G) (μ' : Measure G')
    [μ.IsMulLeftInvariant] [μ'.IsMulLeftInvariant] (hμ : μ.map φ = μ') :
    covolume Γ G μ = covolume Γ' G' μ' := by
  have hΓ'c : Countable Γ' := by
    subst hΓ
    exact Function.Surjective.countable (f := fun g : Γ => (⟨φ g, g, g.2, rfl⟩ : Γ.map φ.toMonoidHom))
      fun ⟨_, g, hg, rfl⟩ => ⟨⟨g, hg⟩, rfl⟩
  have hμ' : μ'.map φ.symm = μ := by
    rw [← hμ, Measure.map_map hφ' hφ]; simp
  have hΓ' : Γ'.map φ.symm.toMonoidHom = Γ := by
    rw [← hΓ, Subgroup.map_map]
    convert Subgroup.map_id Γ
    ext; simp
  by_cases h : HasFundamentalDomain Γ' G' μ'
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' := isFundamentalDomain_preimage Γ Γ' φ hφ hΓ μ μ' hμ hs
    let e : G ≃ᵐ G' := ⟨φ.toEquiv, hφ, hφ'⟩
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, ← hμ, show (φ : G → G') = e from rfl, e.map_apply]
  · have h' : ¬ HasFundamentalDomain Γ G μ := by
      rintro ⟨s, hs⟩
      exact h ⟨_, isFundamentalDomain_preimage Γ' Γ φ.symm hφ' hΓ' μ' μ hμ' hs⟩
    simp only [covolume, h, h', ↓reduceDIte]

/-- $s$ is a fundamental domain for $c\mu$ iff it is one for $\mu$ ($c \ne 0$: same null sets). -/
theorem isFundamentalDomain_smul_iff {Γ : Type*} [Group Γ] [MulAction Γ G] {s : Set G} {μ : Measure G}
    {c : ℝ≥0∞} (hc : c ≠ 0) : IsFundamentalDomain Γ s (c • μ) ↔ IsFundamentalDomain Γ s μ :=
  ⟨fun h => h.mono (absolutelyContinuous_smul hc), fun h => h.mono smul_absolutelyContinuous⟩

/-- **Scaling:** $\mathrm{covol}(\Gamma, G, c\mu) = c\cdot\mathrm{covol}(\Gamma, G, \mu)$ for $c \ne 0$. -/
@[kb "weil1982" "§2.3 (Tamagawa measure up to a constant) [unverified]"]
theorem covolume_smul (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] {c : ℝ≥0∞}
    (hc : c ≠ 0) : covolume Γ G (c • μ) = c * covolume Γ G μ := by
  by_cases h : HasFundamentalDomain Γ G μ
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' : IsFundamentalDomain Γ s (c • μ) := (isFundamentalDomain_smul_iff hc).mpr hs
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]
  · have h' : ¬ HasFundamentalDomain Γ G (c • μ) := by
      rintro ⟨s, hs⟩
      exact h ⟨s, (isFundamentalDomain_smul_iff hc).mp hs⟩
    simp only [covolume, h, h', ↓reduceDIte, mul_zero]

/-- **Transport with a constant:** if $\varphi_*\mu = c\,\mu'$ with $c \ne 0$, then
$\mathrm{covol}(\Gamma, G, \mu) = c\cdot\mathrm{covol}(\Gamma', G', \mu')$. -/
@[kb "weil1982" "§2.3 (transport of Tamagawa measures along k-isomorphisms) [unverified]"]
theorem covolume_eq_mul_of_map_eq_smul (Γ : Subgroup G) (Γ' : Subgroup G') [Countable Γ] (φ : G ≃* G')
    (hφ : Measurable φ) (hφ' : Measurable φ.symm) (hΓ : Γ.map φ.toMonoidHom = Γ') (μ : Measure G)
    (μ' : Measure G') [μ.IsMulLeftInvariant] [μ'.IsMulLeftInvariant] {c : ℝ≥0∞} (hc : c ≠ 0)
    (hμ : μ.map φ = c • μ') : covolume Γ G μ = c * covolume Γ' G' μ' := by
  have hΓ'c : Countable Γ' := by
    subst hΓ
    exact Function.Surjective.countable (f := fun g : Γ => (⟨φ g, g, g.2, rfl⟩ : Γ.map φ.toMonoidHom))
      fun ⟨_, g, hg, rfl⟩ => ⟨⟨g, hg⟩, rfl⟩
  rw [covolume_eq_of_map Γ Γ' φ hφ hφ' hΓ μ (c • μ') hμ, covolume_smul Γ' μ' hc]

end Abstract

section Product

variable {A B A' B' : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace A'] [MeasurableSpace B']

/-- **Product of local comparisons:** for $\varphi_\infty$, $\varphi_f$ measurable with $(\varphi_\infty)_*\mu_\infty =
r_\infty\mu'_\infty$ and $(\varphi_f)_*\mu_f = r_f\mu'_f$, the product map carries $\mu_\infty\times\mu_f$ to
$r_\infty r_f(\mu'_\infty\times\mu'_f)$. -/
theorem map_prodMap_prod {fA : A → A'} {fB : B → B'} (hfA : Measurable fA) (hfB : Measurable fB)
    (μA : Measure A) (μB : Measure B) (μA' : Measure A') (μB' : Measure B') [SFinite μB] [SFinite μB']
    {rA rB : ℝ≥0∞} (hA : μA.map fA = rA • μA') (hB : μB.map fB = rB • μB') :
    (μA.prod μB).map (Prod.map fA fB) = (rA * rB) • (μA'.prod μB') := by
  rw [← Measure.map_prod_map μA μB hfA hfB, hA, hB, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

end Product

section Haar

variable {B B' : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B]
  [MeasurableSpace B] [BorelSpace B] [Group B'] [TopologicalSpace B'] [IsTopologicalGroup B']
  [LocallyCompactSpace B'] [MeasurableSpace B'] [BorelSpace B']

/-- **Haar uniqueness across an isomorphism:** a topological group isomorphism $\varphi$ carries a regular Haar measure
$\mu$ to $c\,\mu'$ for a regular Haar measure $\mu'$, with $c = \mu(\varphi^{-1}K')/\mu'(K')$ for any compact open
$K' \ne \emptyset$. -/
@[kb "weil1982" "§2.3 (local Tamagawa measures under k-isomorphisms) [unverified]"]
theorem map_eq_smul_of_compact_open (φ : B ≃ₜ* B') (μ : Measure B) [μ.IsHaarMeasure] [μ.Regular]
    (μ' : Measure B') [μ'.IsHaarMeasure] [μ'.Regular] {K' : Set B'} (hKc : IsCompact K') (hKo : IsOpen K')
    (hKne : K'.Nonempty) : μ.map φ = (μ (φ ⁻¹' K') / μ' K') • μ' := by
  have : (μ.map φ).IsHaarMeasure := φ.isHaarMeasure_map μ
  have : (μ.map φ).Regular := Regular.map (φ.toHomeomorph)
  have h := isMulLeftInvariant_eq_smul_of_regular (μ.map φ) μ'
  have hK0 : μ' K' ≠ 0 := (hKo.measure_pos μ' hKne).ne'
  have hKt : μ' K' ≠ ∞ := hKc.measure_lt_top.ne
  have hval : μ.map φ K' = μ (φ ⁻¹' K') := Measure.map_apply φ.continuous.measurable hKo.measurableSet
  have hc : (haarScalarFactor (μ.map φ) μ' : ℝ≥0∞) = μ (φ ⁻¹' K') / μ' K' := by
    have := congrArg (fun ν : Measure B' => ν K') h
    simp only [Measure.smul_apply, nnreal_smul_coe_apply, hval] at this
    rw [this, ENNReal.mul_div_cancel_right hK0 hKt]
  conv_lhs => rw [h]
  rw [← hc]; rfl

/-- **Local-factor form** (Weil's $\prod_v r_v$): if $\mu(\varphi^{-1}K') = \prod'_v a_v$ and $\mu'(K') = \prod'_v a'_v$
with $a_v = r_v\,a'_v$, $a'_v > 0$, $r_v \ge 0$, and $(a'_v)$, $(r_v)$ multipliable, then
$\varphi_*\mu = (\prod'_v r_v)\,\mu'$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (product of local ratios) [unverified]"]
theorem map_eq_tprod_smul {ι : Type*} (φ : B ≃ₜ* B') (μ : Measure B) [μ.IsHaarMeasure] [μ.Regular]
    (μ' : Measure B') [μ'.IsHaarMeasure] [μ'.Regular] {K' : Set B'} (hKc : IsCompact K') (hKo : IsOpen K')
    (hKne : K'.Nonempty) (a a' r : ι → ℝ) (ha' : ∀ v, 0 < a' v) (hr : ∀ v, 0 ≤ r v) (har : ∀ v, a v = r v * a' v)
    (hma' : Multipliable a') (hmr : Multipliable r) (hK : μ (φ ⁻¹' K') = ENNReal.ofReal (∏' v, a v))
    (hK' : μ' K' = ENNReal.ofReal (∏' v, a' v)) :
    μ.map φ = ENNReal.ofReal (∏' v, r v) • μ' := by
  rw [map_eq_smul_of_compact_open φ μ μ' hKc hKo hKne, hK, hK']
  congr 1
  have hprod : ∏' v, a v = (∏' v, r v) * ∏' v, a' v := by
    rw [show a = fun v => r v * a' v from funext har]
    exact hmr.tprod_mul hma'
  have hK0 : μ' K' ≠ 0 := (hKo.measure_pos μ' hKne).ne'
  have hpos : 0 < ∏' v, a' v := by
    rw [hK'] at hK0
    rcases (tprod_nonneg fun v => (ha' v).le : 0 ≤ ∏' v, a' v).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h, ENNReal.ofReal_zero]) hK0
  rw [hprod, ENNReal.ofReal_mul (tprod_nonneg hr), ENNReal.mul_div_cancel_right
    (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top]

end Haar

section Headline

variable {A B A' B' : Type*} [Group A] [Group B] [Group A'] [Group B']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace A'] [MeasurableSpace B']
  [MeasurableMul A] [MeasurableMul B] [MeasurableMul A'] [MeasurableMul B']

/-- **Generic measure transport for Tamagawa covolumes**. Let $\varphi = \varphi_\infty\times\varphi_f :
G_\infty\times G_f \to G'_\infty\times G'_f$ be a product of measurable group isomorphisms carrying $\Gamma$ onto $\Gamma'$,
with $(\varphi_\infty)_*\mu_\infty = r_\infty\,\mu'_\infty$ and $(\varphi_f)_*\mu_f = r_f\,\mu'_f$ (e.g. $r_f = \prod'_v r_v$ from
`map_eq_tprod_smul`). If $r_\infty r_f = 1$ (Weil's product formula), the covolumes agree. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (product formula ∏_v r_v = 1); §3.2 transport SO(D⁰) ≅ PD^× [unverified]"]
theorem covolume_eq_of_localFactors (Γ : Subgroup (A × B)) (Γ' : Subgroup (A' × B')) [Countable Γ]
    (φA : A ≃* A') (φB : B ≃* B') (hφA : Measurable φA) (hφA' : Measurable φA.symm) (hφB : Measurable φB)
    (hφB' : Measurable φB.symm) (hΓ : Γ.map (φA.prodCongr φB).toMonoidHom = Γ')
    (μA : Measure A) (μB : Measure B) (μA' : Measure A') (μB' : Measure B') [SFinite μA] [SFinite μB]
    [SFinite μA'] [SFinite μB'] [μA.IsMulLeftInvariant] [μB.IsMulLeftInvariant] [μA'.IsMulLeftInvariant]
    [μB'.IsMulLeftInvariant] {rA rB : ℝ≥0∞} (hA : μA.map φA = rA • μA') (hB : μB.map φB = rB • μB')
    (hr : rA * rB = 1) :
    covolume Γ (A × B) (μA.prod μB) = covolume Γ' (A' × B') (μA'.prod μB') := by
  have hmap : (μA.prod μB).map (φA.prodCongr φB) = μA'.prod μB' := by
    rw [show ((φA.prodCongr φB : A × B ≃* A' × B') : A × B → A' × B') = Prod.map φA φB from rfl,
      map_prodMap_prod hφA hφB μA μB μA' μB' hA hB, hr, one_smul]
  exact covolume_eq_of_map Γ Γ' (φA.prodCongr φB) (hφA.prodMap hφB) (hφA'.prodMap hφB') hΓ _ _ hmap

end Headline

end

end QuadFormsKB.Tamagawa.Measure.Weil
