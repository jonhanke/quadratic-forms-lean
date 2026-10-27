/-
# Abstract spherical unfolding in `[0,∞]`

**Layer:** abstract measure theory (Mathlib + `QuotientIntegral.lean`); nothing arithmetic. This is the
measure-theoretic content of Weil's unfolding of the additive zeta function along the spheres
(Weil 1982, §4.5, p. 109; Step 1), written so that the adelic
instantiation (`SphericalUnfoldAdelic.lean`) only has to supply the arithmetic data.

**Proves**
* `lintegral_mul_quotient` (**the multiplicative stage**): for a countable subgroup `Λ` of a commutative group `M`
  with fundamental domain `D_M`, a `Λ`-invariant weight `w` and any `M`-set `Y`,
  `∫_{D_M} w(z) Σ_{λ∈Λ} Φ(z · λ · y) dν = ∫_M w(z) Φ(z · y) dν`
  (for `M = 𝔸^×`, `Λ = F^×`, `w = ‖·‖^{m+2s}`: the sum over `F^×` unfolds `𝔸^×/F^×` to `𝔸^×`).
* `lintegral_sphere_unfold` (**the group stage, with exact constants**): let `Γ ≤ G` be countable with fundamental
  domain `D`, acting transitively on a set `X` (the rational sphere `T(ρ)(k)`) with base point `ξ₀`, equivariantly
  embedded in a `G`-set `Y` (`V_𝔸`). Suppose the orbit map `g ↦ g⁻¹ ξ₀` is fibred: a measurable equivalence
  `coord : T × H ≃ᵐ G` with `coord(x, h'h) = ι(h') coord(x, h)` and `coord(x,h)⁻¹ ξ₀ = τ(x)`, the stabilizer of `ξ₀`
  in `Γ` is `ι(Γ_H)`, and **`μ = c · coord_*(σ ⊗ μ_H)`** (Weil's Lemma 2.4.1/Thm 2.4.3 in measure form). Then for
  every measurable `f ≥ 0`,
  $$\int_D\sum_{\eta\in X}f(g^{-1}\eta)\,d\mu(g) = c\cdot\operatorname{covol}(\Gamma_H\backslash H)\cdot\int_T f(\tau x)\,d\sigma(x),$$
  an identity in `[0, ∞]` with **no hypothesis on `covol(Γ\G)`**.

**Outside results used:** Mathlib's `IsFundamentalDomain.mk'`, `IsFundamentalDomain.covolume_eq_volume`,
`lintegral_map_equiv`, `lintegral_prod_mul`; the library's `lintegral_orbit_unfold`, `lintegral_quotient_eq`.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.QuotientIntegral

open MeasureTheory MulAction Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

section SphereUnfold

/-! ### The multiplicative stage -/

/-- **The multiplicative stage of the unfolding** (Weil 1982, §4.5, p. 109: the sum over $k^\times$ unfolds
$\int_{\mathbb A^\times/k^\times}$ to $\int_{\mathbb A^\times}$). Let `Λ` be a countable subgroup of a commutative group
`M` with fundamental domain `D_M` for `ν`, `w : M → [0,∞]` a `Λ`-invariant weight and `Y` an `M`-set. For `y ∈ Y` with
`z ↦ w(z) Φ(z • y)` measurable:
$$\int_{D_M}w(z)\sum_{\lambda\in\Lambda}\Phi(z\cdot\lambda\cdot y)\,d\nu(z) = \int_M w(z)\,\Phi(z\cdot y)\,d\nu(z).$$ -/
@[kb "weil1982" "§4.5, p. 109 (∫_{Γ_A/Γ_k}…(dt/t)': the k^×-sum unfolds 𝔸^×/k^× to 𝔸^×) [unverified page]"]
theorem lintegral_mul_quotient {M : Type*} [CommGroup M] [MeasurableSpace M] {ν : Measure M}
    {Λ : Subgroup M} [Countable Λ] [MeasurableConstSMul Λ M] [SMulInvariantMeasure Λ M ν]
    {DM : Set M} (hDM : IsFundamentalDomain Λ DM ν) {Y : Type*} [MulAction M Y]
    (w : M → ℝ≥0∞) (hw : ∀ (l : Λ) (z : M), w ((l : M) * z) = w z) (Φ : Y → ℝ≥0∞) (y : Y)
    (hmeas : Measurable fun z => w z * Φ (z • y)) :
    ∫⁻ z in DM, w z * ∑' l : Λ, Φ (z • (l : M) • y) ∂ν = ∫⁻ z, w z * Φ (z • y) ∂ν := by
  rw [← lintegral_quotient_eq hDM hmeas]
  refine lintegral_congr fun z => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun l => ?_
  show w z * Φ (z • (l : M) • y) = w ((l : M) * z) * Φ (((l : M) * z) • y)
  rw [hw, mul_comm (l : M) z, mul_smul]

/-! ### The group stage -/

variable {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  {Γ : Subgroup G} [Countable Γ] [MeasurableConstSMul Γ G] [SMulInvariantMeasure Γ G μ]
  {Y : Type*} [MulAction G Y] {X : Type*} [MulAction Γ X]
  {H : Type*} [Group H] [MeasurableSpace H] {μH : Measure H} [SFinite μH]
  {ΓH : Subgroup H} [Countable ΓH] [MeasurableConstSMul ΓH H] [SMulInvariantMeasure ΓH H μH]
  {T : Type*} [MeasurableSpace T]

/-- **Fibration data for the orbit map** $g\mapsto g^{-1}\xi_0$ (Weil 1982, Lemma 2.4.1 / Thm 2.4.3, inverted
convention): a measurable bijection $\mathrm{coord} : T\times H \to G$ with
* `mul`: $\mathrm{coord}(x, h'h) = \iota(h')\,\mathrm{coord}(x, h)$ ($H$ acts on the left fibre coordinate through
  $\iota : H\to G$);
* `orbit`: $\mathrm{coord}(x, h)^{-1}\cdot j(\xi_0) = \tau(x)$ (the first coordinate is the point $g^{-1}\xi_0$ of the
  orbit, embedded by $\tau : T \to Y$).
Data (`coord`) with its defining equations; not a cited input. Fields: `coord`, `mul`, `orbit`. -/
structure OrbitCoord (ι : H →* G) (τ : T → Y) (y₀ : Y) where
  /-- The coordinates $T\times H \cong G$. -/
  coord : T × H ≃ᵐ G
  /-- Left equivariance in the fibre coordinate. -/
  mul : ∀ (x : T) (h h' : H), coord (x, h' * h) = ι h' * coord (x, h)
  /-- The first coordinate is the orbit point. -/
  orbit : ∀ (x : T) (h : H), (coord (x, h))⁻¹ • y₀ = τ x

namespace OrbitCoord

variable {ι : H →* G} {τ : T → Y} {y₀ : Y} (C : OrbitCoord ι τ y₀)

theorem coord_eq (x : T) (h : H) : C.coord (x, h) = ι h * C.coord (x, 1) := by
  rw [← C.mul, mul_one]

theorem ι_injective (C : OrbitCoord ι τ y₀) : Function.Injective ι := by
  intro h h' e
  obtain ⟨x⟩ : Nonempty T := ⟨(C.coord.symm 1).1⟩
  have : C.coord (x, h) = C.coord (x, h') := by rw [C.coord_eq, C.coord_eq x h', e]
  exact congrArg Prod.snd (C.coord.injective this)

/-- $g^{-1}y_0 = \tau(\mathrm{coord}^{-1}(g)_1)$. -/
theorem inv_smul_eq (g : G) : g⁻¹ • y₀ = τ (C.coord.symm g).1 := by
  conv_lhs => rw [← C.coord.apply_symm_apply g]
  exact C.orbit _ _

end OrbitCoord

/-- **The group stage of the unfolding, with exact constants** (Weil 1982, §4.5, p. 109, via Lemma 2.4.1 and
Thm 2.4.3; lattice analogue). Setting:
* `Γ ≤ G` countable, `μ` a `Γ`-invariant measure on `G` (left multiplication), `D` a fundamental domain;
* `X` a `Γ`-set on which `Γ` is **transitive** (base point `ξ₀`; Witt's theorem for `X = T(ρ)(k)`), embedded
  equivariantly in a `G`-set `Y` by `j`;
* fibration data `C : OrbitCoord ι τ (j ξ₀)` for the orbit map, `ΓH ≤ H` with the **stabilizer condition**
  $\iota(\Gamma_H) = \operatorname{Stab}_\Gamma(\xi_0)$ (`hιΓ`, `hfix`, `hstab`), and an exact measurable fundamental
  domain `DH` of `ΓH`;
* **the fibration identity** $\mu = c\cdot\mathrm{coord}_*(\sigma\otimes\mu_H)$.
Then for every `f : Y → [0,∞]` with `f ∘ τ` measurable,
$$\int_D\sum_{\eta\in X}f(g^{-1}j(\eta))\,d\mu(g) = c\cdot\operatorname{covol}(\Gamma_H\backslash H, \mu_H)\cdot\int_T f(\tau x)\,d\sigma(x)$$
in $[0,\infty]$. No finiteness of $\operatorname{covol}(\Gamma\backslash G)$ is assumed. -/
@[kb "weil1982" "§4.5, p. 109 (unfolding along T(ρ)); Lemma 2.4.1, Thm 2.4.3 [unverified page]"]
theorem lintegral_sphere_unfold (j : X → Y) (hj : ∀ (γ : Γ) (η : X), j (γ • η) = (γ : G) • j η) (ξ₀ : X)
    (htrans : ∀ η : X, ∃ γ : Γ, γ • ξ₀ = η) (ι : H →* G) (σ : Measure T) [SFinite σ] (τ : T → Y)
    (C : OrbitCoord ι τ (j ξ₀))
    (hιΓ : ∀ h ∈ ΓH, ι h ∈ Γ) (hfix : ∀ (h : H) (hh : h ∈ ΓH), (⟨ι h, hιΓ h hh⟩ : Γ) • ξ₀ = ξ₀)
    (hstab : ∀ γ : Γ, γ • ξ₀ = ξ₀ → ∃ h ∈ ΓH, ι h = γ)
    {DH : Set H} (hDH : MeasurableSet DH) (hDHx : ∀ h : H, ∃! γ : ΓH, γ • h ∈ DH)
    (c : ℝ≥0∞) (hfib : μ = c • (σ.prod μH).map C.coord)
    {D : Set G} (hD : IsFundamentalDomain Γ D μ) (f : Y → ℝ≥0∞) (hf : Measurable fun x => f (τ x)) :
    ∫⁻ g in D, ∑' η : X, f (g⁻¹ • j η) ∂μ = c * covolume ΓH H μH * ∫⁻ x, f (τ x) ∂σ := by
  classical
  -- the equivariant family and the orbit
  set Φ : X → G → ℝ≥0∞ := fun η g => f (g⁻¹ • j η) with hΦdef
  have hΦ : ∀ (γ : Γ) (η : X) (g : G), Φ (γ • η) (γ • g) = Φ η g := by
    intro γ η g
    simp only [hΦdef, hj, Subgroup.smul_def, smul_eq_mul, mul_inv_rev, mul_smul, inv_smul_smul]
  have hΦ0 : Φ ξ₀ = fun g => f (τ (C.coord.symm g).1) := funext fun g => by
    simp only [hΦdef, C.inv_smul_eq]
  have hmeas : Measurable (Φ ξ₀) := by
    rw [hΦ0]; exact hf.comp (measurable_fst.comp C.coord.symm.measurable)
  let e : orbit Γ ξ₀ ≃ X := Equiv.subtypeUnivEquiv fun η => htrans η
  -- the exact fundamental domain of the stabilizer
  set E : Set G := C.coord.symm ⁻¹' (univ ×ˢ DH) with hEdef
  have hE : MeasurableSet E := C.coord.symm.measurable (MeasurableSet.univ.prod hDH)
  have hcoordE : ∀ x h, C.coord (x, h) ∈ E ↔ h ∈ DH := by
    intro x h
    simp [hEdef]
  have hEx : ∀ y : G, ∃! s : stabilizer Γ ξ₀, s • y ∈ E := by
    intro y
    set p := C.coord.symm y with hp
    have hy : y = C.coord p := (C.coord.apply_symm_apply y).symm
    have hsm : ∀ (s : stabilizer Γ ξ₀) (k : H), ι k = ((s : Γ) : G) → s • y = C.coord (p.1, k * p.2) := by
      intro s k hk
      show ((s : Γ) : G) * y = _
      rw [← hk, C.mul, hy]
    obtain ⟨γH, hγH, huniq⟩ := hDHx p.2
    let s₀ : stabilizer Γ ξ₀ := ⟨⟨ι γH, hιΓ γH γH.2⟩, hfix γH γH.2⟩
    refine ⟨s₀, ?_, fun s hs => ?_⟩
    · show s₀ • y ∈ E
      rw [hsm s₀ γH rfl, hcoordE]; exact hγH
    · obtain ⟨k, hk, hks⟩ := hstab s s.2
      have hs : s • y ∈ E := hs
      rw [hsm s k hks, hcoordE] at hs
      have : (⟨k, hk⟩ : ΓH) = γH := huniq _ hs
      apply Subtype.ext; apply Subtype.ext
      show ((s : Γ) : G) = ι γH
      rw [← hks, ← this]
  have hDHf : IsFundamentalDomain ΓH DH μH := IsFundamentalDomain.mk' hDH.nullMeasurableSet hDHx
  have hpt : ∀ p : T × H, E.indicator (Φ ξ₀) (C.coord p) = f (τ p.1) * DH.indicator 1 p.2 := by
    rintro ⟨x, h⟩
    by_cases hh : h ∈ DH
    · rw [indicator_of_mem ((hcoordE x h).mpr hh), indicator_of_mem hh, Pi.one_apply, mul_one, hΦ0]
      simp
    · rw [indicator_of_notMem (fun h' => hh ((hcoordE x h).mp h')), indicator_of_notMem hh, mul_zero]
  calc ∫⁻ g in D, ∑' η : X, f (g⁻¹ • j η) ∂μ = ∫⁻ g in D, ∑' η : orbit Γ ξ₀, Φ η g ∂μ :=
        lintegral_congr fun g => (e.tsum_eq (fun η => Φ η g)).symm
    _ = ∫⁻ g in E, Φ ξ₀ g ∂μ := lintegral_orbit_unfold ξ₀ Φ hΦ hmeas hD hE hEx
    _ = c * ∫⁻ p, E.indicator (Φ ξ₀) (C.coord p) ∂σ.prod μH := by
        rw [← lintegral_indicator hE, hfib, lintegral_smul_measure, lintegral_map_equiv, smul_eq_mul]
    _ = c * ((∫⁻ x, f (τ x) ∂σ) * μH DH) := by
        simp_rw [hpt]
        rw [lintegral_prod_mul hf.aemeasurable (measurable_one.indicator hDH).aemeasurable,
          lintegral_indicator_one hDH]
    _ = c * covolume ΓH H μH * ∫⁻ x, f (τ x) ∂σ := by
        rw [hDHf.covolume_eq_volume μH]; ring

end SphereUnfold

end QuadFormsKB.Tamagawa.Measure.Weil
