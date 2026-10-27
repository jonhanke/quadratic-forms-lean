/-
# Quotient integrals in `[0,∞]` and the Siegel finiteness criterion

**Layer:** abstract measure theory for a countable group `Γ` acting measurably on a measure space `(α, μ)`
(`SMulInvariantMeasure`). Nothing is topological or arithmetic. Written so that the later developments (SL₂ finiteness,
Fujisaki, the indefinite Tamagawa number) can use it for `Γ = G(k)`, `α = G(𝔸)`.

**Proves**
* `lintegral_quotient_eq`: for a fundamental domain `D` and measurable `f : α → [0,∞]`,
  `∫_D Σ_{γ∈Γ} f(γ x) dμ = ∫_α f dμ` (so the quotient integral does not depend on `D`);
  `lintegral_quotient_indep` states this independence.
* `lintegral_orbit_unfold`: **orbit unfolding.** For a `Γ`-set `X`, a point `r ∈ X`, and an equivariant family
  `Φ : X → α → [0,∞]` (`Φ (γ ξ) (γ x) = Φ ξ x`), if `E` is an exact measurable fundamental domain for the stabilizer
  `Γ_r` acting on `α`, then `∫_D Σ_{ξ ∈ Γ r} Φ ξ x dμ = ∫_E Φ r x dμ`.
* `measure_le_tsum_orbit_integrals`, `covolume_le_tsum_orbit_integrals`: **the finiteness criterion** (Siegel's
  mean-value argument). If `Σ_{ξ ∈ X} Φ ξ x ≥ 1` for every `x`, then `covol(Γ, α, μ) ≤ Σ_{orbits q} ∫_{E_q} Φ(r_q, ·)`.
  For `α = G(𝔸)` and `Φ ξ g = f(g⁻¹ ξ)` the right side is the mean value `∫ f` over the orbit-stabilizer quotient.
-/
import Mathlib
import QuadFormsKB.Citation

open MeasureTheory MulAction Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

section QuotientIntegral

variable {Γ α : Type*} [Group Γ] [Countable Γ] [MeasurableSpace α] [MulAction Γ α]
  [MeasurableConstSMul Γ α] {μ : Measure α} [SMulInvariantMeasure Γ α μ]

/-- **Quotient integral.** If `D` is a fundamental domain for `Γ` and `f ≥ 0` is measurable, then
`∫_D Σ_{γ∈Γ} f(γ x) dμ(x) = ∫_α f dμ`. (The orbit sum `Σ_γ f(γ x)` is a function on `Γ\α`; this says its integral
over `Γ\α`, computed on `D`, is the integral of `f`.) -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); finiteness via mean value"]
theorem lintegral_quotient_eq {D : Set α} (hD : IsFundamentalDomain Γ D μ) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x in D, ∑' γ : Γ, f (γ • x) ∂μ = ∫⁻ x, f x ∂μ := by
  rw [lintegral_tsum (f := fun γ x => f (γ • x))
    fun γ => (hf.comp (measurable_const_smul γ)).aemeasurable, hD.lintegral_eq_tsum'' f]

/-- The quotient integral `∫_D Σ_γ f(γ x)` does not depend on the fundamental domain `D`. -/
theorem lintegral_quotient_indep {D D' : Set α} (hD : IsFundamentalDomain Γ D μ)
    (hD' : IsFundamentalDomain Γ D' μ) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in D, ∑' γ : Γ, f (γ • x) ∂μ = ∫⁻ x in D', ∑' γ : Γ, f (γ • x) ∂μ := by
  rw [lintegral_quotient_eq hD hf, lintegral_quotient_eq hD' hf]

variable {X : Type*} [MulAction Γ X]

/-- Pointwise form of the orbit unfolding: if `E` is an exact fundamental domain for `Γ_r`, then
`Σ_{γ∈Γ} 1_E(γ x) Φ(r, γ x) = Σ_{ξ ∈ Γ r} Φ(ξ, x)`. -/
theorem tsum_indicator_orbit (r : X) (Φ : X → α → ℝ≥0∞)
    (hΦ : ∀ (γ : Γ) (ξ : X) (x : α), Φ (γ • ξ) (γ • x) = Φ ξ x) {E : Set α}
    (hEx : ∀ y : α, ∃! s : stabilizer Γ r, s • y ∈ E) (x : α) :
    ∑' γ : Γ, E.indicator (Φ r) (γ • x) = ∑' ξ : orbit Γ r, Φ ξ x := by
  classical
  let p : Γ → orbit Γ r := fun γ => ⟨γ⁻¹ • r, γ⁻¹, rfl⟩
  have hp : ∀ γ : Γ, E.indicator (Φ r) (γ • x) = E.indicator (fun _ => Φ (p γ).1 x) (γ • x) := by
    intro γ
    by_cases h : γ • x ∈ E
    · simp only [indicator_of_mem h]
      have := hΦ γ⁻¹ r (γ • x)
      rw [inv_smul_smul] at this
      exact this.symm
    · simp [indicator_of_notMem h]
  rw [← (Equiv.sigmaFiberEquiv p).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun ξ => ?_
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : Γ, p γ₀ = ξ := by
    obtain ⟨_, δ, rfl⟩ := ξ
    exact ⟨δ⁻¹, by simp [p]⟩
  obtain ⟨s₁, hs₁, hs₁u⟩ := hEx (γ₀ • x)
  have hmem : ∀ γ : Γ, p γ = ξ ↔ ∃ s : stabilizer Γ r, γ = (s : Γ) * γ₀ := by
    intro γ
    rw [← hγ₀]
    constructor
    · intro h
      have h' : γ⁻¹ • r = γ₀⁻¹ • r := congrArg Subtype.val h
      refine ⟨⟨γ * γ₀⁻¹, ?_⟩, by group⟩
      rw [mem_stabilizer_iff, mul_smul]
      have : γ₀⁻¹ • r = γ⁻¹ • r := h'.symm
      rw [this, smul_inv_smul]
    · rintro ⟨s, rfl⟩
      apply Subtype.ext
      show ((s : Γ) * γ₀)⁻¹ • r = γ₀⁻¹ • r
      have hs : (s : Γ)⁻¹ • r = r := by
        have := (mem_stabilizer_iff.mp s.2)
        rw [inv_smul_eq_iff]; exact this.symm
      rw [mul_inv_rev, mul_smul, hs]
  set γ₁ : Γ := (s₁ : Γ) * γ₀ with hγ₁
  have h1 : p γ₁ = ξ := (hmem _).mpr ⟨s₁, rfl⟩
  rw [tsum_eq_single (⟨γ₁, h1⟩ : {γ // p γ = ξ})]
  · show E.indicator (Φ r) (γ₁ • x) = Φ ξ x
    rw [hp, ← h1]
    refine indicator_of_mem ?_ _
    rw [hγ₁, mul_smul]; exact hs₁
  · rintro ⟨γ, hγ⟩ hne
    show E.indicator (Φ r) (γ • x) = 0
    obtain ⟨s, rfl⟩ := (hmem γ).mp hγ
    apply indicator_of_notMem
    intro hmemE
    apply hne
    have : s = s₁ := hs₁u s (by rw [mul_smul] at hmemE; exact hmemE)
    subst this; rfl

/-- **Orbit unfolding** (the abstract form of unfolding a sum over `Γ r` against `Γ_r\α`): if `D` is a fundamental
domain for `Γ` and `E` an exact measurable fundamental domain for the stabilizer `Γ_r`, then
`∫_D Σ_{ξ ∈ Γ r} Φ(ξ, x) dμ = ∫_E Φ(r, x) dμ`. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); finiteness via mean value"]
theorem lintegral_orbit_unfold (r : X) (Φ : X → α → ℝ≥0∞)
    (hΦ : ∀ (γ : Γ) (ξ : X) (x : α), Φ (γ • ξ) (γ • x) = Φ ξ x) (hmeas : Measurable (Φ r))
    {D E : Set α} (hD : IsFundamentalDomain Γ D μ) (hE : MeasurableSet E)
    (hEx : ∀ y : α, ∃! s : stabilizer Γ r, s • y ∈ E) :
    ∫⁻ x in D, ∑' ξ : orbit Γ r, Φ ξ x ∂μ = ∫⁻ x in E, Φ r x ∂μ := by
  rw [← lintegral_indicator hE, ← lintegral_quotient_eq hD (hmeas.indicator hE)]
  exact lintegral_congr fun x => (tsum_indicator_orbit r Φ hΦ hEx x).symm

/-- Splitting a sum over a `Γ`-set `X` into its orbits (with representatives `Quotient.out`). -/
theorem tsum_eq_tsum_orbits (F : X → ℝ≥0∞) :
    ∑' ξ : X, F ξ = ∑' q : orbitRel.Quotient Γ X, ∑' ξ : orbit Γ q.out, F ξ := by
  classical
  let p : X → orbitRel.Quotient Γ X := fun ξ => Quotient.mk'' ξ
  rw [← (Equiv.sigmaFiberEquiv p).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun q => ?_
  exact Equiv.tsum_eq (Equiv.subtypeEquivRight fun ξ => by
    show Quotient.mk'' ξ = q ↔ ξ ∈ orbit Γ q.out
    rw [← orbitRel.Quotient.mem_orbit,
      orbitRel.Quotient.orbit_eq_orbit_out q (φ := Quotient.out) Quotient.out_eq']) (fun ξ : orbit Γ q.out => F ξ.1)

/-- **Siegel's finiteness criterion** (positivity form). Let `Γ` act on `α` (invariant measure `μ`, fundamental domain
`D`) and on a countable set `X`, and let `Φ : X → α → [0,∞]` be measurable and `Γ`-equivariant. If
`Σ_{ξ∈X} Φ(ξ, x) ≥ 1` for every `x ∈ α`, then
`μ(D) ≤ Σ_{orbits q} ∫_{E_q} Φ(r_q, x) dμ`,
where `r_q = q.out` is the chosen representative of the orbit `q` and `E_q` is any exact measurable fundamental
domain for its stabilizer. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); finiteness via mean value"]
theorem measure_le_tsum_orbit_integrals [Countable X] (Φ : X → α → ℝ≥0∞)
    (hΦ : ∀ (γ : Γ) (ξ : X) (x : α), Φ (γ • ξ) (γ • x) = Φ ξ x) (hmeas : ∀ ξ, Measurable (Φ ξ))
    (hone : ∀ x, 1 ≤ ∑' ξ : X, Φ ξ x) {D : Set α} (hD : IsFundamentalDomain Γ D μ)
    (E : orbitRel.Quotient Γ X → Set α) (hE : ∀ q, MeasurableSet (E q))
    (hEx : ∀ (q : orbitRel.Quotient Γ X) (y : α), ∃! s : stabilizer Γ q.out, s • y ∈ E q) :
    μ D ≤ ∑' q : orbitRel.Quotient Γ X, ∫⁻ x in E q, Φ q.out x ∂μ := by
  calc μ D = ∫⁻ x in D, 1 ∂μ := by simp
    _ ≤ ∫⁻ x in D, ∑' ξ : X, Φ ξ x ∂μ := lintegral_mono hone
    _ = ∫⁻ x in D, ∑' q : orbitRel.Quotient Γ X, ∑' ξ : orbit Γ q.out, Φ ξ x ∂μ := by
        exact lintegral_congr fun x => tsum_eq_tsum_orbits (fun ξ => Φ ξ x)
    _ = ∑' q : orbitRel.Quotient Γ X, ∫⁻ x in D, ∑' ξ : orbit Γ q.out, Φ ξ x ∂μ := by
        have : Countable (orbitRel.Quotient Γ X) := Quotient.countable
        refine lintegral_tsum fun q => (Measurable.tsum ?_).aemeasurable
        exact fun ξ => hmeas _
    _ = ∑' q : orbitRel.Quotient Γ X, ∫⁻ x in E q, Φ q.out x ∂μ :=
        tsum_congr fun q => lintegral_orbit_unfold q.out Φ hΦ (hmeas _) hD (hE q) (hEx q)

/-- **Finiteness criterion, covolume form.** Under the hypotheses of `measure_le_tsum_orbit_integrals`,
`covolume Γ α μ ≤ Σ_q ∫_{E_q} Φ(r_q, ·) dμ`. In particular the covolume is finite as soon as each orbit integral is. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); finiteness via mean value"]
theorem covolume_le_tsum_orbit_integrals [Countable X] (Φ : X → α → ℝ≥0∞)
    (hΦ : ∀ (γ : Γ) (ξ : X) (x : α), Φ (γ • ξ) (γ • x) = Φ ξ x) (hmeas : ∀ ξ, Measurable (Φ ξ))
    (hone : ∀ x, 1 ≤ ∑' ξ : X, Φ ξ x) {D : Set α} (hD : IsFundamentalDomain Γ D μ)
    (E : orbitRel.Quotient Γ X → Set α) (hE : ∀ q, MeasurableSet (E q))
    (hEx : ∀ (q : orbitRel.Quotient Γ X) (y : α), ∃! s : stabilizer Γ q.out, s • y ∈ E q) :
    covolume Γ α μ ≤ ∑' q : orbitRel.Quotient Γ X, ∫⁻ x in E q, Φ q.out x ∂μ := by
  rw [hD.covolume_eq_volume μ]
  exact measure_le_tsum_orbit_integrals Φ hΦ hmeas hone hD E hE hEx

end QuotientIntegral

end QuadFormsKB.Tamagawa.Measure.Weil
