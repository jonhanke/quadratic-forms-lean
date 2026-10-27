/-
# Weil's unfolding lemmas, discrete version

**Layer:** abstract measure theory. A countable group $\Gamma$ acts measurably on a measurable space $\alpha$ preserving a
measure $\mu$ (in the application: $\Gamma = SO(V)(F)$ acting on $\alpha = SO(V)(\mathbb A)$ by left
multiplication); $\gamma \le \Gamma$
is a subgroup, acting through $\Gamma$. Fundamental domains are Mathlib's `IsFundamentalDomain` (up to null sets).

**Proves** (all unconditional, standard axioms only)
* `isFundamentalDomain_unfold`: if $D$ is a fundamental domain for $\Gamma$, then $D_\gamma = \bigcup_{\xi\in\gamma\backslash\Gamma}\xi D$
  is a fundamental domain for $\gamma$ (here $\xi$ runs over $q.\mathrm{out}^{-1}$, $q \in \Gamma/\gamma$, a system of
  representatives of the right cosets $\gamma\backslash\Gamma$);
* `lintegral_unfold` (**Weil 1982, Lemma 2.4.2, p. 26, discrete case $g = \gamma$**): for $f \ge 0$ measurable and
  $\gamma$-invariant and any fundamental domains $D$ of $\Gamma$, $D'$ of $\gamma$,
  $$\int_{D'} f\,d\mu = \int_D \sum_{\xi\in\gamma\backslash\Gamma} f(\xi x)\,d\mu(x),$$
  i.e. $\int_{\gamma\backslash\alpha}f = \int_{\Gamma\backslash\alpha}\sum_{\xi\in\gamma\backslash\Gamma}f(\xi x)$
  (Weil writes it for right cosets, $\mu_g\int_{G/g}f = \int_{G/\Gamma}\sum_{\xi\in\Gamma/\gamma}f(x\xi)$);
* `lintegral_unfold_orbits` (**orbit unfolding**, Lemma 2.4.2 applied orbit by orbit; this is the measure-theoretic
  content of Weil's Lemma 2.4.1 for $G/\gamma \to G/g$ with discrete $g$ = a stabilizer): for a countable $\Gamma$-set $X$ and
  $\varphi : X \to \alpha \to [0,\infty]$ with $\varphi(g\xi, gx) = \varphi(\xi, x)$,
  $$\int_D\sum_{\xi\in X}\varphi(\xi, x)\,d\mu(x) = \sum_{\omega\in\Gamma\backslash X}\int_{D_\omega}\varphi(\xi_\omega, x)\,d\mu(x),$$
  $D_\omega$ any fundamental domain of the stabilizer $\Gamma_{\xi_\omega}$. This is the unfolding behind Siegel's formula
  and the representation masses (`two_mul_tamagawaK_mul_repMass_frame`); `Tamagawa/Measure/AdelicRepMass.lean` uses it.

The continuous case (a closed non-discrete $g \supseteq \gamma$, Weil's quotient measures on $G/g$, Theorem 2.4.3) is not
here: Mathlib has no Haar measure on $G/H$ for non-normal $H$.
-/
import QuadFormsKB.Tamagawa.Measure.NeatCovolume

open MeasureTheory Set MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

section Unfold

variable {Γ α : Type*} [Group Γ] [Countable Γ] [MulAction Γ α] [MeasurableSpace α]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableSMul Γ α]
  {μ : Measure α} [SMulInvariantMeasure Γ α μ]

instance countable_quotient (γ : Subgroup Γ) : Countable (Γ ⧸ γ) :=
  Function.Surjective.countable QuotientGroup.mk_surjective

/-- The translates $q.\mathrm{out}^{-1}D$, $q \in \Gamma/\gamma$: a fundamental domain for $\gamma$ (`isFundamentalDomain_unfold`). -/
def unfoldDomain (γ : Subgroup Γ) (D : Set α) : Set α := ⋃ q : Γ ⧸ γ, (q.out)⁻¹ • D

/-- **Fundamental domains for a subgroup** (Weil 1982, §2.4, p. 26): if $D$ is a fundamental domain for $\Gamma$, then
$\bigcup_{q\in\Gamma/\gamma}q.\mathrm{out}^{-1}D$ is one for $\gamma \le \Gamma$. -/
theorem isFundamentalDomain_unfold (γ : Subgroup Γ) {D : Set α} (hD : IsFundamentalDomain Γ D μ) :
    IsFundamentalDomain γ (unfoldDomain γ D) μ where
  nullMeasurableSet := NullMeasurableSet.iUnion fun q => hD.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [hD.ae_covers] with x ⟨g, hg⟩
    obtain ⟨η, hη⟩ := QuotientGroup.mk_out_eq_mul γ g
    refine ⟨η⁻¹, mem_iUnion.mpr ⟨(g : Γ ⧸ γ), ?_⟩⟩
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv, hη]
    show (g * (η : Γ)) • (((η⁻¹ : γ) : Γ) • x) ∈ D
    rw [smul_smul, Subgroup.coe_inv, mul_inv_cancel_right]
    exact hg
  aedisjoint := by
    intro η₁ η₂ hne
    simp only [Function.onFun, unfoldDomain, smul_set_iUnion]
    refine (AEDisjoint.iUnion_left_iff).mpr fun q₁ => (AEDisjoint.iUnion_right_iff).mpr fun q₂ => ?_
    show AEDisjoint μ ((η₁ : Γ) • (q₁.out)⁻¹ • D) ((η₂ : Γ) • (q₂.out)⁻¹ • D)
    rw [smul_smul, smul_smul]
    have h1 : ((η₁ : Γ) * (q₁.out)⁻¹) ≠ (η₂ : Γ) * (q₂.out)⁻¹ := by
      intro heq
      have hq : q₁ = q₂ := by
        rw [← q₁.out_eq', ← q₂.out_eq']
        apply QuotientGroup.eq.mpr
        have : (q₁.out)⁻¹ * q₂.out = (η₁ : Γ)⁻¹ * η₂ := by
          have := congrArg (fun z => (η₁ : Γ)⁻¹ * z * q₂.out) heq
          simpa [mul_assoc] using this
        rw [this]
        exact γ.mul_mem (γ.inv_mem η₁.2) η₂.2
      subst hq
      exact hne (Subtype.ext (mul_right_cancel heq))
    exact hD.aedisjoint h1

/-- The translates $q.\mathrm{out}^{-1}D$ are pairwise a.e. disjoint. -/
theorem aedisjoint_unfold (γ : Subgroup Γ) {D : Set α} (hD : IsFundamentalDomain Γ D μ) :
    Pairwise (Function.onFun (AEDisjoint μ) fun q : Γ ⧸ γ => (q.out)⁻¹ • D) := by
  intro q₁ q₂ hne
  refine hD.aedisjoint fun h => hne ?_
  rw [← q₁.out_eq', ← q₂.out_eq', inv_inj.mp h]

/-- Change of variables for a translate: $\int_{gD}f = \int_D f(g\,\cdot)$. -/
theorem setLIntegral_smul_set (g : Γ) (D : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x in g • D, f x ∂μ = ∫⁻ x in D, f (g • x) ∂μ := by
  have h := (measurePreserving_smul g μ).setLIntegral_comp_preimage_emb (measurableEmbedding_const_smul g) f (g • D)
  rw [← h, Set.preimage_smul, inv_smul_smul]

/-- **Weil's Lemma 2.4.2, discrete case** (Weil 1982, §2.4, Lemma 2.4.2, p. 26, with $g = \gamma$; left actions): for
$\gamma \le \Gamma$, fundamental domains $D$ of $\Gamma$ and $D'$ of $\gamma$, and $f \ge 0$ measurable and $\gamma$-invariant,
$$\int_{D'}f\,d\mu = \int_D\sum_{q\in\Gamma/\gamma}f(q.\mathrm{out}^{-1}x)\,d\mu(x)
  \qquad\Big(\int_{\gamma\backslash\alpha}f = \int_{\Gamma\backslash\alpha}\sum_{\xi\in\gamma\backslash\Gamma}f(\xi x)\Big).$$ -/
@[kb "weil1982" "§2.4, Lemma 2.4.2, p. 26 (unfolding; discrete case)"]
theorem lintegral_unfold (γ : Subgroup Γ) {D D' : Set α} (hD : IsFundamentalDomain Γ D μ)
    (hD' : IsFundamentalDomain γ D' μ) (f : α → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ η ∈ γ, ∀ x, f (η • x) = f x) :
    ∫⁻ x in D', f x ∂μ = ∫⁻ x in D, ∑' q : Γ ⧸ γ, f ((q.out)⁻¹ • x) ∂μ := by
  rw [hD'.setLIntegral_eq (isFundamentalDomain_unfold γ hD) f fun η x => hinv η η.2 x, unfoldDomain,
    lintegral_iUnion₀ (fun q => hD.nullMeasurableSet_smul _) (aedisjoint_unfold γ hD),
    tsum_congr fun q => setLIntegral_smul_set _ D f]
  exact (lintegral_tsum (f := fun (q : Γ ⧸ γ) x => f ((q.out)⁻¹ • x))
    fun q => (hf.comp (measurable_const_smul _)).aemeasurable).symm

/-! ### Orbit unfolding -/

variable {X : Type*} [MulAction Γ X] [Countable X]

/-- **Orbit unfolding** (Weil 1982, §2.4, Lemmas 2.4.1–2.4.2, discrete stabilizers): for a countable $\Gamma$-set $X$, a
family $\varphi : X \to \alpha \to [0,\infty]$ of measurable functions with $\varphi(g\xi, gx) = \varphi(\xi, x)$, a fundamental
domain $D$ of $\Gamma$, and fundamental domains $D_\omega$ of the stabilizers $\Gamma_{\xi_\omega}$ ($\xi_\omega$ = `ω.out`),
$$\int_D\sum_{\xi\in X}\varphi(\xi, x)\,d\mu(x) = \sum_{\omega\in\Gamma\backslash X}\int_{D_\omega}\varphi(\xi_\omega, x)\,d\mu(x).$$ -/
@[kb "weil1982" "§2.4, Lemmas 2.4.1-2.4.2, pp. 25-26 (unfolding over the orbits; discrete case)"]
theorem lintegral_unfold_orbits {D : Set α} (hD : IsFundamentalDomain Γ D μ) (φ : X → α → ℝ≥0∞)
    (hφ : ∀ ξ, Measurable (φ ξ)) (hinv : ∀ (g : Γ) ξ x, φ (g • ξ) (g • x) = φ ξ x)
    (Dω : orbitRel.Quotient Γ X → Set α)
    (hDω : ∀ ω, IsFundamentalDomain (stabilizer Γ ω.out) (Dω ω) μ) :
    ∫⁻ x in D, ∑' ξ, φ ξ x ∂μ = ∑' ω : orbitRel.Quotient Γ X, ∫⁻ x in Dω ω, φ ω.out x ∂μ := by
  -- reorganize the sum over `X` by orbits, and each orbit as `Γ / Stab`
  have hsplit : ∀ x, ∑' ξ, φ ξ x = ∑' ω : orbitRel.Quotient Γ X,
      ∑' q : Γ ⧸ stabilizer Γ ω.out, φ ω.out ((q.out)⁻¹ • x) := by
    intro x
    rw [← (selfEquivSigmaOrbits Γ X).symm.tsum_eq, ENNReal.tsum_sigma']
    refine tsum_congr fun ω => ?_
    rw [← (orbitEquivQuotientStabilizer Γ ω.out).symm.tsum_eq]
    refine tsum_congr fun q => ?_
    have h1 : ((orbitEquivQuotientStabilizer Γ ω.out).symm q : X) = q.out • ω.out := by
      rw [← q.out_eq', orbitEquivQuotientStabilizer_symm_apply, Quotient.out_eq']
    change φ (((orbitEquivQuotientStabilizer Γ ω.out).symm q : X)) x = _
    rw [h1]
    have := hinv q.out ω.out ((q.out)⁻¹ • x)
    rwa [smul_inv_smul] at this
  simp_rw [hsplit]
  rw [lintegral_tsum (f := fun (ω : orbitRel.Quotient Γ X) x => ∑' q : Γ ⧸ stabilizer Γ ω.out, φ ω.out ((q.out)⁻¹ • x))
    fun ω => (Measurable.ennreal_tsum fun q => (hφ _).comp (measurable_const_smul _)).aemeasurable]
  refine tsum_congr fun ω => ?_
  refine (lintegral_unfold (stabilizer Γ ω.out) hD (hDω ω) (φ ω.out) (hφ _) ?_).symm
  intro η hη x
  have := hinv η ω.out x
  rwa [mem_stabilizer_iff.mp hη] at this

end Unfold

end QuadFormsKB.Tamagawa.Measure
