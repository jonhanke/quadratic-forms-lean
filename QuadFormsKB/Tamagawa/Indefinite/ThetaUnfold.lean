/-
# The theta integral of an indefinite form, classically (Siegel's formula for indefinite forms)

**Layer:** abstract group and measure theory (no topology, no number theory). This is the measure-theoretic content of
the
classical translation of
the adelic Siegel–Weil identity for a form of any signature, written so that the arithmetic instantiation only has to
supply the groups, the lattices and the archimedean fibrations.

**Setting.** `G = A × B` (`A = G_∞`, `B = G_f`), `Γ ≤ A × B` countable (`G(F)` embedded diagonally), `K' ≤ B`
measurable (`SO(\hat L)`), `β : ι → B` exact representatives of the double cosets `Γ_f \ B / K'`, and `D_i` exact
measurable fundamental domains of the groups `Γ_{β_i}` = `levelGroup Γ K' (β i)` (the unit groups `SO(M_i)`,
`M_i = β_i\hat L ∩ V`, viewed in `G_∞`). The group `Γ` acts on a set `X` (the rational vectors of value `m`), embedded
equivariantly in an `A`-set `Y` (`V_∞`) by `j_A` and in a `B`-set `Y_f` (`V_{𝔸_f}`) by `j_B`; `Λ ⊆ Y_f` is
`K'`-stable (`\hat L`). For `Φ : Y → [0,∞]` the theta function of `Φ ⊗ 1_Λ` is
$$\theta(g) = \sum_{\eta\in X}\Phi(g_\infty^{-1}j_A\eta)\,1_\Lambda(g_f^{-1}j_B\eta).$$

**Proves** (all unconditional, standard axioms only)
* `lintegral_theta_beta` (**the β-decomposition of the theta integral**): for every fundamental domain `D` of `Γ`,
  $$\int_D\theta\,d(\mu_A\times\mu_B) = \mu_B(K')\sum_i\int_{D_i}\sum_{\eta\in X,\ j_B\eta\in\beta_i\Lambda}
    \Phi(a^{-1}j_A\eta)\,d\mu_A(a).$$
* `lintegral_tsum_eq_repMeasure` (**unfolding along the orbits, with the archimedean fibration**): for a countable
  subgroup `Γ' ≤ A` with fundamental domain `D'`, a countable `Γ'`-stable set `S ⊆ P` (the representations), and an
  archimedean fibration `𝔉` (`ArchFibration`: `μ_A = c · coord_*(σ ⊗ μ_{H_y})` for the stabilizer `H_y` of each
  `y ∈ P`),
  $$\int_{D'}\sum_{y\in S}\Phi(a^{-1}y)\,d\mu_A(a) = c\cdot\rho_{\Gamma'}(S)\cdot\int_T\Phi(\tau x)\,d\sigma(x),\qquad
    \rho_{\Gamma'}(S) = \sum_{y\in\Gamma'\backslash S}\operatorname{vol}(\Gamma'_y\backslash H_y)\quad(\texttt{repMeasureOf}).$$
* `lintegral_theta_eq` (**the classical theta integral**): combining the two,
  $\int_D\theta = \mu_B(K')\cdot c\cdot\sum_i\rho_{\Gamma_{\beta_i}}(S_i)\cdot\int_T\Phi\circ\tau\,d\sigma$, with
  `S_i = j_A(\{\eta : j_B\eta\in\beta_i\Lambda\})`; and `covolume_eq_measure_mul_tsum_covolume` gives
  `covol(Γ) = μ_B(K')·Σ_i covol(Γ_{β_i}\A)`. Both identities hold in `[0, ∞]` with no finiteness hypothesis.

**Outside results used:** Mathlib's `IsFundamentalDomain.setLIntegral_eq`, `lintegral_prod_mul`,
`lintegral_iUnion`; the library's `exists_unique_smul_mem_beta`, `covolume_eq_measure_mul_tsum_covolume`,
`tsum_eq_tsum_orbits` and `lintegral_sphere_unfold`.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.BetaDecomposition
import QuadFormsKB.Tamagawa.Measure.Weil.SphereUnfoldAbstract

open MeasureTheory MulAction Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Tamagawa.Measure.Weil

/-! ### Subgroups act measurably and preserve left-invariant measures -/

section Sub

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A]

theorem measurableConstSMul_subgroup (S : Subgroup A) : MeasurableConstSMul S A :=
  ⟨fun c => measurable_const_mul (c : A)⟩

/-- A subgroup carries the induced measurable multiplication. -/
theorem measurableMul_subgroup (H : Subgroup A) : MeasurableMul H :=
  ⟨fun c => ((measurable_const_mul (c : A)).comp measurable_subtype_coe).subtype_mk,
   fun c => ((measurable_mul_const (c : A)).comp measurable_subtype_coe).subtype_mk⟩

theorem smulInvariantMeasure_subgroup (S : Subgroup A) (μ : Measure A) [μ.IsMulLeftInvariant] :
    SMulInvariantMeasure S A μ :=
  ⟨fun c _ hs => by
    show μ ((fun x => (c : A) * x) ⁻¹' _) = _
    exact measure_preimage_mul μ (c : A) _⟩

/-- A subgroup `S'` of a subgroup `H ≤ A` acts measurably on `H` (subspace structure). -/
theorem measurableConstSMul_subgroupOf (H : Subgroup A) (S : Subgroup H) : MeasurableConstSMul S H :=
  ⟨fun c => ((measurable_const_mul ((c : H) : A)).comp measurable_subtype_coe).subtype_mk⟩

end Sub

/-! ### The archimedean fibration and the measure of representations -/

section Orbits

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] {μA : Measure A}
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T]

/-- **An archimedean fibration over the quadric `P`** (Weil 1982, Lemma 2.4.1 / Thm 2.4.3, inverted convention, for
the orbit maps $g\mapsto g^{-1}y$, $y\in P$): for every point `y ∈ P` a Haar measure `μH y` on its stabilizer
$H_y = \operatorname{Stab}_A(y)$ and coordinates $T\times H_y\cong A$ (`coord y`, an `OrbitCoord` for the inclusion
$H_y\to A$, the parametrization `τ : T → Y` of `P` and the base point `y`), such that
$$\mu_A = c\cdot\mathrm{coord}_*(\sigma\otimes\mu_{H_y})$$
with one constant `c` for all `y`. This is data with its defining properties, constructed (not assumed) in the
applications. Fields: `μH`, `coord`, `sigmaFinite`, `leftInv`, `fib`. -/
structure ArchFibration (μA : Measure A) (P : Set Y) (σ : Measure T) (τ : T → Y) (c : ℝ≥0∞) where
  /-- The measure on the stabilizer $H_y$. -/
  μH : (y : Y) → Measure (stabilizer A y)
  /-- The coordinates $T\times H_y\cong A$ for $y\in P$. -/
  coord : (y : Y) → y ∈ P → OrbitCoord (stabilizer A y).subtype τ y
  /-- `μH y` is σ-finite. -/
  sigmaFinite : ∀ y, SigmaFinite (μH y)
  /-- `μH y` is left invariant. -/
  leftInv : ∀ y, (μH y).IsMulLeftInvariant
  /-- The fibration identity $\mu_A = c\cdot\mathrm{coord}_*(\sigma\otimes\mu_{H_y})$. -/
  fib : ∀ y (hy : y ∈ P), μA = c • (σ.prod (μH y)).map (coord y hy).coord

/-- The arithmetic stabilizer $\Gamma'_y = \Gamma'\cap H_y$, as a subgroup of $H_y$. -/
abbrev stabArith (Γ' : Subgroup A) (y : Y) : Subgroup (stabilizer A y) := Γ'.subgroupOf (stabilizer A y)

/-- **The measure of representations** (abstract form; Siegel's *Darstellungsmaß*): for a subgroup `Γ' ≤ A`, a
`Γ'`-stable set `S ⊆ Y` and measures `μH y` on the stabilizers,
$$\rho_{\Gamma'}(S) = \sum_{y\in\Gamma'\backslash S}\operatorname{vol}(\Gamma'_y\backslash H_y,\ \mu_{H_y}),$$
the sum over the `Γ'`-orbits in `S` (representatives `Quotient.out`), each term the covolume of $\Gamma'_y$ in $H_y$.
Parameters: `Γ'`, `S`, `μH`. -/
def repMeasureOf (Γ' : Subgroup A) (S : SubMulAction Γ' Y) (μH : (y : Y) → Measure (stabilizer A y)) : ℝ≥0∞ :=
  ∑' q : orbitRel.Quotient Γ' S, covolume (stabArith Γ' ((q.out : S) : Y)) (stabilizer A ((q.out : S) : Y))
    (μH ((q.out : S) : Y))

/-- **Unfolding a sum over representations along the orbits** (Weil 1982, §2.4, Lemmas 2.4.1–2.4.2 and Thm 2.4.3,
discrete stabilizers; Siegel 1936). Let `Γ' ≤ A` be countable with fundamental domain `D'`, `S` a countable
`Γ'`-stable subset of the quadric `P`, and `𝔉` an archimedean fibration over `P`. If every arithmetic stabilizer
$\Gamma'_y$ has an exact measurable fundamental domain in $H_y$, then for every `Φ : Y → [0,∞]` with
`a ↦ Φ(a⁻¹y)` and `Φ ∘ τ` measurable,
$$\int_{D'}\sum_{y\in S}\Phi(a^{-1}y)\,d\mu_A(a) = c\cdot\rho_{\Gamma'}(S)\cdot\int_T\Phi(\tau x)\,d\sigma(x).$$ -/
@[kb "weil1982" "§2.4, Lemmas 2.4.1-2.4.2, Thm 2.4.3, pp. 25-26 (unfolding; discrete stabilizers) [unverified page]"]
theorem lintegral_tsum_eq_repMeasure (Γ' : Subgroup A) [Countable Γ'] [μA.IsMulLeftInvariant]
    {P : Set Y} {σ : Measure T} [SFinite σ] {τ : T → Y} {c : ℝ≥0∞} (𝔉 : ArchFibration μA P σ τ c)
    (S : SubMulAction Γ' Y) [Countable S] (hSP : ∀ y ∈ S, y ∈ P)
    (hDH : ∀ y : Y, ∃ DH : Set (stabilizer A y), MeasurableSet DH ∧
      ∀ h : stabilizer A y, ∃! γ : stabArith Γ' y, γ • h ∈ DH)
    {D' : Set A} (hD' : IsFundamentalDomain Γ' D' μA) (Φ : Y → ℝ≥0∞)
    (hΦ : ∀ y, Measurable fun a : A => Φ (a⁻¹ • y)) (hΦτ : Measurable fun x => Φ (τ x)) :
    ∫⁻ a in D', ∑' y : S, Φ (a⁻¹ • (y : Y)) ∂μA = c * repMeasureOf Γ' S 𝔉.μH * ∫⁻ x, Φ (τ x) ∂σ := by
  haveI := measurableConstSMul_subgroup Γ'
  haveI := smulInvariantMeasure_subgroup Γ' μA
  haveI : Countable (orbitRel.Quotient Γ' S) := Quotient.countable
  rw [repMeasureOf, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  have hsplit : ∀ a : A, ∑' y : S, Φ (a⁻¹ • (y : Y)) =
      ∑' q : orbitRel.Quotient Γ' S, ∑' ξ : orbit Γ' q.out, Φ (a⁻¹ • ((ξ : S) : Y)) := fun a =>
    tsum_eq_tsum_orbits (fun y : S => Φ (a⁻¹ • (y : Y)))
  simp_rw [hsplit]
  rw [lintegral_tsum fun q => (Measurable.tsum fun ξ => hΦ _).aemeasurable]
  refine tsum_congr fun q => ?_
  -- one orbit: `lintegral_sphere_unfold` with `X` the orbit (transitive)
  set y₀ : Y := ((q.out : S) : Y) with hy₀
  haveI := 𝔉.sigmaFinite y₀
  haveI := 𝔉.leftInv y₀
  haveI : Countable (stabArith Γ' y₀) := by
    refine Function.Injective.countable (f := fun γ : stabArith Γ' y₀ => (⟨((γ : stabilizer A y₀) : A), γ.2⟩ : Γ'))
      fun γ γ' h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  haveI := measurableConstSMul_subgroupOf (stabilizer A y₀) (stabArith Γ' y₀)
  haveI := measurableMul_subgroup (stabilizer A y₀)
  haveI : SMulInvariantMeasure (stabArith Γ' y₀) (stabilizer A y₀) (𝔉.μH y₀) :=
    smulInvariantMeasure_subgroup _ _
  obtain ⟨DH, hDHm, hDHx⟩ := hDH y₀
  have hy₀P : y₀ ∈ P := hSP _ (q.out : S).2
  let j : orbit Γ' q.out → Y := fun ξ => ((ξ : S) : Y)
  have hj : ∀ (γ : Γ') (η : orbit Γ' q.out), j (γ • η) = (γ : A) • j η := fun _ _ => rfl
  let ξ₀ : orbit Γ' q.out := ⟨q.out, mem_orbit_self _⟩
  have htrans : ∀ η : orbit Γ' q.out, ∃ γ : Γ', γ • ξ₀ = η := by
    rintro ⟨η, γ, rfl⟩
    exact ⟨γ, rfl⟩
  have h := lintegral_sphere_unfold (μ := μA) (ΓH := stabArith Γ' y₀) (μH := 𝔉.μH y₀) j hj ξ₀ htrans
    (stabilizer A y₀).subtype σ τ (𝔉.coord y₀ hy₀P) (fun h hh => hh) (fun h hh => Subtype.ext (Subtype.ext h.2))
    (fun γ hγ => ⟨⟨γ, congrArg (fun z : orbit Γ' q.out => ((z : S) : Y)) hγ⟩, γ.2, rfl⟩)
    hDHm hDHx c (𝔉.fib y₀ hy₀P) hD' Φ hΦτ
  rw [← h]

end Orbits

/-! ### The β-decomposition of the theta integral -/

section Theta

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableMul A] [MeasurableMul B]
  {Γ : Subgroup (A × B)} {X : Type*} [MulAction Γ X]
  {Y : Type*} [MulAction A Y] {Yf : Type*} [MulAction B Yf]

/-- **The theta function of $\Phi\otimes1_\Lambda$**: for embeddings `jA : X → Y` (archimedean) and `jB : X → Yf`
(finite adelic) of the rational points `X`,
$$\theta(g) = \sum_{\eta\in X}\Phi(g_\infty^{-1}j_A\eta)\,1_\Lambda(g_f^{-1}j_B\eta)\in[0,\infty].$$
Parameters: `jA`, `jB`, `Φ`, `Λ`, `g`. -/
def thetaFn (jA : X → Y) (jB : X → Yf) (Φ : Y → ℝ≥0∞) (Λ : Set Yf) (g : A × B) : ℝ≥0∞ :=
  ∑' η : X, Φ (g.1⁻¹ • jA η) * Λ.indicator 1 (g.2⁻¹ • jB η)

/-- The theta function is left `Γ`-invariant. -/
theorem thetaFn_smul {jA : X → Y} {jB : X → Yf} (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η)
    (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η) (Φ : Y → ℝ≥0∞) (Λ : Set Yf) (γ : Γ) (g : A × B) :
    thetaFn jA jB Φ Λ (γ • g) = thetaFn jA jB Φ Λ g := by
  unfold thetaFn
  rw [← (MulAction.toPerm γ : Equiv.Perm X).tsum_eq]
  refine tsum_congr fun η => ?_
  simp only [MulAction.toPerm_apply, hjA, hjB, Subgroup.smul_def, smul_eq_mul, Prod.fst_mul, Prod.snd_mul,
    mul_inv_rev, mul_smul, inv_smul_smul]

/-- The theta function on the translate $D_i\times\beta_iK'$: there $1_\Lambda(g_f^{-1}y) = 1_{\beta_i\Lambda}(y)$. -/
theorem thetaFn_of_mem (jA : X → Y) (jB : X → Yf) (Φ : Y → ℝ≥0∞) {Λ : Set Yf} {K' : Subgroup B}
    (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ) (b : B) {g : A × B} (hg : g.2 ∈ b • (K' : Set B)) :
    thetaFn jA jB Φ Λ g = ∑' η : X, Φ (g.1⁻¹ • jA η) * (b • Λ).indicator 1 (jB η) := by
  obtain ⟨k, hk, hgk⟩ := hg
  have hgk' : g.2 = b * k := hgk.symm
  refine tsum_congr fun η => ?_
  congr 1
  have : g.2⁻¹ • jB η ∈ Λ ↔ jB η ∈ b • Λ := by
    rw [hgk', mul_inv_rev, mul_smul, hΛ _ (K'.inv_mem hk), Set.mem_smul_set_iff_inv_smul_mem]
  by_cases h : jB η ∈ b • Λ
  · rw [indicator_of_mem (this.mpr h), indicator_of_mem h]; rfl
  · rw [indicator_of_notMem (fun h' => h (this.mp h')), indicator_of_notMem h]

/-- **The β-decomposition of the theta integral** (Siegel's formula for indefinite forms, the classical
translation; Weil 1982, §2.4, p. 23 with the double cosets). Let `Γ ≤ A × B` be countable, `K' ≤ B`
measurable, `β : ι → B` exact representatives of the double cosets of `Γ_f` and `K'` in `B` (`hcov`, `hdisj`),
`Γ_i → A` injective (`hinjA`), `D_i` exact measurable fundamental domains of the `Γ_{β_i}` =
`levelGroup Γ K' (β i)` in `A`, and `Λ` a `K'`-stable set. Then for every fundamental domain `E` of `Γ` in `A × B`,
$$\int_E\theta\,d(\mu_A\times\mu_B) = \mu_B(K')\sum_i\int_{D_i}\sum_{\eta\in X}\Phi(a^{-1}j_A\eta)\,
  1_{\beta_i\Lambda}(j_B\eta)\,d\mu_A(a).$$ -/
@[kb "weil1982" "§2.4, p. 23 (double cosets G_k β_i K); Lemma 2.4.2, p. 26 (unfolding) [unverified page]"]
theorem lintegral_theta_beta [Countable Γ] [Countable X] (K' : Subgroup B) (hK' : MeasurableSet (K' : Set B))
    {ι : Type*} [Countable ι] (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (hinjA : ∀ i, ∀ γ ∈ levelStab Γ K' (β i), γ.1 = 1 → γ = 1)
    (D : ι → Set A) (hDm : ∀ i, MeasurableSet (D i))
    (hD : ∀ i (a : A), ∃! s : levelGroup Γ K' (β i), s • a ∈ D i)
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant] [μB.IsMulLeftInvariant]
    {jA : X → Y} {jB : X → Yf} (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η)
    (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η) (Φ : Y → ℝ≥0∞)
    (hΦ : ∀ η, Measurable fun a : A => Φ (a⁻¹ • jA η)) {Λ : Set Yf} (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ)
    {E : Set (A × B)} (hE : IsFundamentalDomain Γ E (μA.prod μB)) :
    ∫⁻ g in E, thetaFn jA jB Φ Λ g ∂μA.prod μB =
      μB K' * ∑' i, ∫⁻ a in D i, ∑' η : X, Φ (a⁻¹ • jA η) * (β i • Λ).indicator 1 (jB η) ∂μA := by
  haveI := measurableConstSMul_subgroup Γ
  haveI := smulInvariantMeasure_subgroup Γ (μA.prod μB)
  have hm : ∀ i, MeasurableSet (D i ×ˢ (β i • (K' : Set B))) := fun i => (hDm i).prod (hK'.const_smul (β i))
  have hdom : IsFundamentalDomain Γ (⋃ i, D i ×ˢ (β i • (K' : Set B))) (μA.prod μB) :=
    IsFundamentalDomain.mk' (MeasurableSet.iUnion hm).nullMeasurableSet
      (exists_unique_smul_mem_beta Γ K' β hcov hdisj hinjA D hD)
  have hdisjSet : Pairwise (Function.onFun Disjoint fun i => D i ×ˢ (β i • (K' : Set B))) := by
    intro i j hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨a, b⟩ ⟨-, k, hk, rfl⟩ ⟨-, k', hk', hb⟩
    exact hne (hdisj i j 1 Γ.one_mem k hk k' hk' (by simpa using hb.symm))
  rw [hE.setLIntegral_eq hdom _ (thetaFn_smul hjA hjB Φ Λ), lintegral_iUnion hm hdisjSet, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  set f : A → ℝ≥0∞ := fun a => ∑' η : X, Φ (a⁻¹ • jA η) * (β i • Λ).indicator 1 (jB η) with hf
  have hfm : Measurable f := Measurable.tsum fun η => (hΦ η).mul_const _
  rw [setLIntegral_congr_fun (hm i) (g := fun p => f p.1) fun p hp => thetaFn_of_mem jA jB Φ hΛ (β i) hp.2,
    ← Measure.prod_restrict]
  have h1 := lintegral_prod_mul (μ := μA.restrict (D i)) (ν := μB.restrict (β i • (K' : Set B))) hfm.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [mul_one] at h1
  rw [h1, lintegral_one, Measure.restrict_apply_univ, measure_smul, mul_comm]

/-- The level groups are countable when `Γ` is. -/
theorem countable_levelGroup [Countable Γ] (K' : Subgroup B) (b : B) : Countable (levelGroup Γ K' b) := by
  haveI : Countable (levelStab Γ K' b) :=
    Function.Injective.countable (f := fun γ : levelStab Γ K' b => (⟨γ.1, γ.2.1⟩ : Γ))
      fun γ γ' h => Subtype.ext (by simpa using congrArg Subtype.val h)
  refine Function.Surjective.countable (f := fun γ : levelStab Γ K' b =>
    (⟨(γ : A × B).1, Subgroup.mem_map_of_mem _ γ.2⟩ : levelGroup Γ K' b)) ?_
  rintro ⟨a, γ, hγ, rfl⟩
  exact ⟨⟨γ, hγ⟩, rfl⟩

/-- **The representations in the class of `b`**: $S_b = j_A(\{\eta\in X : j_B\eta\in b\Lambda\})$ (for `Λ` = $\hat L$
the vectors of value `m` of the lattice $M_b = b\hat L\cap V$, embedded in $V_\infty$), a set stable under the unit
group $\Gamma_b$ = `levelGroup Γ K' b`. Parameters: `jA`, `jB` with their equivariance (`hjA`, `hjB`), `Λ`, its
`K'`-stability (`hΛ`), `b`. -/
def repSet {jA : X → Y} {jB : X → Yf} (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η)
    (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η) {K' : Subgroup B} {Λ : Set Yf}
    (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ) (b : B) : SubMulAction (levelGroup Γ K' b) Y where
  carrier := jA '' {η | jB η ∈ b • Λ}
  smul_mem' := by
    rintro ⟨a, ha⟩ _ ⟨η, hη, rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨(⟨γ, hγ.1⟩ : Γ) • η, ?_, hjA _ η⟩
    obtain ⟨y, hy, hyη⟩ := hη
    have hk : b⁻¹ * γ.2 * b ∈ K' := hγ.2
    show jB _ ∈ b • Λ
    rw [hjB, Set.mem_smul_set_iff_inv_smul_mem]
    show b⁻¹ • γ.2 • jB η ∈ Λ
    rw [← hyη, smul_smul, smul_smul, hΛ _ hk]
    exact hy

theorem mem_repSet {jA : X → Y} {jB : X → Yf} (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η)
    (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η) {K' : Subgroup B} {Λ : Set Yf}
    (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ) (b : B) (y : Y) :
    y ∈ repSet hjA hjB hΛ b ↔ y ∈ jA '' {η | jB η ∈ b • Λ} := Iff.rfl

/-- The sum over `X` with the indicator of $b\Lambda$ is the sum over the representations $S_b$ (`jA` injective). -/
theorem tsum_indicator_eq_tsum_repSet {jA : X → Y} {jB : X → Yf}
    (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η) (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η)
    (hinj : Function.Injective jA) {K' : Subgroup B} {Λ : Set Yf} (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ) (b : B)
    (Φ : Y → ℝ≥0∞) (a : A) :
    ∑' η : X, Φ (a⁻¹ • jA η) * (b • Λ).indicator 1 (jB η) = ∑' y : repSet hjA hjB hΛ b, Φ (a⁻¹ • (y : Y)) := by
  have h1 : ∀ η, Φ (a⁻¹ • jA η) * (b • Λ).indicator 1 (jB η) =
      {η | jB η ∈ b • Λ}.indicator (fun η => Φ (a⁻¹ • jA η)) η := by
    intro η
    by_cases h : jB η ∈ b • Λ
    · rw [indicator_of_mem h, indicator_of_mem (show η ∈ {η | jB η ∈ b • Λ} from h), Pi.one_apply, mul_one]
    · rw [indicator_of_notMem h, indicator_of_notMem (show η ∉ {η | jB η ∈ b • Λ} from h), mul_zero]
  simp_rw [h1]
  rw [← tsum_subtype, ← tsum_image (fun y : Y => Φ (a⁻¹ • y)) hinj.injOn]
  rfl

/-- **The classical theta integral** (Siegel's formula for indefinite forms, the classical translation of the adelic
identity; Siegel 1936, Weil 1982 §2.4 and §4.5). Under the hypotheses of `lintegral_theta_beta`, if moreover `jA`
is injective with values in the quadric `P`, `𝔉` is an archimedean fibration over `P` (constant `c`), and every
arithmetic stabilizer $\Gamma_{\beta_i,y}$ has an exact measurable fundamental domain in $H_y$, then
$$\int_E\theta\,d(\mu_A\times\mu_B) = \mu_B(K')\cdot c\cdot\sum_i\rho_{\Gamma_{\beta_i}}(S_{\beta_i})\cdot
  \int_T\Phi(\tau x)\,d\sigma(x),$$
with $\rho_{\Gamma_{\beta_i}}(S_{\beta_i}) = \sum_{y\in\Gamma_{\beta_i}\backslash S_{\beta_i}}
\operatorname{vol}(\Gamma_{\beta_i,y}\backslash H_y)$ the measure of representations of the class $\beta_i$
(`repMeasureOf`, `repSet`). An identity in $[0,\infty]$; nothing is assumed about the covolume of `Γ`. -/
@[kb "siegel1936" "Indefinite quadratische Formen; measure of representations (Darstellungsmaß) [unverified]"]
theorem lintegral_theta_eq [Countable Γ] [Countable X] (K' : Subgroup B) (hK' : MeasurableSet (K' : Set B))
    {ι : Type*} [Countable ι] (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (hinjA : ∀ i, ∀ γ ∈ levelStab Γ K' (β i), γ.1 = 1 → γ = 1)
    (D : ι → Set A) (hDm : ∀ i, MeasurableSet (D i))
    (hD : ∀ i (a : A), ∃! s : levelGroup Γ K' (β i), s • a ∈ D i)
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant] [μB.IsMulLeftInvariant]
    {jA : X → Y} {jB : X → Yf} (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η)
    (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η) (hinj : Function.Injective jA)
    {Λ : Set Yf} (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ)
    {T : Type*} [MeasurableSpace T] {P : Set Y} {σ : Measure T} [SFinite σ] {τ : T → Y} {c : ℝ≥0∞}
    (𝔉 : ArchFibration μA P σ τ c) (hP : ∀ η, jA η ∈ P)
    (hDH : ∀ i, ∀ y : Y, ∃ DH : Set (stabilizer A y), MeasurableSet DH ∧
      ∀ h : stabilizer A y, ∃! γ : stabArith (levelGroup Γ K' (β i)) y, γ • h ∈ DH)
    (Φ : Y → ℝ≥0∞) (hΦ : ∀ y, Measurable fun a : A => Φ (a⁻¹ • y)) (hΦτ : Measurable fun x => Φ (τ x))
    {E : Set (A × B)} (hE : IsFundamentalDomain Γ E (μA.prod μB)) :
    ∫⁻ g in E, thetaFn jA jB Φ Λ g ∂μA.prod μB =
      μB K' * c * (∑' i, repMeasureOf (levelGroup Γ K' (β i)) (repSet hjA hjB hΛ (β i)) 𝔉.μH) *
        ∫⁻ x, Φ (τ x) ∂σ := by
  rw [lintegral_theta_beta K' hK' β hcov hdisj hinjA D hDm hD μA μB hjA hjB Φ (fun η => hΦ _) hΛ hE]
  have key : ∀ i, ∫⁻ a in D i, ∑' η : X, Φ (a⁻¹ • jA η) * (β i • Λ).indicator 1 (jB η) ∂μA =
      c * repMeasureOf (levelGroup Γ K' (β i)) (repSet hjA hjB hΛ (β i)) 𝔉.μH * ∫⁻ x, Φ (τ x) ∂σ := by
    intro i
    haveI := countable_levelGroup (Γ := Γ) K' (β i)
    haveI : Countable (repSet hjA hjB hΛ (β i)) :=
      ((Set.countable_range jA).mono (Set.image_subset_range _ _)).to_subtype
    haveI := measurableConstSMul_subgroup (levelGroup Γ K' (β i))
    haveI := smulInvariantMeasure_subgroup (levelGroup Γ K' (β i)) μA
    simp_rw [tsum_indicator_eq_tsum_repSet hjA hjB hinj hΛ (β i) Φ]
    exact lintegral_tsum_eq_repMeasure (levelGroup Γ K' (β i)) 𝔉 (repSet hjA hjB hΛ (β i))
      (fun y hy => by obtain ⟨η, -, rfl⟩ := hy; exact hP η) (hDH i)
      (IsFundamentalDomain.mk' (hDm i).nullMeasurableSet (hD i)) Φ hΦ hΦτ
  rw [tsum_congr key, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  ring

/-- **The mean-value identity** (classical form): under the hypotheses of `lintegral_theta_eq`, with
`v_i = covol(Γ_{β_i}\A)` the unit-group volumes,
$$\Big(\int_E\theta\Big)\cdot\sum_iv_i = \operatorname{covol}(\Gamma\backslash(A\times B))\cdot c\cdot
  \sum_i\rho_{\Gamma_{\beta_i}}(S_{\beta_i})\cdot\int_T\Phi\circ\tau\,d\sigma .$$
Once the covolume is known (finite and nonzero; for `Γ = G(F)` it is $\tau(G) = 2$ for the Tamagawa measure), this
is Siegel's mean value $\int\theta/\operatorname{covol} = c\,\sum_i\rho_i\big/\sum_iv_i\cdot\int\Phi\,d\sigma$. -/
@[kb "siegel1936" "Indefinite quadratische Formen; Hauptsatz in measure form [unverified]"]
theorem lintegral_theta_mul_tsum_covolume [Countable Γ] [Countable X] (K' : Subgroup B)
    (hK' : MeasurableSet (K' : Set B)) {ι : Type*} [Countable ι] (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (hinjA : ∀ i, ∀ γ ∈ levelStab Γ K' (β i), γ.1 = 1 → γ = 1)
    (D : ι → Set A) (hDm : ∀ i, MeasurableSet (D i))
    (hD : ∀ i (a : A), ∃! s : levelGroup Γ K' (β i), s • a ∈ D i)
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant] [μB.IsMulLeftInvariant]
    {jA : X → Y} {jB : X → Yf} (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η)
    (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η) (hinj : Function.Injective jA)
    {Λ : Set Yf} (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ)
    {T : Type*} [MeasurableSpace T] {P : Set Y} {σ : Measure T} [SFinite σ] {τ : T → Y} {c : ℝ≥0∞}
    (𝔉 : ArchFibration μA P σ τ c) (hP : ∀ η, jA η ∈ P)
    (hDH : ∀ i, ∀ y : Y, ∃ DH : Set (stabilizer A y), MeasurableSet DH ∧
      ∀ h : stabilizer A y, ∃! γ : stabArith (levelGroup Γ K' (β i)) y, γ • h ∈ DH)
    (Φ : Y → ℝ≥0∞) (hΦ : ∀ y, Measurable fun a : A => Φ (a⁻¹ • y)) (hΦτ : Measurable fun x => Φ (τ x))
    {E : Set (A × B)} (hE : IsFundamentalDomain Γ E (μA.prod μB)) :
    (∫⁻ g in E, thetaFn jA jB Φ Λ g ∂μA.prod μB) * ∑' i, covolume (levelGroup Γ K' (β i)) A μA =
      covolume Γ (A × B) (μA.prod μB) * c *
        (∑' i, repMeasureOf (levelGroup Γ K' (β i)) (repSet hjA hjB hΛ (β i)) 𝔉.μH) * ∫⁻ x, Φ (τ x) ∂σ := by
  haveI := fun i => countable_levelGroup (Γ := Γ) K' (β i)
  haveI := fun i => smulInvariantMeasure_subgroup (levelGroup Γ K' (β i)) μA
  haveI := fun i => measurableConstSMul_subgroup (levelGroup Γ K' (β i))
  rw [lintegral_theta_eq K' hK' β hcov hdisj hinjA D hDm hD μA μB hjA hjB hinj hΛ 𝔉 hP hDH Φ hΦ hΦτ hE,
    covolume_eq_measure_mul_tsum_covolume Γ K' hK' β hcov hdisj hinjA D hDm hD μA μB]
  ring

end Theta

end QuadFormsKB.Tamagawa.Indefinite
