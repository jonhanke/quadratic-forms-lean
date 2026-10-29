/-
# Hanke, AWS 2009 notes, §4.6: constructing the integral over $\Gamma\backslash G$

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §4.4, (4.3), and §4.6,
(4.4)–(4.11) (pp. 61–64). This file **constructs** the integral over $\Gamma\backslash G$ assumed by the
input `QuotientIntegralInputs` (`AWS/Unfolding.lean`) whenever $G$ has finitely many double cosets
$\Gamma\backslash G/K$ with finite stabilizers, which is the situation of the notes
($G = O(V_\mathbb{A})$, $\Gamma = O(V)$, $K = K_\mathbb{A}$, $Q$ positive definite).

**Setting.** A group $G$ with a measurable space structure for which translations are measurable
(`MeasurableMul G`), a left-invariant measure $\mu$, a countable subgroup $\Gamma$ and a subgroup $K$ with
$K$ measurable. Let $\alpha_i$ ($i \in I$, $I$ finite) be representatives of the double cosets
$\Gamma\alpha_iK$, with each $\Gamma_i := \Gamma \cap \alpha_iK\alpha_i^{-1}$ finite.

**Construction** (`dosetIntegral`): for $F : G \to \mathbb{C}$,
$$I(F) := \sum_{i \in I} \frac{1}{|\Gamma_i|}\int_K F(\alpha_i h)\,d\mu(h).$$

**Main result** (`weil_dosetIntegral`): $I$ satisfies **Weil's formula**: for every $\mu$-integrable
$f : G \to \mathbb{C}$,
$$I\Bigl(g \mapsto \sum_{\gamma \in \Gamma} f(\gamma g)\Bigr) = \int_G f\,d\mu .$$
Hence (`QuotientIntegralInputs.ofDoubleCosets`) the input `QuotientIntegralInputs Γ K μ` holds as soon as
$\mu(K) = 1$. Weil's formula characterizes the quotient integral on periodizations of integrable functions,
so this $I$ is the integral over $\Gamma\backslash G$ against the quotient of $\mu$ by counting measure on
$\Gamma$ (and, by the unfolding `integral_eq_sum_doset`, it does not depend on the choice of the
$\alpha_i$ on left-$\Gamma$-invariant functions integrable on each $\alpha_iK$).

**Proof idea.** $\int_K F(\alpha_ih)\,dh = \int_{\alpha_iK} F$ by left invariance; exchanging sum and
integral and translating by $\gamma^{-1}$,
$\int_{\alpha_iK}\sum_\gamma f(\gamma g)\,dg = \int_G \#\{\gamma : \gamma g \in \alpha_iK\}\,f(g)\,dg$,
and the count is $|\Gamma_i|$ on $\Gamma\alpha_iK$ and $0$ off it (`card_setOf_mul_mem`). Summing over the
disjoint double cosets gives $\int_G f$. Only left invariance of $\mu$ is used.
-/
import QuadFormsKB.Literature.AWS.Unfolding

open MeasureTheory
open scoped Pointwise ENNReal

namespace QuadFormsKB.AWS

variable {G : Type*} [Group G] [MeasurableSpace G] {Γ K : Subgroup G}

/-- **The integral over $\Gamma\backslash G$ from a double coset decomposition** (§4.6, (4.13)):
$$I(F) := \sum_{i \in I} \frac{1}{|\Gamma \cap \alpha_iK\alpha_i^{-1}|}\int_K F(\alpha_i h)\,d\mu(h),$$
for representatives $\alpha_i$ ($i \in I$, $I$ finite) of the double cosets $\Gamma\alpha_iK$. -/
noncomputable def dosetIntegral (Γ K : Subgroup G) (μ : Measure G) {ι : Type*} [Fintype ι]
    (α : ι → G) (F : G → ℂ) : ℂ :=
  ∑ i, ((Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ))⁻¹ * ∫ h in (K : Set G), F (α i * h) ∂μ

omit [MeasurableSpace G] in
/-- $g \in \Gamma\alpha K$ iff some $\gamma \in \Gamma$ has $\gamma g \in \alpha K$. -/
theorem mem_doubleCoset_iff_exists_mul_mem (α g : G) :
    g ∈ DoubleCoset.doubleCoset α Γ K ↔ ∃ γ : Γ, (γ : G) * g ∈ α • (K : Set G) := by
  constructor
  · intro hg
    obtain ⟨γ₀, hγ₀, k₀, hk₀, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    refine ⟨⟨γ₀⁻¹, Γ.inv_mem hγ₀⟩, Set.mem_smul_set.mpr ⟨k₀, hk₀, ?_⟩⟩
    simp only [smul_eq_mul]; group
  · rintro ⟨γ, hγ⟩
    by_contra hn
    have := setOf_mul_mem_eq_empty (Γ := Γ) (K := K) α g hn
    exact (Set.eq_empty_iff_forall_notMem.mp this) γ hγ

variable [MeasurableMul G]

/-- A double coset $\Gamma\alpha K$ of a countable $\Gamma$ and a measurable $K$ is measurable: it is
$\bigcup_{\gamma\in\Gamma}\gamma^{-1}\alpha K$. -/
theorem measurableSet_doubleCoset [Countable Γ] (hK : MeasurableSet (K : Set G)) (α : G) :
    MeasurableSet (DoubleCoset.doubleCoset α Γ K) := by
  have : DoubleCoset.doubleCoset α Γ K = ⋃ γ : Γ, (fun g => (γ : G) * g) ⁻¹' (α • (K : Set G)) := by
    ext g
    rw [mem_doubleCoset_iff_exists_mul_mem, Set.mem_iUnion]
    rfl
  rw [this]
  exact MeasurableSet.iUnion fun γ => measurable_const_mul _ (hK.const_smul α)

omit [MeasurableSpace G] [MeasurableMul G] in
/-- **The counting step** (proof of (4.9)–(4.11)): for $g \in G$ and a weight $a$,
$$\sum_{\gamma \in \Gamma} \mathbf 1_{\alpha K}(\gamma g)\,a = |\Gamma \cap \alpha K\alpha^{-1}|\cdot
\mathbf 1_{\Gamma\alpha K}(g)\,a,$$
provided $\Gamma\cap\alpha K\alpha^{-1}$ is finite. -/
theorem tsum_indicator_mul_mem (α g : G) (hfin : Finite (Γ ⊓ conjSub α K : Subgroup G)) (a : ℂ) :
    ∑' γ : Γ, ((fun x => (γ : G) * x) ⁻¹' (α • (K : Set G))).indicator (fun _ => a) g =
      (DoubleCoset.doubleCoset α Γ K).indicator
        (fun _ => (Nat.card (Γ ⊓ conjSub α K : Subgroup G) : ℂ) * a) g := by
  set S := {γ : Γ | (γ : G) * g ∈ α • (K : Set G)}
  have hpt : ∀ γ : Γ, ((fun x => (γ : G) * x) ⁻¹' (α • (K : Set G))).indicator (fun _ => a) g =
      S.indicator (fun _ => a) γ := by
    intro γ
    by_cases h : γ ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show g ∈ _ from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show g ∉ _ from h)]
  simp_rw [hpt]
  by_cases hg : g ∈ DoubleCoset.doubleCoset α Γ K
  · have hS : Nat.card S = Nat.card (Γ ⊓ conjSub α K : Subgroup G) := card_setOf_mul_mem α g hg
    have : Finite S := by
      apply Nat.finite_of_card_ne_zero
      rw [hS]
      exact Nat.card_pos.ne'
    rw [Set.indicator_of_mem hg, ← tsum_subtype S (fun _ => a), tsum_const, nsmul_eq_mul, hS]
  · have hS0 : S = ∅ := setOf_mul_mem_eq_empty α g hg
    rw [Set.indicator_of_notMem hg, hS0]
    simp

omit [MeasurableSpace G] [MeasurableMul G] in
/-- The `ℝ≥0∞` version of the counting step, as an upper bound. -/
theorem tsum_indicator_mul_mem_le (α g : G) (hfin : Finite (Γ ⊓ conjSub α K : Subgroup G))
    (a : ℝ≥0∞) :
    ∑' γ : Γ, ((fun x => (γ : G) * x) ⁻¹' (α • (K : Set G))).indicator (fun _ => a) g ≤
      (Nat.card (Γ ⊓ conjSub α K : Subgroup G) : ℝ≥0∞) * a := by
  set S := {γ : Γ | (γ : G) * g ∈ α • (K : Set G)}
  have hpt : ∀ γ : Γ, ((fun x => (γ : G) * x) ⁻¹' (α • (K : Set G))).indicator (fun _ => a) g =
      S.indicator (fun _ => a) γ := by
    intro γ
    by_cases h : γ ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show g ∈ _ from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show g ∉ _ from h)]
  simp_rw [hpt]
  rw [← tsum_subtype S (fun _ => a), ENNReal.tsum_set_const]
  gcongr
  by_cases hg : g ∈ DoubleCoset.doubleCoset α Γ K
  · have hS : Nat.card S = Nat.card (Γ ⊓ conjSub α K : Subgroup G) := card_setOf_mul_mem α g hg
    have : Finite S := by
      apply Nat.finite_of_card_ne_zero
      rw [hS]
      exact Nat.card_pos.ne'
    rw [Set.Finite.encard_eq_coe_toFinset_card (Set.toFinite S), ← hS, Nat.card_eq_card_finite_toFinset (Set.toFinite S)]
    simp
  · have hS0 : S = ∅ := setOf_mul_mem_eq_empty α g hg
    rw [hS0]
    simp

/-- **One double coset of Weil's formula**: for $\mu$ left-invariant and $f$ integrable,
$$\int_K \sum_{\gamma\in\Gamma} f(\gamma\alpha h)\,d\mu(h)
= |\Gamma\cap\alpha K\alpha^{-1}|\int_{\Gamma\alpha K} f\,d\mu .$$ -/
theorem setIntegral_tsum_mul_eq [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (α : G) (hfin : Finite (Γ ⊓ conjSub α K : Subgroup G))
    (f : G → ℂ) (hf : Integrable f μ) :
    ∫ h in (K : Set G), ∑' γ : Γ, f (γ * (α * h)) ∂μ =
      (Nat.card (Γ ⊓ conjSub α K : Subgroup G) : ℂ) *
        ∫ g in DoubleCoset.doubleCoset α Γ K, f g ∂μ := by
  set s : Set G := α • (K : Set G) with hs_def
  have hs : MeasurableSet s := hK.const_smul α
  set c : ℕ := Nat.card (Γ ⊓ conjSub α K : Subgroup G)
  -- ψ γ g = 1_s(g) f(γ g), χ γ g = 1_s(γ g) f(g)
  set ψ : Γ → G → ℂ := fun γ => s.indicator (fun g => f (γ * g)) with hψ
  set χ : Γ → G → ℂ := fun γ => ((fun x => (γ : G) * x) ⁻¹' s).indicator f with hχ
  have hsγ : ∀ γ : G, MeasurableSet ((fun x => γ * x) ⁻¹' s) := fun γ => measurable_const_mul γ hs
  have hψχ : ∀ γ : Γ, ∀ x, ψ γ ((γ : G)⁻¹ * x) = χ γ⁻¹ x := by
    intro γ x
    simp only [hψ, hχ, Set.indicator, Set.mem_preimage, Subgroup.coe_inv, mul_inv_cancel_left]
    rfl
  have hψ_meas : ∀ γ : Γ, AEStronglyMeasurable (ψ γ) μ := fun γ =>
    (hf.aestronglyMeasurable.comp_measurePreserving (measurePreserving_mul_left μ (γ : G))).indicator hs
  have hχ_meas : ∀ γ : Γ, AEStronglyMeasurable (χ γ) μ := fun γ =>
    hf.aestronglyMeasurable.indicator (hsγ γ)
  -- the ℝ≥0∞ bound
  have hχ_norm : ∀ γ : Γ, ∀ x, ‖χ γ x‖ₑ =
      ((fun y => (γ : G) * y) ⁻¹' s).indicator (fun _ => ‖f x‖ₑ) x := by
    intro γ x
    simp only [hχ, Set.indicator]
    split_ifs <;> simp
  have hχ_sum : ∑' γ : Γ, ∫⁻ x, ‖χ γ x‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_tsum fun γ => (hχ_meas γ).enorm]
    refine ne_top_of_le_ne_top (b := ∫⁻ x, (c : ℝ≥0∞) * ‖f x‖ₑ ∂μ) ?_ (lintegral_mono fun x => ?_)
    · rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top c)]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top c) hf.hasFiniteIntegral.ne
    · simp_rw [hχ_norm]
      exact tsum_indicator_mul_mem_le α x hfin _
  have hψ_lint : ∀ γ : Γ, ∫⁻ x, ‖ψ γ x‖ₑ ∂μ = ∫⁻ x, ‖χ γ⁻¹ x‖ₑ ∂μ := by
    intro γ
    rw [← lintegral_mul_left_eq_self (fun x => ‖ψ γ x‖ₑ) (γ : G)⁻¹]
    simp_rw [hψχ]
  have hψ_sum : ∑' γ : Γ, ∫⁻ x, ‖ψ γ x‖ₑ ∂μ ≠ ∞ := by
    simp_rw [hψ_lint]
    have e := (Equiv.inv Γ).tsum_eq (fun γ => ∫⁻ x, ‖χ γ x‖ₑ ∂μ)
    simp only [Equiv.inv_apply] at e
    rwa [e]
  -- the computation
  calc ∫ h in (K : Set G), ∑' γ : Γ, f (γ * (α * h)) ∂μ
      = ∫ g, s.indicator (fun g => ∑' γ : Γ, f (γ * g)) g ∂μ := by
        rw [← integral_indicator hK,
          ← integral_mul_left_eq_self (s.indicator (fun g => ∑' γ : Γ, f (γ * g))) α]
        congr 1
        funext h
        by_cases hh : h ∈ (K : Set G)
        · rw [Set.indicator_of_mem hh,
            Set.indicator_of_mem (show α * h ∈ s from Set.smul_mem_smul_set (a := α) hh)]
        · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem]
          intro hmem
          apply hh
          obtain ⟨k, hk, e⟩ := Set.mem_smul_set.mp hmem
          rw [smul_eq_mul, mul_left_cancel_iff] at e
          exact e ▸ hk
    _ = ∫ g, ∑' γ : Γ, ψ γ g ∂μ := by
        congr 1
        funext g
        by_cases hg : g ∈ s
        · simp only [hψ, Set.indicator_of_mem hg]
        · simp only [hψ, Set.indicator_of_notMem hg, tsum_zero]
    _ = ∑' γ : Γ, ∫ g, ψ γ g ∂μ := integral_tsum hψ_meas hψ_sum
    _ = ∑' γ : Γ, ∫ g, χ γ⁻¹ g ∂μ := by
        congr 1
        funext γ
        rw [← integral_mul_left_eq_self (ψ γ) (γ : G)⁻¹]
        simp_rw [hψχ]
    _ = ∑' γ : Γ, ∫ g, χ γ g ∂μ := by
        have e := (Equiv.inv Γ).tsum_eq (fun γ => ∫ g, χ γ g ∂μ)
        simp only [Equiv.inv_apply] at e
        exact e
    _ = ∫ g, ∑' γ : Γ, χ γ g ∂μ := (integral_tsum hχ_meas hχ_sum).symm
    _ = ∫ g, (DoubleCoset.doubleCoset α Γ K).indicator (fun g => (c : ℂ) * f g) g ∂μ := by
        congr 1
        funext g
        have hpt : ∀ γ : Γ, χ γ g =
            ((fun x => (γ : G) * x) ⁻¹' s).indicator (fun _ => f g) g := by
          intro γ
          simp only [hχ, Set.indicator]
        simp_rw [hpt]
        rw [tsum_indicator_mul_mem α g hfin]
        rfl
    _ = (c : ℂ) * ∫ g in DoubleCoset.doubleCoset α Γ K, f g ∂μ := by
        rw [integral_indicator (measurableSet_doubleCoset hK α), integral_const_mul]

/-- **Weil's formula for the double coset integral** (§4.6, (4.4)–(4.13), read backwards): with
$\mu$ left-invariant, $\Gamma$ countable, $K$ measurable, $G = \bigsqcup_{i\in I}\Gamma\alpha_iK$ ($I$ finite;
`hcov`, `hdisj`) and each $\Gamma\cap\alpha_iK\alpha_i^{-1}$ finite (`hfin`), for every $\mu$-integrable $f$,
$$\sum_{i\in I}\frac{1}{|\Gamma\cap\alpha_iK\alpha_i^{-1}|}\int_K\sum_{\gamma\in\Gamma}f(\gamma\alpha_ih)\,d\mu(h)
= \int_G f\,d\mu .$$ -/
@[kb "hanke2011aws" "§4.6, (4.4)-(4.13), pp. 63-64"]
theorem weil_dosetIntegral [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G))
    (f : G → ℂ) (hf : Integrable f μ) :
    dosetIntegral Γ K μ α (fun g => ∑' γ : Γ, f (γ * g)) = ∫ g, f g ∂μ := by
  classical
  -- uniqueness of the double coset of g
  have huniq : ∀ g i j, g ∈ DoubleCoset.doubleCoset (α i) Γ K →
      g ∈ DoubleCoset.doubleCoset (α j) Γ K → i = j := by
    intro g i j hi hj
    apply hdisj
    exact (DoubleCoset.mk_eq_of_doubleCoset_eq (DoubleCoset.doubleCoset_eq_of_mem hi)).symm.trans
      (DoubleCoset.mk_eq_of_doubleCoset_eq (DoubleCoset.doubleCoset_eq_of_mem hj))
  have hpart : ∀ g, ∑ i, (DoubleCoset.doubleCoset (α i) Γ K).indicator f g = f g := by
    intro g
    obtain ⟨i₀, hi₀⟩ := hcov g
    rw [Finset.sum_eq_single i₀, Set.indicator_of_mem hi₀]
    · intro j _ hj
      exact Set.indicator_of_notMem (fun h => hj (huniq g j i₀ h hi₀)) _
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold dosetIntegral
  simp_rw [setIntegral_tsum_mul_eq hK _ (hfin _) f hf]
  calc ∑ i, ((Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ))⁻¹ *
        ((Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ) *
          ∫ g in DoubleCoset.doubleCoset (α i) Γ K, f g ∂μ)
      = ∑ i, ∫ g, (DoubleCoset.doubleCoset (α i) Γ K).indicator f g ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hfin i
        have hpos : (Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        rw [← mul_assoc, inv_mul_cancel₀ hpos, one_mul,
          integral_indicator (measurableSet_doubleCoset hK _)]
    _ = ∫ g, ∑ i, (DoubleCoset.doubleCoset (α i) Γ K).indicator f g ∂μ :=
        (integral_finsetSum _ fun i _ =>
          hf.indicator (measurableSet_doubleCoset hK _)).symm
    _ = ∫ g, f g ∂μ := by simp_rw [hpart]

/-- **Discharge of `QuotientIntegralInputs`** from a finite double coset decomposition: if $\mu$ is
left-invariant, $\Gamma$ is countable, $K$ is measurable with $\mu(K) = 1$, and
$G = \bigsqcup_{i\in I}\Gamma\alpha_iK$ ($I$ finite) with every $\Gamma\cap\alpha_iK\alpha_i^{-1}$ finite, then
`dosetIntegral Γ K μ α` is an integral over $\Gamma\backslash G$ satisfying Weil's formula. -/
noncomputable def QuotientIntegralInputs.ofDoubleCosets [Countable Γ] {μ : Measure G}
    (hμ : μ.IsMulLeftInvariant) (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1)
    {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G)) :
    QuotientIntegralInputs Γ K μ where
  I := dosetIntegral Γ K μ α
  weil f hf := weil_dosetIntegral hK α hcov hdisj hfin f hf
  left_invariant := hμ
  measurableSet_K := hK
  measure_K := hK1

end QuadFormsKB.AWS
