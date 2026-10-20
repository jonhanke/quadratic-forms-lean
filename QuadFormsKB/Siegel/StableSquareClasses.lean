/-
# The finite set $B_{\mathbb T}$ and the minimum over it in Theorem 5.7

**Layer:** number field (and ℚ, at the end). Hanke 2004, p. 372: by Remark 3.6.1 there is an ideal $\mathfrak s$ such that every
locally represented $m$ with $m_\mathfrak p \in \mathfrak s_\mathfrak p$ is stable; choosing representatives one gets a **finite** set
$B_{\mathbb T}$ of $T'$ such that every locally represented $m$ is $T'(m')^2$ with $T' \in B_{\mathbb T}$ and $m'$ supported on
$\mathrm{Stable}(T')$; the constants of Theorem 5.7 are minima over $T' \in B_{\mathbb T}$ of quantities depending on $T'$ only
through its classes at the bad primes.

**Formalization.**
* The stable ideal: `LocalDensity.NF.isStable_of_dvd` (every locally represented $m \in 8\det(H)\mathcal O_F$ is
  $\mathfrak p$-stable at every $\mathfrak p$), from `NFDepth.lean`.
* $B_{\mathbb T}$ is modelled by the **bad-reduced** $T'$ (`IsBadReducedNF`): $T' \notin \mathfrak p^{K_0(\mathfrak p)+2}$ at every bad
  $\mathfrak p \mid 2\det H$, $K_0 = \mathrm{ord}_\mathfrak p(4N) + 1$ (`NF.depthLevel`). Pushing square factors into $m'$ until this holds
  leaves $T' \in \mathfrak p^{K_0}$ at the bad $\mathfrak p \mid m'$, where $T'$ is $\mathfrak p$-stable and locally represented iff $m$ is
  (`NF.isPStable_of_mem`, `NF.isLocallyRepresentedAt_pow_mul_iff`).
* **Finiteness** (`finite_badFactorNF_image`): the bad local factor $\Lambda(T') = \prod_{\mathfrak p \mid 2\det H}\beta_\mathfrak p(T')
  \prod_{\mathfrak p \mid 2\det H,\ \mathfrak p \in \mathrm{Iso}}C'_\mathfrak p(T')$ (`badFactorNF`) takes only finitely many values on
  bad-reduced $T'$, because $\beta_\mathfrak p$ and $C'_\mathfrak p$ are locally constant (`NF.localDensity_congr`) and $T'$ ranges over
  finitely many classes mod $\prod_\mathfrak p\mathfrak p^{2K_0 + 1}$.
* **The minimum** (`minBadFactorNF`, `minBadFactorNF_le`, `exists_eq_minBadFactorNF`, `minBadFactorNF_pos`): over any
  nonempty set $\mathcal T$ of bad-reduced $T'$ the minimum of $\Lambda$ exists and is attained.
* **Theorem 5.7 with the minimum over $B_{\mathbb T}$** (`thm_5_7_b_global_min_NF`, `thm_5_7_c_global_min_NF`): the global
  forms with $\Lambda(T')$ replaced by $\min_{\mathcal T}\Lambda$, uniformly in $T' \in \mathcal T$.
* Over ℚ (`IsBadReduced`, `badFactor`, `finite_badFactor_image`, `minBadFactor`, `lambdaHat4Min`, `hglob_four_min`): the
  same for $\hat\Lambda_4$ of Thm 5.7(b) (`lambdaHat4`), the constant used by Theorem 6.3, and the decomposition
  $m = T'x^2$ (`exists_badReduced_decomp`).

**Depends on** `NFGlobalLowerBound.lean`, `GlobalLowerBound.lean`, `LocalDensity/NFDepth.lean`.
-/
import QuadFormsKB.Siegel.NFGlobalLowerBound
import QuadFormsKB.Siegel.GlobalLowerBound
import QuadFormsKB.LocalDensity.NFDepth

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open LocalDensity NFEuler Classical

/-- A product of factors in $[0, 1]$ over a larger set is smaller. -/
theorem prod_le_prod_of_subset_unitInterval {ι : Type*} {s t : Finset ι} (hst : s ⊆ t) (f : ι → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  rw [← Finset.prod_sdiff hst]
  refine mul_le_of_le_one_left (Finset.prod_nonneg fun i hi => h0 i (hst hi)) ?_
  exact Finset.prod_le_one₀ (fun i hi => h0 i (Finset.sdiff_subset hi))
    fun i hi => h1 i (Finset.sdiff_subset hi)

/-! ### Over a number field -/

section NF

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "N𝔭" v => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)

/-- **Bad-reduced** $T'$ (the shape of the elements of $B_{\mathbb T}$, Hanke 2004, p. 372): at every bad prime
$\mathfrak p \mid 2\det H$, $T' \notin \mathfrak p^{K_0(\mathfrak p) + 2}$, with $K_0 = \mathrm{ord}_\mathfrak p(4N) + 1$ (`NF.depthLevel`). -/
def IsBadReducedNF (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) : Prop :=
  ∀ v ∈ badPrimesNF Q, T ∉ v.asIdeal ^ (NF.depthLevel v Q + 2)

/-- **The bad local factor** $\Lambda(T') = \prod_{\mathfrak p \mid 2\det H}\beta_\mathfrak p(T')\prod_{\mathfrak p \mid 2\det H,\ \mathfrak p \in
\mathrm{Iso}}C'_\mathfrak p(T')$: the part of the constants $\hat b_4$, $\hat b_n$ of Theorem 5.7 (Hanke 2004, p. 373) that depends on
$T'$ through its classes at the bad primes (the products over $\mathfrak p \mid N$). -/
def badFactorNF (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) : ℝ :=
  (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
    ∏ v ∈ (badPrimesNF Q).filter (IsIsotropicNF Q), NF.localConstC' v Q T

/-- **$\Lambda$ is locally constant on bad-reduced $T'$**: if $T'$ is bad-reduced and $T' \equiv T'' \pmod{\mathfrak p^{2K_0+1}}$ at every
bad $\mathfrak p$, then $\Lambda(T') = \Lambda(T'')$. -/
theorem badFactorNF_congr (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {T T' : 𝓞 F}
    (hT : IsBadReducedNF Q T)
    (h : ∀ v ∈ badPrimesNF Q, T - T' ∈ v.asIdeal ^ (2 * NF.depthLevel v Q + 1)) :
    badFactorNF Q T = badFactorNF Q T' := by
  have hc : ∀ v ∈ badPrimesNF Q, NF.localDensity v Q T = NF.localDensity v Q T' ∧
      NF.localConstC' v Q T = NF.localConstC' v Q T' := by
    intro v hv
    refine NF.localDensity_congr v Q hQ (a := NF.depthLevel v Q + 1) ?_ ?_
    · rw [show NF.depthLevel v Q + 1 + 1 = NF.depthLevel v Q + 2 by ring]; exact hT v hv
    · rw [show NF.depthLevel v Q + 1 + NF.depthLevel v Q = 2 * NF.depthLevel v Q + 1 by ring]; exact h v hv
  unfold badFactorNF
  rw [Finset.prod_congr rfl fun v hv => (hc v hv).1,
    Finset.prod_congr rfl fun v hv => (hc v (Finset.mem_filter.1 hv).1).2]

/-- **$B_{\mathbb T}$ is finite** (Hanke 2004, p. 372), in the form used by Theorem 5.7: on any set $S$ of bad-reduced $T'$, the bad
local factor $\Lambda$ takes only finitely many values. -/
@[kb "hanke2004" "p. 372 (B_T finite)"]
theorem finite_badFactorNF_image (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (S : Set (𝓞 F))
    (hS : ∀ T ∈ S, IsBadReducedNF Q T) : (badFactorNF Q '' S).Finite := by
  let M : HeightOneSpectrum (𝓞 F) → ℕ := fun v => 2 * NF.depthLevel v Q + 1
  let C := ∀ v : badPrimesNF Q, 𝓞 F ⧸ v.1.asIdeal ^ M v.1
  have hfin : Finite C := by
    have : ∀ v : badPrimesNF Q, Finite (𝓞 F ⧸ v.1.asIdeal ^ M v.1) := fun v =>
      Ring.HasFiniteQuotients.instFiniteQuotientIdealOfNeZero
    exact Pi.finite
  let ρ : 𝓞 F → C := fun T v => Ideal.Quotient.mk _ T
  let g : C → ℝ := fun c => if h : ∃ T ∈ S, ρ T = c then badFactorNF Q h.choose else 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨T, hT, rfl⟩
  have hex : ∃ T' ∈ S, ρ T' = ρ T := ⟨T, hT, rfl⟩
  refine ⟨ρ T, ?_⟩
  simp only [g]
  rw [dif_pos hex]
  obtain ⟨hT₁, hρ⟩ := hex.choose_spec
  symm
  refine badFactorNF_congr Q hQ (hS T hT) fun v hv => ?_
  have := congrFun hρ ⟨v, hv⟩
  simp only [ρ] at this
  rw [← Ideal.Quotient.eq]
  exact this.symm

/-- **The minimum of $\Lambda$ over a set $\mathcal T$ of bad-reduced $T'$** ("$\min_{T' \in B_{\mathbb T}}$" in Theorem 5.7(a)–(c),
Hanke 2004, pp. 372–373). Well defined by `finite_badFactorNF_image`: it is a value of $\Lambda$ (`exists_eq_minBadFactorNF`) and a
lower bound for every value (`minBadFactorNF_le`). -/
@[kb "hanke2004" "Thm 5.7, pp. 372–373 (min over B_T)"]
def minBadFactorNF (Q : QuadForm (𝓞 F) n) (𝒯 : Set (𝓞 F)) : ℝ := sInf (badFactorNF Q '' 𝒯)

theorem minBadFactorNF_le (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {𝒯 : Set (𝓞 F)}
    (h𝒯 : ∀ T ∈ 𝒯, IsBadReducedNF Q T) {T : 𝓞 F} (hT : T ∈ 𝒯) :
    minBadFactorNF Q 𝒯 ≤ badFactorNF Q T :=
  csInf_le (finite_badFactorNF_image Q hQ 𝒯 h𝒯).bddBelow ⟨T, hT, rfl⟩

/-- **The minimum over $B_{\mathbb T}$ is attained.** -/
theorem exists_eq_minBadFactorNF (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {𝒯 : Set (𝓞 F)}
    (h𝒯 : ∀ T ∈ 𝒯, IsBadReducedNF Q T) (hne : 𝒯.Nonempty) :
    ∃ T₀ ∈ 𝒯, minBadFactorNF Q 𝒯 = badFactorNF Q T₀ := by
  obtain ⟨T₀, hT₀, h⟩ := (hne.image _).csInf_mem (finite_badFactorNF_image Q hQ 𝒯 h𝒯)
  exact ⟨T₀, hT₀, h.symm⟩

/-- **The minimum over $B_{\mathbb T}$ is positive** when every $\Lambda(T')$, $T' \in \mathcal T$, is. -/
theorem minBadFactorNF_pos (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {𝒯 : Set (𝓞 F)}
    (h𝒯 : ∀ T ∈ 𝒯, IsBadReducedNF Q T) (hne : 𝒯.Nonempty) (hpos : ∀ T ∈ 𝒯, 0 < badFactorNF Q T) :
    0 < minBadFactorNF Q 𝒯 := by
  obtain ⟨T₀, hT₀, h⟩ := exists_eq_minBadFactorNF Q hQ h𝒯 hne
  rw [h]; exact hpos T₀ hT₀

/-- $\Lambda(T') \le \prod_{\mathfrak p \mid 2\det H}\beta_\mathfrak p(T')\prod_{\mathfrak p \in S \cap \mathrm{Iso},\ \mathfrak p\ \mathrm{bad}}C'_\mathfrak p(T')$
($C' \in [0, 1]$; the product over all bad isotropic $\mathfrak p$ is the uniform choice). -/
theorem badFactorNF_le (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {T : 𝓞 F} (hT0 : T ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    badFactorNF Q T ≤ (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
      ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v), NF.localConstC' v Q T := by
  unfold badFactorNF
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => localDensityNF_nonneg v Q hQ hT0)
  refine prod_le_prod_of_subset_unitInterval ?_ _ (fun v _ => localConstC'NF_nonneg v Q hQ hn hT0)
    (fun v _ => min_le_left _ _)
  intro v hv
  simp only [Finset.mem_filter] at hv ⊢
  exact ⟨(mem_badPrimesNF hQ).2 hv.2, hv.1.2⟩

/-- **Theorem 5.7(b) over $F$ with the minimum over $B_{\mathbb T}$** (Hanke 2004, p. 373): under the hypotheses of
`thm_5_7_b_global_NF`, for every $T'$ in a set $\mathcal T$ of bad-reduced elements,
$$a_E(T'x^2) \ge (6/\pi^2)^d\,\beta_\infty(T')\,\min_{\mathcal T}\Lambda\;N\big((x)_{\mathrm{Iso}}\big)^2
  \prod_{\substack{\mathfrak p \mid T'\ \mathrm{good}\\ \chi(\mathfrak p) = -1}}\frac{N\mathfrak p - 1}{N\mathfrak p + 1}
  \prod_{\substack{\mathfrak p \in S\ \mathrm{good},\ \mathfrak p \nmid T'\\ \chi(\mathfrak p) = -1}}\Big(1 + \frac1{N\mathfrak p}\Big)^{-1}.$$
The constant $(6/\pi^2)^d\min_{\mathcal T}\Lambda$ is uniform in $T' \in \mathcal T$ (Hanke's $\hat b_4$, with $\beta_\infty(T') =
c_\infty N(T')$ by `betaInfNF_eq_norm`). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (min over B_T, over F)"]
theorem thm_5_7_b_global_min_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) 4) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v) {𝒯 : Set (𝓞 F)}
    (h𝒯 : ∀ T ∈ 𝒯, IsBadReducedNF Q T) {T : 𝓞 F} (hT𝒯 : T ∈ 𝒯)
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) * minBadFactorNF Q 𝒯 *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal),
          (1 + 1 / (N𝔭 v))⁻¹ ≤
      aENF Q (T * x ^ 2) := by
  refine le_trans ?_ (thm_5_7_b_global_NF Q hQ hQnd hshape hT0 hT hx hS hst hT2)
  have hm := (minBadFactorNF_le Q hQnd h𝒯 hT𝒯).trans (badFactorNF_le Q hQnd (by norm_num) hT0 S)
  have hA : 0 ≤ (6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F) :=
    mul_nonneg (by positivity) (betaInfNF_nonneg hQ hT)
  have hN : 0 ≤ (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 := by positivity
  have hP : 0 ≤ ∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
      ((N𝔭 v) - 1) / ((N𝔭 v) + 1) := Finset.prod_nonneg fun v _ => by
    have := two_le_normP_real v
    exact div_nonneg (by linarith) (by linarith)
  have hI : 0 ≤ ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
      (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹ := by positivity
  calc _ = ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F)) * minBadFactorNF Q 𝒯 *
        ((∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹) := by ring
    _ ≤ ((6 / Real.pi ^ 2) ^ Module.finrank ℚ F * betaInfNF Q (T : F)) *
        ((∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
          ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v), NF.localConstC' v Q T) *
        ((∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ 2 *
        (∏ v ∈ (primesDividing T \ badPrimesNF Q).filter (fun v => charNF v Q.hessian.det = -1),
          ((N𝔭 v) - 1) / ((N𝔭 v) + 1)) *
        ∏ v ∈ (S.filter (IsGoodPrimeNF Q)).filter
            (fun v => charNF v Q.hessian.det = -1 ∧ T ∉ v.asIdeal), (1 + 1 / (N𝔭 v))⁻¹) := by
          gcongr
    _ = _ := by ring

/-- **Theorem 5.7(c) over $F$ with the minimum over $B_{\mathbb T}$**, $n \ge 5$ (Hanke 2004, p. 373): under the hypotheses of
`thm_5_7_c_global_NF`, for every $T'$ in a set $\mathcal T$ of bad-reduced elements,
$$a_E(T'x^2) \ge (6/\pi^2)^{2d}\,\beta_\infty(T')\prod_{\mathfrak p \mid T',\ \mathfrak p\ \mathrm{good}}\beta_\mathfrak p(T')\;
  N\big((x)_{\mathrm{Iso}}\big)^{n-2}\,\min_{\mathcal T}\Lambda,$$
with $\min_{\mathcal T}\Lambda$ uniform in $T'$ (Hanke's $\min_{T' \in B_{\mathbb T}}\hat B_n(T')$). -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (min over B_T, over F)"]
theorem thm_5_7_c_global_min_NF [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef Q)
    (hQnd : Q.Nondegenerate) (hn : 5 ≤ n) (hshape : ∀ v, IsGoodPrimeNF Q v → GoodPrimeShape Q v)
    {𝒯 : Set (𝓞 F)} (h𝒯 : ∀ T ∈ 𝒯, IsBadReducedNF Q T) {T : 𝓞 F} (hT𝒯 : T ∈ 𝒯)
    (hT0 : T ≠ 0) (hT : ∀ w : RealPlace F, 0 ≤ realEmb w T) {x : 𝓞 F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, x ∉ v.asIdeal)
    (hst : ∀ v ∈ S, NF.IsPStable v Q T) (hT2 : ∀ v ∈ S, IsGoodPrimeNF Q v → T ∉ v.asIdeal ^ 2) :
    (6 / Real.pi ^ 2) ^ (2 * Module.finrank ℚ F) * betaInfNF Q (T : F) *
        (∏ v ∈ primesDividing T \ badPrimesNF Q, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) * minBadFactorNF Q 𝒯 ≤
      aENF Q (T * x ^ 2) := by
  refine le_trans ?_ (thm_5_7_c_global_NF Q hQ hQnd hn hshape hT0 hT hx hS hst hT2)
  have hm := (minBadFactorNF_le Q hQnd h𝒯 hT𝒯).trans (badFactorNF_le Q hQnd (by omega) hT0 S)
  have hsplit : ∏ v ∈ badPrimesNF Q ∪ primesDividing T, NF.localDensity v Q T =
      (∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
        ∏ v ∈ primesDividing T \ badPrimesNF Q, NF.localDensity v Q T := by
    rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  have hA : 0 ≤ (6 / Real.pi ^ 2) ^ (2 * Module.finrank ℚ F) * betaInfNF Q (T : F) *
      (∏ v ∈ primesDividing T \ badPrimesNF Q, NF.localDensity v Q T) *
      (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (betaInfNF_nonneg hQ hT))
      (Finset.prod_nonneg fun v _ => localDensityNF_nonneg v Q hQnd hT0)) (by positivity)
  calc _ ≤ (6 / Real.pi ^ 2) ^ (2 * Module.finrank ℚ F) * betaInfNF Q (T : F) *
        (∏ v ∈ primesDividing T \ badPrimesNF Q, NF.localDensity v Q T) *
        (∏ v ∈ S.filter (IsIsotropicNF Q), (N𝔭 v) ^ ordNF v x) ^ (n - 2) *
        ((∏ v ∈ badPrimesNF Q, NF.localDensity v Q T) *
          ∏ v ∈ (S.filter (IsIsotropicNF Q)).filter (fun v => ¬ IsGoodPrimeNF Q v),
            NF.localConstC' v Q T) := mul_le_mul_of_nonneg_left hm hA
    _ = _ := by rw [hsplit]; ring

end NF

/-! ### Over $\mathbb{Q}$ -/

section Rat

variable {n : ℕ}

/-- $K_0(p) = \mathrm{ord}_p(4N) + 1$ for every natural $p$ (`depthLevelP` at primes, $0$ otherwise). -/
def depthLevelQ (Q : QuadForm ℤ n) (p : ℕ) : ℕ :=
  if h : p.Prime then @depthLevelP n Q p ⟨h⟩ else 0

theorem depthLevelQ_eq (Q : QuadForm ℤ n) (p : ℕ) [hp : Fact p.Prime] : depthLevelQ Q p = depthLevelP Q p := by
  rw [depthLevelQ, dif_pos hp.out]

theorem one_le_depthLevelQ (Q : QuadForm ℤ n) {p : ℕ} (hp : p.Prime) : 1 ≤ depthLevelQ Q p := by
  have := Fact.mk hp
  rw [depthLevelQ_eq, depthLevelP, DVR.depthLevel]; omega

/-- **Good primes are isotropic** for $n \ge 3$ (Hanke 2004, Remark 3.8.1, p. 364, over $\mathbb{Q}$; from
`DVR.isotropicIn_of_isLocalLevel_zero` at $\mathbb{Z}_p$). -/
theorem isIsotropicPrime_of_isGoodPrime (Q : QuadForm ℤ n) (hn : 3 ≤ n) {p : ℕ} (hG : IsGoodPrime Q p) :
    IsIsotropicPrime Q p := by
  obtain ⟨hp, h2, hdet⟩ := hG
  have := Fact.mk hp
  rw [isIsotropicPrime_iff, isotropicIn_iff_padic]
  letI : Fintype (IsLocalRing.ResidueField ℤ_[p]) := Fintype.ofFinite _
  have hπ2 : ¬ (p : ℤ_[p]) ∣ 2 := by
    have := (padicInt_pow_dvd_two p).2
    simpa [h2] using this
  have hdet' : ¬ (p : ℤ_[p]) ∣ (Q.map (Int.castRingHom ℤ_[p])).hessian.det := by
    rw [det_map_padic]
    intro h
    exact hdet (by simpa using (padic_pow_dvd_int_iff p 1 _).1 (by simpa using h))
  exact DVR.isotropicIn_of_isLocalLevel_zero ℚ_[p] _ PadicInt.irreducible_p (padic_two_ne_zero p)
    ((DVR.isLocalLevel_zero_iff PadicInt.irreducible_p hπ2).2 hdet') hn

/-- **The anisotropic part is supported on the bad primes** ($n \ge 3$): $(T)_{\mathrm{Aniso}} = \prod_{p \mid 2\det H,\ p \notin \mathrm{Iso}}
p^{\mathrm{ord}_p T}$. -/
theorem anisoPart_eq_prod_bad (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {T : ℕ} (hT : T ≠ 0) :
    anisoPart Q T = ∏ p ∈ (badPrimes Q).filter (fun p => ¬ IsIsotropicPrime Q p), p ^ T.factorization p := by
  let g : ℕ → ℕ := fun p => if IsIsotropicPrime Q p then 1 else p ^ T.factorization p
  have h1 : anisoPart Q T = ∏ p ∈ T.primeFactors ∪ badPrimes Q, g p := by
    rw [anisoPart, Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_subset Finset.subset_union_left fun p _ hp => ?_
    have : T.factorization p = 0 := Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])
    simp [this]
  have h2 : ∏ p ∈ (badPrimes Q).filter (fun p => ¬ IsIsotropicPrime Q p), p ^ T.factorization p =
      ∏ p ∈ T.primeFactors ∪ badPrimes Q, g p := by
    rw [Finset.prod_filter]
    calc ∏ p ∈ badPrimes Q, (if ¬ IsIsotropicPrime Q p then p ^ T.factorization p else 1)
        = ∏ p ∈ badPrimes Q, g p := Finset.prod_congr rfl fun p _ => by
          by_cases h : IsIsotropicPrime Q p <;> simp [g, h]
      _ = ∏ p ∈ T.primeFactors ∪ badPrimes Q, g p := by
          refine Finset.prod_subset Finset.subset_union_right fun p hp hpb => ?_
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors
            ((Finset.mem_union.1 hp).resolve_right hpb)
          have hG : IsGoodPrime Q p := by
            by_contra h; exact hpb ((mem_badPrimes hQ).2 ⟨hpp, h⟩)
          simp [g, isIsotropicPrime_of_isGoodPrime Q hn hG]
  rw [h1, h2]

/-- **Bad-reduced** positive integers $T'$ (the shape of $B_{\mathbb T}$ over $\mathbb{Q}$): $p^{K_0(p) + 2} \nmid T'$ at every $p \mid 2\det H$. -/
def IsBadReduced (Q : QuadForm ℤ n) (T : ℕ) : Prop :=
  ∀ p ∈ badPrimes Q, ¬ (p : ℤ) ^ (depthLevelQ Q p + 2) ∣ (T : ℤ)

/-- **The bad local factor over $\mathbb{Q}$**: $\Lambda(T') = (T')_{\mathrm{Aniso}}\prod_{p \mid 2\det H}\beta_p(T')
\prod_{p \mid 2\det H,\ p \in \mathrm{Iso}}C'_p(T')$, the $T'$-dependent part of $\hat\Lambda_4$ (`lambdaHat4`). -/
def badFactor (Q : QuadForm ℤ n) (T : ℕ) : ℝ :=
  (anisoPart Q T : ℝ) * (∏ p ∈ badPrimes Q, localDensity Q p T) *
    ∏ p ∈ (badPrimes Q).filter (IsIsotropicPrime Q), localConstC' Q p T

/-- Equal $p$-adic orders at a bad prime for congruent bad-reduced values. -/
theorem factorization_eq_of_congr (Q : QuadForm ℤ n) {T T' : ℕ} (hT0 : T ≠ 0) (hT0' : T' ≠ 0) {p : ℕ}
    (hp : p.Prime) (hT : ¬ (p : ℤ) ^ (depthLevelQ Q p + 2) ∣ (T : ℤ))
    (h : (p : ℤ) ^ (2 * depthLevelQ Q p + 1) ∣ (T : ℤ) - T') : T.factorization p = T'.factorization p := by
  set K := depthLevelQ Q p
  have hK := one_le_depthLevelQ Q hp
  have hdvd : ∀ k, k ≤ 2 * K + 1 → ((p : ℤ) ^ k ∣ T ↔ (p : ℤ) ^ k ∣ T') := by
    intro k hk
    have hk' := (pow_dvd_pow (p : ℤ) hk).trans h
    constructor
    · intro hT1; have := dvd_sub hT1 hk'; rwa [sub_sub_cancel] at this
    · intro hT1; have := dvd_add hk' hT1; rwa [sub_add_cancel] at this
  have hnat : ∀ (k : ℕ) (U : ℕ), U ≠ 0 → ((p : ℤ) ^ k ∣ (U : ℤ) ↔ k ≤ U.factorization p) := by
    intro k U hU
    rw [← hp.pow_dvd_iff_le_factorization hU]; exact_mod_cast Iff.rfl
  have hle : T.factorization p ≤ K + 1 := by
    by_contra hc; exact hT ((hnat _ T hT0).2 (by omega))
  have hle' : T'.factorization p ≤ K + 1 := by
    by_contra hc
    exact hT ((hdvd _ (by omega)).2 ((hnat _ T' hT0').2 (by omega)))
  apply le_antisymm
  · exact (hnat _ T' hT0').1 ((hdvd _ (by omega)).1 ((hnat _ T hT0).2 le_rfl))
  · exact (hnat _ T hT0).1 ((hdvd _ (by omega)).2 ((hnat _ T' hT0').2 le_rfl))

/-- **$\Lambda$ is locally constant on bad-reduced $T'$ over $\mathbb{Q}$** ($n \ge 3$): $T' \equiv T'' \pmod{p^{2K_0(p)+1}}$ at every bad
$p$ gives $\Lambda(T') = \Lambda(T'')$. -/
theorem badFactor_congr (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {T T' : ℕ} (hT0 : T ≠ 0)
    (hT0' : T' ≠ 0) (hT : IsBadReduced Q T)
    (h : ∀ p ∈ badPrimes Q, (p : ℤ) ^ (2 * depthLevelQ Q p + 1) ∣ (T : ℤ) - T') :
    badFactor Q T = badFactor Q T' := by
  have hc : ∀ p ∈ badPrimes Q, localDensity Q p T = localDensity Q p T' ∧
      localConstC' Q p T = localConstC' Q p T' := by
    intro p hp
    have := Fact.mk ((mem_badPrimes hQ).1 hp).1
    have hTp := hT p hp
    have hp' := h p hp
    rw [depthLevelQ_eq] at hTp hp'
    refine localDensity_congr_padic Q hQ p (a := depthLevelP Q p + 1) ?_ ?_
    · rwa [show depthLevelP Q p + 1 + 1 = depthLevelP Q p + 2 by ring]
    · rwa [show depthLevelP Q p + 1 + depthLevelP Q p = 2 * depthLevelP Q p + 1 by ring]
  have ha : anisoPart Q T = anisoPart Q T' := by
    rw [anisoPart_eq_prod_bad Q hQ hn hT0, anisoPart_eq_prod_bad Q hQ hn hT0']
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpb := (Finset.mem_filter.1 hp).1
    rw [factorization_eq_of_congr Q hT0 hT0' ((mem_badPrimes hQ).1 hpb).1 (hT p hpb) (h p hpb)]
  unfold badFactor
  rw [ha, Finset.prod_congr rfl fun p hp => (hc p hp).1,
    Finset.prod_congr rfl fun p hp => (hc p (Finset.mem_filter.1 hp).1).2]

/-- **$B_{\mathbb T}$ is finite over $\mathbb{Q}$** (Hanke 2004, p. 372): on any set of positive bad-reduced $T'$ the bad local
factor $\Lambda$ takes finitely many values ($n \ge 3$). -/
@[kb "hanke2004" "p. 372 (B_T finite, over Q)"]
theorem finite_badFactor_image (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (S : Set ℕ)
    (hS : ∀ T ∈ S, 0 < T ∧ IsBadReduced Q T) : (badFactor Q '' S).Finite := by
  let M : ℕ → ℕ := fun p => p ^ (2 * depthLevelQ Q p + 1)
  have hM : ∀ p ∈ badPrimes Q, 0 < M p := fun p hp =>
    pow_pos ((mem_badPrimes hQ).1 hp).1.pos _
  let C := ∀ p : badPrimes Q, Fin (M p.1)
  let ρ : ℕ → C := fun T p => ⟨T % M p.1, Nat.mod_lt _ (hM p.1 p.2)⟩
  let g : C → ℝ := fun c => if h : ∃ T ∈ S, ρ T = c then badFactor Q h.choose else 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨T, hT, rfl⟩
  have hex : ∃ T' ∈ S, ρ T' = ρ T := ⟨T, hT, rfl⟩
  refine ⟨ρ T, ?_⟩
  simp only [g]
  rw [dif_pos hex]
  obtain ⟨hT₁, hρ⟩ := hex.choose_spec
  symm
  refine badFactor_congr Q hQ hn (hS T hT).1.ne' (hS _ hT₁).1.ne' (hS T hT).2 fun p hp => ?_
  have := congrArg Fin.val (congrFun hρ ⟨p, hp⟩)
  simp only [ρ] at this
  have hmod : hex.choose ≡ T [MOD M p] := this
  have hd := Nat.modEq_iff_dvd.1 hmod
  simp only [M] at hd
  push_cast at hd
  exact hd

/-- **The minimum of $\Lambda$ over a set $\mathcal T$ of bad-reduced $T'$** over $\mathbb{Q}$ (Hanke's $\min_{T' \in B_{\mathbb T}}$). -/
def minBadFactor (Q : QuadForm ℤ n) (𝒯 : Set ℕ) : ℝ := sInf (badFactor Q '' 𝒯)

theorem minBadFactor_le (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {𝒯 : Set ℕ}
    (h𝒯 : ∀ T ∈ 𝒯, 0 < T ∧ IsBadReduced Q T) {T : ℕ} (hT : T ∈ 𝒯) : minBadFactor Q 𝒯 ≤ badFactor Q T :=
  csInf_le (finite_badFactor_image Q hQ hn 𝒯 h𝒯).bddBelow ⟨T, hT, rfl⟩

theorem exists_eq_minBadFactor (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {𝒯 : Set ℕ}
    (h𝒯 : ∀ T ∈ 𝒯, 0 < T ∧ IsBadReduced Q T) (hne : 𝒯.Nonempty) :
    ∃ T₀ ∈ 𝒯, minBadFactor Q 𝒯 = badFactor Q T₀ := by
  obtain ⟨T₀, hT₀, h⟩ := (hne.image _).csInf_mem (finite_badFactor_image Q hQ hn 𝒯 h𝒯)
  exact ⟨T₀, hT₀, h.symm⟩

theorem minBadFactor_pos (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) {𝒯 : Set ℕ}
    (h𝒯 : ∀ T ∈ 𝒯, 0 < T ∧ IsBadReduced Q T) (hne : 𝒯.Nonempty) (hpos : ∀ T ∈ 𝒯, 0 < badFactor Q T) :
    0 < minBadFactor Q 𝒯 := by
  obtain ⟨T₀, hT₀, h⟩ := exists_eq_minBadFactor Q hQ hn h𝒯 hne
  rw [h]; exact hpos T₀ hT₀

/-- **Hanke's $\hat\Lambda_4$: the minimum over $B_{\mathbb T}$** (Hanke 2004, Thm 5.7(b), p. 373): $6D^{-1/2}\min_{\mathcal T}\Lambda$,
uniform in $T' \in \mathcal T$ and in $S$ (`lambdaHat4Min_le`). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (Λ̂₄ = min over B_T)"]
def lambdaHat4Min (Q : QuadForm ℤ 4) (𝒯 : Set ℕ) : ℝ := 6 * gramDet Q ^ (-(1 / 2 : ℝ)) * minBadFactor Q 𝒯

/-- $\hat\Lambda_4^{\min}(\mathcal T) \le \hat\Lambda_4(S, T')$ for every $T' \in \mathcal T$ and every finite set $S$ of primes. -/
theorem lambdaHat4Min_le (Q : IntQF 4) (hQ : IntQF.PosDef Q) {𝒯 : Set ℕ}
    (h𝒯 : ∀ T ∈ 𝒯, 0 < T ∧ IsBadReduced Q T) {T : ℕ} (hT : T ∈ 𝒯) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    lambdaHat4Min Q 𝒯 ≤ lambdaHat4 Q S T := by
  have hQnd := hQ.nondegenerate
  have hT0 : (T : ℤ) ≠ 0 := by exact_mod_cast (h𝒯 T hT).1.ne'
  have hm := minBadFactor_le Q hQnd (by norm_num) h𝒯 hT
  have hD : 0 ≤ gramDet Q ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (gramDet_pos hQ).le _
  have hb : badFactor Q T ≤ (anisoPart Q T : ℝ) * (∏ p ∈ badPrimes Q, localDensity Q p T) *
      ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p), localConstC' Q p T := by
    unfold badFactor
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp => ?_))
    · refine prod_le_prod_of_subset_unitInterval ?_ _ (fun p hp => ?_) (fun p _ => min_le_left _ _)
      · intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨(mem_badPrimes hQnd).2 ⟨hS p hp.1.1, hp.2⟩, hp.1.2⟩
      · have := Fact.mk ((mem_badPrimes hQnd).1 (Finset.mem_filter.1 hp).1).1
        exact localConstC'_nonneg Q hQnd (by norm_num) p _ hT0
    · have := Fact.mk ((mem_badPrimes hQnd).1 hp).1
      exact localDensity_nonneg Q hQnd p _ hT0
  unfold lambdaHat4Min lambdaHat4
  calc 6 * gramDet Q ^ (-(1 / 2 : ℝ)) * minBadFactor Q 𝒯 ≤ 6 * gramDet Q ^ (-(1 / 2 : ℝ)) * badFactor Q T :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ 6 * gramDet Q ^ (-(1 / 2 : ℝ)) * ((anisoPart Q T : ℝ) * (∏ p ∈ badPrimes Q, localDensity Q p T) *
      ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p), localConstC' Q p T) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- **Theorem 5.7(b) over $\mathbb{Q}$, global form, with the minimum over $B_{\mathbb T}$** (Hanke 2004, p. 373; the hypothesis
`hglob` of `thm_6_3` with one constant for all $T' \in \mathcal T$): for $Q$ positive definite quaternary satisfying Siegel's
formula, $S$ a finite set of primes and $T' \in \mathcal T$ (positive, bad-reduced),
$$\hat\Lambda_4^{\min}(\mathcal T)\,(T')_{\mathrm{Iso}}\prod_{\substack{p \mid T'\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \le a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T').$$ -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (global, min over B_T, over Q)"]
theorem hglob_four_min (Q : IntQF 4) (hQ : IntQF.PosDef Q) (hSF : SiegelFormula Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {𝒯 : Set ℕ} (h𝒯 : ∀ T ∈ 𝒯, 0 < T ∧ IsBadReduced Q T) {T : ℕ} (hT : T ∈ 𝒯) :
    lambdaHat4Min Q 𝒯 * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T := by
  refine le_trans ?_ (hglob_four Q hQ hSF hS (h𝒯 T hT).1)
  have hP : 0 ≤ ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
      ((p : ℝ) - 1) / ((p : ℝ) + 1) := Finset.prod_nonneg fun p hp => by
    have h1 : (1 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).one_lt.le
    exact div_nonneg (by linarith) (by linarith)
  have hI : (0 : ℝ) ≤ isoPart Q T := Nat.cast_nonneg _
  gcongr
  exact lambdaHat4Min_le Q hQ h𝒯 hT S hS

/-- **Every positive $m$ is $T'x^2$ with $T'$ bad-reduced** (Hanke 2004, p. 372, the covering property of $B_{\mathbb T}$, over
$\mathbb{Q}$): $m = T'x^2$ with $T' > 0$ bad-reduced, $x$ supported on the bad primes, and $p^{K_0(p)} \mid T'$ at every $p \mid x$
(so $T'$ is $p$-stable there and locally represented iff $m$ is: `badReduced_decomp_spec`). *Proof:* strip $p^2$ while
$p^{K_0+2} \mid T'$ at a bad $p$. -/
@[kb "hanke2004" "p. 372 (m = T'(m')² with T' ∈ B_T, over Q)"]
theorem exists_badReduced_decomp (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) {m : ℕ} (hm : 0 < m) :
    ∃ T x : ℕ, m = T * x ^ 2 ∧ 0 < T ∧ IsBadReduced Q T ∧
      ∀ p ∈ x.primeFactors, p ∈ badPrimes Q ∧ (p : ℤ) ^ depthLevelQ Q p ∣ (T : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  by_cases hred : IsBadReduced Q m
  · exact ⟨m, 1, by ring, hm, hred, by simp⟩
  simp only [IsBadReduced, not_forall, not_not] at hred
  obtain ⟨p, hpB, hdvd⟩ := hred
  have hp := ((mem_badPrimes hQ).1 hpB).1
  set K := depthLevelQ Q p
  have hdvd' : p ^ (K + 2) ∣ m := by exact_mod_cast hdvd
  obtain ⟨m₁, hm₁⟩ : p ^ 2 ∣ m := (pow_dvd_pow p (by omega)).trans hdvd'
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hm₁pos : 0 < m₁ := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h, mul_zero] at hm₁; omega
    · exact h
  have hlt : m₁ < m := by
    rw [hm₁]
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    nlinarith
  have hK₁ : p ^ K ∣ m₁ := by
    rw [hm₁, show K + 2 = 2 + K by ring, pow_add] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_left hp2 hdvd'
  obtain ⟨T, x₁, h1, hT, hTred, hx₁⟩ := IH m₁ hlt hm₁pos
  have hx₁0 : x₁ ≠ 0 := by rintro rfl; rw [h1] at hm₁pos; simp at hm₁pos
  refine ⟨T, p * x₁, by rw [hm₁, h1]; ring, hT, hTred, fun q hq => ?_⟩
  rw [Nat.primeFactors_mul hp.ne_zero hx₁0, Finset.mem_union, hp.primeFactors,
    Finset.mem_singleton] at hq
  rcases hq with rfl | hq
  · refine ⟨hpB, ?_⟩
    by_cases hpx : q ∣ x₁
    · exact (hx₁ q (Nat.mem_primeFactors.2 ⟨hp, hpx, hx₁0⟩)).2
    · have hcop : Nat.Coprime (q ^ K) (x₁ ^ 2) :=
        Nat.Coprime.pow K 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpx)
      have : q ^ K ∣ T := hcop.dvd_of_dvd_mul_right (h1 ▸ hK₁)
      exact_mod_cast this
  · exact hx₁ q hq

/-- **The decomposition of `exists_badReduced_decomp` is stable** (Hanke 2004, p. 372: "$m$ is locally represented $\iff T'$ is",
and $m'$ supported on $\mathrm{Stable}(T')$): if $m = T'x^2$ and $p^{K_0(p)} \mid T'$ at a prime $p \mid x$, then $m$ is locally
represented at $p$ iff $T'$ is, and then $T'$ is $p$-stable. -/
theorem badReduced_decomp_spec (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (S₀ : Finset (Fin n)) {m T x : ℕ}
    (hmTx : m = T * x ^ 2) {p : ℕ} (hp : p.Prime) (hx : x ≠ 0)
    (hT : (p : ℤ) ^ depthLevelQ Q p ∣ (T : ℤ)) :
    (IsLocallyRepresentedAt Q p m ↔ IsLocallyRepresentedAt Q p T) ∧
      (IsLocallyRepresentedAt Q p m → IsPStable Q S₀ p T) := by
  have := Fact.mk hp
  rw [depthLevelQ_eq] at hT
  set ν := x.factorization p
  set u := x / p ^ ν
  have hxu : x = p ^ ν * u := (Nat.ordProj_mul_ordCompl_eq_self x p).symm
  have hu : ¬ (p : ℤ) ∣ (u : ℤ) := by
    rw [Int.natCast_dvd_natCast]; exact Nat.not_dvd_ordCompl hp hx
  have hm' : (m : ℤ) = (u : ℤ) ^ 2 * ((p : ℤ) ^ (2 * ν) * T) := by
    rw [hmTx, hxu]; push_cast; ring
  have hloc : IsLocallyRepresentedAt Q p m ↔ IsLocallyRepresentedAt Q p T := by
    rw [← isLocallyRepresentedAt_pow_mul_iff_padic Q hQ p hT ν]
    unfold IsLocallyRepresentedAt
    simp only [hm', repCount_mul_sq_of_not_dvd Q p _ hu]
  refine ⟨hloc, fun h => isPStable_of_dvd_padic Q hQ S₀ p ?_ (hloc.1 h)⟩
  refine (pow_dvd_pow _ ?_).trans hT
  rw [depthLevelP, DVR.depthLevel]; unfold levelExpP; omega

end Rat

end QuadFormsKB.Siegel
