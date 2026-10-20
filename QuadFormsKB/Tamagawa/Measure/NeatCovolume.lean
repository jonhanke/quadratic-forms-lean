/-
# Exact fundamental domain and covolume for a neat level

**Layer:** abstract group and measure theory. No topology, no number theory.

**Setting.** $G = G_\infty \times G_f$ (types `A × B`), groups with measurable multiplication and left-invariant
s-finite measures $\mu_\infty$ on $G_\infty$ and $\mu_f$ on $G_f$; the measure on $G$ is $\mu_\infty \times \mu_f$.
A countable subgroup $\Gamma \le G_\infty \times G_f$ acts on the **left** (Mathlib's `covolume`, the KB's
$\Gamma\backslash G/K$) and is injective under the projection to $G_f$ (`hinj`; true for the diagonal embedding of
$SO(V)(F)$). $\Gamma_f$ = `Γ.map (MonoidHom.snd A B)` is its image in $G_f$. $K \le G_f$ is a measurable subgroup (in the
application the compact open $SO(\hat L)$). Compactness of $G_\infty$ is **not** needed: $\mu_\infty(G_\infty)$ simply
appears as a factor (it is finite in the definite case).

**Defines**
* `neatDomain K' β` $= G_\infty \times \bigcup_i \beta_i K'$.

**Proves**
* `isFundamentalDomain_neatDomain`: if $K'$ is neat for $\Gamma_f$ and $\beta_i$ represent $\Gamma_f\backslash G_f/K'$ exactly,
  then $G_\infty \times \bigcup_i \beta_i K'$ is a fundamental domain for $\Gamma$ (every $\Gamma$-orbit meets it in exactly one
  point, so it is exact, not just up to null sets);
* `covolume_eq_of_isNeat_reps`, `covolume_eq_of_isNeat`:
  $\mathrm{covol}(\Gamma\backslash G) = \mu_\infty(G_\infty)\cdot\mu_f(K')\cdot\#(\Gamma_f\backslash G_f/K')$;
* `relIndex_mul_measure`: $[K : K']\,\mu_f(K') = \mu_f(K)$ (compare FLT's `relIndex_mul_measure`; here
  proved directly);
* **`covolume_eq_measure_mul_dcMass`** (the headline): with a separating filtration of $K$ (`SepFiltration`),
  finitely many double cosets and finite stabilizers,
  $$\mathrm{covol}(\Gamma\backslash (G_\infty \times G_f)) = \mu_\infty(G_\infty)\cdot\mu_f(K)\cdot\mathrm{dcMass}(\Gamma_f, K),$$
  where `dcMass` $= \sum_{\Gamma_f\alpha K}1/|\Gamma_f \cap \alpha K\alpha^{-1}|$ is the KB's double-coset mass (`OrbitMass.lean`).
  This is the unfolding $\tau = \mu(K)\cdot\mathrm{mass}$ that `tauSO` (`MassFormula.lean`) takes as its definition; `AdelicSO.lean`
  instantiates it with $SO(V)(\mathbb A)$.

*Proof.* `exists_isNeat` gives a neat $K' = K_k$. Then the $\Gamma$-translates of $G_\infty \times \bigcup_\beta\beta K'$ tile
$G$, so covol $= \mu_\infty(G_\infty)\,\mu_f(K')\,h'$ with $h' = \#(\Gamma_f\backslash G_f/K') = \mathrm{dcMass}(\Gamma_f, K')$
(`dcMass_of_isNeat`) $= [K:K']\,\mathrm{dcMass}(\Gamma_f, K)$ (`dcMass_of_le`), and $[K:K']\,\mu_f(K') = \mu_f(K)$.
Weil 1982, §2.4, p. 23 defines $\tau(G)$ as this covolume.
-/
import QuadFormsKB.Tamagawa.Measure.Neat

open MeasureTheory MulAction Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

/-! ### Measurable multiplication on a product (absent from Mathlib v4.35.0) -/

/-- Left and right multiplication by a constant are measurable on `A × B` (product σ-algebra) when they are on each
factor. Mathlib v4.35.0 has no such instance; it is needed for `Measure.prod.instIsMulLeftInvariant` and for
`covolume`. -/
instance prodMeasurableMul {A B : Type*} [Mul A] [Mul B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableMul A] [MeasurableMul B] : MeasurableMul (A × B) where
  measurable_const_mul c :=
    ((measurable_const_mul c.1).comp measurable_fst).prodMk ((measurable_const_mul c.2).comp measurable_snd)
  measurable_mul_const c :=
    ((measurable_mul_const c.1).comp measurable_fst).prodMk ((measurable_mul_const c.2).comp measurable_snd)

/-! ### Cosets of a finite-index subgroup -/

section Index

variable {B : Type*} [Group B] [MeasurableSpace B] [MeasurableMul B]

/-- **Measure and index:** for subgroups $K' \le K$ with $[K:K'] < \infty$ and $K'$ measurable, and a left-invariant
measure $\mu$, $[K : K']\cdot\mu(K') = \mu(K)$ ($K$ is the disjoint union of $[K:K']$ left translates of $K'$).
(The relative version of Mathlib's `Subgroup.index_mul_measure`; FLT has the same statement as
`relIndex_mul_measure`.) -/
@[kb "hanke2011aws" "§4.6 (masses as volumes) [unverified]"]
theorem relIndex_mul_measure {K' K : Subgroup B} (hle : K' ≤ K) (hfin : K'.relIndex K ≠ 0)
    (hK' : MeasurableSet (K' : Set B)) (μ : Measure B) [μ.IsMulLeftInvariant] :
    (K'.relIndex K : ℝ≥0∞) * μ K' = μ K := by
  have : (K'.subgroupOf K).FiniteIndex := ⟨hfin⟩
  have := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let t : K ⧸ K'.subgroupOf K → Set B := fun q => ((q.out : K) : B) • (K' : Set B)
  have hU : (K : Set B) = ⋃ q, t q := by
    ext x
    simp only [mem_iUnion, t, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) (⟨x, hx⟩ : K)
      refine ⟨((h : K) : B)⁻¹, K'.inv_mem h.2, ?_⟩
      rw [hh]; show x * ((h : K) : B) * ((h : K) : B)⁻¹ = x; group
    · rintro ⟨q, y, hy, rfl⟩
      exact K.mul_mem (q.out : K).2 (hle hy)
  have hdisj : Pairwise (Function.onFun Disjoint t) := by
    intro q₁ q₂ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, hz⟩
    apply hne
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq]
    show (((q₁.out : K) : B))⁻¹ * ((q₂.out : K) : B) ∈ K'
    have hz' : ((q₂.out : K) : B) * y₂ = ((q₁.out : K) : B) * y₁ := hz
    have : (((q₁.out : K) : B))⁻¹ * ((q₂.out : K) : B) = y₁ * y₂⁻¹ := by
      rw [show ((q₂.out : K) : B) = ((q₁.out : K) : B) * y₁ * y₂⁻¹ by rw [← hz']; group]
      group
    rw [this]; exact K'.mul_mem hy₁ (K'.inv_mem hy₂)
  rw [hU, measure_iUnion hdisj (fun q => hK'.const_smul _), tsum_fintype]
  simp only [t, measure_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

end Index

/-! ### The exact fundamental domain -/

section FundamentalDomain

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableMul A] [MeasurableMul B]

/-- **The neat fundamental domain** $G_\infty \times \bigcup_i \beta_i K' \subseteq G_\infty \times G_f$, for representatives
$\beta_i$ of $\Gamma_f\backslash G_f/K'$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
def neatDomain (K' : Subgroup B) {ι : Type*} (β : ι → B) : Set (A × B) :=
  univ ×ˢ ⋃ i, β i • (K' : Set B)

/-- **Exact fundamental domain.** Let $\Gamma \le G_\infty \times G_f$ with injective projection to $G_f$ (`hinj`), let $K'$ be
neat for $\Gamma_f$ (`hneat`) and measurable, and let $\beta : \iota \to G_f$ represent the double cosets
$\Gamma_f\backslash G_f/K'$ exactly: every $g = \gamma_f\beta_i k$ (`hcov`), and $\gamma_f\beta_i k = \beta_j k'$ forces $i = j$
(`hdisj`). Then `neatDomain K' β` $= G_\infty \times \bigcup_i\beta_iK'$ is a fundamental domain for $\Gamma$ acting on the
left, for every measure $\mu$: each $\Gamma$-orbit meets it in exactly one point. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem isFundamentalDomain_neatDomain (Γ : Subgroup (A × B)) (K' : Subgroup B)
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1) (hneat : IsNeat (Γ.map (MonoidHom.snd A B)) K')
    (hK' : MeasurableSet (K' : Set B)) {ι : Type*} [Countable ι] (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (μ : Measure (A × B)) :
    IsFundamentalDomain Γ (neatDomain K' β) μ := by
  refine IsFundamentalDomain.mk'
    (MeasurableSet.univ.prod (MeasurableSet.iUnion fun i => hK'.const_smul (β i))).nullMeasurableSet
    fun x => ?_
  have hmem : ∀ (γ : Γ), γ • x ∈ neatDomain K' β ↔
      ∃ i, ∃ k ∈ K', (γ : A × B).2 * x.2 = β i * k := by
    intro γ
    simp only [neatDomain, mem_prod, mem_univ, true_and, mem_iUnion]
    show (∃ i, ((γ : A × B) * x).2 ∈ β i • (K' : Set B)) ↔ _
    simp only [Prod.snd_mul, mem_smul_set, SetLike.mem_coe, smul_eq_mul]
    exact exists_congr fun i => ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩, fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩⟩
  obtain ⟨i, γ, hγ, k, hk, hx⟩ := hcov x.2
  refine ⟨⟨γ, hγ⟩⁻¹, (hmem _).mpr ⟨i, k, hk, ?_⟩, fun δ hδ => ?_⟩
  · show (γ⁻¹).2 * x.2 = β i * k
    rw [hx, Prod.snd_inv]; group
  · obtain ⟨j, k', hk', hj⟩ := (hmem δ).mp hδ
    -- $\varepsilon = \delta\gamma$ maps $\beta_i k$ to $\beta_j k'$
    set ε : A × B := (δ : A × B) * γ
    have hε : ε ∈ Γ := Γ.mul_mem δ.2 hγ
    have hεx : ε.2 * β i * k = β j * k' := by
      rw [← hj, hx]; simp only [ε, Prod.snd_mul]; group
    obtain rfl := hdisj i j ε hε k hk k' hk' hεx
    have hconj : (β i)⁻¹ * ε.2 * β i = k' * k⁻¹ := by
      rw [show ε.2 = β i * k' * k⁻¹ * (β i)⁻¹ by
        rw [← hεx]; group]
      group
    have hε2 : ε.2 = 1 :=
      hneat (β i) ε.2 ⟨ε, hε, rfl⟩ (by rw [hconj]; exact K'.mul_mem hk' (K'.inv_mem hk))
    have hε1 : ε = 1 := hinj ε hε hε2
    apply Subtype.ext
    show (δ : A × B) = γ⁻¹
    rw [eq_inv_iff_mul_eq_one]; exact hε1

/-- **Volume of the neat fundamental domain:** $(\mu_\infty\times\mu_f)(G_\infty \times \bigcup_i\beta_iK') =
\mu_\infty(G_\infty)\cdot\mu_f(K')\cdot\#\iota$, when the translates $\beta_iK'$ are disjoint (`hdisj` with $\gamma = 1$). -/
theorem measure_neatDomain (K' : Subgroup B) (hK' : MeasurableSet (K' : Set B)) {ι : Type*} [Finite ι]
    (β : ι → B) (hdisj : ∀ i j, ∀ k ∈ K', ∀ k' ∈ K', β i * k = β j * k' → i = j)
    (μA : Measure A) (μB : Measure B) [SFinite μB] [μB.IsMulLeftInvariant] :
    (μA.prod μB) (neatDomain K' β) = μA univ * μB K' * Nat.card ι := by
  have := Fintype.ofFinite ι
  have hpd : Pairwise (Function.onFun Disjoint fun i => β i • (K' : Set B)) := by
    intro i j hne
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨k, hk, rfl⟩ ⟨k', hk', hz⟩
    exact hne (hdisj i j k hk k' hk' hz.symm)
  rw [neatDomain, Measure.prod_prod, measure_iUnion hpd (fun i => hK'.const_smul _), tsum_fintype]
  simp only [measure_smul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

/-- **Covolume of $\Gamma$ (representatives version):**
$\mathrm{covol}(\Gamma\backslash(G_\infty\times G_f)) = \mu_\infty(G_\infty)\cdot\mu_f(K')\cdot\#\iota$ for a neat $K'$ and exact
representatives $\beta : \iota \to G_f$ of $\Gamma_f\backslash G_f/K'$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem covolume_eq_of_isNeat_reps (Γ : Subgroup (A × B)) [Countable Γ] (K' : Subgroup B)
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1) (hneat : IsNeat (Γ.map (MonoidHom.snd A B)) K')
    (hK' : MeasurableSet (K' : Set B)) {ι : Type*} [Finite ι] (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant] :
    covolume Γ (A × B) (μA.prod μB) = μA univ * μB K' * Nat.card ι := by
  rw [(isFundamentalDomain_neatDomain Γ K' hinj hneat hK' β hcov hdisj _).covolume_eq_volume,
    measure_neatDomain K' hK' β (fun i j k hk k' hk' h => hdisj i j 1 Γ.one_mem k hk k' hk'
      (by simpa using h))]

/-- **Covolume of $\Gamma$ for a neat level:** for $K'$ neat for $\Gamma_f$, measurable, with finitely many double cosets,
$$\mathrm{covol}(\Gamma\backslash(G_\infty\times G_f)) = \mu_\infty(G_\infty)\cdot\mu_f(K')\cdot\#(\Gamma_f\backslash G_f/K').$$ -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem covolume_eq_of_isNeat (Γ : Subgroup (A × B)) [Countable Γ] (K' : Subgroup B)
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1) (hneat : IsNeat (Γ.map (MonoidHom.snd A B)) K')
    (hK' : MeasurableSet (K' : Set B))
    [Finite (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K'))]
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant] :
    covolume Γ (A × B) (μA.prod μB) =
      μA univ * μB K' * Nat.card (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K')) := by
  set Γf := Γ.map (MonoidHom.snd A B)
  refine covolume_eq_of_isNeat_reps Γ K' hinj hneat hK' (dcRep Γf K') (fun g => ?_)
    (fun i j γ hγ k hk k' hk' h => ?_) μA μB
  · obtain ⟨γf, ⟨γ, hγ, rfl⟩, k, hk, h⟩ := exists_eq_mul_dcRep Γf K' g
    exact ⟨_, γ, hγ, k, hk, h⟩
  · exact dcRep_eq_of_mul Γf K' i j ⟨γ, hγ, rfl⟩ hk hk' h

end FundamentalDomain

/-! ### Comparison with the double-coset mass -/

section Mass

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableMul A] [MeasurableMul B]

/-- **Covolume = $\mu_\infty(G_\infty)\cdot\mu_f(K)\cdot\mathrm{dcMass}$ (the unfolding).** Let $\Gamma \le G_\infty \times G_f$
be countable with injective projection $\Gamma \to \Gamma_f \le G_f$ (`hinj`), let $K \le G_f$ be a subgroup with finitely
many double cosets $\Gamma_f\backslash G_f/K$ and finite stabilizers $\Gamma_f \cap \alpha K\alpha^{-1}$ (`hstab`), and let
`Kf` be a separating filtration of $K$ by normal finite-index subgroups, all measurable (`hmeas`). Then for
left-invariant s-finite measures $\mu_\infty$, $\mu_f$:
$$\mathrm{covol}(\Gamma\backslash (G_\infty\times G_f), \mu_\infty\times\mu_f) = \mu_\infty(G_\infty)\cdot\mu_f(K)\cdot
  \sum_{\Gamma_f\alpha K}\frac{1}{|\Gamma_f\cap\alpha K\alpha^{-1}|}.$$
No discreteness of $\Gamma$ and no reduction theory are used: finiteness of the class set and of the stabilizers
suffices. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem covolume_eq_measure_mul_dcMass (Γ : Subgroup (A × B)) [Countable Γ] (K : Subgroup B)
    (Kf : SepFiltration K) (hmeas : ∀ k, MeasurableSet (Kf.sub k : Set B))
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1)
    [Finite (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K))]
    (hstab : ∀ x : B ⧸ K, Finite (stabilizer (Γ.map (MonoidHom.snd A B)) x))
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant] :
    covolume Γ (A × B) (μA.prod μB) =
      μA univ * μB K * ENNReal.ofReal (dcMass (Γ.map (MonoidHom.snd A B)) K) := by
  set Γf := Γ.map (MonoidHom.snd A B)
  obtain ⟨k, hneat⟩ := exists_isNeat Γf K Kf hstab
  set K' := Kf.sub k
  have hfin := Kf.relIndex_ne_zero k
  have := finite_orbits_of_relIndex Γf (K := K) (K' := K') hfin
  set h' := Nat.card (orbitRel.Quotient Γf (B ⧸ K'))
  set m := K'.relIndex K
  rw [covolume_eq_of_isNeat Γ K' hinj hneat (hmeas k) μA μB,
    ← relIndex_mul_measure (Kf.le k) hfin (hmeas k) μB]
  -- $\mathrm{dcMass}(\Gamma_f, K) = h'/m$
  have hdc : dcMass Γf K = (h' : ℝ) / m := by
    have h1 := dcMass_of_isNeat hneat
    have h2 := dcMass_of_le Γf (Kf.le k) hfin hstab
    have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hfin
    rw [eq_div_iff hm, mul_comm, ← h2, h1]
  have hm0 : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hfin
  have hmT : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  rw [hdc, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hfin)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  calc μA univ * μB K' * (h' : ℝ≥0∞)
      = μA univ * μB K' * h' * ((m : ℝ≥0∞) / m) := by rw [ENNReal.div_self hm0 hmT, mul_one]
    _ = μA univ * (m * μB K') * (h' / m) := by
        simp only [div_eq_mul_inv]; ring

/-- **Real form of the unfolding**, for finite measures: $\mathrm{covol}(\Gamma\backslash G)$ as a real number equals
$\mu_\infty(G_\infty)\cdot\mu_f(K)\cdot\mathrm{dcMass}(\Gamma_f, K)$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem covolume_toReal_eq_measure_mul_dcMass (Γ : Subgroup (A × B)) [Countable Γ] (K : Subgroup B)
    (Kf : SepFiltration K) (hmeas : ∀ k, MeasurableSet (Kf.sub k : Set B))
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1)
    [Finite (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K))]
    (hstab : ∀ x : B ⧸ K, Finite (stabilizer (Γ.map (MonoidHom.snd A B)) x))
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant] :
    (covolume Γ (A × B) (μA.prod μB)).toReal =
      (μA univ).toReal * (μB K).toReal * dcMass (Γ.map (MonoidHom.snd A B)) K := by
  rw [covolume_eq_measure_mul_dcMass Γ K Kf hmeas hinj hstab μA μB, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  unfold dcMass orbitMass
  exact finsum_nonneg fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)

end Mass

end QuadFormsKB.Tamagawa.Measure
