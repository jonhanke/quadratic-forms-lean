/-
# Neat subgroups of a compact open subgroup

**Layer:** pure group theory (any group $G$). No topology and no number theory.

**Setting.** $G$ is a group (in the application $G = SO(V)(\mathbb A_f)$), $K \le G$ a subgroup (the compact open
$SO(\hat L)$), $\Gamma \le G$ a subgroup (the rational points $SO(V)(F)$). We assume the hypotheses that the KB's
`dcMass_of_le` uses: finitely many double cosets $\Gamma\backslash G/K$, and every stabilizer
$\Gamma \cap \alpha K \alpha^{-1}$ finite.

**Defines**
* `IsNeat Γ K'`: $\Gamma \cap \beta K' \beta^{-1} = 1$ for **every** $\beta \in G$ ("$K'$ is neat for $\Gamma$");
* `SepFiltration K`: a decreasing sequence $K_0 \ge K_1 \ge \dots$ of subgroups of $K$, each normal in $K$ and of finite
  index in $K$, with $\bigcap_k K_k = 1$ (in the application: the principal congruence subgroups $K(\mathfrak p^k)$ at
  one prime $\mathfrak p$);
* `dcRep Γ K ω`: a representative in $G$ of a double coset $\omega \in \Gamma\backslash G/K$.

**Proves**
* `exists_isNeat_of_reps` (neat member of a separating filtration): given representatives $\beta_1, \dots, \beta_h$ of $\Gamma\backslash G/K$ with every
  $\Gamma \cap \beta_i K \beta_i^{-1}$ finite, some member $K_k$ of the filtration is neat for $\Gamma$;
* `exists_isNeat`: the same with the hypotheses of `dcMass_of_le` (finitely many orbits, finite stabilizers);
* `dcMass_of_isNeat`: for a neat $K'$ all stabilizers are trivial, so $\mathrm{dcMass}(\Gamma, K') = \#(\Gamma\backslash G/K')$;
* `finite_orbits_of_relIndex`: $\Gamma\backslash G/K'$ is finite when $\Gamma\backslash G/K$ is and $[K : K'] < \infty$.

*Proof idea.* The finitely many elements $s = \beta_i^{-1}\gamma\beta_i \ne 1$ ($\gamma \in \Gamma \cap \beta_i K\beta_i^{-1}$) lie
in $K$, so each misses some $K_k$; one $K_k$ misses all of them (the filtration decreases). If $\gamma \in \Gamma$ and
$\beta^{-1}\gamma\beta \in K_k$, write $\beta = \delta\beta_i\kappa$ ($\delta \in \Gamma$, $\kappa \in K$); normality of $K_k$ in $K$ gives
$\beta_i^{-1}(\delta^{-1}\gamma\delta)\beta_i \in K_k$, hence $\delta^{-1}\gamma\delta = 1$. This replaces Minkowski's torsion-freeness
of $\ker(GL_n(\mathcal O_\mathfrak p) \to GL_n(\mathcal O/\mathfrak p))$ by the finiteness of the $\Gamma_\alpha$.
-/
import QuadFormsKB.Tamagawa.OrbitMass

open MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

variable {G : Type*} [Group G]

/-- **Neat subgroup.** $K'$ is *neat for* $\Gamma$ if $\Gamma \cap \beta K'\beta^{-1} = \{1\}$ for every $\beta \in G$, i.e.
$\gamma \in \Gamma$ and $\beta^{-1}\gamma\beta \in K'$ force $\gamma = 1$. Equivalently, $\Gamma$ acts freely on $G/K'$
(`stabilizer_eq_bot_of_isNeat`). (The name follows the usual "neat level" of arithmetic groups; here the notion is
purely group-theoretic.) -/
@[kb "hanke2011aws" "§4.6 (masses as volumes) [unverified]"]
def IsNeat (Γ K' : Subgroup G) : Prop :=
  ∀ β : G, ∀ γ ∈ Γ, β⁻¹ * γ * β ∈ K' → γ = 1

theorem IsNeat.mono {Γ K₁ K₂ : Subgroup G} (h : IsNeat Γ K₂) (hle : K₁ ≤ K₂) : IsNeat Γ K₁ :=
  fun β γ hγ hk => h β γ hγ (hle hk)

/-- **A separating filtration of $K$** by normal subgroups of finite index: subgroups
$K \ge K_0 \ge K_1 \ge \cdots$ (field `sub k` $= K_k$) with
* `le`: $K_k \le K$;
* `normal`: $K_k$ is normal in $K$ ($x y x^{-1} \in K_k$ for $x \in K$, $y \in K_k$);
* `antitone`: $K_{k+1} \le K_k$ (as `Antitone sub`);
* `relIndex_ne_zero`: $[K : K_k] < \infty$ (`relIndex` $\ne 0$, the convention of `dcMass_of_le`);
* `sep`: $\bigcap_k K_k = \{1\}$ (an element of $K$ lying in every $K_k$ is $1$).

For $K = SO(\hat L)$ the principal congruence subgroups at one prime are such a filtration. -/
structure SepFiltration (K : Subgroup G) where
  /-- The $k$-th subgroup $K_k$. -/
  sub : ℕ → Subgroup G
  /-- $K_k \le K$. -/
  le : ∀ k, sub k ≤ K
  /-- $K_k$ is normal in $K$. -/
  normal : ∀ k, ∀ x ∈ K, ∀ y ∈ sub k, x * y * x⁻¹ ∈ sub k
  /-- The filtration decreases. -/
  antitone : Antitone sub
  /-- $[K : K_k]$ is finite. -/
  relIndex_ne_zero : ∀ k, (sub k).relIndex K ≠ 0
  /-- $\bigcap_k K_k = 1$. -/
  sep : ∀ x ∈ K, (∀ k, x ∈ sub k) → x = 1

/-- **A neat member of the filtration exists** (representatives version). Let $\beta : \iota \to G$ ($\iota$ finite)
be representatives of $\Gamma\backslash G/K$ (`hcov`: every $g = \gamma\beta_i k$ with $\gamma \in \Gamma$, $k \in K$) such that every
$\Gamma \cap \beta_i K\beta_i^{-1}$ is finite (`hfin`). Then some $K_k$ of a separating filtration of $K$ is neat for $\Gamma$:
$\Gamma \cap \beta K_k\beta^{-1} = 1$ for every $\beta \in G$. -/
@[kb "hanke2011aws" "§4.6 (masses as volumes) [unverified]"]
theorem exists_isNeat_of_reps (Γ K : Subgroup G) (Kf : SepFiltration K) {ι : Type*} [Finite ι]
    (β : ι → G) (hcov : ∀ g : G, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * β i * k)
    (hfin : ∀ i, {γ : G | γ ∈ Γ ∧ (β i)⁻¹ * γ * β i ∈ K}.Finite) :
    ∃ k, IsNeat Γ (Kf.sub k) := by
  -- the finite set of conjugated stabilizer elements
  set S : Set G := ⋃ i, (fun γ => (β i)⁻¹ * γ * β i) '' {γ : G | γ ∈ Γ ∧ (β i)⁻¹ * γ * β i ∈ K}
  have hS : S.Finite := Set.finite_iUnion fun i => (hfin i).image _
  have hSK : ∀ s ∈ S, s ∈ K := by
    intro s hs
    obtain ⟨i, γ, ⟨-, hγK⟩, rfl⟩ := Set.mem_iUnion.mp hs |>.imp fun _ h => h
    exact hγK
  have hev : ∀ᶠ k in Filter.atTop, ∀ s ∈ S, s ≠ 1 → s ∉ Kf.sub k := by
    rw [Filter.eventually_all_finite hS]
    intro s hs
    by_cases h1 : s = 1
    · exact Filter.Eventually.of_forall fun _ h => absurd h1 h
    · have : ∃ k₀, s ∉ Kf.sub k₀ := by
        by_contra hc
        push Not at hc
        exact h1 (Kf.sep s (hSK s hs) hc)
      obtain ⟨k₀, hk₀⟩ := this
      filter_upwards [Filter.eventually_ge_atTop k₀] with k hk _ hmem
      exact hk₀ (Kf.antitone hk hmem)
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨k, fun g γ hγ hg => ?_⟩
  obtain ⟨i, δ, hδ, κ, hκ, rfl⟩ := hcov g
  -- $\gamma' = \delta^{-1}\gamma\delta$ is conjugated into $K_k$ by $\beta_i$
  have hconj : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i = κ * ((δ * β i * κ)⁻¹ * γ * (δ * β i * κ)) * κ⁻¹ := by
    group
  have hmem : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i ∈ Kf.sub k := by
    rw [hconj]; exact Kf.normal k κ hκ _ hg
  have hγ' : δ⁻¹ * γ * δ ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hδ) hγ) hδ
  have hS' : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i ∈ S :=
    Set.mem_iUnion.mpr ⟨i, _, ⟨hγ', Kf.le k hmem⟩, rfl⟩
  have h1 : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i = 1 := by
    by_contra hne; exact hk _ hS' hne hmem
  have : δ⁻¹ * γ * δ = 1 := by
    have := congrArg (fun x => β i * x * (β i)⁻¹) h1
    simpa [mul_assoc] using this
  have h2 := congrArg (fun x => δ * x * δ⁻¹) this
  simpa [mul_assoc] using h2

/-! ### Canonical representatives of $\Gamma\backslash G/K$ -/

/-- **A representative** $\alpha \in G$ of a double coset $\omega = \Gamma\alpha K \in \Gamma\backslash G/K$ (an orbit of
$\Gamma$ on $G/K$): `ω.out` is a coset $\alpha K$, and `Quotient.out` picks $\alpha$. -/
def dcRep (Γ K : Subgroup G) (ω : orbitRel.Quotient Γ (G ⧸ K)) : G := (ω.out : G ⧸ K).out

theorem mk_dcRep (Γ K : Subgroup G) (ω : orbitRel.Quotient Γ (G ⧸ K)) :
    (QuotientGroup.mk (dcRep Γ K ω) : G ⧸ K) = ω.out :=
  QuotientGroup.out_eq' _

/-- The orbit of the coset $\alpha_\omega K$ of the representative is $\omega$. -/
theorem orbit_mk_dcRep (Γ K : Subgroup G) (ω : orbitRel.Quotient Γ (G ⧸ K)) :
    (Quotient.mk'' (QuotientGroup.mk (dcRep Γ K ω) : G ⧸ K) : orbitRel.Quotient Γ (G ⧸ K)) = ω := by
  rw [mk_dcRep]; exact Quotient.out_eq' ω

/-- **Double coset decomposition:** $g = \gamma\,\alpha_\omega\,k$ with $\gamma \in \Gamma$, $k \in K$, where $\omega$ is the
double coset of $g$. -/
theorem exists_eq_mul_dcRep (Γ K : Subgroup G) (g : G) :
    ∃ γ ∈ Γ, ∃ k ∈ K,
      g = γ * dcRep Γ K (Quotient.mk'' (QuotientGroup.mk g : G ⧸ K)) * k := by
  set ω : orbitRel.Quotient Γ (G ⧸ K) := Quotient.mk'' (QuotientGroup.mk g : G ⧸ K)
  obtain ⟨γ, hγ⟩ := out_mem_orbit ω (QuotientGroup.mk g : G ⧸ K) rfl
  rw [← mk_dcRep] at hγ
  have h : (QuotientGroup.mk ((γ : G) * g) : G ⧸ K) = QuotientGroup.mk (dcRep Γ K ω) := hγ
  rw [QuotientGroup.eq] at h
  refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (((γ : G) * g)⁻¹ * dcRep Γ K ω)⁻¹, K.inv_mem h, ?_⟩
  group

/-- Two representatives $\alpha_\omega, \alpha_{\omega'}$ with $\gamma\alpha_\omega k = \alpha_{\omega'} k'$ ($\gamma \in \Gamma$,
$k, k' \in K$) are equal double cosets. -/
theorem dcRep_eq_of_mul (Γ K : Subgroup G) (ω ω' : orbitRel.Quotient Γ (G ⧸ K)) {γ k k' : G}
    (hγ : γ ∈ Γ) (hk : k ∈ K) (hk' : k' ∈ K) (h : γ * dcRep Γ K ω * k = dcRep Γ K ω' * k') :
    ω = ω' := by
  rw [← orbit_mk_dcRep Γ K ω, ← orbit_mk_dcRep Γ K ω']
  apply Quotient.sound'
  rw [orbitRel_apply]
  refine ⟨⟨γ, hγ⟩⁻¹, ?_⟩
  show (QuotientGroup.mk (γ⁻¹ * dcRep Γ K ω') : G ⧸ K) = QuotientGroup.mk (dcRep Γ K ω)
  rw [QuotientGroup.eq]
  have : (γ⁻¹ * dcRep Γ K ω')⁻¹ * dcRep Γ K ω = k' * k⁻¹ := by
    rw [show dcRep Γ K ω' = γ * dcRep Γ K ω * k * k'⁻¹ by rw [h]; group]
    group
  rw [this]; exact K.mul_mem hk' (K.inv_mem hk)

/-- **A neat member of the filtration exists**, under the hypotheses of `dcMass_of_le`: finitely many double
cosets $\Gamma\backslash G/K$ and finite stabilizers $\Gamma \cap \alpha K\alpha^{-1}$. -/
@[kb "hanke2011aws" "§4.6 (masses as volumes) [unverified]"]
theorem exists_isNeat (Γ K : Subgroup G) (Kf : SepFiltration K)
    [Finite (orbitRel.Quotient Γ (G ⧸ K))] (hstab : ∀ x : G ⧸ K, Finite (stabilizer Γ x)) :
    ∃ k, IsNeat Γ (Kf.sub k) := by
  refine exists_isNeat_of_reps Γ K Kf (dcRep Γ K) (fun g => ?_) (fun ω => ?_)
  · obtain ⟨γ, hγ, k, hk, h⟩ := exists_eq_mul_dcRep Γ K g
    exact ⟨_, γ, hγ, k, hk, h⟩
  · have := hstab (QuotientGroup.mk (dcRep Γ K ω))
    refine (Set.finite_range (fun s : stabilizer Γ (QuotientGroup.mk (dcRep Γ K ω) : G ⧸ K) =>
      ((s : Γ) : G))).subset ?_
    rintro γ ⟨hγ, hK⟩
    exact ⟨⟨⟨γ, hγ⟩, (mem_stabilizer_coset Γ K _ ⟨γ, hγ⟩).mpr hK⟩, rfl⟩

/-! ### Masses for a neat subgroup -/

/-- For a neat $K'$, $\Gamma$ acts freely on $G/K'$: every stabilizer is trivial. -/
theorem stabilizer_eq_bot_of_isNeat {Γ K' : Subgroup G} (h : IsNeat Γ K') (x : G ⧸ K') :
    stabilizer Γ x = ⊥ := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  rw [eq_bot_iff]
  intro γ hγ
  rw [mem_stabilizer_coset] at hγ
  exact (Subgroup.mem_bot).mpr (Subtype.ext (h α γ γ.2 hγ))

/-- **The mass of a neat level is the class number:** $\mathrm{dcMass}(\Gamma, K') = \#(\Gamma\backslash G/K')$ when $K'$ is
neat for $\Gamma$ (all stabilizers are trivial). (Both sides are $0$ if there are infinitely many double cosets.) -/
@[kb "hanke2011aws" "§4.6 (masses as volumes) [unverified]"]
theorem dcMass_of_isNeat {Γ K' : Subgroup G} (h : IsNeat Γ K') :
    dcMass Γ K' = Nat.card (orbitRel.Quotient Γ (G ⧸ K')) := by
  have h1 : ∀ ω : orbitRel.Quotient Γ (G ⧸ K'), ((Nat.card (stabilizer Γ ω.out) : ℝ))⁻¹ = 1 := by
    intro ω
    rw [stabilizer_eq_bot_of_isNeat h, Subgroup.card_bot, Nat.cast_one, inv_one]
  unfold dcMass orbitMass
  simp_rw [h1]
  rcases finite_or_infinite (orbitRel.Quotient Γ (G ⧸ K')) with hf | hf
  · have := Fintype.ofFinite (orbitRel.Quotient Γ (G ⧸ K'))
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  · rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero]
    apply finsum_of_infinite_support
    rw [Function.support_const one_ne_zero]
    exact Set.infinite_univ

/-- **Finiteness passes down to finite-index subgroups:** if $\Gamma\backslash G/K$ is finite and $[K : K'] < \infty$,
then $\Gamma\backslash G/K'$ is finite (it is covered by the images of $\alpha_\omega q$, $q \in K/K'$). -/
theorem finite_orbits_of_relIndex (Γ : Subgroup G) {K' K : Subgroup G} (hfin : K'.relIndex K ≠ 0)
    [Finite (orbitRel.Quotient Γ (G ⧸ K))] : Finite (orbitRel.Quotient Γ (G ⧸ K')) := by
  have : (K'.subgroupOf K).FiniteIndex := ⟨hfin⟩
  let f : orbitRel.Quotient Γ (G ⧸ K) × (K ⧸ K'.subgroupOf K) → orbitRel.Quotient Γ (G ⧸ K') :=
    fun p => Quotient.mk'' (QuotientGroup.mk (dcRep Γ K p.1 * ((p.2.out : K) : G)) : G ⧸ K')
  refine Finite.of_surjective f fun ω' => ?_
  induction ω' using Quotient.inductionOn' with | h x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨γ, hγ, k, hk, hg⟩ := exists_eq_mul_dcRep Γ K g
  set ω : orbitRel.Quotient Γ (G ⧸ K) := Quotient.mk'' (QuotientGroup.mk g : G ⧸ K)
  set q : K ⧸ K'.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
  refine ⟨(ω, q), ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) (⟨k, hk⟩ : K)
  apply Quotient.sound'
  rw [orbitRel_apply]
  refine ⟨⟨γ, hγ⟩⁻¹, ?_⟩
  show (QuotientGroup.mk (γ⁻¹ * g) : G ⧸ K') = QuotientGroup.mk (dcRep Γ K ω * ((q.out : K) : G))
  rw [QuotientGroup.eq]
  have hq : ((q.out : K) : G) = k * ((h : K) : G) := by
    rw [show q.out = (⟨k, hk⟩ : K) * (h : K) from hh]; rfl
  have hh' : ((h : K) : G) ∈ K' := h.2
  rw [hq]
  have : (γ⁻¹ * g)⁻¹ * (dcRep Γ K ω * (k * ((h : K) : G))) = ((h : K) : G) := by
    rw [hg]; group
  rw [this]; exact hh'

end QuadFormsKB.Tamagawa.Measure
