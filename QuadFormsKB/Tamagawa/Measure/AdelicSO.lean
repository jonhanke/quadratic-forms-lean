/-
# The adelic Tamagawa measure on $SO(V)(\mathbb A)$ and $\tau(SO) = \mathrm{covol}$

**Layer:** number fields; the KB's concrete groups (`Lattices/ClassSet.lean`): $O(V)(\mathbb A_f)$ = `OAf QF`, the
restricted product of the $O(V)(F_v)$ with respect to the $O(V)(\mathfrak o_v)$, and its subgroup
$SO(V)(\mathbb A_f)$ = `soAf QF`. Definite case: $Q_0$ over $\mathcal O_F$, nondegenerate, $Q_0 \otimes F$ totally positive
definite, $F$ totally real, $L = \mathcal O_F^n$.

**Defines**
* the restricted-product topology on `OAf Q` (Mathlib's `Πʳ` topology, a locally compact topological group because the
  $O(V)(\mathfrak o_v)$ are compact open, `LocalSO.lean`) and its **Borel** $\sigma$-algebra;
* `SOAf Q₀` = $SO(V)(\mathbb A_f)$ (closed subgroup, subspace topology, Borel), `KSO Q₀` = $SO(\hat L)$ (compact open),
  `GammaSOf Q₀` = $SO(V)(F) \le SO(V)(\mathbb A_f)$ (exactly the groups in `tauSO`);
* `finFactor Q₀ λ` $= \prod'_v \mu_v(SO(L_v))$ for the local measures $\mu_v$ = `muLocSO v Q₀ λ_v` of `LocalSO.lean`, and
  `muFin Q₀ λ`: **the Haar measure on $SO(V)(\mathbb A_f)$ normalized by $\mu_f(SO(\hat L)) = \prod'_v \mu_v(SO(L_v)) =
  \prod'_v\alpha_v(L,L)/\lambda_v$**;
* `realEmb σ`, `Qσ Q₀ σ`: the real form at each embedding $\sigma : F \to \mathbb C$ (real since $F$ is totally real);
  `muInfTam` $= |d_F|^{-n(n-1)/4}\cdot\mu_\infty$ with $\mu_\infty = \prod_\sigma\mu_\sigma$;
* `muAdele Q₀ λ` $= c_F\,\mu_\infty \times \mu_f$ on $SO(V)(\mathbb A) = G_\infty\times SO(V)(\mathbb A_f)$ (`muAdele_eq_smul`);
* `GammaSO Q₀` $= SO(V)(F)$ embedded **diagonally** in $G_\infty \times SO(V)(\mathbb A_f)$ ($\gamma \mapsto
  ((\sigma(\gamma))_\sigma, (\gamma)_v)$), acting on the left.

**Proves** (all unconditional, standard axioms only)
* topology: `isCompact_locStab`, `isOpen_locStab` ($O(\hat L)$ compact open in $O(V)(\mathbb A_f)$), `isClosed_soAf`,
  `isCompact_KSO`, `isOpen_KSO`; `sep_KSO` ($SO(\hat L)$ is profinite: open normal subgroups separate points);
* `isPosDefR_Qσ`: the real forms are positive definite (density of $\mathbb Q^n$ in $\mathbb R^n$ + nondegeneracy);
* `countable_GammaSO`, `GammaSO_inj`, `map_snd_GammaSO` ($\Gamma_f$ = `GammaSOf`), `finite_orbits_SO`, `finite_stabilizer_SO`
  ($SO$-level finiteness of $\Gamma_f\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ and of the $\Gamma_f\cap\alpha K\alpha^{-1}$),
  `sigmaFinite_muFin` ($SO(V)(\mathbb A_f)$ is a countable union of translates of $SO(\hat L)$);
* abstract: `finite_orbits_of_finiteIndex`, `exists_isNeat_of_reps_sep`, `covolume_eq_measure_mul_dcMass_of_sep` (the unfolding with a separating *family* of open normal subgroups instead of a sequence; no countability needed);
* `covolume_muAdele`: $\mathrm{covol}(SO(V)(F)\backslash SO(V)(\mathbb A), \mu_{\mathbb A}) = c_F\,\mu_\infty(G_\infty)\,\mu_f(SO(\hat L))\,
  \mathrm{mass}_{SO}$ for every $\lambda$;
* **`tauSO_eq_covolume`**: for $\lambda_v = 1$, `tauSO Q₀` $= \mathrm{covol}(SO(V)(F)\backslash SO(V)(\mathbb A), \mu_{\mathbb A})$
  (as `ENNReal` and as a real number, `tauSO_eq_covolume_toReal`), and
  `tamagawaNumberTwo_iff_covolume`: `TamagawaNumberTwo Q₀` $\iff$ the covolume is $2$.

So $\tau(SO) = 2$ is now a statement about a genuine Haar measure on $SO(V)(\mathbb A)$ (Weil 1982, §2.4, p. 23:
$\tau(G) = \mathrm{vol}(G_{\mathbb A}/G_k)$), no longer definitionally the mass formula.

**What the measure is (and is not yet).** $\mu_f$ is a genuine left Haar measure on the locally compact group
$SO(V)(\mathbb A_f)$, normalized on the compact open $SO(\hat L)$ by the product of the local masses
$\mu_v(SO(L_v)) = \alpha_v/\lambda_v$ of `LocalSO.lean`. The *product characterization* ($\mu_f$ agrees with $\prod_v\mu_v$ on boxes
$\prod_{v\in S}U_v\times\prod_{v\notin S}SO(L_v)$) is in `ProductSO.lean`; it is not used here. The identification of
$\mu_v$, $\mu_\sigma$ with gauge-form (Leray) measures is in the `Leray*` files.

-/
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.ArchSO
import QuadFormsKB.Tamagawa.Measure.NeatCovolume
import QuadFormsKB.Tamagawa.MassFormula

open MeasureTheory MulAction Set Topology
open scoped ENNReal NNReal Pointwise RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

/-! ### Part 1: abstract group theory and the unfolding with a separating family -/

section Abstract

variable {G : Type*} [Group G]

/-- **Orbits of a finite-index subgroup:** if $H$ has finitely many orbits on $X$ and $H' \le H$ has finite index, then
$H'$ has finitely many orbits ($x = h\,y_\omega$ and $h = h'c$ with $c$ in a finite set of coset representatives). -/
theorem finite_orbits_of_finiteIndex {H : Type*} [Group H] {X : Type*} [MulAction H X] (H' : Subgroup H)
    [H'.FiniteIndex] [Finite (orbitRel.Quotient H X)] : Finite (orbitRel.Quotient H' X) := by
  refine Finite.of_surjective (fun p : (H ⧸ H') × orbitRel.Quotient H X =>
    (Quotient.mk'' ((p.1.out)⁻¹ • p.2.out) : orbitRel.Quotient H' X)) ?_
  intro ω
  induction ω using Quotient.inductionOn' with | h x => ?_
  set ω₀ : orbitRel.Quotient H X := Quotient.mk'' x
  obtain ⟨g, hg⟩ := out_mem_orbit ω₀ x rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H' g
  refine ⟨(QuotientGroup.mk g, ω₀), ?_⟩
  apply Quotient.sound'
  rw [orbitRel_apply]
  refine ⟨h⁻¹, ?_⟩
  change ((h⁻¹ : H') : H) • x = ((QuotientGroup.mk g : H ⧸ H').out)⁻¹ • ω₀.out
  rw [hh, ← hg, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rfl

/-- **Avoiding finitely many elements.** Let $P$ be a property of subgroups, true for $K$ and stable under finite
intersections, such that every $s \in K \setminus 1$ is avoided by some $N$ with $P(N)$. Then for every finite set
$S \subseteq K$ there is $N$ with $P(N)$ containing no element of $S \setminus 1$. -/
theorem exists_avoiding (K : Subgroup G) (P : Subgroup G → Prop) (hK : P K)
    (hinf : ∀ N₁ N₂, P N₁ → P N₂ → P (N₁ ⊓ N₂)) (hsep : ∀ s ∈ K, s ≠ 1 → ∃ N, P N ∧ s ∉ N)
    (S : Finset G) (hSK : ∀ s ∈ S, s ∈ K) : ∃ N, P N ∧ ∀ s ∈ S, s ≠ 1 → s ∉ N := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨K, hK, by simp⟩
  | insert a S _ ih =>
    obtain ⟨N, hN, hNS⟩ := ih fun s hs => hSK s (Finset.mem_insert_of_mem hs)
    by_cases ha : a = 1
    · refine ⟨N, hN, fun s hs hs1 => ?_⟩
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact absurd ha hs1
      · exact hNS s hs hs1
    · obtain ⟨Na, hPa, haN⟩ := hsep a (hSK a (Finset.mem_insert_self a S)) ha
      refine ⟨N ⊓ Na, hinf N Na hN hPa, fun s hs hs1 hmem => ?_⟩
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact haN (Subgroup.mem_inf.mp hmem).2
      · exact hNS s hs hs1 (Subgroup.mem_inf.mp hmem).1

/-- **Neat filtration member with a separating family** (variant of `exists_isNeat_of_reps`): given finite representatives of
$\Gamma\backslash G/K$ with finite stabilizers, and a property $P$ of subgroups (each $N$ with $P(N)$ is normal in $K$ and
contained in $K$; $P(K)$; $P$ stable under $\cap$; every $s \in K\setminus 1$ avoided by some $N$), some $N$ with $P(N)$
is neat for $\Gamma$. -/
@[kb "hanke2011aws" "§4.6 (masses as volumes) [unverified]"]
theorem exists_isNeat_of_reps_sep (Γ K : Subgroup G) (P : Subgroup G → Prop) (hPle : ∀ N, P N → N ≤ K)
    (hPnormal : ∀ N, P N → ∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) (hK : P K)
    (hinf : ∀ N₁ N₂, P N₁ → P N₂ → P (N₁ ⊓ N₂)) (hsep : ∀ s ∈ K, s ≠ 1 → ∃ N, P N ∧ s ∉ N)
    {ι : Type*} [Finite ι] (β : ι → G) (hcov : ∀ g : G, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * β i * k)
    (hfin : ∀ i, {γ : G | γ ∈ Γ ∧ (β i)⁻¹ * γ * β i ∈ K}.Finite) :
    ∃ N, P N ∧ IsNeat Γ N := by
  set S : Set G := ⋃ i, (fun γ => (β i)⁻¹ * γ * β i) '' {γ : G | γ ∈ Γ ∧ (β i)⁻¹ * γ * β i ∈ K}
  have hS : S.Finite := Set.finite_iUnion fun i => (hfin i).image _
  have hSK : ∀ s ∈ S, s ∈ K := by
    intro s hs
    obtain ⟨i, γ, ⟨-, hγK⟩, rfl⟩ := Set.mem_iUnion.mp hs |>.imp fun _ h => h
    exact hγK
  obtain ⟨N, hN, hNS⟩ := exists_avoiding K P hK hinf hsep hS.toFinset
    (fun s hs => hSK s (hS.mem_toFinset.mp hs))
  refine ⟨N, hN, fun g γ hγ hg => ?_⟩
  obtain ⟨i, δ, hδ, κ, hκ, rfl⟩ := hcov g
  have hconj : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i = κ * ((δ * β i * κ)⁻¹ * γ * (δ * β i * κ)) * κ⁻¹ := by
    group
  have hmem : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i ∈ N := by
    rw [hconj]; exact hPnormal N hN κ hκ _ hg
  have hγ' : δ⁻¹ * γ * δ ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hδ) hγ) hδ
  have hS' : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i ∈ S :=
    Set.mem_iUnion.mpr ⟨i, _, ⟨hγ', hPle N hN hmem⟩, rfl⟩
  have h1 : (β i)⁻¹ * (δ⁻¹ * γ * δ) * β i = 1 := by
    by_contra hne; exact hNS _ (hS.mem_toFinset.mpr hS') hne hmem
  have : δ⁻¹ * γ * δ = 1 := by
    have := congrArg (fun x => β i * x * (β i)⁻¹) h1
    simpa [mul_assoc] using this
  have h2 := congrArg (fun x => δ * x * δ⁻¹) this
  simpa [mul_assoc] using h2

end Abstract

section Mass

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableMul A] [MeasurableMul B]

/-- **The unfolding with a separating family** (`covolume_eq_measure_mul_dcMass` with the filtration replaced by
the hypothesis `hsep`: every $s \in K\setminus 1$ lies outside some measurable subgroup $N \le K$, normal in $K$, of finite
index). Then
$$\mathrm{covol}(\Gamma\backslash(G_\infty\times G_f), \mu_\infty\times\mu_f) = \mu_\infty(G_\infty)\cdot\mu_f(K)\cdot
  \mathrm{dcMass}(\Gamma_f, K).$$
For a profinite $K$ (here $SO(\hat L)$) `hsep` holds with $N$ open normal; no countable basis is needed. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem covolume_eq_measure_mul_dcMass_of_sep (Γ : Subgroup (A × B)) [Countable Γ] (K : Subgroup B)
    (hK : MeasurableSet (K : Set B))
    (hsep : ∀ s ∈ K, s ≠ 1 → ∃ N : Subgroup B, N ≤ K ∧ (∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧
      N.relIndex K ≠ 0 ∧ MeasurableSet (N : Set B) ∧ s ∉ N)
    (hinj : ∀ γ ∈ Γ, γ.2 = 1 → γ = 1)
    [Finite (orbitRel.Quotient (Γ.map (MonoidHom.snd A B)) (B ⧸ K))]
    (hstab : ∀ x : B ⧸ K, Finite (stabilizer (Γ.map (MonoidHom.snd A B)) x))
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant] :
    covolume Γ (A × B) (μA.prod μB) =
      μA univ * μB K * ENNReal.ofReal (dcMass (Γ.map (MonoidHom.snd A B)) K) := by
  set Γf := Γ.map (MonoidHom.snd A B)
  let P : Subgroup B → Prop := fun N => N ≤ K ∧ (∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧
    N.relIndex K ≠ 0 ∧ MeasurableSet (N : Set B)
  have hPK : P K := ⟨le_rfl, fun x hx y hy => K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx),
    by rw [Subgroup.relIndex_self]; exact one_ne_zero, hK⟩
  have hinf : ∀ N₁ N₂, P N₁ → P N₂ → P (N₁ ⊓ N₂) := by
    rintro N₁ N₂ ⟨h1, n1, i1, m1⟩ ⟨h2, n2, i2, m2⟩
    exact ⟨inf_le_left.trans h1, fun x hx y hy => Subgroup.mem_inf.mpr
      ⟨n1 x hx y (Subgroup.mem_inf.mp hy).1, n2 x hx y (Subgroup.mem_inf.mp hy).2⟩,
      Subgroup.relIndex_inf_ne_zero i1 i2, m1.inter m2⟩
  have hsep' : ∀ s ∈ K, s ≠ 1 → ∃ N, P N ∧ s ∉ N := by
    intro s hs hs1
    obtain ⟨N, h1, h2, h3, h4, h5⟩ := hsep s hs hs1
    exact ⟨N, ⟨h1, h2, h3, h4⟩, h5⟩
  obtain ⟨K', ⟨hle, -, hfin, hmeas⟩, hneat⟩ :=
    exists_isNeat_of_reps_sep Γf K P (fun N h => h.1) (fun N h => h.2.1) hPK hinf hsep' (dcRep Γf K)
      (fun g => by
        obtain ⟨γ, hγ, k, hk, h⟩ := exists_eq_mul_dcRep Γf K g
        exact ⟨_, γ, hγ, k, hk, h⟩)
      (fun ω => by
        have := hstab (QuotientGroup.mk (dcRep Γf K ω))
        refine (Set.finite_range (fun s : stabilizer Γf (QuotientGroup.mk (dcRep Γf K ω) : B ⧸ K) =>
          ((s : Γf) : B))).subset ?_
        rintro γ ⟨hγ, hK⟩
        exact ⟨⟨⟨γ, hγ⟩, (mem_stabilizer_coset Γf K _ ⟨γ, hγ⟩).mpr hK⟩, rfl⟩)
  have := finite_orbits_of_relIndex Γf (K := K) (K' := K') hfin
  set h' := Nat.card (orbitRel.Quotient Γf (B ⧸ K'))
  set m := K'.relIndex K
  rw [covolume_eq_of_isNeat Γ K' hinj hneat hmeas μA μB, ← relIndex_mul_measure hle hfin hmeas μB]
  have hdc : dcMass Γf K = (h' : ℝ) / m := by
    have h1 := dcMass_of_isNeat hneat
    have h2 := dcMass_of_le Γf hle hfin hstab
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

/-- **Profinite separation** (abstract): in a Hausdorff totally disconnected topological group with a compact open
subgroup $K$, every $s \in K\setminus 1$ lies outside an open (so Borel-measurable, finite-index) subgroup $N \le K$ normal
in $K$ (Mathlib's `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` on $K$). -/
theorem sep_of_isCompact_isOpen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [TotallyDisconnectedSpace G] (K : Subgroup G)
    (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    ∀ s ∈ K, s ≠ 1 → ∃ N : Subgroup G, N ≤ K ∧ (∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧ N.relIndex K ≠ 0 ∧
      MeasurableSet (N : Set G) ∧ s ∉ N := by
  intro s hs hs1
  have : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have hWo : IsOpen ({⟨s, hs⟩}ᶜ : Set K) := isOpen_compl_singleton
  have hW1 : (1 : K) ∈ ({⟨s, hs⟩}ᶜ : Set K) := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; exact hs1 (congrArg Subtype.val h).symm
  obtain ⟨H', hH'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo hW1
  have hNeq : ((H'.toSubgroup.map K.subtype : Subgroup G) : Set G) = Subtype.val '' (H'.toSubgroup : Set K) := by
    rw [Subgroup.coe_map]; rfl
  have hNo : IsOpen ((H'.toSubgroup.map K.subtype : Subgroup G) : Set G) := by
    rw [hNeq]; exact ho.isOpenEmbedding_subtypeVal.isOpenMap _ H'.isOpen'
  refine ⟨H'.toSubgroup.map K.subtype, Subgroup.map_subtype_le _, ?_,
    relIndex_ne_zero_of_isOpen hc hNo, hNo.measurableSet, ?_⟩
  · intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, H'.isNormal'.conj_mem y hy ⟨x, hx⟩, by simp⟩
  · rintro ⟨y, hy, hys⟩
    have : y = ⟨s, hs⟩ := Subtype.ext hys
    exact hH' hy (by rw [this]; exact Set.mem_singleton _)

/-- **$\sigma$-finiteness from a finite class set** (abstract): if $\Gamma$ is countable, $\Gamma\backslash B/K$ is finite and
$\mu(K) < \infty$ for a left-invariant $\mu$, then $\mu$ is $\sigma$-finite ($B = \bigcup_{\gamma,\omega}\gamma\beta_\omega K$). -/
theorem sigmaFinite_of_finite_dc {B : Type*} [Group B] [MeasurableSpace B] [MeasurableMul B] (μ : Measure B)
    [μ.IsMulLeftInvariant] (Γ K : Subgroup B) [Countable Γ] [Finite (orbitRel.Quotient Γ (B ⧸ K))]
    (hK : μ K < ∞) : SigmaFinite μ := by
  refine Measure.sigmaFinite_of_countable (S := Set.range fun p : Γ × orbitRel.Quotient Γ (B ⧸ K) =>
      ((p.1 : B) * dcRep Γ K p.2) • (K : Set B)) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨p, rfl⟩
    rw [measure_smul μ ((p.1 : B) * dcRep Γ K p.2) (K : Set B)]; exact hK
  · refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨γ, hγ, k, hk, h⟩ := exists_eq_mul_dcRep Γ K g
    refine Set.mem_sUnion.mpr ⟨_, ⟨(⟨γ, hγ⟩, Quotient.mk'' (QuotientGroup.mk g)), rfl⟩, ?_⟩
    exact Set.mem_smul_set.mpr ⟨k, hk, h.symm⟩

end Mass

/-! ### Part 2: the topology and Borel structure of $O(V)(\mathbb A_f)$ and $SO(V)(\mathbb A_f)$ -/

section Adelic

open NumberField IsDedekindDomain QuadFormsKB.Lattices Matrix

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section General

variable (Q : QuadForm F n)

/-- The local stabilizers $O(V)(\mathfrak o_v)$ are open, so the restricted product carries Mathlib's restricted
product topology and is a topological group. -/
instance fact_isOpen_stdStab :
    Fact (∀ v : HeightOneSpectrum (𝓞 F), IsOpen (stdStab Q v : Set (orthGroup Q (v.adicCompletion F)))) :=
  ⟨fun v => isOpen_stdStab v Q⟩

instance compactSpace_stdStab (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (stdStab Q v) :=
  isCompact_iff_compactSpace.mp (isCompact_stdStab v Q)

example : IsTopologicalGroup (OAf Q) := inferInstance
example : LocallyCompactSpace (OAf Q) := inferInstance

/-- **The Borel $\sigma$-algebra on $O(V)(\mathbb A_f)$** (as in FLT's `Constructions/BorelSpace/RestrictedProduct.lean`). -/
instance measurableSpace_OAf : MeasurableSpace (OAf Q) := borel _

instance borelSpace_OAf : BorelSpace (OAf Q) := ⟨rfl⟩

theorem coe_locStab_std :
    (locStab Q (stdLat F n) : Set (OAf Q)) = {f | ∀ v, f.1 v ∈ (stdStab Q v : Set _)} := by
  ext h; exact mem_locStab_intVec Q h

/-- **$O(\hat L)$ is open in $O(V)(\mathbb A_f)$.** -/
theorem isOpen_locStab : IsOpen (locStab Q (stdLat F n) : Set (OAf Q)) := by
  rw [coe_locStab_std]
  exact RestrictedProduct.isOpen_forall_mem (fun v => isOpen_stdStab v Q)

/-- **$O(\hat L) = \prod_v O(L_v)$ is compact** (Tychonoff; it is the image of $\prod_v O(L_v)$ under the structure map). -/
theorem isCompact_locStab : IsCompact (locStab Q (stdLat F n) : Set (OAf Q)) := by
  rw [coe_locStab_std]
  have : CompactSpace ((v : HeightOneSpectrum (𝓞 F)) → (stdStab Q v : Set (orthGroup Q (v.adicCompletion F)))) :=
    @Pi.compactSpace _ _ _ fun v => isCompact_iff_compactSpace.mp (isCompact_stdStab v Q)
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => orthGroup Q (v.adicCompletion F))
    (A := fun v => (stdStab Q v : Set (orthGroup Q (v.adicCompletion F)))) (𝓕 := Filter.cofinite)).continuous
  rwa [RestrictedProduct.range_structureMap] at h

/-- **$SO(V)(\mathbb A_f)$ is closed in $O(V)(\mathbb A_f)$.** -/
theorem isClosed_soAf : IsClosed (soAf Q : Set (OAf Q)) := by
  have : (soAf Q : Set (OAf Q)) =
      ⋂ v, (fun h : OAf Q => ((h v : orthGroup Q _) : GL (Fin n) (v.adicCompletion F)).val.det) ⁻¹' {1} := by
    ext h; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun v => isClosed_singleton.preimage
    ((continuous_det_orth v Q).comp (RestrictedProduct.continuous_eval v))

instance totallyDisconnected_OAf : TotallyDisconnectedSpace (OAf Q) :=
  ⟨isTotallyDisconnected_of_image (f := fun h : OAf Q => (h : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q _))
    RestrictedProduct.continuous_coe.continuousOn (fun a b h => by ext1 v; exact congrFun h v)
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end General

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **$SO(V)(\mathbb A_f)$** as a type: the closed subgroup `soAf QF` of $O(V)(\mathbb A_f)$, with the subspace topology and
the subspace (= Borel) $\sigma$-algebra. -/
abbrev SOAf : Type := soAf QF

example : BorelSpace (SOAf Q₀) := inferInstance
example : IsTopologicalGroup (SOAf Q₀) := inferInstance
example : MeasurableMul (SOAf Q₀) := inferInstance

/-- **$SO(\hat L)$**, $L = \mathcal O_F^n$, as a subgroup of $SO(V)(\mathbb A_f)$ (the $K$ of `tauSO`). -/
abbrev KSO : Subgroup (SOAf Q₀) := (locStab QF (stdLat F n)).subgroupOf (soAf QF)

/-- **$SO(V)(F)$** inside $SO(V)(\mathbb A_f)$ (the $\Gamma$ of `tauSO`). -/
abbrev GammaSOf : Subgroup (SOAf Q₀) := (ratPoints QF).subgroupOf (soAf QF)

theorem isCompact_KSO : IsCompact (KSO Q₀ : Set (SOAf Q₀)) :=
  (isClosed_soAf QF).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_locStab QF)

theorem isOpen_KSO : IsOpen (KSO Q₀ : Set (SOAf Q₀)) :=
  (isOpen_locStab QF).preimage continuous_subtype_val

/-- **$SO(\hat L)$ is profinite:** every $s \ne 1$ in $SO(\hat L)$ lies outside an open (hence measurable, finite-index)
subgroup $N \le SO(\hat L)$ normal in $SO(\hat L)$. -/
theorem sep_KSO : ∀ s ∈ KSO Q₀, s ≠ 1 → ∃ N : Subgroup (SOAf Q₀), N ≤ KSO Q₀ ∧
    (∀ x ∈ KSO Q₀, ∀ y ∈ N, x * y * x⁻¹ ∈ N) ∧ N.relIndex (KSO Q₀) ≠ 0 ∧
    MeasurableSet (N : Set (SOAf Q₀)) ∧ s ∉ N :=
  sep_of_isCompact_isOpen (KSO Q₀) (isCompact_KSO Q₀) (isOpen_KSO Q₀)

/-! ### Part 3: the measure $\mu_f$ on $SO(V)(\mathbb A_f)$ -/

/-- **The finite-adelic normalizing constant** $\prod'_v \mu_v(SO(L_v))$, the product of the masses of the local Tamagawa
measures `muLocSO v Q₀ λ_v` on $SO(L_v)$; it equals $\prod'_v \alpha_v(L, L)/\lambda_v$ (`finFactor_eq`). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1} ω_v)"]
def finFactor (lam : HeightOneSpectrum (𝓞 F) → ℝ) : ℝ :=
  ∏' v, (muLocSO v Q₀ (lam v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal

theorem siegelDensity_self_pos' (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    0 < LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
  simp only [LocalDensity.NF.siegelDensity, ↓reduceIte]
  exact mul_pos (by norm_num) (LatChange.localDensityForm_self_pos v Q₀ hQ)

/-- $\prod'_v \mu_v(SO(L_v)) = \prod'_v \alpha_v(L,L)/\lambda_v$ for $\lambda_v > 0$. -/
theorem finFactor_eq (hQ : Q₀.Nondegenerate) {lam : HeightOneSpectrum (𝓞 F) → ℝ} (hlam : ∀ v, 0 < lam v) :
    finFactor Q₀ lam = ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ / lam v := by
  refine tprod_congr fun v => ?_
  rw [muLocSO_soStabSO, ENNReal.toReal_ofReal (div_pos (siegelDensity_self_pos' Q₀ hQ v) (hlam v)).le]

theorem finFactor_one (hQ : Q₀.Nondegenerate) :
    finFactor Q₀ (fun _ => 1) = ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
  rw [finFactor_eq Q₀ hQ (fun _ => one_pos)]; simp

theorem finFactor_nonneg (lam : HeightOneSpectrum (𝓞 F) → ℝ) : 0 ≤ finFactor Q₀ lam :=
  tprod_nonneg fun _ => ENNReal.toReal_nonneg

/-- **The Tamagawa measure on $SO(V)(\mathbb A_f)$** with convergence factors $(\lambda_v)$: the Haar measure normalized by
$$\mu_f(SO(\hat L)) = \prod'_v \mu_v(SO(L_v)) = \prod'_v \alpha_v(L, L)/\lambda_v$$
(`muLocSO` is the local factor). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1} ω_v)"]
def muFin (lam : HeightOneSpectrum (𝓞 F) → ℝ) : Measure (SOAf Q₀) :=
  haarNorm (KSO Q₀) (isCompact_KSO Q₀) (isOpen_KSO Q₀) (Real.toNNReal (finFactor Q₀ lam))

instance (lam : HeightOneSpectrum (𝓞 F) → ℝ) : (muFin Q₀ lam).IsMulLeftInvariant := by
  unfold muFin; infer_instance

/-- $\mu_f(SO(\hat L)) = \prod'_v \mu_v(SO(L_v))$. -/
theorem muFin_KSO (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    muFin Q₀ lam (KSO Q₀ : Set (SOAf Q₀)) = ENNReal.ofReal (finFactor Q₀ lam) :=
  haarNorm_self _ _ _

end Adelic

/-! ### Part 4: the archimedean factor, the diagonal $\Gamma$, and $\tau(SO) = \mathrm{covol}$ -/

section Global

open NumberField IsDedekindDomain QuadFormsKB.Lattices Matrix QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- A number field is countable. -/
local instance countable_numberField : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem countable_orthGroup : Countable (orthGroup QF F) := by
  have : Countable (Matrix (Fin n) (Fin n) F) := inferInstanceAs (Countable (Fin n → Fin n → F))
  exact Function.Injective.countable (f := fun g : orthGroup QF F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    fun a b h => Subtype.ext (Units.ext h)

theorem countable_soSub : Countable (soSub QF F) := by
  have := countable_orthGroup Q₀
  exact Function.Injective.countable (f := fun g : soSub QF F => (g : orthGroup QF F)) Subtype.val_injective

/-- $\Gamma_f = SO(V)(F)$ is countable. -/
theorem countable_GammaSOf : Countable (GammaSOf Q₀) := by
  have := countable_orthGroup Q₀
  have hR : Countable (ratPoints QF) := by
    have h : ((ratPoints QF : Subgroup (OAf QF)) : Set (OAf QF)) = Set.range (diagF QF) := MonoidHom.coe_range _
    have := (h ▸ Set.countable_range (diagF QF)).to_subtype
    exact this
  exact Function.Injective.countable (f := fun γ : GammaSOf Q₀ => (⟨((γ : SOAf Q₀) : OAf QF), γ.2⟩ : ratPoints QF))
    fun a b h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))

/-! #### $SO$-level finiteness of the class set and of the stabilizers -/

/-- **Finite stabilizers at the $SO$ level:** $\Gamma_f \cap \alpha\,SO(\hat L)\,\alpha^{-1}$ is finite (it embeds in the
finite group $O(V)(F) \cap \alpha\,O(\hat L)\,\alpha^{-1}$, `finite_stabilizer`). -/
theorem finite_stabilizer_SO (hpd : IsTotallyPosDef QF) (hLi : IsIntegral QF (stdLat F n).1)
    (x : SOAf Q₀ ⧸ KSO Q₀) : Finite (stabilizer (GammaSOf Q₀) x) := by
  induction x using QuotientGroup.induction_on with | H α => ?_
  have hO := finite_stabilizer hpd (stdLat F n) hLi (QuotientGroup.mk (α : OAf QF))
  have hmem : ∀ s : stabilizer (GammaSOf Q₀) (QuotientGroup.mk α : SOAf Q₀ ⧸ KSO Q₀),
      (⟨((s : GammaSOf Q₀) : SOAf Q₀), (s : GammaSOf Q₀).2⟩ : ratPoints QF) ∈
        stabilizer (ratPoints QF) (QuotientGroup.mk (α : OAf QF) : OAf QF ⧸ locStab QF (stdLat F n)) := by
    intro s
    rw [mem_stabilizer_coset]
    exact (mem_stabilizer_coset (GammaSOf Q₀) (KSO Q₀) α (s : GammaSOf Q₀)).mp s.2
  exact Finite.of_injective (fun s => (⟨_, hmem s⟩ : stabilizer (ratPoints QF)
      (QuotientGroup.mk (α : OAf QF) : OAf QF ⧸ locStab QF (stdLat F n))))
    fun a b h => Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun t => ((t.1 : ratPoints QF) : OAf QF)) h)))

/-- **Finitely many $SO$-classes:** $\Gamma_f\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ is finite. The map
$SO(V)(\mathbb A_f)/SO(\hat L) \to O(V)(\mathbb A_f)/O(\hat L)$ is injective and equivariant for
$SO(V)(F) = O(V)(F) \cap SO(V)(\mathbb A_f)$, which has index $2$ in $O(V)(F)$ (`index_soAf_ratPoints`); the
$O(V)(F)$-orbits are finite (`finite_orbits`), hence so are the orbits of the index-$2$ subgroup
(`finite_orbits_of_finiteIndex`). -/
theorem finite_orbits_SO (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) :
    Finite (orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀)) := by
  have := finite_orbits hpd (stdLat F n) hLi
  set H' : Subgroup (ratPoints QF) := (soAf QF).subgroupOf (ratPoints QF)
  have : H'.FiniteIndex := ⟨by rw [index_soAf_ratPoints Q₀ hQ hn]; norm_num⟩
  have hfin := finite_orbits_of_finiteIndex (X := OAf QF ⧸ locStab QF (stdLat F n)) H'
  let ι : SOAf Q₀ ⧸ KSO Q₀ → OAf QF ⧸ locStab QF (stdLat F n) :=
    Quotient.map' (fun a : SOAf Q₀ => (a : OAf QF)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact hab)
  have hι : ∀ a : SOAf Q₀, ι (QuotientGroup.mk a) = QuotientGroup.mk (a : OAf QF) := fun _ => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [hι, hι, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hab
  let e : GammaSOf Q₀ → H' := fun γ => ⟨⟨((γ : SOAf Q₀) : OAf QF), γ.2⟩, (γ : SOAf Q₀).2⟩
  have hcomm : ∀ (γ : GammaSOf Q₀) (y : SOAf Q₀ ⧸ KSO Q₀), ι (γ • y) = e γ • ι y := by
    intro γ y
    induction y using QuotientGroup.induction_on with | H a => rfl
  let Φ : orbitRel.Quotient (GammaSOf Q₀) (SOAf Q₀ ⧸ KSO Q₀) →
      orbitRel.Quotient H' (OAf QF ⧸ locStab QF (stdLat F n)) :=
    Quotient.map' ι (fun a b hab => by
      have hab' : a ∈ orbit (GammaSOf Q₀) b := hab
      obtain ⟨γ, rfl⟩ := hab'
      show ι (γ • b) ∈ orbit H' (ι b)
      exact ⟨e γ, (hcomm γ b).symm⟩)
  refine Finite.of_injective Φ ?_
  intro p q hpq
  induction p using Quotient.inductionOn' with | h a => ?_
  induction q using Quotient.inductionOn' with | h b => ?_
  have h1 : ι a ∈ orbit H' (ι b) := Quotient.exact' hpq
  obtain ⟨h, hh⟩ := h1
  apply Quotient.sound'
  show a ∈ orbit (GammaSOf Q₀) b
  let γ : GammaSOf Q₀ := ⟨⟨((h : ratPoints QF) : OAf QF), h.2⟩, (h : ratPoints QF).2⟩
  exact ⟨γ, hιinj (by rw [hcomm]; exact hh)⟩

/-- **$\mu_f$ is $\sigma$-finite:** $SO(V)(\mathbb A_f) = \bigcup_{\gamma, \omega}\gamma\,\beta_\omega\,SO(\hat L)$ is a countable
union of translates of the compact open $SO(\hat L)$ ($\Gamma_f$ countable, finitely many classes $\omega$). -/
theorem sigmaFinite_muFin (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) (lam : HeightOneSpectrum (𝓞 F) → ℝ) : SigmaFinite (muFin Q₀ lam) := by
  have := finite_orbits_SO Q₀ hQ hn hpd hLi
  have := countable_GammaSOf Q₀
  refine sigmaFinite_of_finite_dc (muFin Q₀ lam) (GammaSOf Q₀) (KSO Q₀) ?_
  rw [muFin_KSO]; exact ENNReal.ofReal_lt_top

/-! #### The real places -/

variable [IsTotallyReal F]

/-- **The real embedding** $\rho_\sigma : F \to \mathbb R$ underlying an embedding $\sigma : F \to \mathbb C$ of the totally real
field $F$. -/
def realEmb (σ : F →ₐ[ℚ] ℂ) : F →+* ℝ :=
  (IsTotallyReal.complexEmbedding_isReal (σ : F →+* ℂ)).embedding

theorem realEmb_apply (σ : F →ₐ[ℚ] ℂ) (x : F) : ((realEmb σ x : ℝ) : ℂ) = σ x :=
  ComplexEmbedding.IsReal.coe_embedding_apply _ x

/-- **The real form at $\sigma$:** $Q_\sigma = \rho_\sigma(Q_0)$ on $\mathbb R^n$. -/
abbrev realQ (σ : F →ₐ[ℚ] ℂ) : QuadForm ℝ n := Q₀.map ((realEmb σ).comp (algebraMap (𝓞 F) F))

omit [IsTotallyReal F] in
theorem eval_map_real (ρ : F →+* ℝ) (x : Fin n → F) :
    (Q₀.map (ρ.comp (algebraMap (𝓞 F) F))).eval (fun i => ρ (x i)) = ρ ((QF).eval x) := by
  simp [QuadForm.evalIn, QuadForm.map, map_sum, apply_ite, map_mul]

omit [IsTotallyReal F] in
/-- **Totally positive definite $\Rightarrow$ positive definite at every real embedding.** $Q_\rho > 0$ on $\mathbb Q^n\setminus 0$,
hence $Q_\rho \ge 0$ on $\mathbb R^n$ by density; a positive semidefinite form with $\det H \ne 0$ is definite. -/
theorem isPosDefR_map (ρ : F →+* ℝ) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF) :
    IsPosDefR (Q₀.map (ρ.comp (algebraMap (𝓞 F) F))) := by
  set R := Q₀.map (ρ.comp (algebraMap (𝓞 F) F))
  have h1 : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < R.eval (fun i => (x i : ℝ)) := by
    intro x hx
    have hy : (fun i => (x i : F)) ≠ 0 := by
      intro h; apply hx; funext i; have := congrFun h i; simpa using this
    have hpos := hpd _ hy ((Complex.ofRealHom.comp ρ).toRatAlgHom)
    have e : R.eval (fun i => (x i : ℝ)) = ρ ((QF).eval fun i => (x i : F)) := by
      rw [← eval_map_real]; simp only [map_ratCast]; rfl
    rw [e]
    exact Complex.zero_lt_real.mp hpos
  have hcont : Continuous fun y : Fin n → ℝ => R.eval y := by
    simp only [QuadForm.evalIn]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · fun_prop
    · exact continuous_const
  have h2 : ∀ y : Fin n → ℝ, 0 ≤ R.eval y := by
    intro y
    have hd : DenseRange (Pi.map fun _ : Fin n => ((↑) : ℚ → ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on y (isClosed_le continuous_const hcont) fun x => ?_
    by_cases hx : x = 0
    · subst hx; simp [QuadForm.evalIn, Pi.map]
    · exact (h1 x hx).le
  intro y hy
  rcases (h2 y).lt_or_eq with h | h
  · exact h
  exfalso
  set H := R.hessian with hH
  have hHs : Hᵀ = H := by simp [H, QuadForm.hessian, Matrix.transpose_add, add_comm]
  have hexp : ∀ (z : Fin n → ℝ) (t : ℝ),
      R.eval (y + t • z) = R.eval y + t * (y ⬝ᵥ (H *ᵥ z)) + t ^ 2 * R.eval z := by
    intro z t
    rw [eval_eq_dotProduct_hessian, eval_eq_dotProduct_hessian, eval_eq_dotProduct_hessian, ← hH]
    have hsw : z ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ z) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hHs, dotProduct_comm]
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hsw]
    ring
  have hb : ∀ z, y ⬝ᵥ (H *ᵥ z) = 0 := by
    intro z
    set b := y ⬝ᵥ (H *ᵥ z)
    set c := R.eval z
    have key : ∀ t : ℝ, 0 ≤ t * b + t ^ 2 * c := by
      intro t; have := h2 (y + t • z); rw [hexp, ← h] at this; linarith
    by_contra hb0
    have hc1 : 0 < |c| + 1 := by positivity
    set s := -b / (|c| + 1)
    have e : s * b + s ^ 2 * |c| = -b ^ 2 / (|c| + 1) ^ 2 := by
      simp only [s]; field_simp; ring
    have hneg : -b ^ 2 / (|c| + 1) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_ne_zero hb0]) (by positivity)
    nlinarith [key s, mul_le_mul_of_nonneg_left (le_abs_self c) (sq_nonneg s)]
  have hHy : H *ᵥ y = 0 := by
    funext i
    have := hb (Pi.single i 1)
    rw [dotProduct_mulVec, ← mulVec_transpose, hHs, dotProduct_single, mul_one] at this
    exact this
  have hdet : H.det ≠ 0 := by
    simp only [H, R]
    rw [hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ (fun a b h => RingOfIntegers.coe_injective (ρ.injective h))).mpr hQ
  exact hy (Matrix.eq_zero_of_mulVec_eq_zero hdet hHy)

theorem isPosDefR_realQ (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF) (σ : F →ₐ[ℚ] ℂ) :
    IsPosDefR (realQ Q₀ σ) :=
  isPosDefR_map Q₀ (realEmb σ) hQ hpd

/-! #### The diagonal embedding of $SO(V)(F)$ -/

/-- $\gamma \mapsto \rho_\sigma(\gamma)$: $SO(V)(F) \to SO(Q_\sigma)(\mathbb R)$. -/
def archHom (σ : F →ₐ[ℚ] ℂ) : soSub QF F →* ArchSO (realQ Q₀ σ) :=
  ((Matrix.GeneralLinearGroup.map (realEmb σ)).comp ((orthGroup QF F).subtype.comp (soSub QF F).subtype)).codRestrict
    (soReal (realQ Q₀ σ)) fun γ => by
      set M := ((γ : orthGroup QF F) : GL (Fin n) F).val
      have hM : ((Matrix.GeneralLinearGroup.map (realEmb σ)).comp ((orthGroup QF F).subtype.comp
          (soSub QF F).subtype) γ : Matrix (Fin n) (Fin n) ℝ) = M.map (realEmb σ) := rfl
      have hγ := (mem_orthGroup QF).mp (γ : orthGroup QF F).2
      have hH : (realQ Q₀ σ).hessian = (QF).hessian.map (realEmb σ) := by
        rw [hessian_map_NF, hessian_map_NF, Matrix.map_map, RingHom.coe_comp]
      have hid : (QF).hessian.map (algebraMap F F) = (QF).hessian := by
        rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
      rw [hid] at hγ
      rw [mem_soReal_iff, hM, hH]
      refine ⟨?_, ?_⟩
      · rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hγ]
      · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, show M.det = 1 from mem_soSub.mp γ.2, map_one]

/-- $\gamma \mapsto (\gamma)_v$: $SO(V)(F) \to SO(V)(\mathbb A_f)$. -/
def finHom : soSub QF F →* SOAf Q₀ :=
  ((diagF QF).comp (soSub QF F).subtype).codRestrict (soAf QF) fun γ v => by
    show (((diagF QF (γ : orthGroup QF F)) v : orthGroup QF _) : GL (Fin n) (v.adicCompletion F)).val.det = 1
    rw [det_diagF, show ((γ : orthGroup QF F) : GL (Fin n) F).val.det = 1 from mem_soSub.mp γ.2, map_one]

/-- **The diagonal embedding** $SO(V)(F) \to G_\infty \times SO(V)(\mathbb A_f)$,
$\gamma \mapsto ((\rho_\sigma(\gamma))_\sigma, (\gamma)_v)$. -/
def diagSO : soSub QF F →* ArchSOProd (realQ Q₀) × SOAf Q₀ :=
  (MonoidHom.pi fun σ => archHom Q₀ σ).prod (finHom Q₀)

/-- **$\Gamma = SO(V)(F)$, diagonally in $SO(V)(\mathbb A) = G_\infty\times SO(V)(\mathbb A_f)$.** -/
@[kb "weil1982" "§2.4, p. 23 (G_k ⊂ G_𝔸)"]
def GammaSO : Subgroup (ArchSOProd (realQ Q₀) × SOAf Q₀) := (diagSO Q₀).range

theorem countable_GammaSO : Countable (GammaSO Q₀) := by
  have := countable_soSub Q₀
  have h : ((GammaSO Q₀ : Subgroup _) : Set (ArchSOProd (realQ Q₀) × SOAf Q₀)) = Set.range (diagSO Q₀) :=
    MonoidHom.coe_range _
  have := (h ▸ Set.countable_range (diagSO Q₀)).to_subtype
  exact this

/-- $\Gamma \to SO(V)(\mathbb A_f)$ is injective. -/
theorem GammaSO_inj : ∀ γ ∈ GammaSO Q₀, γ.2 = 1 → γ = 1 := by
  rintro _ ⟨g, rfl⟩ h
  have h1 : diagF QF (g : orthGroup QF F) = 1 := congrArg Subtype.val h
  have hg : g = 1 := Subtype.ext (diagF_injective QF (h1.trans (map_one _).symm))
  rw [hg, map_one]

/-- **The finite-adelic projection of $\Gamma$ is the $\Gamma$ of `tauSO`:** $\Gamma_f = SO(V)(F)$ = `(ratPoints QF).subgroupOf
(soAf QF)` (a rational isometry in $SO(V)(\mathbb A_f)$ has determinant $1$). -/
theorem map_snd_GammaSO : (GammaSO Q₀).map (MonoidHom.snd _ _) = GammaSOf Q₀ := by
  ext x
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨(g : orthGroup QF F), rfl⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨v₀⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)))
    have hγ' : diagF QF γ = (x : OAf QF) := hγ
    have hdet : (γ : GL (Fin n) F).val.det = 1 := by
      have : (((x : OAf QF) v₀ : orthGroup QF _) : GL (Fin n) (v₀.adicCompletion F)).val.det = 1 := x.2 v₀
      rw [← hγ', det_diagF] at this
      exact (algebraMap F (v₀.adicCompletion F)).injective (by rw [this, map_one])
    exact ⟨_, ⟨⟨γ, hdet⟩, rfl⟩, Subtype.ext hγ'⟩

/-! #### The measure on $SO(V)(\mathbb A)$ and the covolume -/

/-- Weil's global factor $c_F = |d_F|^{-\dim SO_n/2} = |d_F|^{-n(n-1)/4}$ (Weil 1982, §2.3, p. 21: $\mu_k^{-\dim}$ with
$\mu_k = |d_F|^{1/2}$, §2.1.3). -/
def cF (F : Type) [Field F] [NumberField F] (n : ℕ) : ℝ := |(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4))

theorem cF_nonneg : 0 ≤ cF F n := Real.rpow_nonneg (abs_nonneg _) _

/-- **The archimedean Tamagawa factor** $c_F\cdot\mu_\infty$ on $G_\infty = \prod_\sigma SO(Q_\sigma)(\mathbb R)$, with
$\mu_\infty = \prod_\sigma\mu_\sigma$ (`ArchSO.lean`, $\mu_\sigma(SO(Q_\sigma)(\mathbb R)) = $ `archVolSO`). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure)"]
def muInfTam (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF) : Measure (ArchSOProd (realQ Q₀)) :=
  haveI : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
  ENNReal.ofReal (cF F n) • muInf (realQ Q₀)

/-- **The Tamagawa measure on $SO(V)(\mathbb A) = G_\infty \times SO(V)(\mathbb A_f)$** with convergence factors $(\lambda_v)$:
$\mu_{\mathbb A} = c_F\,\mu_\infty \times \mu_f$ (`muAdele_eq_smul`). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure (ω,(λ_v)))"]
def muAdele (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF) (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    Measure (ArchSOProd (realQ Q₀) × SOAf Q₀) :=
  (muInfTam Q₀ hQ hpd).prod (muFin Q₀ lam)

theorem muAdele_eq_smul (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    haveI : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
    muAdele Q₀ hQ hpd lam = ENNReal.ofReal (cF F n) • (muInf (realQ Q₀)).prod (muFin Q₀ lam) := by
  have := sigmaFinite_muFin Q₀ hQ hn hpd hLi lam
  unfold muAdele muInfTam
  rw [Measure.prod_smul_left]

theorem muInfTam_univ (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef QF) :
    muInfTam Q₀ hQ hpd univ =
      ENNReal.ofReal (cF F n) * ∏ σ : F →ₐ[ℚ] ℂ, ENNReal.ofReal (archVolSO n (detGram Q₀ σ)) := by
  have : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
  rw [muInfTam, Measure.smul_apply, smul_eq_mul,
    muInf_univ_detGram (realQ Q₀) Q₀ (fun σ => σ) (fun σ => realEmb σ) (fun σ x => (realEmb_apply σ x).symm)
      (fun σ => rfl)]

/-- **Covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ for every choice of convergence factors:**
$$\mathrm{covol}(SO(V)(F)\backslash SO(V)(\mathbb A), \mu_{\mathbb A}) = c_F\cdot\prod_\sigma\mathrm{vol}(SO(V_\sigma))\cdot
  \prod'_v\mu_v(SO(L_v))\cdot\mathrm{mass}_{SO}.$$ -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem covolume_muAdele (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    covolume (GammaSO Q₀) (ArchSOProd (realQ Q₀) × SOAf Q₀) (muAdele Q₀ hQ hpd lam) =
      ENNReal.ofReal (cF F n) * (∏ σ : F →ₐ[ℚ] ℂ, ENNReal.ofReal (archVolSO n (detGram Q₀ σ))) *
        ENNReal.ofReal (finFactor Q₀ lam) * ENNReal.ofReal (dcMass (GammaSOf Q₀) (KSO Q₀)) := by
  have : ∀ σ, Fact (IsPosDefR (realQ Q₀ σ)) := fun σ => ⟨isPosDefR_realQ Q₀ hQ hpd σ⟩
  have := countable_GammaSO Q₀
  have := sigmaFinite_muFin Q₀ hQ hn hpd hLi lam
  have : SFinite (muInfTam Q₀ hQ hpd) := by unfold muInfTam; infer_instance
  have : (muInfTam Q₀ hQ hpd).IsMulLeftInvariant := by unfold muInfTam; infer_instance
  have hmap := map_snd_GammaSO Q₀
  have hfin : Finite (orbitRel.Quotient ((GammaSO Q₀).map (MonoidHom.snd _ _)) (SOAf Q₀ ⧸ KSO Q₀)) := by
    rw [hmap]; exact finite_orbits_SO Q₀ hQ hn hpd hLi
  have hstab : ∀ x : SOAf Q₀ ⧸ KSO Q₀, Finite (stabilizer ((GammaSO Q₀).map (MonoidHom.snd _ _)) x) := by
    intro x; rw [hmap]; exact finite_stabilizer_SO Q₀ hpd hLi x
  unfold muAdele
  rw [covolume_eq_measure_mul_dcMass_of_sep (GammaSO Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet
    (sep_KSO Q₀) (GammaSO_inj Q₀) hstab (muInfTam Q₀ hQ hpd) (muFin Q₀ lam), hmap, muInfTam_univ, muFin_KSO]

theorem archVolSO_detGram_pos (hQ : Q₀.Nondegenerate) (σ : F →ₐ[ℚ] ℂ) : 0 < archVolSO n (detGram Q₀ σ) := by
  refine archVolSO_pos n (norm_pos_iff.mpr ?_)
  rw [map_div₀, div_ne_zero_iff]
  refine ⟨(map_ne_zero_iff _ σ.toRingHom.injective).mpr ?_, (map_ne_zero_iff _ σ.toRingHom.injective).mpr
    (pow_ne_zero _ two_ne_zero)⟩
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ

theorem dcMass_nonneg' {G : Type*} [Group G] (Γ K : Subgroup G) : 0 ≤ dcMass Γ K := by
  unfold dcMass orbitMass
  exact finsum_nonneg fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem tamagawaK_nonneg (hQ : Q₀.Nondegenerate) : 0 ≤ tamagawaK Q₀ := by
  unfold tamagawaK
  refine mul_nonneg (mul_nonneg (cF_nonneg (F := F) (n := n)) ?_) ?_
  · exact Finset.prod_nonneg fun σ _ => (archVolSO_detGram_pos Q₀ hQ σ).le
  · exact tprod_nonneg fun v => (siegelDensity_self_pos' Q₀ hQ v).le

theorem tauSO_nonneg (hQ : Q₀.Nondegenerate) : 0 ≤ tauSO Q₀ :=
  mul_nonneg (tamagawaK_nonneg Q₀ hQ) (dcMass_nonneg' _ _)

/-- **$\tau(SO(V))$ is the Tamagawa covolume** (definite case; Weil 1982, §2.4, p. 23: $\tau(G) = \mathrm{vol}(G_{\mathbb A}/G_k)$
for the Tamagawa measure; Lemma 2.4.2, p. 26 for the unfolding). For $Q_0$ over $\mathcal O_F$ nondegenerate, $n \ge 1$,
$Q_0 \otimes F$ totally positive definite and $\mathcal O_F^n$ integral, with convergence factors $\lambda_v = 1$:
$$\texttt{tauSO}\ Q_0 = \mathrm{covol}\bigl(SO(V)(F)\backslash SO(V)(\mathbb A),\ \mu_{\mathbb A}\bigr),$$
where $\Gamma = SO(V)(F)$ is embedded diagonally in $SO(V)(\mathbb A) = \prod_\sigma SO(V_\sigma)(\mathbb R)\times SO(V)(\mathbb A_f)$
and $\mu_{\mathbb A} = c_F\,\mu_\infty\times\mu_f$ is a genuine Haar measure. So the definition of `tauSO` as
$\mu_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{mass}_{SO}$ agrees with Weil's $\tau(SO(V))$. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); Lemma 2.4.2, p. 26"]
theorem tauSO_eq_covolume (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) :
    covolume (GammaSO Q₀) (ArchSOProd (realQ Q₀) × SOAf Q₀) (muAdele Q₀ hQ hpd fun _ => 1) =
      ENNReal.ofReal (tauSO Q₀) := by
  have hprod : 0 ≤ ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ) :=
    Finset.prod_nonneg fun σ _ => (archVolSO_detGram_pos Q₀ hQ σ).le
  have htp : 0 ≤ ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
    tprod_nonneg fun v => (siegelDensity_self_pos' Q₀ hQ v).le
  have hK : tamagawaK Q₀ = cF F n * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) *
      ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ := rfl
  rw [covolume_muAdele Q₀ hQ hn hpd hLi, finFactor_one Q₀ hQ, tauSO, hK,
    ENNReal.ofReal_mul (mul_nonneg (mul_nonneg cF_nonneg hprod) htp),
    ENNReal.ofReal_mul (mul_nonneg cF_nonneg hprod), ENNReal.ofReal_mul cF_nonneg,
    ENNReal.ofReal_prod_of_nonneg fun σ _ => (archVolSO_detGram_pos Q₀ hQ σ).le]

/-- Real form of `tauSO_eq_covolume`. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k))"]
theorem tauSO_eq_covolume_toReal (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) :
    tauSO Q₀ = (covolume (GammaSO Q₀) (ArchSOProd (realQ Q₀) × SOAf Q₀) (muAdele Q₀ hQ hpd fun _ => 1)).toReal := by
  rw [tauSO_eq_covolume Q₀ hQ hn hpd hLi, ENNReal.toReal_ofReal (tauSO_nonneg Q₀ hQ)]

/-- **`TamagawaNumberTwo` is the statement that the Tamagawa covolume is $2$:**
$\tau(SO(V)) = 2 \iff \mathrm{covol}(SO(V)(F)\backslash SO(V)(\mathbb A), \mu_{\mathbb A}) = 2$. -/
@[kb "weil1982" "§2.4, p. 23; Ch. IV (τ(SO) = 2) [unverified]"]
theorem tamagawaNumberTwo_iff_covolume (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) :
    TamagawaNumberTwo Q₀ ↔
      covolume (GammaSO Q₀) (ArchSOProd (realQ Q₀) × SOAf Q₀) (muAdele Q₀ hQ hpd fun _ => 1) = 2 := by
  rw [tauSO_eq_covolume Q₀ hQ hn hpd hLi, TamagawaNumberTwo, ← ENNReal.ofReal_ofNat 2,
    ENNReal.ofReal_eq_ofReal_iff (tauSO_nonneg Q₀ hQ) (by norm_num)]

end Global

end QuadFormsKB.Tamagawa.Measure

