/-
# O'Meara §21, §33H: Dedekind axioms for subsets of spots; class number at a set of spots

**Setting.** As in `Sec21.lean`. `ClassGroupAt K S` is the ideal class group $I(S)/P(S)$ of O'Meara 22C for a set
$S$ of primes of a Dedekind domain, defined as the group of invertible fractional ideals modulo the products of a
principal ideal and an ideal supported outside $S$ (this is the same group as fractional ideals of $\mathfrak o(S)$
modulo principal ones; the ring $\mathfrak o(S)$ itself is not constructed).

**Proves** (number field $F$)
* 33:12 `dedekindAxiomsOn_numberField`: every non-empty set of finite primes satisfies (D1)-(D3), and $\Omega \ne S$;
* 33:13 `finite_classGroupAt`: $h_F(S) < \infty$ for every $S$ (quotient of $\mathrm{Cl}(\mathcal O_F)$);
* 33:13a `exists_finite_set_classGroupAt_subsingleton`: $h_F(S) = 1$ whenever $S$ avoids a suitable finite set $T$.

*Proof notes.* Finiteness is transported from Mathlib's `ClassGroup (𝓞 F)` along the surjection `ClassGroup.mk`;
the book's proof (bounding norms of ideal representatives via idèles) is not followed.
-/
import Mathlib.NumberTheory.NumberField.ClassNumber
import QuadFormsKB.Literature.OMeara.Sec21
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain FractionalIdeal WithZero
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.OMeara

section ClassGroupAt

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The invertible fractional ideals that are trivial at every spot of $S$ (their order at each $\mathfrak p \in S$
is $0$), i.e. the fractional ideals supported outside $S$. -/
def outsideIdeals (S : Set (HeightOneSpectrum R)) : Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {I | ∀ v ∈ S, count K v (I : FractionalIdeal R⁰ K) = 0}
  mul_mem' := by
    intro I J hI hJ v hv
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv]; rfl
  one_mem' := fun v _ => by simpa using count_one K v
  inv_mem' := by
    intro I hI v hv
    have : ((I⁻¹ : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = (I : FractionalIdeal R⁰ K)⁻¹ := by
      simp
    rw [this, count_inv, hI v hv]; rfl

/-- The subgroup of invertible fractional ideals that are principal at $S$: products of a principal ideal
and an ideal supported outside $S$. The fractional ideals at $S$ are the quotient of all fractional ideals by the
ideals supported outside $S$ (restriction of the order function to $S$), and the principal ideals at $S$ are the
images of the principal ideals, so the ideal class group at $S$ is the quotient by this subgroup. -/
def principalAt (S : Set (HeightOneSpectrum R)) : Subgroup (FractionalIdeal R⁰ K)ˣ :=
  outsideIdeals K S ⊔ (toPrincipalIdeal R K).range

/-- **The ideal class group $I(S)/P(S)$ of O'Meara §22C at a set $S$ of spots** of the Dedekind domain $\mathfrak o$:
$I(S) = J/J_{S^c}$ is the group of fractional ideals at $S$ (ideals with their orders at the spots outside $S$
forgotten) and $P(S)$ the image of the principal ideals. Its order is the class number $h_F(S)$. -/
@[kb "omeara1963" "§22C, p. 48 (ideal class group of F at S, class number h_F(S))"]
abbrev ClassGroupAt (S : Set (HeightOneSpectrum R)) : Type _ :=
  (FractionalIdeal R⁰ K)ˣ ⧸ principalAt K S


theorem classGroup_mk_surjective : Function.Surjective (ClassGroup.mk K : (FractionalIdeal R⁰ K)ˣ →* ClassGroup R) := by
  intro c
  obtain ⟨J, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨Units.map (↑(canonicalEquiv R⁰ (FractionRing R) K)) J, ?_⟩
  rw [ClassGroup.mk_canonicalEquiv]
  exact (ClassGroup.Quot_mk_eq_mk J).symm

theorem inv_mul_mem_range_of_mk_eq {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) : I⁻¹ * J ∈ (toPrincipalIdeal R K).range := by
  have h1 : ClassGroup.mk K (I⁻¹ * J) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨g, hg⟩ := (ClassGroup.mk_eq_one_iff.1 h1).principal
  rw [mem_principal_ideals_iff]
  refine ⟨g, ?_⟩
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [coe_spanSingleton]
  exact hg.symm

end ClassGroupAt

section DedekindOn

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **The Dedekind axioms (D1)–(D3) for a subset $S$ of the primes** of a Dedekind domain $\mathfrak o$ (O'Meara §21;
`DedekindAxioms` is the case of all primes): $S$ non-empty, every spot discrete, $|a|_{\mathfrak p} \le 1$ for almost
all $\mathfrak p \in S$, and the approximation property (D3) for two distinct spots of $S$ with all other spots of
$S$ integral. -/
@[kb "omeara1963" "§21, p. 42 (Dedekind axioms (D1)-(D3) for a set S of spots)"]
def DedekindAxiomsOn (S : Set (HeightOneSpectrum R)) : Prop :=
  S.Nonempty ∧ (∀ v ∈ S, (v.valuation K).IsNontrivial) ∧
  (∀ a : K, {v | v ∈ S ∧ ¬ v.valuation K a ≤ 1}.Finite) ∧
  ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ∀ ε : ℤᵐ⁰, ε ≠ 0 → ∃ a : K,
    v.valuation K (a - 1) < ε ∧ w.valuation K a < ε ∧
      ∀ u ∈ S, u ≠ v → u ≠ w → u.valuation K a ≤ 1

theorem dedekindAxiomsOn_of_nonempty {S : Set (HeightOneSpectrum R)} (hS : S.Nonempty) :
    DedekindAxiomsOn K S := by
  refine ⟨hS, fun v _ => inferInstance, fun a => ?_, fun v _ w _ hvw ε hε => ?_⟩
  · have := Filter.eventually_cofinite.1 (valuation_le_one_cofinite (R := R) K a)
    exact this.subset fun v hv => hv.2
  · obtain ⟨a, h1, h2, h3⟩ := exists_approx_pair K v w hvw hε
    exact ⟨a, h1, h2, fun u _ hu1 hu2 => h3 u hu1 hu2⟩

end DedekindOn


section NumberField

variable (F : Type*) [Field F] [NumberField F]

/-- **O'Meara 33:13.** The ideal class number $h_F(S)$ is finite: for every set $S$ of primes of the number
field $F$ (in particular for every Dedekind set), the class group of $F$ at $S$ is finite, being a quotient of the
finite class group of $\mathcal O_F$. -/
@[kb "omeara1963" "§33H, 33:13, p. 79"]
theorem finite_classGroupAt (S : Set (HeightOneSpectrum (𝓞 F))) : Finite (ClassGroupAt F S) := by
  classical
  have hsurj := classGroup_mk_surjective (R := 𝓞 F) F
  let g : ClassGroup (𝓞 F) → ClassGroupAt F S :=
    fun c => (QuotientGroup.mk (Classical.choose (hsurj c)) : ClassGroupAt F S)
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨ClassGroup.mk F x, ?_⟩
    have hy := Classical.choose_spec (hsurj (ClassGroup.mk F x))
    show (QuotientGroup.mk (Classical.choose (hsurj (ClassGroup.mk F x))) : ClassGroupAt F S) = _
    rw [QuotientGroup.eq]
    exact Subgroup.mem_sup_right (inv_mul_mem_range_of_mk_eq F hy)
  exact Finite.of_surjective g hg

/-- **O'Meara 33:13a.** There is a finite set $T$ of primes of $F$ such that the class number $h_F(S) = 1$ for every
set $S$ of primes disjoint from $T$, i.e. for every $S \subseteq S_0$ with $S_0$ the Dedekind set of all primes
outside $T$ (almost all spots). -/
@[kb "omeara1963" "§33H, 33:13a, p. 80"]
theorem exists_finite_set_classGroupAt_subsingleton :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Set (HeightOneSpectrum (𝓞 F)),
      Disjoint S (T : Set _) → Subsingleton (ClassGroupAt F S) := by
  classical
  have hsurj := classGroup_mk_surjective (R := 𝓞 F) F
  choose r hr using hsurj
  let T : Finset (HeightOneSpectrum (𝓞 F)) := Finset.univ.biUnion fun c : ClassGroup (𝓞 F) =>
    (Filter.eventually_cofinite.1 (finite_factors ((r c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F))).toFinset
  refine ⟨T, fun S hS => ⟨fun a b => ?_⟩⟩
  have key : ∀ q : ClassGroupAt F S, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hrc : r (ClassGroup.mk F x) ∈ outsideIdeals F S := by
      intro v hv
      by_contra hne
      have : v ∈ T := by
        simp only [T, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
        exact ⟨ClassGroup.mk F x, hne⟩
      exact Set.disjoint_left.1 hS hv (Finset.mem_coe.2 this)
    rw [QuotientGroup.eq_one_iff]
    have h2 := inv_mul_mem_range_of_mk_eq F (hr (ClassGroup.mk F x))
    have h3 : x = r (ClassGroup.mk F x) * ((r (ClassGroup.mk F x))⁻¹ * x) := by group
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hrc) (Subgroup.mem_sup_right h2)
  rw [key a, key b]

/-- **O'Meara 33:12.** A set $S$ of discrete spots on a global field is Dedekind if and only if $S \ne \Omega$. For a
number field $F$ the set $\Omega$ of all non-trivial spots contains the infinite places, so $S \ne \Omega$ always
holds, and the theorem says that every non-empty set $S$ of finite primes satisfies the Dedekind axioms (the book
derives this from the Very Strong Approximation Theorem; here (D3) is a Chinese-remainder consequence). The "only
if" direction (a Dedekind set is not all of $\Omega$) is the existence of an infinite place. -/
@[kb "omeara1963" "§33H, 33:12, p. 78"]
theorem dedekindAxiomsOn_numberField :
    Nonempty (InfinitePlace F) ∧
      ∀ S : Set (HeightOneSpectrum (𝓞 F)), S.Nonempty → DedekindAxiomsOn F S :=
  ⟨inferInstance, fun _ hS => dedekindAxiomsOn_of_nonempty F hS⟩

end NumberField

end QuadFormsKB.OMeara
