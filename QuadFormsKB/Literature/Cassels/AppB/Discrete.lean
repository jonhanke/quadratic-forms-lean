/-
# Cassels, Appendix B, §4: the rational points are a discrete subgroup

Cassels, *Rational Quadratic Forms* (1978), Appendix B, §4, p. 379: the adelic group $O^+_{\mathbb A}$ carries the
restricted product topology, and $O^+(V)$, embedded diagonally, is a discrete subgroup.

**Formalized.** For a totally positive definite quadratic form $Q$ over a number field $F$ with $Q$ integral on the
standard lattice, the group of rational points `ratPoints Q` $= O(V)(F)$ is a discrete subgroup of the finite-adelic
orthogonal group `OAf Q` $= O(V)(\mathbb A_f)$, and likewise the rational special orthogonal group `GammaSOf Q₀` inside
`SOAf Q₀`. The proof: the open compact subgroup $O(\hat L)$ meets the rational points in a finite set
(`finite_stabilizer` at the trivial coset); `OAf Q` is Hausdorff, so the finitely many non-identity points can be removed
from $O(\hat L)$, leaving an open neighbourhood of $1$ that contains no other rational point.

**Relation to the printed statement.** Cassels works in the full adele group (places $p \le \infty$ included) and for
every regular space $V$. The library has no full-adelic orthogonal group and works with the finite places only. For a
totally positive definite $V$ the archimedean factor $\prod_{\sigma} O_n(\mathbb R)$ is compact, so a subgroup of
(finite adeles) $\times$ (archimedean factor) that is the diagonal image of $O(V)(F)$ is discrete exactly when its image in
the finite adeles is discrete and the fibres are finite; both hold here. Thus discreteness in the full adeles and in the
finite adeles are equivalent in this case; only the finite-adelic statement is proved.

Indices are 0-based (`Fin n`).
-/
import QuadFormsKB.Tamagawa.Measure.AdelicSO

open NumberField IsDedekindDomain MulAction Matrix
open scoped RestrictedProduct

namespace QuadFormsKB.Tamagawa

open Lattices QuadFormsKB.Tamagawa.Measure

section Generic

/-- Helper: a subgroup $H$ of a topological group $G$ with an open neighbourhood $U$ of $1$ in $G$ containing no element
of $H$ other than $1$ is discrete in the subspace topology. Arguments: `H` the subgroup, `U` the open set,
`hU` openness, `h1 : 1 ∈ U`, `hH` that $H \cap U \subseteq \{1\}$. -/
theorem discrete_of_isolated_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) (hH : ∀ h ∈ H, h ∈ U → h = 1) :
    DiscreteTopology H := by
  apply discreteTopology_of_isOpen_singleton_one
  have : ({1} : Set H) = (Subtype.val ⁻¹' U) := by
    ext h
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; simpa using h1
    · intro hh; exact Subtype.ext (hH h h.2 hh)
  rw [this]
  exact hU.preimage continuous_subtype_val

end Generic

section Adelic

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- Helper: the finite-adelic orthogonal group is Hausdorff (it embeds continuously and injectively into the product of
the local groups). -/
instance t2Space_OAf (Q : QuadForm F n) : T2Space (OAf Q) :=
  T2Space.of_injective_continuous
    (f := fun h : OAf Q => (h : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q (v.adicCompletion F)))
    (fun a b h => by ext1 v; exact congrFun h v) RestrictedProduct.continuous_coe

/-- Helper: an open neighbourhood $U$ of $1$ in $O(V)(\mathbb A_f)$ meeting the rational points only in $1$. -/
theorem exists_isolating_open {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) (hLi : IsIntegral Q (stdLat F n).1) :
    ∃ U : Set (OAf Q), IsOpen U ∧ (1 : OAf Q) ∈ U ∧ ∀ h ∈ ratPoints Q, h ∈ U → h = 1 := by
  have hfin : Finite (stabilizer (ratPoints Q) (QuotientGroup.mk 1 : OAf Q ⧸ locStab Q (stdLat F n))) :=
    finite_stabilizer hQ (stdLat F n) hLi _
  -- the finite set of non-identity rational points in the open subgroup
  set T : Set (OAf Q) := {h | h ∈ ratPoints Q ∧ h ∈ locStab Q (stdLat F n) ∧ h ≠ 1} with hT
  have hTfin : T.Finite := by
    have : T ⊆ Set.range (fun s : stabilizer (ratPoints Q)
        (QuotientGroup.mk 1 : OAf Q ⧸ locStab Q (stdLat F n)) => ((s : ratPoints Q) : OAf Q)) := by
      rintro h ⟨hr, hl, -⟩
      refine ⟨⟨⟨h, hr⟩, ?_⟩, rfl⟩
      rw [mem_stabilizer_coset]
      simpa using hl
    exact (Set.finite_range _).subset this
  refine ⟨(locStab Q (stdLat F n) : Set (OAf Q)) \ T, ?_, ?_, ?_⟩
  · exact (isOpen_locStab Q).sdiff hTfin.isClosed
  · exact ⟨(locStab Q (stdLat F n)).one_mem, fun ⟨_, _, h⟩ => h rfl⟩
  · intro h hr ⟨hl, hnT⟩
    by_contra hne
    exact hnT ⟨hr, hl, hne⟩

/-- **$O(V)(F)$ is a discrete subgroup of $O(V)(\mathbb A_f)$.** For a totally positive definite quadratic form $Q$ over a
number field $F$ that is integral on the standard lattice, the group of rational points `ratPoints Q` has the discrete
subspace topology inside the finite-adelic orthogonal group `OAf Q`. Arguments: `hQ` total positive definiteness, `hLi`
integrality of $Q$ on the standard lattice. Cassels states this for the full adeles and all regular $V$; for totally
positive definite $V$ the archimedean factor is compact, so the two versions are equivalent (see the module docstring). -/
@[kb "cassels1978" "App. B, §4, p. 379 (O⁺(V) is a discrete subgroup; here finite adeles, V totally positive definite)"]
theorem discreteTopology_ratPoints {Q : QuadForm F n} (hQ : IsTotallyPosDef Q)
    (hLi : IsIntegral Q (stdLat F n).1) : DiscreteTopology (ratPoints Q) := by
  obtain ⟨U, hU, h1, hH⟩ := exists_isolating_open hQ hLi
  exact discrete_of_isolated_one _ U hU h1 hH

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **$SO(V)(F)$ is a discrete subgroup of $SO(V)(\mathbb A_f)$.** Same hypotheses as `discreteTopology_ratPoints`,
for the form $Q_0$ over the ring of integers and its extension `QF` to $F$: `GammaSOf Q₀` has the discrete subspace
topology in `SOAf Q₀`. -/
@[kb "cassels1978" "App. B, §4, p. 379 (O⁺(V) is a discrete subgroup; here finite adeles, V totally positive definite)"]
theorem discreteTopology_GammaSOf (hpd : IsTotallyPosDef QF) (hLi : IsIntegral QF (stdLat F n).1) :
    DiscreteTopology (GammaSOf Q₀) := by
  obtain ⟨U, hU, h1, hH⟩ := exists_isolating_open hpd hLi
  refine discrete_of_isolated_one _ (Subtype.val ⁻¹' U) (hU.preimage continuous_subtype_val) (by simpa using h1) ?_
  intro h hh hU'
  exact Subtype.ext (hH _ hh hU')

end Adelic

end QuadFormsKB.Tamagawa
