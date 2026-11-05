/-
# O'Meara §94: a norm generator from a base

**Setting** (as in `Sec93.lean`): $R$ a discrete valuation ring (O'Meara's $\mathfrak o$) with fraction field $F$,
$2 \ne 0$ in $F$, a quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`; $\mathfrak sL$ = `scale Q L`,
$\mathfrak nL$ = `normIdeal Q L`, norm generators `IsNormGenerator Q L a` ($a \in \mathfrak gL$ with
$a\mathfrak o = \mathfrak nL$).

**Proves** the recipe for a norm generator of §94 (O'Meara 1973 printing, p. 280: "The norm generator is easy: if
$\mathfrak nL = 2(\mathfrak sL)$ take any $a$ with $a\mathfrak o = 2(\mathfrak sL)$, otherwise take $a = Q(x_i)$ for
any value of $i$ which makes $Q(x_i)\mathfrak o$ largest"):
* `isNormGenerator_of_eq_two_scale`: if $\mathfrak nL = 2\mathfrak sL$, every $a$ with $a\mathfrak o =
  2\mathfrak sL$ is a norm generator;
* `isNormGenerator_Q_of_basis`: otherwise, for a base $x_1, \dots, x_n$ of $L$, $Q(x_j)$ is a norm generator for
  every $j$ with $Q(x_j)\mathfrak o$ largest among the $Q(x_i)\mathfrak o$.
-/
import QuadFormsKB.Literature.OMeara.Sec94
import QuadFormsKB.Literature.OMeara.Sec93
import QuadFormsKB.Literature.OMeara.Sec63A

open QuadraticMap Submodule Module
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Norm generator, first case** (O'Meara 1973, §94, p. 280): if $\mathfrak nL = 2(\mathfrak sL)$, any $a$ with
$a\mathfrak o = 2(\mathfrak sL)$ is a norm generator of $L$. -/
@[kb "omeara1963" "§94, p. 280 (norm generator: if nL = 2(sL) take any a with ao = 2(sL))"]
theorem isNormGenerator_of_eq_two_scale {L : Submodule R V} (hL : normIdeal Q L = (2 : F) • scale Q L) {a : F}
    (ha : R ∙ a = (2 : F) • scale Q L) : IsNormGenerator Q L a := by
  refine ⟨?_, ha.trans hL.symm⟩
  have hmem : a ∈ (2 : F) • scale Q L := ha ▸ mem_span_singleton_self a
  obtain ⟨c, hc, hca⟩ := (Submodule.mem_smul_pointwise_iff_exists a (2 : F) (scale Q L)).mp hmem
  exact ⟨0, L.zero_mem, c, hc, by rw [← hca, smul_eq_mul]; simp⟩

/-- In a discrete valuation ring any two principal fractional ideals are comparable. -/
theorem span_singleton_le_total (x y : F) : (R ∙ x) ≤ (R ∙ y) ∨ (R ∙ y) ≤ (R ∙ x) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  by_cases hx : x = 0
  · left; simp [hx]
  by_cases hy : y = 0
  · right; simp [hy]
  rcases le_total (dord hπ x) (dord hπ y) with h | h
  · right
    rw [span_singleton_le_iff_mem]
    exact (mem_span_iff hπ hy hx).mpr h
  · left
    rw [span_singleton_le_iff_mem]
    exact (mem_span_iff hπ hx hy).mpr h

/-- **Norm generator, second case** (O'Meara 1973, §94, p. 280): if $\mathfrak nL \ne 2(\mathfrak sL)$ and
$x_1, \dots, x_n$ is a base of $L$ (`b`), then $Q(x_j)$ is a norm generator for every $j$ such that
$Q(x_j)\mathfrak o$ is the largest of the ideals $Q(x_i)\mathfrak o$. -/
@[kb "omeara1963" "§94, p. 280 (norm generator: otherwise a = Q(x_i) with Q(x_i)o largest)"]
theorem isNormGenerator_Q_of_basis {L : Submodule R V} {ι : Type*} [Finite ι] (b : Basis ι R L)
    (hL : normIdeal Q L ≠ (2 : F) • scale Q L) {j : ι} (hj : ∀ k, Q (b k : V) ∈ R ∙ Q (b j : V)) :
    IsNormGenerator Q L (Q (b j : V)) := by
  refine ⟨Q_mem_normGroup Q (b j).2, ?_⟩
  have hn := (scale_normIdeal_of_basis Q b).2
  have hspan : span R (Set.range fun i => Q (b i : V)) = R ∙ Q (b j : V) := by
    refine le_antisymm (span_le.mpr ?_) (span_le.mpr ?_)
    · rintro _ ⟨k, rfl⟩; exact hj k
    · rintro _ hz
      rw [Set.mem_singleton_iff] at hz
      exact subset_span ⟨j, hz.symm⟩
  rw [hspan] at hn
  -- `2(sL)` is principal (or zero), so comparable with `Q(x_j)o`
  have hfg : ((2 : F) • scale Q L).FG := by
    have hLfg : L.FG := by
      rw [← span_basis_eq b]
      exact fg_span (Set.finite_range _)
    exact (scale_fg Q hLfg).map _
  by_cases h0 : (2 : F) • scale Q L = ⊥
  · rw [hn, h0, sup_bot_eq]
  obtain ⟨s, -, hs⟩ := exists_eq_span_singleton hfg h0
  rcases span_singleton_le_total (R := R) (Q (b j : V)) s with h | h
  · exact absurd (by rw [hn, hs, sup_eq_right.mpr h]) hL
  · rw [hn, hs, sup_eq_left.mpr h]

end QuadFormsKB.OMeara
