/-
# O'Meara §94: effective determination of the invariants (scale and norm from a base)

**Setting** (as in `Sec82.lean`): $R$ a commutative ring with an algebra map to a field $F$, $2 \in F^\times$, a
quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`.

**Proves** `normIdeal_span` (O'Meara 1963, 82:8 (2), p. 227, with all $\mathfrak a_i = \mathfrak o$): if
$L = \sum_i \mathfrak o z_i$ then $\mathfrak nL = \sum_i \mathfrak o Q(z_i) + 2\,\mathfrak sL$; with `scale_span` (82:8 (1))
this is the first remark of §94 (p. 279): for a base $x_1, \dots, x_n$ of $L$,
$\mathfrak sL = \sum_{i,j} \mathfrak o B(x_i, x_j)$ and $\mathfrak nL = \sum_i \mathfrak o Q(x_i) + 2\,\mathfrak sL$
(`scale_normIdeal_of_basis`).
-/
import QuadFormsKB.Literature.OMeara.Sec91Chain

open QuadraticMap Submodule Module
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Field

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The norm from a spanning family** (O'Meara 1963, 82:8 (2), p. 227, with all $\mathfrak a_i = \mathfrak o$): if
$L = \sum_i \mathfrak o z_i$ then $\mathfrak nL = \sum_i \mathfrak o\,Q(z_i) + 2\,\mathfrak sL$. -/
@[kb "omeara1963" "§82E, 82:8 (2), p. 227"]
theorem normIdeal_span {ι : Type*} (z : ι → V) :
    normIdeal Q (span R (Set.range z)) =
      span R (Set.range fun i => Q (z i)) ⊔ (2 : F) • scale Q (span R (Set.range z)) := by
  set L := span R (Set.range z) with hL
  apply le_antisymm
  · rw [normIdeal, span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine span_induction (p := fun x hx => Q x ∈ span R (Set.range fun i => Q (z i)) ⊔ (2 : F) • scale Q L)
      ?_ (by simp) ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact mem_sup_left (subset_span ⟨i, rfl⟩)
    · intro a b ha hb hQa hQb
      rw [Q_add]
      have h2 : 2 * bil Q a b ∈ (2 : F) • scale Q L :=
        Submodule.smul_mem_pointwise_smul _ _ _ (bil_mem_scale Q ha hb)
      have : Q a + 2 * bil Q a b + Q b = Q a + Q b + 2 * bil Q a b := by ring
      rw [this]
      exact add_mem (add_mem hQa hQb) (mem_sup_right (by simpa [smul_eq_mul] using h2))
    · intro r a _ hQa
      rw [Q_rsmul, _root_.sq, mul_assoc, ← Algebra.smul_def, ← Algebra.smul_def]
      exact smul_mem _ _ (smul_mem _ _ hQa)
  · refine sup_le ?_ ?_
    · rw [span_le]; rintro _ ⟨i, rfl⟩; exact Q_mem_normIdeal Q (subset_span ⟨i, rfl⟩)
    · rintro _ ⟨c, hc, rfl⟩
      simpa [smul_eq_mul] using two_mul_mem_normIdeal Q hc

/-- **§94, first remark** (O'Meara 1963, p. 279): for a base $x_1, \dots, x_n$ of a lattice $L$,
$\mathfrak sL = \sum_{i,j} \mathfrak o B(x_i, x_j)$ and $\mathfrak nL = \sum_i \mathfrak o Q(x_i) + 2\,\mathfrak sL$. -/
@[kb "omeara1963" "§94, p. 279 (sL and nL from the matrix of a base)"]
theorem scale_normIdeal_of_basis [IsDomain R] [IsFractionRing R F] {L : Submodule R V} {ι : Type*}
    (b : Basis ι R L) :
    scale Q L = span R (Set.range fun p : ι × ι => bil Q (b p.1 : V) (b p.2 : V)) ∧
      normIdeal Q L = span R (Set.range fun i => Q (b i : V)) ⊔ (2 : F) • scale Q L := by
  have h := span_basis_eq b
  constructor
  · conv_lhs => rw [← h]
    exact scale_span Q _
  · conv_lhs => rw [← h]
    rw [normIdeal_span, h]

end Field

end QuadFormsKB.OMeara
