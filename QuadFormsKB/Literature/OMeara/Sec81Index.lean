/-
# O'Meara §81D: the invariant factors of $K$ in $L$ (Definition 81:12) and 82:11

**Setting** (as in `Sec81.lean`): $R$ a Dedekind domain with fraction field $F$, $V$ a finite-dimensional vector space
over $F$, lattices $L$, $K$ on $V$ (`Submodule.IsLattice F`).

**Index convention.** O'Meara's $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$ are
`invFactors hL hK 0, …, invFactors hL hK (n-1)`, $n = \dim V$.

**Defines** the invariant factors $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$ of $K$ in $L$
(`invFactors`, **Definition 81:12**, p. 216).

**Proves**
* `exists_basis_invFactors` (they occur in a base adapted to $L$ and $K$), `invFactors_eq` (any such base gives them:
  they are invariants, by the uniqueness part of 81:11), `invFactors_antitone`;
* `invFactors_le_one` (§81D, p. 216: if $K \subseteq L$ the invariant factors are integral);
* `volume_eq_prod_invFactors_sq` (**82:11**, p. 230, as stated: $\mathfrak vK = \mathfrak a^2\,\mathfrak vL$ and
  $\mathfrak aL \subseteq K$ for $\mathfrak a$ the product of the invariant factors of $K \subseteq L$).
-/
import QuadFormsKB.Literature.OMeara.Sec81Invariant
import QuadFormsKB.Literature.OMeara.Sec81InvariantUnique
import QuadFormsKB.Literature.OMeara.Sec82Volume

open Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]

/-- **The invariant factors of $K$ in $L$** (O'Meara 1963, Definition 81:12, p. 216): the fractional ideals
$\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$ of Theorem 81:11, for which $L = \sum_i\mathfrak a_ix_i$ and
$K = \sum_i\mathfrak a_i\mathfrak t_ix_i$ in some base $x$ of $V$; they do not depend on the base (`invFactors_eq`).
The $i$-th invariant factor is `invFactors hL hK i` (0-based). -/
@[kb "omeara1963" "§81D, 81:12, p. 216 (the invariant factors of K in L)"]
def invFactors {L K : Submodule R V} (hL : L.IsLattice F) (hK : K.IsLattice F) :
    Fin (finrank F V) → Submodule R F :=
  (exists_invariant_factors hL hK).choose_spec.choose_spec.choose

/-- The invariant factors occur in a base adapted to $L$ and $K$ (O'Meara 1963, 81:11–81:12). -/
theorem exists_basis_invFactors {L K : Submodule R V} (hL : L.IsLattice F) (hK : K.IsLattice F) :
    ∃ x : Basis (Fin (finrank F V)) F V, ∃ a : Fin (finrank F V) → Submodule R F,
      (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧ (∀ i, (invFactors hL hK i).FG ∧ invFactors hL hK i ≠ ⊥) ∧
        Antitone (invFactors hL hK) ∧ L = ⨆ i, a i • span R {x i} ∧
          K = ⨆ i, (a i * invFactors hL hK i) • span R {x i} :=
  ⟨_, _, (exists_invariant_factors hL hK).choose_spec.choose_spec.choose_spec⟩

/-- **The invariant factors are invariants** (O'Meara 1963, 81:11–81:12): any base $x$ with
$L = \sum_i\mathfrak a_ix_i$, $K = \sum_i\mathfrak a_i\mathfrak t_ix_i$, $\mathfrak t_1 \supseteq \cdots \supseteq
\mathfrak t_n$ gives $\mathfrak t_i$ = the $i$-th invariant factor of $K$ in $L$. -/
@[kb "omeara1963" "§81D, 81:11–81:12, pp. 215–216 (the invariant factors do not depend on the base)"]
theorem invFactors_eq {L K : Submodule R V} (hL : L.IsLattice F) (hK : K.IsLattice F)
    (x : Basis (Fin (finrank F V)) F V) (a t : Fin (finrank F V) → Submodule R F)
    (ha : ∀ i, (a i).FG ∧ a i ≠ ⊥) (ht : ∀ i, (t i).FG ∧ t i ≠ ⊥) (hta : Antitone t)
    (hLx : L = ⨆ i, a i • span R {x i}) (hKx : K = ⨆ i, (a i * t i) • span R {x i}) :
    invFactors hL hK = t := by
  obtain ⟨x', a', ha', ht', hta', hL', hK'⟩ := exists_basis_invFactors hL hK
  exact invariant_factors_unique x' x a' a _ t ha' ha ht' ht hta' hta (hL'.symm.trans hLx)
    (hK'.symm.trans hKx)

theorem invFactors_antitone {L K : Submodule R V} (hL : L.IsLattice F) (hK : K.IsLattice F) :
    Antitone (invFactors hL hK) :=
  (exists_basis_invFactors hL hK).choose_spec.choose_spec.2.2.1

/-- **The invariant factors of $K \subseteq L$ are integral** (O'Meara 1963, §81D, p. 216: "In this event the
invariant factors of $K$ in $L$ are all integral ideals"). -/
@[kb "omeara1963" "§81D, p. 216 (K ⊆ L: the invariant factors are integral)"]
theorem invFactors_le_one {L K : Submodule R V} (hL : L.IsLattice F) (hK : K.IsLattice F) (hKL : K ≤ L)
    (i : Fin (finrank F V)) : invFactors hL hK i ≤ 1 := by
  classical
  obtain ⟨x, a, ha, -, -, hLx, hKx⟩ := exists_basis_invFactors hL hK
  set t := invFactors hL hK
  -- `𝔞ᵢ𝔱ᵢxᵢ ⊆ K ⊆ L = ⋯ + 𝔞ᵢxᵢ + ⋯` gives `𝔱ᵢ𝔞ᵢ ⊆ 𝔞ᵢ`; cancel `𝔞ᵢ`
  have hsub : t i * a i ≤ a i := by
    intro γ hγ
    have hmem : γ • x i ∈ K := by
      rw [hKx, mem_iSup_smul_span_iff]
      intro j
      by_cases hj : j = i
      · subst hj; simpa [mul_comm] using hγ
      · simp [Ne.symm hj]
    have := (mem_iSup_smul_span_iff x a _).mp (hLx ▸ hKL hmem) i
    simpa using this
  calc t i = t i * (a i * (1 / a i)) := by rw [mul_one_div_cancel_of_fg (ha i).1 (ha i).2, mul_one]
    _ = (t i * a i) * (1 / a i) := by rw [mul_assoc]
    _ ≤ a i * (1 / a i) := mul_le_mul' hsub le_rfl
    _ = 1 := mul_one_div_cancel_of_fg (ha i).1 (ha i).2

variable [Invertible (2 : F)] (Q : QuadraticForm F V)

/-- **Proposition 82:11** (O'Meara 1963, p. 230), as stated. Let $K \subseteq L$ be lattices on the quadratic space $V$
and $\mathfrak a$ the product of the invariant factors of $K$ in $L$. Then $\mathfrak a$ is an integral ideal,
$\mathfrak vK = \mathfrak a^2\,\mathfrak vL$ and $\mathfrak aL \subseteq K$. (O'Meara assumes $V$ regular and
$K, L \ne 0$; neither is needed.) -/
@[kb "omeara1963" "§82E, 82:11, p. 230"]
theorem volume_eq_prod_invFactors_sq {L K : Submodule R V} (hL : L.IsLattice F) (hK : K.IsLattice F)
    (hKL : K ≤ L) :
    (∏ i, invFactors hL hK i) ≤ 1 ∧ volume Q K = (∏ i, invFactors hL hK i) ^ 2 * volume Q L ∧
      (∏ i, invFactors hL hK i) • L ≤ K := by
  classical
  obtain ⟨x, a, ha, ht, -, hLx, hKx⟩ := exists_basis_invFactors hL hK
  set t := invFactors hL hK
  have hle : ∀ i, t i ≤ 1 := invFactors_le_one hL hK hKL
  have hat : ∀ i, (a i * t i).FG ∧ a i * t i ≠ ⊥ := fun i =>
    ⟨(ha i).1.mul (ht i).1, by
      rw [← Submodule.zero_eq_bot] at *; exact mul_ne_zero (ha i).2 (ht i).2⟩
  -- the product of the integral ideals `𝔱ⱼ` lies in each of them
  have hprod : ∀ i, ∏ j, t j ≤ t i := fun i => by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    calc t i * ∏ j ∈ Finset.univ.erase i, t j ≤ t i * 1 :=
          mul_le_mul' le_rfl (by
            simpa using prod_le_prod_submodule (Finset.univ.erase i) t (fun _ => 1) hle)
      _ = t i := mul_one _
  refine ⟨?_, ?_, ?_⟩
  · simpa using prod_le_prod_submodule Finset.univ t (fun _ => 1) hle
  · rw [hKx, hLx, volume_eq_of_adapted Q (⇑x) x.linearIndependent _ hat,
      volume_eq_of_adapted Q (⇑x) x.linearIndependent _ ha, Finset.prod_mul_distrib, mul_pow]
    ring
  · rw [hLx, hKx, Submodule.smul_iSup]
    refine iSup_mono fun i => ?_
    rw [← Submodule.smul_assoc, smul_eq_mul, mul_comm]
    exact Submodule.smul_mono_left (mul_le_mul' le_rfl (hprod i))

end QuadFormsKB.OMeara
