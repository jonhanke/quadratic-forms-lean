/-
# O'Meara §54, p. 135: the even Clifford algebra has dimension $2^{n-1}$

**Setting** (as in `Sec54Dim`): $F$ a field with `Invertible (2 : F)`, $V$ a finite-dimensional quadratic space,
$C$ = Mathlib's `CliffordAlgebra Q`, $C^+$ = `CliffordAlgebra.even Q` (the subalgebra of even elements).
Indices are 0-based: an orthogonal basis is $x_0, \dots, x_{n-1}$.

**Proves** (running text of O'Meara §54, p. 135)
* `word_mem_evenOdd`: the word of a subset $s$ lies in the graded piece of degree $|s| \bmod 2$;
* `even_toSubmodule_eq_span_word`: $C^+$ is spanned by the derived-base words of even length;
* `finrank_even_of_basis`, `finrank_even`: $\dim C^+ = 2^{n-1}$ for $n = \dim V \ge 1$.

*Update:* O'Meara assumes $V$ regular; none of this needs regularity (only $2$ invertible).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec54Dim

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace CliffordEven

open CliffordDim

/-- The number of subsets of $\{0, \dots, n-1\}$ ($n \ge 1$) of even cardinality is $2^{n-1}$. -/
theorem card_even_finset (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {s : Finset (Fin n) // Even s.card} = 2 ^ (n - 1) := by
  classical
  rw [Fintype.card_subtype]
  set A := (Finset.univ : Finset (Finset (Fin n))).filter (fun s => Even s.card) with hA
  set B := (Finset.univ : Finset (Finset (Fin n))).filter (fun s => ¬ Even s.card) with hB
  have h1 : A.card + B.card = 2 ^ n := by
    rw [hA, hB, Finset.card_filter_add_card_filter_not]
    simp
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have h2 := Finset.sum_powerset_neg_one_pow_card_of_nonempty hne
  rw [Finset.powerset_univ,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Finset (Fin n) => Even s.card)] at h2
  have e1 : ∑ s ∈ A, (-1 : ℤ) ^ s.card = A.card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun s hs => by
      exact Even.neg_one_pow (Finset.mem_filter.mp hs).2)]
    simp
  have e2 : ∑ s ∈ B, (-1 : ℤ) ^ s.card = -(B.card : ℤ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ)) (fun s hs => by
      exact Odd.neg_one_pow (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hs).2))]
    simp
  rw [e1, e2] at h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h3 : (A.card : ℤ) = B.card := by linarith
  have h4 : A.card = B.card := by exact_mod_cast h3
  rw [pow_succ] at h1
  simp only [Nat.add_sub_cancel]
  omega

section

variable {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  (Q : QuadraticForm F V) {n : ℕ} (e : Module.Basis (Fin n) F V)

/-- The word of a subset $s$ lies in the graded piece of degree $|s| \bmod 2$ of the Clifford algebra. -/
theorem word_mem_evenOdd (s : Finset (Fin n)) :
    word (CliffordAlgebra.ι Q) e s ∈ CliffordAlgebra.evenOdd Q (s.card : ZMod 2) := by
  induction s using finset_induction_min with
  | empty =>
    rw [word_empty]
    simpa using (CliffordAlgebra.one_le_evenOdd_zero Q) (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  | step a s hk ih =>
    have ha : a ∉ s := fun hm => lt_irrefl _ (hk a hm)
    rw [word_insert_min _ e hk, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, add_comm]
    exact SetLike.mul_mem_graded (CliffordAlgebra.ι_mem_evenOdd_one Q _) ih

variable (horth : ∀ i k, i ≠ k → (QuadraticMap.associated Q) (e i) (e k) = 0)
include horth

/-- **$C^+$ is spanned by the derived-base words of even length** (O'Meara 1973, §54, p. 135). -/
theorem even_toSubmodule_eq_span_word [FiniteDimensional F V] :
    Subalgebra.toSubmodule (CliffordAlgebra.even Q) =
      Submodule.span F {w | ∃ s : Finset (Fin n), Even s.card ∧ word (CliffordAlgebra.ι Q) e s = w} := by
  classical
  set E := Submodule.span F {w | ∃ s : Finset (Fin n), Even s.card ∧ word (CliffordAlgebra.ι Q) e s = w}
  set O := Submodule.span F {w | ∃ s : Finset (Fin n), ¬ Even s.card ∧ word (CliffordAlgebra.ι Q) e s = w}
  have hE : E ≤ CliffordAlgebra.evenOdd Q 0 := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨s, hs, rfl⟩
    have := word_mem_evenOdd Q e s
    rwa [(ZMod.natCast_eq_zero_iff_even).mpr hs] at this
  have hO : O ≤ CliffordAlgebra.evenOdd Q 1 := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨s, hs, rfl⟩
    have := word_mem_evenOdd Q e s
    rwa [(ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp hs)] at this
  rw [CliffordAlgebra.even_toSubmodule]
  refine le_antisymm (fun x hx => ?_) hE
  have hspan : x ∈ Submodule.span F (Set.range (word (CliffordAlgebra.ι Q) e)) := by
    rw [span_word_cliffordAlgebra Q e horth]; trivial
  have hsup : Submodule.span F (Set.range (word (CliffordAlgebra.ι Q) e)) ≤ E ⊔ O := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨s, rfl⟩
    by_cases hs : Even s.card
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨s, hs, rfl⟩)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hsup hspan)
  have hb0 : b ∈ CliffordAlgebra.evenOdd Q 0 := by
    have : b = (a + b) - a := by abel
    rw [this]
    exact sub_mem hx (hE ha)
  have : b = 0 := by
    have := (CliffordAlgebra.evenOdd_isCompl Q).disjoint
    exact (Submodule.disjoint_def.mp this) b hb0 (hO hb)
  rw [this, add_zero]
  exact ha

/-- **$\dim C^+ = 2^{n-1}$** for an orthogonal basis $x_0, \dots, x_{n-1}$ of $V$ with $n \ge 1$
(O'Meara 1973, §54, p. 135). -/
theorem finrank_even_of_basis [FiniteDimensional F V] (hn : 1 ≤ n) :
    finrank F (CliffordAlgebra.even Q) = 2 ^ (n - 1) := by
  rw [← Subalgebra.finrank_toSubmodule, even_toSubmodule_eq_span_word Q e horth]
  have hli : LinearIndependent F (fun s : {s : Finset (Fin n) // Even s.card} =>
      word (CliffordAlgebra.ι Q) e s.1) :=
    (linearIndependent_word_cliffordAlgebra Q e horth).comp _ Subtype.val_injective
  have hr : Set.range (fun s : {s : Finset (Fin n) // Even s.card} =>
      word (CliffordAlgebra.ι Q) e s.1) =
      {w | ∃ s : Finset (Fin n), Even s.card ∧ word (CliffordAlgebra.ι Q) e s = w} := by
    ext w
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact ⟨⟨s, hs⟩, rfl⟩
  rw [← hr, finrank_span_eq_card hli, card_even_finset n hn]

end

end CliffordEven

section Main

variable {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (Q : QuadraticForm F V)

/-- **dim $C^+ = 2^{n-1}$** (O'Meara 1973, §54, p. 135, running text after 54:3a): for a quadratic space $V$ of
dimension $n \ge 1$ over a field $F$ with $2$ invertible, the even Clifford algebra $C^+$ (`CliffordAlgebra.even Q`)
has dimension $2^{n-1}$. It is spanned by the derived-base words of even length
(`CliffordEven.even_toSubmodule_eq_span_word`). Regularity of $V$ is not needed (generalization). -/
@[kb "omeara1963" "§54, p. 135 (dim C⁺ = 2^(n−1))"]
theorem finrank_even (hn : 1 ≤ finrank F V) :
    finrank F (CliffordAlgebra.even Q) = 2 ^ (finrank F V - 1) := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (K := F) (V := V) (B := QuadraticMap.associated Q) ⟨fun x y => by
      exact QuadraticMap.associated_isSymm F Q x y⟩
  exact CliffordEven.finrank_even_of_basis Q v hv hn

end Main

end QuadFormsKB.OMeara
