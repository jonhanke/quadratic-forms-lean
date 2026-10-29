/-
# Cassels, Chapter 2, Lemma 3.1: Witt's chain lemma for normal bases

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, §3, Lemma 3.1, pp. 16–18.
Checked against the printed page (pp. 16–17) on 2026-10-27: the same statement as the formulation below.

**Setting.** As in `QuadFormsKB.Literature.Cassels.Ch2.Basic`: $U$ = `V` is a finite-dimensional vector space over a
field $k$ = `K` of characteristic $\ne 2$ with a symmetric bilinear form $\phi$ = `B : LinearMap.BilinForm K V`,
`B.IsSymm`; *regular* is `B.Nondegenerate`. A *normal basis* is a basis $b_0, \dots, b_{n-1}$ (0-based, $n = \dim U$)
with $\phi(b_i, b_j) = 0$ for $i \ne j$ (`IsNormalBasis`).

**Proves.**
* `exists_reflTransGen_normalBasis` (Lemma 3.1): any two normal bases of a regular space are joined by a chain of
  normal bases in which consecutive bases differ in at most two vectors.

**Proof notes.** The library already contains the same lemma for orthogonal bases in O'Meara's setting
(`QuadFormsKB.OMeara.exists_adjacent_chain_of_orthogonal_bases`, 58:1), with steps altering two *adjacent* vectors,
which is stronger than Cassels' statement. We apply it to the quadratic form $x \mapsto \phi(x, x)$, whose
associated bilinear form is $\phi$ since $2$ is invertible, and forget adjacency.

**Formulation.** "Consecutive bases have at least $n-2$ vectors in common" is expressed positionally: the two bases
agree at every index outside a set of at most two indices (`DifferInAtMostTwo`).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec58Bases

open Module

namespace QuadFormsKB.Cassels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A **normal basis** of the quadratic space $(U, \phi)$: a basis $b_0, \dots, b_{n-1}$ of $U$ whose vectors are
pairwise orthogonal, $\phi(b_i, b_j) = 0$ for $i \ne j$. -/
def IsNormalBasis {n : ℕ} (B : LinearMap.BilinForm K V) (b : Basis (Fin n) K V) : Prop :=
  ∀ i j, i ≠ j → B (b i) (b j) = 0

/-- The basis $c$ **differs from $b$ in at most two vectors**: there is a set $S$ of at most two indices such that
$c_k = b_k$ for all $k \notin S$. -/
def DifferInAtMostTwo {n : ℕ} (b c : Basis (Fin n) K V) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ 2 ∧ ∀ k, k ∉ S → c k = b k

/-- **Cassels, Ch. 2, Lemma 3.1 (Witt's chain lemma).** Let $(U, \phi)$ be a regular finite-dimensional quadratic
space over a field of characteristic $\ne 2$ (here $\phi$ symmetric and nondegenerate, $2 \ne 0$), of dimension $n$,
and let $b$, $c$ be two normal bases of $U$. Then there is a chain of normal bases
$b = b^{(0)}, b^{(1)}, \dots, b^{(r)} = c$ such that $b^{(t+1)}$ differs from $b^{(t)}$ in at most two vectors (so
consecutive bases have at least $n - 2$ vectors in common). Formalized as membership in the reflexive-transitive
closure of the relation "both are normal bases and the second differs from the first in at most two vectors".
Checked against the printed page (pp. 16–17) on 2026-10-27: the same statement (Cassels: a sequence $C_1 = A, \dots, C_T = B$
of normal bases with $C_t, C_{t+1}$ having at least $n-2$ elements in common at the same indices). -/
@[kb "cassels1978" "Ch. 2, Lemma 3.1, pp. 16–18"]
theorem exists_reflTransGen_normalBasis [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hB : B.IsSymm) (hreg : B.Nondegenerate) (h2 : (2 : K) ≠ 0) {n : ℕ} (b c : Basis (Fin n) K V)
    (hb : IsNormalBasis B b) (hc : IsNormalBasis B c) :
    Relation.ReflTransGen (fun x y : Basis (Fin n) K V =>
      IsNormalBasis B x ∧ IsNormalBasis B y ∧ DifferInAtMostTwo x y) b c := by
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  have hsym : ∀ x y, B x y = B y x := fun x y => hB.eq x y
  have hass : QuadraticMap.associated (R := K) B.toQuadraticMap = B :=
    QuadraticMap.associated_left_inverse K hsym
  have hQ : (QuadraticMap.associated (R := K) B.toQuadraticMap).Nondegenerate := by
    rw [hass]; exact hreg
  have conv : ∀ x : Basis (Fin n) K V, IsNormalBasis B x ↔
      QuadFormsKB.OMeara.IsOrthogonalBasis B.toQuadraticMap x := by
    intro x
    unfold IsNormalBasis QuadFormsKB.OMeara.IsOrthogonalBasis QuadFormsKB.OMeara.bil
    rw [hass]
  obtain ⟨k, Z, h0, hl, hZ, hadj⟩ :=
    QuadFormsKB.OMeara.exists_adjacent_chain_of_orthogonal_bases hQ b c ((conv b).1 hb) ((conv c).1 hc)
  have key : ∀ m : ℕ, ∀ hm : m < k + 1, Relation.ReflTransGen (fun x y : Basis (Fin n) K V =>
      IsNormalBasis B x ∧ IsNormalBasis B y ∧ DifferInAtMostTwo x y) b (Z ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero => intro hm; rw [← h0]; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro hm
      refine (ih (by omega)).tail ⟨(conv _).2 (hZ _), (conv _).2 (hZ _), ?_⟩
      obtain ⟨i, hi⟩ := hadj ⟨m, by omega⟩
      refine ⟨Finset.univ.filter (fun j : Fin n => (j : ℕ) = i ∨ (j : ℕ) = i + 1), ?_, ?_⟩
      · calc _ ≤ ({i, i + 1} : Finset ℕ).card :=
              Finset.card_le_card_of_injOn (fun j : Fin n => (j : ℕ))
                (by intro j hj; simpa using hj) Fin.val_injective.injOn
          _ ≤ 2 := Finset.card_le_two
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hj
        exact hi j hj.1 hj.2
  have := key k (Nat.lt_succ_self k)
  have e : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [e, hl] at this
  exact this

end QuadFormsKB.Cassels
