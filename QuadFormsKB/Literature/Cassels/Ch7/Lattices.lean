/-
# Cassels, Chapter 7, §§2–3: bases of lattices

**Setting.** Cassels, *Rational Quadratic Forms*, Chapter 7: $I$ is a ring with $1$ inside a field $k$, $U$ its group of
units; the *lattice with basis* $b_1, \dots, b_n$ of an $n$-dimensional $k$-space $V$ is
$\Lambda = Ib_1 + \cdots + Ib_n$. In Lean a lattice with a given basis is either an $I$-module `Λ` with a basis
`b : Basis (Fin n) I Λ` (Lemma 2.1, which only concerns $\Lambda$ itself), or the $I$-span
`span I (Set.range b)` of a $k$-basis `b` of `V` (Lemma 3.1, which compares two lattices in $V$). Indices run over
$0, \dots, n-1$ (Cassels: $1, \dots, n$).

**Proves**
* Lemma 2.1: elements $c_i = \sum_j r_{ij}b_j$ of $\Lambda$ form a basis of $\Lambda$ iff $\det(r_{ij}) \in U$
  (`isBasis_iff_isUnit_det`; from Mathlib's `Basis.is_basis_iff_det`);
* Lemma 3.1: for a sublattice $\Gamma \subseteq \Lambda$ the relative determinant $d = d(\Gamma/\Lambda)$ lies in $I$ and
  $d\Lambda \subseteq \Gamma$ (`exists_det_mem_and_smul_mem`; adjugate matrix);
* Lemma 3.3: a subgroup of finite index of a $\mathbb Z$-lattice is a lattice (`exists_basis_of_finiteIndex`; from
  Mathlib's `AddSubgroup.finrank_eq_of_finiteIndex` and freeness of submodules over a PID).

**Conventions.** The relative determinant $d(\Gamma/\Lambda) \in k^\times/U$ is represented by the determinant
`b.det e` of the basis $e$ of $\Gamma$ in terms of the basis $b$ of $\Lambda$ (Cassels' (3.1)–(3.2)).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

open Module Submodule Matrix

variable {n : ℕ}

/-- **Cassels, Ch. 7, Lemma 2.1**: *let $\Lambda$ be the lattice with basis $b_1, \dots, b_n$ and let
$c_1, \dots, c_n \in \Lambda$ be given by $c_i = \sum_j r_{ij}b_j$ ($r_{ij} \in I$); then $c_1, \dots, c_n$ is a basis of
$\Lambda$ if and only if $\det(r_{ij}) \in U$.* "Basis" means linearly independent over $I$ and spanning $\Lambda$ over
$I$; $\Lambda$ is any $I$-module with basis $b$ ($I$ any commutative ring). -/
@[kb "cassels1978" "Ch. 7, Lemma 2.1, p. 103"]
theorem isBasis_iff_isUnit_det {I Λ : Type*} [CommRing I] [AddCommGroup Λ] [Module I Λ]
    (b : Basis (Fin n) I Λ) (r : Matrix (Fin n) (Fin n) I) (c : Fin n → Λ)
    (hc : ∀ i, c i = ∑ j, r i j • b j) :
    (LinearIndependent I c ∧ span I (Set.range c) = ⊤) ↔ IsUnit r.det := by
  rw [Basis.is_basis_iff_det b]
  have : b.toMatrix c = rᵀ := by
    ext i j
    simp [Basis.toMatrix_apply, hc, Finset.sum_apply, map_sum, Finsupp.single_apply]
  rw [Basis.det_apply, this, det_transpose]

/-- **Cassels, Ch. 7, Lemma 3.1**: *suppose that $\Lambda, \Gamma$ are lattices and that $\Gamma \subseteq \Lambda$;
then $d(\Gamma/\Lambda) \in I/U$ and $d(\Gamma/\Lambda)\Lambda \subseteq \Gamma$.* Here $\Lambda$ is the $I$-span of a
$k$-basis $b$ of $V$, $\Gamma$ is the $I$-span of $e_0, \dots, e_{n-1}$ with each $e_i \in \Lambda$, and the relative
determinant is $d = \det_b(e)$ (`b.det e`, the determinant of the matrix $t_{ij}$ of Cassels' (3.1)); the statement is:
there is $d \in I$ whose image in $k$ is $\det_b(e)$ with $d\vec x \in \Gamma$ for every $\vec x \in \Lambda$. The scan
lost the hypothesis; it is reconstructed from the proof ("since $e_j \in \Gamma \subseteq \Lambda$") and the footnote
defining a sublattice. -/
@[kb "cassels1978" "Ch. 7, Lemma 3.1, p. 104"]
theorem exists_det_mem_and_smul_mem {I k V : Type*} [CommRing I] [Field k] [Algebra I k] [AddCommGroup V] [Module k V]
    [Module I V] [IsScalarTower I k V] (b : Basis (Fin n) k V) (e : Fin n → V)
    (he : ∀ i, e i ∈ span I (Set.range b)) :
    ∃ d : I, algebraMap I k d = b.det e ∧ ∀ x ∈ span I (Set.range b), d • x ∈ span I (Set.range e) := by
  choose T hT using fun i => (Submodule.mem_span_range_iff_exists_fun I).1 (he i)
  refine ⟨(Matrix.of T).det, ?_, ?_⟩
  · rw [Basis.det_apply, ← det_transpose, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply, of_apply, transpose_apply, Basis.toMatrix_apply]
    rw [← hT j]
    rw [map_sum, Finset.sum_apply' ]
    have : ∀ c, (b.repr (T j c • b c)) i = if c = i then algebraMap I k (T j c) else 0 := by
      intro c
      rw [← algebraMap_smul k (T j c) (b c), map_smul, Basis.repr_self]
      simp [Finsupp.single_apply, Algebra.smul_def]
    simp [this]
  · have key : ∀ l, (Matrix.of T).det • b l = ∑ i, (Matrix.of T).adjugate l i • e i := by
      intro l
      have hadj := congrFun (adjugate_mul (Matrix.of T)) l
      symm
      calc ∑ i, (Matrix.of T).adjugate l i • e i
          = ∑ i, ∑ m, ((Matrix.of T).adjugate l i * T i m) • b m := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← hT i, Finset.smul_sum]
            simp_rw [smul_smul]
        _ = ∑ m, (∑ i, (Matrix.of T).adjugate l i * T i m) • b m := by
            rw [Finset.sum_comm]; simp_rw [Finset.sum_smul]
        _ = ∑ m, ((Matrix.of T).det • (1 : Matrix (Fin n) (Fin n) I)) l m • b m := by
            rw [← hadj]; rfl
        _ = (Matrix.of T).det • b l := by
            simp [Matrix.one_apply, ite_smul]
    intro x hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun I).1 hx
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [smul_comm, key]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩))

/-- **Cassels, Ch. 7, Lemma 3.3**: *suppose that $I = \mathbb Z$; let $\Lambda$ be a lattice and $\Gamma$ a subgroup of
finite index of $\Lambda$, considered as a group under addition; then $\Gamma$ is a lattice*, i.e. $\Gamma$ has a
$\mathbb Z$-basis of $n$ elements (here $\Lambda$ is any abelian group with a $\mathbb Z$-basis
$b_0, \dots, b_{n-1}$). -/
@[kb "cassels1978" "Ch. 7, Lemma 3.3, p. 105"]
theorem exists_basis_of_finiteIndex {Λ : Type*} [AddCommGroup Λ] (b : Basis (Fin n) ℤ Λ) (Γ : AddSubgroup Λ)
    [Γ.FiniteIndex] : Nonempty (Basis (Fin n) ℤ Γ.toIntSubmodule) := by
  have : Module.Finite ℤ Λ := Module.Finite.of_basis b
  have : Module.Free ℤ Λ := Module.Free.of_basis b
  have h := AddSubgroup.finrank_eq_of_finiteIndex Γ
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin] at h
  exact ⟨Module.finBasisOfFinrankEq ℤ Γ.toIntSubmodule h⟩

end QuadFormsKB.Cassels
