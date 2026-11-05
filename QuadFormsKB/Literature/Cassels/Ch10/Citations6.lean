/-
# Cassels, Chapter 10: running-text items and citations
Items of Cassels' Chapter 10 (*The spin and orthogonal groups*, pp. 169–195) that had no citation tag yet.

* Theorem 2.1, existence (pp. 172–174): Mathlib's `CliffordAlgebra Q` is an algebra with Cassels' properties (i)–(iii)
  (`exists_cliffordAlgebra_properties`, a comparison theorem bundling `finrank_cliffordAlgebra`,
  `iSup_range_ι_pow_eq_top`, `ι_mul_ι_self` of `Ch10/Clifford.lean`). Cassels constructs the algebra on the basis
  $e(J)$, $J \subseteq \{1, \dots, n\}$; Mathlib constructs it as a quotient of the tensor algebra.
* Proof of Theorem 2.1, (2.10) (p. 172): $xy + yx = 2\phi(x, y)$ (`ι_mul_ι_add_swap_eq`, Mathlib's
  `CliffordAlgebra.ι_mul_ι_add_swap`).
* §4, p. 182: $\Omega(\Lambda) = \Omega(V) \cap O(\Lambda)$ and $\Theta(\Lambda) = \Theta(V) \cap O(\Lambda)$ for a lattice $\Lambda$ over a number
  field (`Lattices.omegaLat`, `Lattices.thetaLat`), with $\Omega(V)$ the commutator subgroup of $O(V)$ and
  $\Theta(V)$ = `Lattices.spinorKernel` (O'Meara's $O'(V)$), $O(\Lambda)$ = `Lattices.autLat`.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Citations

open Module CliffordAlgebra

namespace QuadFormsKB

namespace Cassels

variable {k V : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (Q : QuadraticForm k V)

/-- **Existence of the Clifford algebra** (Cassels, Ch. 10, Theorem 2.1, pp. 172–174): for a finite-dimensional
quadratic space $(V, Q)$ over a field $k$ of characteristic $\ne 2$, Mathlib's `CliffordAlgebra Q` with the linear map
$\iota : V \to C(V)$ has (i) dimension $2^n$, $n = \dim V$; (ii) it is spanned by the products of elements of
$\iota(V)$ (the powers of the subspace $\iota(V)$ span everything); (iii) $\iota(x)^2 = Q(x)$ for every $x \in V$; and
$\iota$ is injective, so $V$ is a subspace of $C(V)$. -/
@[kb "cassels1978" "Ch. 10, Thm. 2.1, pp. 172–174 (existence of C(V); Mathlib's construction)"]
theorem exists_cliffordAlgebra_properties :
    finrank k (CliffordAlgebra Q) = 2 ^ finrank k V ∧
      (⨆ i : ℕ, LinearMap.range (ι Q) ^ i = ⊤) ∧
      (∀ x : V, ι Q x * ι Q x = algebraMap k (CliffordAlgebra Q) (Q x)) ∧
      Function.Injective (ι Q) :=
  ⟨finrank_cliffordAlgebra Q, iSup_range_ι_pow_eq_top Q, ι_mul_ι_self Q, cliffordι_injective Q⟩

omit [Invertible (2 : k)] [FiniteDimensional k V] in
/-- **The relation (2.10)** (Cassels, Ch. 10, proof of Theorem 2.1, p. 172): for $x, y \in V$,
$xy + yx = 2\phi(x, y)$ in $C(V)$, where $2\phi(x, y) = Q(x + y) - Q(x) - Q(y)$ is the polar form
(`QuadraticMap.polar`). Mathlib's `CliffordAlgebra.ι_mul_ι_add_swap`. -/
@[kb "cassels1978" "Ch. 10, Thm. 2.1, proof, (2.10), p. 172 (xy + yx = 2φ(x, y))"]
theorem ι_mul_ι_add_swap_eq (x y : V) :
    ι Q x * ι Q y + ι Q y * ι Q x = algebraMap k (CliffordAlgebra Q) (QuadraticMap.polar Q x y) :=
  CliffordAlgebra.ι_mul_ι_add_swap x y

attribute [kb "cassels1978" "Ch. 10, Thm. 2.1, proof, p. 173 (dim C(V) = 2^n; proved through the exterior algebra, not the basis e(J))"]
  finrank_cliffordAlgebra

end Cassels

namespace Lattices

open NumberField

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **$\Theta(\Lambda)$** (Cassels, Ch. 10, §4, p. 182): for a lattice $\Lambda$ (`L`, an $\mathcal O_F$-submodule of $F^n$) on
the quadratic space $(F^n, Q)$ over a number field $F$, the elements of $\Theta(V)$ (`spinorKernel Q F`, O'Meara's
$O'(V)$) that carry $\Lambda$ onto itself (`autLat Q L`). -/
@[kb "cassels1978" "Ch. 10, §4, p. 182 (Θ(Λ) = Θ(V) ∩ O(Λ); generalization: number field)"]
def thetaLat (L : Submodule (𝓞 F) (Fin n → F)) : Subgroup (orthGroup Q F) :=
  spinorKernel Q F ⊓ autLat Q L

/-- **$\Omega(\Lambda)$** (Cassels, Ch. 10, §4, p. 182): for a lattice $\Lambda$ (`L`) on $(F^n, Q)$, the elements of the
commutator subgroup $\Omega(V)$ of $O(V)$ (`commutator (orthGroup Q F)`) that carry $\Lambda$ onto itself. -/
@[kb "cassels1978" "Ch. 10, §4, p. 182 (Ω(Λ) = Ω(V) ∩ O(Λ); generalization: number field)"]
def omegaLat (L : Submodule (𝓞 F) (Fin n → F)) : Subgroup (orthGroup Q F) :=
  commutator (orthGroup Q F) ⊓ autLat Q L

end Lattices

end QuadFormsKB
