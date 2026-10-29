/-
# O'Meara §52: full matrix algebras (52:5, 52:6)

**Setting.** $F$ a field, $M_n(F)$ the algebra of $n \times n$ matrices over $F$ (`Matrix (Fin n) (Fin n) F`).
O'Meara's *central simple* is `Algebra.IsCentral F A` together with `IsSimpleRing A` (as in `Sec52A.lean`).

**Proves**
* `matrix_isCentral_isSimpleRing` (**52:5**): for $n \ge 1$, $M_n(F)$ is central simple over $F$;
* `matrix_tensor_matrix_equiv` (**52:6**): an algebra isomorphism
  $M_m(F) \otimes_F M_n(F) \cong M_{mn}(F)$.

**Proof notes.** Both are Mathlib facts: `Algebra.IsCentral` of matrix algebras (`Mathlib/Algebra/Central/Matrix`),
`IsSimpleRing.matrix`, and `Matrix.kroneckerAlgEquiv` (the Kronecker product, which is O'Meara's base
$E_{\lambda\mu} = e_{ij} \otimes f_{kl}$), followed by the reindexing $\mathrm{Fin}\,m \times \mathrm{Fin}\,n \simeq
\mathrm{Fin}(mn)$ (`finProdFinEquiv`). The book needs $n \ge 1$ implicitly (for $n = 0$ the algebra is $0$, which is
not simple). Indices are $0$-based.
-/
import Mathlib
import QuadFormsKB.Citation

open scoped TensorProduct

noncomputable section

namespace QuadFormsKB.OMeara

/-- **Proposition 52:5** (O'Meara 1963, p. 122): for $n \ge 1$ the full matrix algebra $M_n(F)$ over a field $F$ is
central simple over $F$: its centre is $F \cdot 1$ and its only two-sided ideals are $0$ and $M_n(F)$. -/
@[kb "omeara1963" "§52, 52:5, p. 122"]
theorem matrix_isCentral_isSimpleRing (F : Type*) [Field F] (n : ℕ) [NeZero n] :
    Algebra.IsCentral F (Matrix (Fin n) (Fin n) F) ∧ IsSimpleRing (Matrix (Fin n) (Fin n) F) :=
  ⟨inferInstance, inferInstance⟩

/-- **Proposition 52:6** (O'Meara 1963, pp. 122–123): there is an $F$-algebra isomorphism
$M_m(F) \otimes_F M_n(F) \cong M_{mn}(F)$ (the Kronecker product, sending $e_{ij} \otimes f_{kl}$ to a defining matrix
of $M_{mn}(F)$). -/
@[kb "omeara1963" "§52, 52:6, pp. 122–123"]
def matrix_tensor_matrix_equiv (F : Type*) [Field F] (m n : ℕ) :
    Matrix (Fin m) (Fin m) F ⊗[F] Matrix (Fin n) (Fin n) F ≃ₐ[F] Matrix (Fin (m * n)) (Fin (m * n)) F :=
  (Matrix.kroneckerAlgEquiv (Fin m) (Fin n) F).trans (Matrix.reindexAlgEquiv F F finProdFinEquiv)

end QuadFormsKB.OMeara
