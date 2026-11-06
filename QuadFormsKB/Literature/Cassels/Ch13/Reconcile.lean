import QuadFormsKB.Literature.Cassels.Ch13.Sec3
import QuadFormsKB.Literature.Cassels.Ch13.Sec3Matrix
import QuadFormsKB.Literature.Cassels.Ch13.Sec5
import QuadFormsKB.Literature.Cassels.Ch13.Sec5Matrix

/-!
# Cassels, Chapter 13: bridges between the two versions of §3 and §5

Chapter 13, §§3–5, was formalized twice: first in namespace `QuadFormsKB.Cassels.Ch13` (`Ch13/Sec3Matrix.lean`,
`Ch13/Sec4Matrix.lean`, `Ch13/Sec4Aut.lean`, `Ch13/Sec5Matrix.lean`), then in namespace `QuadFormsKB.Reduction`
(`Ch13/Sec3*.lean`, `Ch13/Sec4.lean`, `Ch13/Sec5.lean`). The tagged statement for each item is one of the two versions. This file proves the identities
between the two sets of definitions that these choices rely on:

* the matrix (3.14) is the same in both versions (`pellMat_eq_autMat`);
* the homomorphism `Cassels.Ch13.spinRep` is Cassels' literal matrix (5.6), `Reduction.spinMat`, of the transposed
  matrix: $\mathrm{spinRep}(S) = T(S^{\mathsf T})$ (`coe_spinRep_eq_spinMat_transpose`).
-/

open Matrix

namespace QuadFormsKB.Cassels.Ch13

/-- The matrix $\begin{pmatrix}t-bu&-cu\\au&t+bu\end{pmatrix}$ of Cassels (3.14) is the same in both versions of
§3: `Reduction.pellMat` (`Ch13/Sec3.lean`) equals `autMat` (`Ch13/Sec3Matrix.lean`). -/
theorem pellMat_eq_autMat {R : Type*} [CommRing R] (a b c t u : R) :
    Reduction.pellMat a b c t u = autMat a b c t u := rfl

/-- The homomorphism `spinRep` of `Ch13/Sec5Matrix.lean` is Cassels' map $T$ of (5.6) (`Reduction.spinMat`,
`Ch13/Sec5.lean`) applied to the transposed matrix: $\mathrm{spinRep}(S) = T(S^{\mathsf T})$ for
$S \in \mathrm{GL}_2(K)$, $K$ a field. As $S \mapsto T(S)$ reverses products (the *Erratum* to Lemma 5.1),
$S \mapsto T(S^{\mathsf T})$ is a homomorphism. -/
theorem coe_spinRep_eq_spinMat_transpose {K : Type*} [Field K] (S : GL (Fin 2) K) :
    ((spinRep S : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Reduction.spinMat (S : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [coe_spinRep_field, Reduction.spinMat, det_transpose]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [symSq, mul_comm]

end QuadFormsKB.Cassels.Ch13
