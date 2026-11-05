/-
# Cassels, Chapter 13, §11: Theorem 11.2 (stated, not proved in the book)

Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §11, p. 324, states without proof (referring to Siegel (1940))
that for a regular integral form $f$ which is not an isotropic binary form, the quotient $O^+(f)\backslash O_{\mathbb R}(f)$
has finite invariant measure. Here the statement is a named proposition, `FiniteCovolume`; it is not proved and not
used as a hypothesis anywhere.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic
import QuadFormsKB.Literature.Cassels.Ch9Sec1

open Matrix MeasureTheory

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- The integral matrix $T$ as a real invertible matrix. -/
def glReal (T : GL (Fin n) ℤ) : GL (Fin n) ℝ := Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) T

/-- **Theorem 11.2** (Cassels, Ch. 13, §11, p. 324, "[not proved here]"), as a proposition: for the integral form $Q$
(real matrix $F$ = `realMat Q`) there are a Haar measure $\mu$ on the group $O_{\mathbb R}(f)$ = `realAut F` (with its
topology as a subgroup of $\mathrm{GL}_n(\mathbb R)$ and the Borel $\sigma$-algebra) and a measurable set $\mathcal S$ of
finite measure meeting every class $O^+(f)S$, $S \in O_{\mathbb R}(f)$: for every $S$ there is an integral proper automorph
$T$ with $TS \in \mathcal S$. Cassels: true when $f$ is regular and not an isotropic binary form (Siegel (1940)); the
isotropic binary forms are "a genuine exception". Stated only; Cassels gives no proof, and none is given here. -/
@[kb "cassels1978" "Ch. 13, §11, Thm. 11.2, p. 324 (stated)"]
def FiniteCovolume (Q : IntQF n) : Prop :=
  letI : MeasurableSpace (realAut (realMat Q)) := borel _
  ∃ (μ : Measure (realAut (realMat Q))) (_ : μ.IsHaarMeasure) (𝒮 : Set (realAut (realMat Q))),
    MeasurableSet 𝒮 ∧ μ 𝒮 < ⊤ ∧
      ∀ S : realAut (realMat Q), ∃ T ∈ Siegel.AutPlus Q, ∃ h : glReal T * S ∈ realAut (realMat Q),
        (⟨glReal T * S, h⟩ : realAut (realMat Q)) ∈ 𝒮

end QuadFormsKB.Reduction
