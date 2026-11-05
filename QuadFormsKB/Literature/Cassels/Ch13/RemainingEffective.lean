import QuadFormsKB.Siegel.Genus

/-!
# Cassels, Chapter 13, §12: Problem 2 for definite forms

Cassels, *Rational Quadratic Forms* (1978), Ch. 13, §12, p. 327, (i): "$f_1$ and $f_2$ are definite forms. Then the
solution of Problem 2 is trivial, as already remarked in Chapter 9, Section 1." Problem 2 (p. 325) asks whether two
integral forms are integrally equivalent and, if so, for an explicit equivalence.

As elsewhere in the library (`Ch13/Sec12.lean`, `Ch13/Sec3.lean`), the effective statement is formalized in its
*effective form*: the equivalences lie in an explicit finite set, so a finite search decides Problem 2. Here: the
$j$-th column of an integral $P$ with $f_1(P\vec x) = f_2(\vec x)$ represents the integer $f_2(\vec e_j)$ by $f_1$,
and for positive definite $f_1$ these representations form a finite set (`IntQF.PosDef.repSet_finite`, a box
$\lvert x_i\rvert \le \lceil R\rceil$ with $R$ explicit in `IntQF.PosDef.finite_setOf_eval_le`). The computability of
the search itself is not formalized.
-/

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **Problem 2 for definite forms** (Cassels, Ch. 13, §12, p. 327, (i); Ch. 9, §1): let $f_1$ be a positive
definite integral form and $f_2$ any integral form in $n$ variables. The set of integral equivalences
$\{P \in \mathrm{GL}_n(\mathbb Z) : f_1(P\vec x) = f_2(\vec x) \text{ for all } \vec x \in \mathbb Z^n\}$ is finite:
the $j$-th column $P\vec e_j$ is one of the finitely many representations of $f_2(\vec e_j)$ by $f_1$, and
$P \mapsto (P\vec e_j)_j$ is injective. So a finite search decides whether $f_1$ and $f_2$ are equivalent and finds
all equivalences. (A negative definite $f_1$ is the case $-f_1$.) -/
@[kb "cassels1978" "Ch. 13, §12, p. 327, (i) (Problem 2 for definite forms)"]
theorem finite_equiv_of_posDef {f₁ : IntQF n} (hf₁ : f₁.PosDef) (f₂ : IntQF n) :
    {P : GL (Fin n) ℤ | ∀ x, f₁.eval (P.val *ᵥ x) = f₂.eval x}.Finite := by
  set t : Fin n → Set (Fin n → ℤ) := fun j => Siegel.repSet f₁ (f₂.eval (Pi.single j 1))
  have ht : {c : Fin n → Fin n → ℤ | ∀ j, c j ∈ t j}.Finite :=
    Set.Finite.pi' fun j => hf₁.repSet_finite _
  refine Set.Finite.of_finite_image (f := fun P : GL (Fin n) ℤ => fun j => P.val *ᵥ Pi.single j 1)
    (ht.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ j
    exact hP _
  · intro P _ P' _ h
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrFun (congrFun h j) i
    simpa [mulVec_single_one] using this

end QuadFormsKB.Reduction
