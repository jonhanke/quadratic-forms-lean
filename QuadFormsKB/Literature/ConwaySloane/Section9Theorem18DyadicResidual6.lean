/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, the sixth residual statement

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$.

**Defines**
* `Theorem18DyadicCovered6 Q L v` (a **condition**): the shapes of `Theorem18DyadicCovered5`, or a peeling chain with
  a spinor-norm remainder (`PeelChainTheta`: the remainder after peeling has rank $\le 2$, or is a scaled even
  unimodular block, or a scaled $E \perp \langle 2u\rangle$ block), or the shape
  $2^k(E \perp \langle 2a, 2b\rangle)$ with $a + b \equiv 0 \pmod 4$ (`IsScaledEvenUnimodularPerpTwoPair`);
* `Theorem18DyadicResidual6` (a **named statement**): the "only if" direction at the prime over $2$ for every lattice
  not covered by `Theorem18DyadicCovered6`.

**Proves** `theorem18OnlyIf_of_covered6` (unconditional on the covered shapes),
`theorem18DyadicResidual5_of_residual6`, `theorem18Dyadic_of_residual6`, `theorem18Statement_of_residual6`.

*Computer check* (outside Lean): for all 3654 $2$-adic Jordan forms of
rank $3$ and $4$ with scales $1, 2, 4, 8$, a sampled lower bound of $\theta(O^+(L_2))$ (Cayley transforms and
Zassenhaus' formula) lies in the root group; the root group is everything or exactly the unit classes. No
counterexample to Theorem 18 was found.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPeelTheta
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPairGlue

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Covered6

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, sixth version**: `Theorem18DyadicCovered5`, or
$L_2$ has a basis $\gamma$ and a list of indices with the shape `PeelChainTheta (locGram Q v γ) ∅ ks`, or $L_2$ has the
shape `IsScaledEvenUnimodularPerpTwoPair`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, sixth version)"]
def Theorem18DyadicCovered6 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered5 Q L v ∨
    (∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n)),
      loc v L.1 = locAct v γ (std v) ∧ PeelChainTheta (locGram Q v γ) ∅ ks) ∨
    IsScaledEvenUnimodularPerpTwoPair Q L v

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, sixth version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, sixth version)"]
theorem theorem18OnlyIf_of_covered6 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered6 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨γ, ks, hγ, hks⟩ | hc
  · exact theorem18OnlyIf_of_covered5 hQ h2 hc
  · exact theorem18OnlyIf_of_peelChainTheta hQ h2 γ hγ ks hks
  · exact theorem18OnlyIf_of_pairGlue hQ h2 hc

end Covered6

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, sixth version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered
by `Theorem18DyadicCovered6`, every $2$-adically automorphous number is, up to squares, the product of the norms of an
even number of $2$-adic root vectors (`Theorem18OnlyIf`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, sixth version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual6 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered6 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The fifth residual statement from the sixth.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the sixth residual statement)"]
theorem theorem18DyadicResidual5_of_residual6 (h : Theorem18DyadicResidual6) : Theorem18DyadicResidual5 where
  exists_rootVectors n Q hQ L v h2 _ := by
    by_cases hs : Theorem18DyadicCovered6 Q L v
    · exact theorem18OnlyIf_of_covered6 hQ h2 hs
    · exact h.exists_rootVectors n Q hQ L v h2 hs

/-- **`Theorem18Dyadic` from the sixth residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, sixth version)"]
theorem theorem18Dyadic_of_residual6 (h : Theorem18DyadicResidual6) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual5 (theorem18DyadicResidual5_of_residual6 h)

/-- **Conway–Sloane's Theorem 18 from the sixth residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual6`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, sixth version)"]
theorem theorem18Statement_of_residual6 (h : Theorem18DyadicResidual6) : Theorem18Statement :=
  theorem18Statement_of_residual5 (theorem18DyadicResidual5_of_residual6 h)

end QuadFormsKB.ConwaySloane
