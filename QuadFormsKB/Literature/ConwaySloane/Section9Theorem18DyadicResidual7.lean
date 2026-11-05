/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, the seventh residual statement

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$.

**Defines**
* `Theorem18DyadicCovered7 Q L v` (a **condition**): `Theorem18DyadicCovered6`, or $L_2$ has a basis $\gamma$ with a
  chain of canonical overlattices (`OverChain Q v γ`) and root vectors for every unit class (`UnitRoots Q v γ`);
* `Theorem18DyadicResidual7` (a **named statement**): the "only if" direction at the prime over $2$ for every lattice
  not covered by `Theorem18DyadicCovered7`.

**Proves** `theorem18OnlyIf_of_covered7`, `theorem18DyadicResidual6_of_residual7`, `theorem18Dyadic_of_residual7`,
`theorem18Statement_of_residual7`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual6
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicOverChain

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Covered7

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, seventh version**: `Theorem18DyadicCovered6`,
or $L_2$ has a basis $\gamma$ with `OverChain Q v γ` and `UnitRoots Q v γ`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, seventh version)"]
def Theorem18DyadicCovered7 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered6 Q L v ∨
    ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧ OverChain Q v γ ∧ UnitRoots Q v γ

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, seventh version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, seventh version)"]
theorem theorem18OnlyIf_of_covered7 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered7 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨γ, hγ, hch, hu⟩
  · exact theorem18OnlyIf_of_covered6 hQ h2 hc
  · exact theorem18OnlyIf_of_overChain hQ h2 γ hγ hch hu

end Covered7

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, seventh version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered
by `Theorem18DyadicCovered7`, every $2$-adically automorphous number is, up to squares, the product of the norms of an
even number of $2$-adic root vectors (`Theorem18OnlyIf`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, seventh version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual7 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered7 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The sixth residual statement from the seventh.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the seventh residual statement)"]
theorem theorem18DyadicResidual6_of_residual7 (h : Theorem18DyadicResidual7) : Theorem18DyadicResidual6 where
  exists_rootVectors n Q hQ L v h2 _ := by
    by_cases hs : Theorem18DyadicCovered7 Q L v
    · exact theorem18OnlyIf_of_covered7 hQ h2 hs
    · exact h.exists_rootVectors n Q hQ L v h2 hs

/-- **`Theorem18Dyadic` from the seventh residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, seventh version)"]
theorem theorem18Dyadic_of_residual7 (h : Theorem18DyadicResidual7) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual6 (theorem18DyadicResidual6_of_residual7 h)

/-- **Conway–Sloane's Theorem 18 from the seventh residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual7`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, seventh version)"]
theorem theorem18Statement_of_residual7 (h : Theorem18DyadicResidual7) : Theorem18Statement :=
  theorem18Statement_of_residual6 (theorem18DyadicResidual6_of_residual7 h)

end QuadFormsKB.ConwaySloane
