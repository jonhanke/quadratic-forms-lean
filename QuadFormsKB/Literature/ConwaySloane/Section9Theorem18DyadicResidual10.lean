/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, the tenth residual statement

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$.

**Defines**
* `Theorem18DyadicCovered10 Q L v` (a **condition**): `Theorem18DyadicCovered9 Q L v`; or $L_2$ has a basis $\gamma$
  with a peeling chain with partners (`PeelChainPair Q v γ ∅ ks`, `Section9Theorem18DyadicPeelPair.lean`); or the same
  holds for a lattice $L'$ with $L'_2 = L_2^\#$ and $L_2 = L_2'^\#$ (duality step);
* `Theorem18DyadicResidual10` (a **named statement**): the "only if" direction at the prime over $2$ for every lattice
  not covered by `Theorem18DyadicCovered10`.

**What `Theorem18DyadicResidual10` still contains.** A computer check finds no
lattice outside `Theorem18DyadicCovered10` among the Jordan forms it enumerates (ranks 3 to 5, scales 1 to 16):
the three shapes left by the earlier steps, $\langle a, b\rangle \perp 16\langle c, d\rangle$,
$\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$ and
$\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$ are covered. Outside the checked range (higher
rank, larger scales, Jordan components not orthogonally diagonal in the chosen basis) the statement is open; a
complete proof needs either a proof that every $2$-adic Jordan form has a basis satisfying one of the covered shape
predicates, or the Earnest–Hsia computation of $\theta(O^+(L_2))$ for every Jordan configuration.

**Proves** `theorem18OnlyIf_of_covered10`, `theorem18DyadicResidual9_of_residual10`, `theorem18Dyadic_of_residual10`,
`theorem18Statement_of_residual10`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicPeelPair
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual9

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Covered10

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, tenth version**: `Theorem18DyadicCovered9`, or
$L_2$ (or the dual of $L_2$, as the localization of a lattice $L'$) has a basis $\gamma$ with
`PeelChainPair Q v γ ∅ ks`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, tenth version)"]
def Theorem18DyadicCovered10 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered9 Q L v ∨
    (∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n × Option (Fin n))),
      loc v L.1 = locAct v γ (std v) ∧ PeelChainPair Q v γ ∅ ks) ∨
    (∃ (L' : Lat ℚ n) (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n × Option (Fin n))),
      IsDualLoc Q (loc v L.1) (loc v L'.1) ∧ IsDualLoc Q (loc v L'.1) (loc v L.1) ∧
      loc v L'.1 = locAct v γ (std v) ∧ PeelChainPair Q v γ ∅ ks)

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, tenth version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, tenth version)"]
theorem theorem18OnlyIf_of_covered10 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered10 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨γ, ks, hγ, hch⟩ | ⟨L', γ, ks, h₁, h₂, hγ, hch⟩
  · exact theorem18OnlyIf_of_covered9 hQ h2 hc
  · exact theorem18OnlyIf_of_peelChainPair hQ h2 γ hγ ks hch
  · exact theorem18OnlyIf_of_dual hQ h₁ h₂ (theorem18OnlyIf_of_peelChainPair hQ h2 γ hγ ks hch)

end Covered10

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, tenth version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered
by `Theorem18DyadicCovered10`, every $2$-adically automorphous number is, up to squares, the product of the norms of
an even number of $2$-adic root vectors (`Theorem18OnlyIf`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, tenth version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual10 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered10 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The ninth residual statement from the tenth.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the tenth residual statement)"]
theorem theorem18DyadicResidual9_of_residual10 (h : Theorem18DyadicResidual10) : Theorem18DyadicResidual9 where
  exists_rootVectors n Q hQ L v h2 _ := by
    by_cases hs : Theorem18DyadicCovered10 Q L v
    · exact theorem18OnlyIf_of_covered10 hQ h2 hs
    · exact h.exists_rootVectors n Q hQ L v h2 hs

/-- **`Theorem18Dyadic` from the tenth residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, tenth version)"]
theorem theorem18Dyadic_of_residual10 (h : Theorem18DyadicResidual10) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual9 (theorem18DyadicResidual9_of_residual10 h)

/-- **Conway–Sloane's Theorem 18 from the tenth residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual10`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, tenth version)"]
theorem theorem18Statement_of_residual10 (h : Theorem18DyadicResidual10) : Theorem18Statement :=
  theorem18Statement_of_residual9 (theorem18DyadicResidual9_of_residual10 h)

end QuadFormsKB.ConwaySloane
