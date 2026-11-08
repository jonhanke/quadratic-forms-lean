/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, the ninth residual statement

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$.

**Layer.** Over $\mathbb Q$ at the prime $v$ over $2$; a basis $\gamma$ of $L_2$ with Gram matrix $G$ =
`locGram Q v γ` of $B$ ($G_{kk} = 2Q(b_k)$). Indices are $0$-based.

**Defines**
* `Theorem18DyadicCovered9 Q L v` (a **condition**): `Theorem18DyadicCovered8 Q L v`; or $L_2$ has a basis $\gamma$
  with a peeling chain followed by a relative chain of canonical overlattices (`PeelChainRel Q v γ ∅ ks`,
  `Section9Theorem18DyadicRelChain.lean`) and `UnitRoots Q v γ`; or the same holds for a lattice $L'$ with
  $L'_2 = L_2^\#$ and $L_2 = L_2'^\#$ (duality step, `Section9Theorem18DyadicDual.lean`);
* `Theorem18DyadicResidual9` (a **named statement**): the "only if" direction at the prime over $2$ for every lattice
  not covered by `Theorem18DyadicCovered9`.

**What `Theorem18DyadicResidual9` still contains.** A computer check (all Jordan
forms of rank $3$–$5$ with scales $1, \dots, 16$; no counterexample to Theorem 18) leaves, of the three shapes left
by the earlier steps,
the two shapes $\langle a, b\rangle \perp 16\langle c, d\rangle$ and $\langle a, b\rangle \perp 4\langle c\rangle \perp
16\langle d, e\rangle$ (Conway–Sloane's notation, $Q(x) = x^{\mathsf T}Mx$) outside `Theorem18DyadicCovered9`; the
third, $\langle a\rangle \perp 4\langle b, c\rangle \perp 16\langle d\rangle$ ($b + c \equiv 0 \pmod 4$), is covered
(`theorem18OnlyIf_of_shapeA`). In higher rank and at larger scales further shapes are expected; a complete proof needs
the Earnest–Hsia computation of $\theta(O^+(L_2))$ for every Jordan configuration.

**Proves** `theorem18OnlyIf_of_covered9`, `theorem18DyadicResidual8_of_residual9`, `theorem18Dyadic_of_residual9`,
`theorem18Statement_of_residual9`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicRelChain

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Covered9

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, ninth version**: `Theorem18DyadicCovered8`, or
$L_2$ (or the dual of $L_2$, as the localization of a lattice $L'$) has a basis $\gamma$ with
`PeelChainRel Q v γ ∅ ks` and `UnitRoots Q v γ`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, ninth version)"]
def Theorem18DyadicCovered9 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered8 Q L v ∨
    (∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n)), loc v L.1 = locAct v γ (std v) ∧
      PeelChainRel Q v γ ∅ ks ∧ UnitRoots Q v γ) ∨
    (∃ (L' : Lat ℚ n) (γ : GL (Fin n) (v.adicCompletion ℚ)) (ks : List (Fin n)),
      IsDualLoc Q (loc v L.1) (loc v L'.1) ∧ IsDualLoc Q (loc v L'.1) (loc v L.1) ∧
      loc v L'.1 = locAct v γ (std v) ∧ PeelChainRel Q v γ ∅ ks ∧ UnitRoots Q v γ)

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, ninth version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, ninth version)"]
theorem theorem18OnlyIf_of_covered9 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered9 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨γ, ks, hγ, hch, hu⟩ | ⟨L', γ, ks, h₁, h₂, hγ, hch, hu⟩
  · exact theorem18OnlyIf_of_covered8 hQ h2 hc
  · exact theorem18OnlyIf_of_peelChainRel hQ h2 γ hγ ks hch (units_of_unitRoots h2 γ hγ hu)
  · exact theorem18OnlyIf_of_dual hQ h₁ h₂
      (theorem18OnlyIf_of_peelChainRel hQ h2 γ hγ ks hch (units_of_unitRoots h2 γ hγ hu))

end Covered9

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, ninth version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered
by `Theorem18DyadicCovered9`, every $2$-adically automorphous number is, up to squares, the product of the norms of an
even number of $2$-adic root vectors (`Theorem18OnlyIf`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, ninth version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual9 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered9 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The eighth residual statement from the ninth.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the ninth residual statement)"]
theorem theorem18DyadicResidual8_of_residual9 (h : Theorem18DyadicResidual9) : Theorem18DyadicResidual8 where
  exists_rootVectors n Q hQ L v h2 _ := by
    by_cases hs : Theorem18DyadicCovered9 Q L v
    · exact theorem18OnlyIf_of_covered9 hQ h2 hs
    · exact h.exists_rootVectors n Q hQ L v h2 hs

/-- **`Theorem18Dyadic` from the ninth residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, ninth version)"]
theorem theorem18Dyadic_of_residual9 (h : Theorem18DyadicResidual9) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual8 (theorem18DyadicResidual8_of_residual9 h)

/-- **Conway–Sloane's Theorem 18 from the ninth residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual9`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, ninth version)"]
theorem theorem18Statement_of_residual9 (h : Theorem18DyadicResidual9) : Theorem18Statement :=
  theorem18Statement_of_residual8 (theorem18DyadicResidual8_of_residual9 h)

end QuadFormsKB.ConwaySloane
