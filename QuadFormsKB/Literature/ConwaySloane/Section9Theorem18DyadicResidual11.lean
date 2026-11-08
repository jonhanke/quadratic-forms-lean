/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, the eleventh residual statement

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$.

**Defines**
* `Theorem18DyadicCovered11 Q L v` (a **condition**): `Theorem18DyadicCovered10 Q L v`; or $L_2$ has a basis
  $\gamma$ with `IsDiagBlock` (diagonal except for one scaled even unimodular block,
  `Section9Theorem18DyadicDiagBlock.lean`), or with `IsDiagCore` and a terminal core; or $L_2$ has a basis $\gamma$ with a two-sided peeling chain
  (`TwoSidedChain`, `Section9Theorem18DyadicTwoSided.lean`);
* `Theorem18DyadicResidual11` (a **named statement**): the "only if" direction at the prime over $2$ for every
  lattice not covered by `Theorem18DyadicCovered11`.

**What `Theorem18DyadicResidual11` still contains.** In a Jordan basis (O'Meara 93:15; odd unimodular constituents
diagonalized), every $2$-adic lattice whose Jordan decomposition has **at most one even (type II) constituent**
satisfies `IsDiagBlock` (the dual Gram matrix restricted to the block is the inverse of the block, scaled by
$c^{-1}$), so it is covered, for every rank and every choice of scales (`theorem18OnlyIf_of_diagBlock`). The
statement therefore concerns only lattices with **at least two even constituents** at different scales which are
not covered by the shapes of `Theorem18DyadicCovered10`. If the root group is not everything, two even constituents
lie at scales of the same parity, the odd constituents lie at scales of the other parity and have rank at most $2$
(otherwise `rootGroup_eq_top_of_binary_binary`, `rootGroup_eq_top_of_binary_single`, `rootGroup_eq_top_of_three`
give the root group everything), and the root group is exactly the unit classes; after two-sided peeling the
remainder has an even constituent at each end. A computer check finds every
such lattice in its range covered by `Theorem18DyadicCovered10`. A complete proof needs a general upper bound
$\theta(O^+(L_2)) \subseteq \mathbb Z_2^\times\mathbb Q_2^{\times 2}$ for these lattices (the Earnest–Hsia
computation), which is not formalized.

**Proves** `theorem18OnlyIf_of_covered11`, `theorem18DyadicResidual10_of_residual11`,
`theorem18Dyadic_of_residual11`, `theorem18Statement_of_residual11`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicDiagBlock

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Covered11

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved, eleventh version**: `Theorem18DyadicCovered10`,
or $L_2$ has a basis $\gamma$ (with dual Gram matrix $N$, $GN = 1$) satisfying `IsDiagBlock` (at most one even
Jordan constituent), or `IsDiagCore` with a terminal core (the $1$-dimensional constituents outside the scale range of
the core), or a two-sided peeling chain `TwoSidedChain Q v γ N hN ∅ ks`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library, eleventh version)"]
def Theorem18DyadicCovered11 (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Theorem18DyadicCovered10 Q L v ∨
    (∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (N : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ))
      (B : Finset (Fin n)) (c : v.adicCompletion ℚ),
      loc v L.1 = locAct v γ (std v) ∧ locGram Q v γ * N = 1 ∧ IsDiagBlock v (locGram Q v γ) N B c) ∨
    (∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (N : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ))
      (hN : locGram Q v γ * N = 1) (B : Finset (Fin n)),
      loc v L.1 = locAct v γ (std v) ∧ IsDiagCore v (locGram Q v γ) N B ∧ TwoSidedChain Q v γ N hN Bᶜ []) ∨
    (∃ (γ : GL (Fin n) (v.adicCompletion ℚ)) (N : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ))
      (hN : locGram Q v γ * N = 1) (ks : List (Fin n × Option (Fin n) × Bool)),
      loc v L.1 = locAct v γ (std v) ∧ TwoSidedChain Q v γ N hN ∅ ks)

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes, eleventh version** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes, eleventh version)"]
theorem theorem18OnlyIf_of_covered11 (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hc : Theorem18DyadicCovered11 Q L v) : Theorem18OnlyIf Q L v hQ := by
  rcases hc with hc | ⟨γ, N, B, c, hγ, hN, hdb⟩ | ⟨γ, N, hN, B, hγ, hdc, ht⟩ | ⟨γ, N, hN, ks, hγ, hch⟩
  · exact theorem18OnlyIf_of_covered10 hQ h2 hc
  · exact theorem18OnlyIf_of_diagBlock hQ h2 γ hγ N hN hdb
  · exact theorem18OnlyIf_of_diagCore hQ h2 γ hγ N hN hdc ht
  · exact theorem18OnlyIf_of_twoSidedChain hQ h2 γ hγ N hN ks hch

end Covered11

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices, eleventh version** (Conway–Sloane §9.5, p. 391,
"based on Theorem 81 of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every
regular form $Q$ over $\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered
by `Theorem18DyadicCovered11` (in particular, by the module docstring, $L_2$ has at least two even Jordan
constituents), every $2$-adically automorphous number is, up to squares, the product of the norms of an even number of
$2$-adic root vectors (`Theorem18OnlyIf`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes, eleventh version; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual11 : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered11 Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **The tenth residual statement from the eleventh.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': residual shapes from the eleventh residual statement)"]
theorem theorem18DyadicResidual10_of_residual11 (h : Theorem18DyadicResidual11) : Theorem18DyadicResidual10 where
  exists_rootVectors n Q hQ L v h2 _ := by
    by_cases hs : Theorem18DyadicCovered11 Q L v
    · exact theorem18OnlyIf_of_covered11 hQ h2 hs
    · exact h.exists_rootVectors n Q hQ L v h2 hs

/-- **`Theorem18Dyadic` from the eleventh residual statement.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes, eleventh version)"]
theorem theorem18Dyadic_of_residual11 (h : Theorem18DyadicResidual11) : Theorem18Dyadic :=
  theorem18Dyadic_of_residual10 (theorem18DyadicResidual10_of_residual11 h)

/-- **Conway–Sloane's Theorem 18 from the eleventh residual statement**: the full Theorem 18 (`Theorem18Statement`,
every prime, both directions) follows from `Theorem18DyadicResidual11`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes, eleventh version)"]
theorem theorem18Statement_of_residual11 (h : Theorem18DyadicResidual11) : Theorem18Statement :=
  theorem18Statement_of_residual10 (theorem18DyadicResidual10_of_residual11 h)

end QuadFormsKB.ConwaySloane
