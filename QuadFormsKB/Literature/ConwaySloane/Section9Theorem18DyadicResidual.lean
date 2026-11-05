/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ from a residual statement

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$
(`Theorem18Dyadic`, `Section9Theorem18Odd.lean`).

**Layer.** As in `Section9Theorem18DyadicRootGroup.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a regular form
$Q$, a lattice $L$, the root group (`rootGroup`: products of an even number of norms of $2$-adic root vectors, up to
squares) and the per-lattice condition `Theorem18OnlyIf` ($\theta(O^+(L_2))$ lies in the root group).

**Defines**
* `Theorem18DyadicCovered Q L v` (the **shape predicate**): the $2$-adic lattices for which the "only if" direction is
  proved in the library. It is the disjunction of
  (0) $n \le 1$ (`theorem18OnlyIf_of_le_one`);
  (1) the integral automorphisms of $L_2$ are products of integral reflections (`GeneratedByRootReflections`;
      `theorem18OnlyIf_of_generated`);
  (2) $L_2 = 2^kE$ with $E$ even unimodular (`IsScaledEvenUnimodular`; `theorem18OnlyIf_of_scaledEvenUnimodular`);
  (3) the root group is all of $\mathbb Q_2^\times/\mathbb Q_2^{\times 2}$ (`theorem18OnlyIf_of_eq_top`). Clause (3)
      is proved (and Theorem 18 is proved through it) for the Jordan shapes of `Section9Theorem18DyadicRootGroup.lean` (a binary constituent of type (i) with a
      unary or binary constituent at odd relative order) and `Section9Theorem18DyadicTernary.lean` (three unary
      constituents of orders $(e, e, e \pm 1)$ or $(e, e+1, e+2)$, or $(e, e, e)$ with a further unary constituent
      at odd relative order).
* `Theorem18DyadicResidual` (a **named statement**, smaller than `Theorem18Dyadic`): the "only if" direction at the
  prime over $2$ for every lattice **not** covered by the shape predicate.

**Proves**
* `theorem18OnlyIf_of_covered`: the condition holds on the covered shapes (unconditional);
* `theorem18Dyadic_of_residual`: `Theorem18Dyadic` follows from `Theorem18DyadicResidual`;
* `theorem18Statement_of_residual`: Conway–Sloane's full Theorem 18 (`Theorem18Statement`, all primes, both
  directions) follows from `Theorem18DyadicResidual`.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicEven

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

/-- **The $2$-adic shapes for which Theorem 18 ("only if") is proved** (the shape predicate of the residual
statement): (0) the dimension $n$ is at most $1$; or (1) every integral automorphism of $L_2$ is a product of
reflections in $2$-adic root vectors (`GeneratedByRootReflections`); or (2) $L_2 = 2^kE$ with $E$ even unimodular
(`IsScaledEvenUnimodular`); or (3) the products of an even number of norms of $2$-adic root vectors give every square
class of $\mathbb Q_2^\times$ (`rootGroup Q L v = ⊤`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the 2-adic shapes proved in the library)"]
def Theorem18DyadicCovered {n : ℕ} (Q : QuadForm ℚ n) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  n ≤ 1 ∨ GeneratedByRootReflections Q v L ∨ IsScaledEvenUnimodular Q L v ∨ rootGroup Q L v = ⊤

/-- **Theorem 18, "only if", at $p = 2$ on the covered shapes** (unconditional). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': the covered 2-adic shapes)"]
theorem theorem18OnlyIf_of_covered {n : ℕ} {Q : QuadForm ℚ n} (hQ : Q.Nondegenerate) {L : Lat ℚ n}
    {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hc : Theorem18DyadicCovered Q L v) :
    Theorem18OnlyIf Q L v hQ := by
  rcases hc with hn | hg | he | ht
  · exact theorem18OnlyIf_of_le_one hQ hn
  · exact theorem18OnlyIf_of_generated hQ hg
  · exact theorem18OnlyIf_of_scaledEvenUnimodular hQ h2 he
  · exact theorem18OnlyIf_of_eq_top hQ ht

/-- **Theorem 18 at $p = 2$, "only if", for the residual lattices** (Conway–Sloane §9.5, p. 391, "based on Theorem 81
of [Wat3]", G. L. Watson, *Integral Quadratic Forms*, 1960), as a **named statement**: for every regular form $Q$ over
$\mathbb Q$, lattice $L$ and the prime $v$ over $2$ such that $L_2$ is **not** of a shape covered by
`Theorem18DyadicCovered`, every $2$-adically automorphous number $A \in \theta(O^+(L_2))$ is, up to squares, the
product of the norms of an even number of $2$-adic root vectors (`Theorem18OnlyIf`).

Together with the proved shapes (`theorem18OnlyIf_of_covered`) it gives `Theorem18Dyadic`
(`theorem18Dyadic_of_residual`). The remaining lattices are those with $n \ge 2$ whose integral automorphisms are not
all products of integral reflections, which are not a scaled even unimodular lattice, and whose root group is a proper
subgroup of $\mathbb Q_2^\times/\mathbb Q_2^{\times 2}$: for them an upper bound $\theta(O^+(L_2)) \subseteq$ root
group is needed, i.e. the computation of $\theta(O^+(L_2))$ from a Jordan splitting (Earnest–Hsia 1975). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', lattices outside the proved 2-adic shapes; stated; Watson 1960, Thm. 81)"]
structure Theorem18DyadicResidual : Prop where
  exists_rootVectors : ∀ (n : ℕ) (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ¬ Theorem18DyadicCovered Q L v →
      Theorem18OnlyIf Q L v hQ

/-- **`Theorem18Dyadic` from the residual statement**: on the covered shapes the "only if" direction is proved
(`theorem18OnlyIf_of_covered`), on the others it is `Theorem18DyadicResidual`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', conditional on the residual shapes)"]
theorem theorem18Dyadic_of_residual (h : Theorem18DyadicResidual) : Theorem18Dyadic where
  exists_rootVectors n Q hQ L v h2 A hA := by
    have key : Theorem18OnlyIf Q L v hQ := by
      by_cases hc : Theorem18DyadicCovered Q L v
      · exact theorem18OnlyIf_of_covered hQ h2 hc
      · exact h.exists_rootVectors n Q hQ L v h2 hc
    rw [← instAlgebraAdicCompletion_rat_eq v]
    exact key A hA

/-- **Conway–Sloane's Theorem 18 from the residual statement**: the full Theorem 18 (`Theorem18Statement`, every
prime, both directions) follows from `Theorem18DyadicResidual`; everything else is proved. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (conditional on the residual 2-adic shapes)"]
theorem theorem18Statement_of_residual (h : Theorem18DyadicResidual) : Theorem18Statement :=
  theorem18Statement_of_dyadic (theorem18Dyadic_of_residual h)

end QuadFormsKB.ConwaySloane
