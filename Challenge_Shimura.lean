/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.HClassFinite

/-!
# Headline statements: G. Shimura, Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups

The fundamental theorem on representations (Theorem 11.6) and the mass formula (13.18).

Every proof here is a deliberate `sorry`. `Solution_Shimura.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/Shimura.json`) checks that each theorem of
`Solution_Shimura.lean` has exactly the statement given here and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. The headlines are split into one file per book or topic (`comparator.json`
lists them), so that each check loads only what its statements need.

**Conventions.** Q denotes a quadratic form (`QuadForm R n`: the polynomial ∑_{i ≤ j} c_ij x_i x_j) or a quadratic
form on an abstract vector space (Mathlib's `QuadraticForm F V`). Classes of lattices are isometry classes under the
full orthogonal group O(Q) (improper isometries included), and every lattice L' in a genus is weighted by 1/|O(L')|.
F is a number field with ring of integers 𝓞 F; "totally positive" means positive under every real embedding.

**No hidden default values.** Some notions in the formulas take a default value outside their intended range:
`∏'` (Mathlib's unconditional infinite product) is `1` when the product does not converge unconditionally, `∑ᶠ` is
`0` over an infinite set, `Nat.card` is `0` for an infinite type, and `L_F(1, χ)` (`LOne`, a limit) is a junk value
when the limit does not exist. Each headline therefore states, as extra conjuncts, the facts that make every such
term meaningful: the genus has finitely many classes, the automorphism groups and representation sets are finite,
the infinite products converge unconditionally, and L_F(1, χ) exists (and is positive).
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.HilbertModular

/-! ## Shimura's fundamental theorem on representations and the mass formula (13.18) (new in 0.6.0)

G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups* (2004): Theorem 11.6 (i) and
(v) and the formula (13.18), over every number field, with Theorem 10.5 (the local transitivity theorem) proved at
every finite place, the dyadic ones included. The statements are the library's named propositions; their content
is given in each docstring. -/

section ShimuraFundamental

/-- **Shimura's fundamental theorem, Theorem 11.6 (i) and (11.7)** (G. Shimura, *Arithmetic and Analytic Theories
of Quadratic Forms and Clifford Groups*, Mathematical Surveys and Monographs 109, AMS, 2004, p. 104).
`Shimura2004.Theorem11_6_i` states: let F be a number field, (V, φ) = (F^n, Q) nondegenerate with n > 2 satisfying
Shimura's condition (9.2) (`Shimura2004.Cond92`), L a 𝔤-maximal lattice (`Shimura2004.IsGMaximal`), h ∈ V with
q = Q(h) ≠ 0, 𝔟 = φ(h, L) (`Shimura2004.phiIdeal`), G = SO(V), H = SO((Fh)^⊥), and (L_i)_{i ∈ I} a family of
lattices in the H-genus of L whose G-classes cover it (`Shimura2004.IsHGenusCover`). Then I is finite, each orbit
set L_i[q, 𝔟]/Γ(L_i) of the solutions x ∈ L_i of Q(x) = q with φ(x, L_i) = 𝔟 is finite
(`Shimura2004.solOrbits`), their disjoint union is in bijection with the H-classes in the H-genus of L
(`Shimura2004.hClassesInHGenus`), and #(H \ H_𝔸 / (H_𝔸 ∩ C)) = ∑_i #(L_i[q, 𝔟]/Γ(L_i)) (11.7)
(`Shimura2004.hDoubleCosets`). -/
theorem shimura_theorem11_6_i : Shimura2004.Theorem11_6_i := by
  sorry

/-- **Shimura's Theorem 11.6 (v)** (Shimura 2004, p. 104). `Shimura2004.Theorem11_6_v` states: with the notation of
`shimura_theorem11_6_i`, a lattice Λ in the SO-genus of L (`Shimura2004.soGenus`) has a solution x ∈ Λ of Q(x) = q
with φ(x, Λ) = 𝔟 (`Shimura2004.solSetLat`) if and only if Λ is SO-equivalent to some L_i
(`Shimura2004.SOClassRel`). -/
theorem shimura_theorem11_6_v : Shimura2004.Theorem11_6_v := by
  sorry

/-- **Shimura's mass formula for representations, (13.18)** (Shimura 2004, pp. 134–135, the totally definite case
of Theorem 13.12 (13.17b)). `Shimura2004.Formula13_18` states: with the notation of `shimura_theorem11_6_i` and Q
totally positive definite (F totally real),
∑_{i ∈ I} #L_i[q, 𝔟] / [Γ(L_i) : 1] = m(H, H_𝔸 ∩ C),
the left side a `finsum` of `Set.ncard (Shimura2004.solSetLat …) / Nat.card (Shimura2004.gammaLat …)`, the right
side the mass of the double cosets H \ H_𝔸 / (H_𝔸 ∩ C) inside the finite adelic points (`Tamagawa.dcMass`, with
`Shimura2004.hRat`, `Shimura2004.hAf`, `Shimura2004.stabC`, `Shimura2004.diagF`): the weighted number of
representations of q by the lattices of the cover is the mass of the orthogonal complement group. -/
theorem shimura_formula13_18 : Shimura2004.Formula13_18 := by
  sorry

end ShimuraFundamental

end QuadFormsKB.Headlines
