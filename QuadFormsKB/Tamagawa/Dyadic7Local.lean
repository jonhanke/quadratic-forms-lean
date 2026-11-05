/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.LocalSmith
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal
import QuadFormsKB.Literature.Hanke2011Structure.LocalGeneraNF
import QuadFormsKB.Literature.Hanke2011Structure.SquareclassSeries
import QuadFormsKB.Literature.Hanke2011Ternary.DyadicTables

/-!
# Paper 7 at $p = 2$: status of the dyadic inputs, and the residual named statement

**Part 1 (status).** Two of the three dyadic statements named in the audit of paper 7 are already theorems:

* `TraceZeroRamDyadicLocalFactors F` (`TernaryBadLocal.lean`) is `QuatOrder.traceZeroRamDyadicLocalFactors`
  (`TernaryRamDyadicLocal.lean`, via `localDensityForm_ram_dyadic`).
* `DyadicAlphaLaw Q₀` (`OrbitalNonStd.lean`) is `Tamagawa.dyadicAlphaLaw` (`LocalSmith.lean`).

The wrappers below restate them and are the places where the axioms check is recorded.

**Part 2 (Theorem 4.12 of paper 7).** What remains of the dyadic part of `TernaryLocalMassFormula` is the identification of
the *true* normalized local mass sums of $\mathbb Z_2$-valued primitive ternary forms with Table 5.3, which the repository
records as data (`dyadicA`, `dyadicB`). `DyadicTernaryLocalMassTable` states exactly that identification and nothing else.

Indices are 0-based.
-/

open IsDedekindDomain NumberField

namespace QuadFormsKB.Dyadic7

noncomputable section

/-! ### Part 1: the first two inputs are theorems -/

section Status

variable {F : Type} [Field F] [NumberField F]

/-- **The local factors of the trace-zero lattice at the ramified dyadic places hold** for every number field $F$ whose ring of
integers is a principal ideal domain: this is the statement `Tamagawa.TraceZeroRamDyadicLocalFactors F`, proved in
`QuatOrder.traceZeroRamDyadicLocalFactors`. -/
@[kb "voight2021" "§§13.3, 22.1 (the maximal order of the dyadic division algebra) [unverified]; Weil 1982, §3.7(a)"]
theorem traceZeroRamDyadicLocalFactors_holds [IsPrincipalIdealRing (𝓞 F)] :
    QuatOrder.TraceZeroRamDyadicLocalFactors F :=
  QuatOrder.traceZeroRamDyadicLocalFactors

/-- **The dyadic $\alpha$ transformation law holds** for every nondegenerate integral quadratic form $Q_0$ in $n+1$ variables over
the ring of integers of a totally real number field: this is `Tamagawa.DyadicAlphaLaw Q₀`, proved in `Tamagawa.dyadicAlphaLaw`. -/
@[kb "weil1982" "§2.4 and §3.4 (Haar measures of lattice stabilizers at the dyadic places) [unverified]"]
theorem dyadicAlphaLaw_holds [IsTotallyReal F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate) :
    Tamagawa.DyadicAlphaLaw Q₀ :=
  Tamagawa.dyadicAlphaLaw Q₀ hQ₀

end Status

/-! ### Part 2: the residual statement behind Table 5.3 -/

section Table

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary

/-- **The class of $2$** in $\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$ at a prime $v$ of $\mathbb Q$: the squareclass of the
image of $2 \in \mathbb Q^\times$ in the completion. At a prime $v \mid 2$ it is a uniformizing class (valuation $1$). -/
def twoSqCl (v : HeightOneSpectrum (𝓞 ℚ)) : LocalSqCl v :=
  SqCl.mk (Units.mk0 (algebraMap ℚ (v.adicCompletion ℚ) 2) (by simp))

/-- **The normalization of a Hessian squareclass at $p = 2$ for ternary forms.** For $S$ of valuation $h$, the class
$\widetilde S = S \cdot 2^{\,1 - h}$ of valuation $1 = \operatorname{ord}_2(2)$, i.e. $S = 2^{h}u$ gives $\widetilde S = 2u$
(Hanke 2011, Definition 4.3, with $e = \operatorname{ord}_2(h_3) = 1$ and the uniformizing class $2$). -/
def tildeTernary (v : HeightOneSpectrum (𝓞 ℚ)) (S : LocalSqCl v) : LocalSqCl v :=
  S * twoSqCl v ^ (1 - SqCl.ordZ (localOrd v) (localUnits_le_ker v) S)

/-- **Named statement (paper 7, Theorem 4.12 with Tables 5.1–5.3; paper 6, Definition 4.6 at $p = 2$ for $n = 3$):** the normalized
local mass sums of the primitive nondegenerate $\mathbb Z_2$-valued ternary local genera of Hessian determinant class $S$ are the
entries of Table 5.3.

Let $v$ be the prime $2$ of $\mathbb Q$, $S$ a squareclass in $\mathrm{SqCl}(\mathbb Q_2^\times,\mathbb Z_2^\times)$ of valuation
$h \ge 1$ (so $S = 2^{h}u$ with $u$ a unit), and $G_0$ any nondegenerate primitive local genus with $\det_H(G_0) = \widetilde S$
(it exists and is unique, `uniqueNormalizedLocalGenus_of_dyadic`; its density $\beta_{G_0,2}(G_0)$ is the paper's generic density
$\beta_{3,2}(\widetilde S)$). For $\varepsilon \in \{\pm1\}$ write
$\widetilde M^{\varepsilon}(S) = \sum_{G}\beta_{G_0,2}(G_0)/\beta_{G,2}(G)$ over the local genera $G$ that are nondegenerate, primitive,
with $\det_H(G) = S$ and Hasse invariant $c_2(G) = \varepsilon$ (`LocGenus.IsGenStar`).

Fields:
* `A_eq`: $\widetilde M^{+}(S) + \widetilde M^{-}(S) = A^*_2(S)$, which Table 5.3 gives as `dyadicA h`
  ($=\tfrac14\cdot$ the $4A^*$ column at $h$).
* `B_eq`: $\widetilde M^{+}(S) - \widetilde M^{-}(S) = B^*_2(S)$, which Table 5.3 gives as
  $-\varepsilon_u\cdot\frac14\cdot$`dyadicBmag h`, $\varepsilon_u = (-1,u)_2$. Here $\varepsilon_u = -c_2(G_0)$: for $G_0 \cong \langle1,-1\rangle\perp\langle c\rangle$
  with $\det_H = -2c = 2u$ one has $c_2(G_0) = (-1,c)_2 = (-1,-u)_2 = -(-1,u)_2$; so the field is stated with $c_2(G_0)$
  (an integer $\pm1$): $B^*_2(S) = c_2(G_0)\cdot\frac14\cdot$`dyadicBmag h`.

*Status.* Not proved; this is the 2-adic genus theory of Theorem 4.12 (Conway–Sloane's 2-adic mass formula for the local genera
of Lemma 4.2 plus the Hasse-invariant counts of Lemma 4.10). It concerns only $\mathbb Z_2$-valued forms in three variables: no
global forms, classes or masses, and it is not the conclusion `TernaryLocalMassFormula`. (The sums are `finsum`s, so the statement
also entails finiteness whenever the right side is nonzero; finiteness of the set of classes of given determinant is true.)
The $h = 1$ row is the check that the sign conventions match: the unique genus is $G_0$, so the left sides are $1$ and
$c_2(G_0)$, i.e. $A^*_2 = 1$ and $B^*_2 = -\varepsilon_u$, as Table 5.3 (row 5, $\nu = -2$) records.

*Reduction.* `Dyadic7.dyadicTernaryLocalMassTable_of` (`Dyadic7Table.lean`) proves this statement from the
Conway–Sloane input `ConwaySloane.Mass.PMassFormulaTwo` and the purely combinatorial named statement
`Dyadic7.TernaryDyadicMassCount` (Table 5.3 as a class-weighted sum over ternary block decompositions, checked for
$h \le 12$ by a computer calculation outside Lean). -/
@[kb "hanke2011ternary" "Thm. 4.12 and Tables 5.1–5.3, pp. 14–22"]
structure DyadicTernaryLocalMassTable : Prop where
  /-- $\widetilde M^{+}(S) + \widetilde M^{-}(S) = $ `dyadicA h`. -/
  A_eq : ∀ (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal →
    ∀ (S : LocalSqCl v) (G₀ : LocGenus v 3), 1 ≤ SqCl.ordZ (localOrd v) (localUnits_le_ker v) S →
      G₀.Nondeg → G₀.Prim → G₀.det = tildeTernary v S →
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, G₀.beta / G.beta) +
        (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, G₀.beta / G.beta) =
        ((dyadicA (SqCl.ordZ (localOrd v) (localUnits_le_ker v) S).toNat : ℚ) : ℝ)
  /-- $\widetilde M^{+}(S) - \widetilde M^{-}(S) = c_2(G_0)\cdot$ `dyadicBmag h` $/\,4$. -/
  B_eq : ∀ (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal →
    ∀ (S : LocalSqCl v) (G₀ : LocGenus v 3), 1 ≤ SqCl.ordZ (localOrd v) (localUnits_le_ker v) S →
      G₀.Nondeg → G₀.Prim → G₀.det = tildeTernary v S →
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, G₀.beta / G.beta) -
        (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, G₀.beta / G.beta) =
        (G₀.hasse : ℝ) *
          ((dyadicBmag (SqCl.ordZ (localOrd v) (localUnits_le_ker v) S).toNat : ℚ) : ℝ) / 4

/-- **Comparison with the data in `DyadicTables.lean`.** The $B$ field equals Table 5.3's `dyadicB` with
$\varepsilon_u = -c_2(G_0)$ (for $c_2(G_0) = \pm1$): `dyadicB εu h = c₂(G₀) * dyadicBmag h / 4`. -/
@[kb "hanke2011ternary" "§5, Table 5.3, pp. 21–22 (sign convention)"]
theorem dyadicB_neg_hasse (c : ℤˣ) (h : ℕ) :
    dyadicB (-c) h = ((c : ℤ) : ℚ) * dyadicBmag h / 4 := by
  unfold dyadicB
  simp

end Table

end

end QuadFormsKB.Dyadic7

#print axioms QuadFormsKB.Dyadic7.traceZeroRamDyadicLocalFactors_holds
#print axioms QuadFormsKB.Dyadic7.dyadicAlphaLaw_holds
#print axioms QuadFormsKB.Dyadic7.dyadicB_neg_hasse
