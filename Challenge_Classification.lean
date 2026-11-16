/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmasHold
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicClassify
import QuadFormsKB.Literature.OMeara.Sec93FStep8
import QuadFormsKB.Literature.Watson1963.Theorem1

/-!
# Headline statements: Classification of lattices and genera, and class numbers

Conway–Sloane's Theorem 18, O'Meara 93:28 and 93:29, genera from discriminant forms, and Watson's theorem.

Every proof here is a deliberate `sorry`. `Solution_Classification.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/Classification.json`) checks that each theorem of
`Solution_Classification.lean` has exactly the statement given here and depends only on the axioms `propext`,
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

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## Classification of lattices and genera

O'Meara's classification of lattices over the completion of a number field at a dyadic prime (93:28) and at a prime
where 2 is prime (93:29); Conway–Sloane's description of the p-adically automorphous numbers (Sphere Packings,
Lattices and Groups, Chapter 15, Theorem 18) at every prime; and the description of the genus of a positive definite
integral lattice by its discriminant form (Conway–Sloane 1988, §11, Lemmas 2 and 4). The two O'Meara statements and
Theorem 18 are named propositions of the library (`OMeara.DyadicClassification`, `OMeara.TwoAdicClassification`,
`ConwaySloane.Theorem18Statement`), each a single field stating the theorem; the docstrings spell them out. -/

section Classification

/-- **Conway–Sloane, Theorem 18, at every prime** (J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and
Groups, Chapter 15, §9.5; "based on Theorem 81" of Watson). `ConwaySloane.Theorem18Statement` says: for every
nondegenerate form Q over ℚ in n variables, every lattice L in ℚ^n and every prime p (`v`, a nonzero prime of
𝓞_ℚ = ℤ), a p-adic unit A ∈ ℚ_p^× is p-adically automorphous, i.e. lies in θ(O⁺(L_p)), the group of spinor norms
of the proper automorphisms of L_p (`Lattices.localSpinorNormGroup Q hQ v L`), if and only if, up to squares, A is
the product Q(x_1) ⋯ Q(x_{2k}) of the norms of an even number of p-adic root vectors x_i: vectors with Q(x_i) ≠ 0
whose reflection maps L_p onto itself (`ConwaySloane.IsRootVector`). The book quotes the theorem without proof;
both directions are proved here, at p = 2 included. -/
theorem automorphous_iff_rootVectors : ConwaySloane.Theorem18Statement := by
  sorry

/-- **O'Meara 93:28: classification of lattices at a dyadic prime** (O. T. O'Meara, Introduction to Quadratic
Forms, §93F, 93:28). Let F be a number field, 𝔭 = `w` a nonzero prime of 𝓞 F, F_𝔭 the completion with ring of
integers 𝔬, and V a finite-dimensional quadratic space over F_𝔭 with form Q. `OMeara.DyadicClassification 𝔬 Q`
says: if 2 is not a unit of 𝔬 (𝔭 is dyadic) and Q is regular, let L and K be lattices on V with Jordan splittings
L = L_1 ⊥ ⋯ ⊥ L_t and K = K_1 ⊥ ⋯ ⊥ K_t (`OMeara.IsJordanSplitting`) having the same fundamental invariants
t, dim L_i, 𝔰_i, 𝔴_i, a_i (`OMeara.SameFundamentalInvariants`), and let L_(i) = L_1 ⊥ ⋯ ⊥ L_i and K_(i) be the
Jordan chains (`OMeara.jordanChain`). Then L and K are isometric (`OMeara.cls Q L = OMeara.cls Q K`) if and only if
for 1 ≤ i ≤ t - 1:
1. dL_(i)/dK_(i) ≅ 1 mod 𝔣_i (`OMeara.DiscQuotSqEquivMod`), with 𝔣_i the ideal of §93E (`OMeara.fIdeal`);
2. FL_(i) → FK_(i) ⊥ ⟨a_{i+1}⟩ (`OMeara.SpanRepresents`) when 𝔣_i ⊊ 4 a_{i+1} 𝔴_{i+1}^{-1};
3. FL_(i) → FK_(i) ⊥ ⟨a_i⟩ when 𝔣_i ⊊ 4 a_i 𝔴_i^{-1}.
Indices are 0-based in Lean: the condition for O'Meara's i is stated for the pair i, j = i + 1. -/
theorem dyadicClassification {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {V : Type*}
    [AddCommGroup V] [Module (w.adicCompletion F) V] [FiniteDimensional (w.adicCompletion F) V]
    [Module (w.adicCompletionIntegers F) V] [IsScalarTower (w.adicCompletionIntegers F) (w.adicCompletion F) V]
    (Q : QuadraticForm (w.adicCompletion F) V) :
    OMeara.DyadicClassification (w.adicCompletionIntegers F) Q := by
  sorry

/-- **O'Meara 93:29: classification of lattices at a 2-adic prime** (O. T. O'Meara, Introduction to Quadratic
Forms, §93G, 93:29). Let F be a number field, 𝔭 = `v` a nonzero prime of 𝓞 F, F_𝔭 the completion with ring of
integers 𝔬, and V a finite-dimensional quadratic space over F_𝔭 with form Q. `OMeara.TwoAdicClassification 𝔬 Q`
says: if 2 is a prime element of 𝔬 (`OMeara.IsTwoAdic`; for example F_𝔭 = ℚ_2) and Q is regular, let L and K be
lattices on V with Jordan splittings L = L_1 ⊥ ⋯ ⊥ L_t and K = K_1 ⊥ ⋯ ⊥ K_t having the same Jordan invariants
t, dim L_i, 𝔰_i, 𝔫_i (`OMeara.SameJordanInvariants`), and let L_(i), K_(i) be the Jordan chains. Then L and K are
isometric if and only if for 1 ≤ i ≤ t - 1:
1. dL_(i)/dK_(i) ≅ 1 mod 𝔫_i 𝔫_{i+1}/𝔰_i²;
2. FL_(i) → FK_(i) ⊥ ⟨2^{u_i}⟩ when 𝔫_{i+1} ⊆ 4 𝔫_i, where 2^{u_i} 𝔬 = 𝔫_i.
Here 𝔰_i is the scale and 𝔫_i the norm ideal of L_i (`OMeara.scale`, `OMeara.normIdeal`). Indices are 0-based in
Lean, as in `dyadicClassification`. -/
theorem twoAdicClassification {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {V : Type*}
    [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
    [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]
    (Q : QuadraticForm (v.adicCompletion F) V) :
    OMeara.TwoAdicClassification (v.adicCompletionIntegers F) Q := by
  sorry

/-- **The genus from the discriminant form, modulo the type** (J. H. Conway and N. J. A. Sloane, "Low-dimensional
lattices IV: the mass formula", 1988, §11, Lemma 2). Two positive definite integral lattices L and M of dimension n,
given by their Gram matrices A and B (`ConwaySloane.Mass.PosDefGram`), are in the same genus (the forms xᵀAx and
xᵀBx are in the same genus, `Siegel.SameGenus`) if and only if they have the same type T (T = 1 if the lattice is
odd, T = 2 if it is even, `ConwaySloane.Mass.gramType`) and there is an isomorphism L*/L ≅ M*/M of the discriminant
groups preserving norms modulo T (`ConwaySloane.Mass.DiscIso T A B`). -/
theorem sameGenus_iff_discIso {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} (hA : ConwaySloane.Mass.PosDefGram A)
    (hB : ConwaySloane.Mass.PosDefGram B) :
    Siegel.SameGenus (LocalDensity.ofMatrixZ A) (LocalDensity.ofMatrixZ B) ↔
      (ConwaySloane.Mass.gramType A = ConwaySloane.Mass.gramType B ∧
        ConwaySloane.Mass.DiscIso (ConwaySloane.Mass.gramType A) A B) := by
  sorry

/-- **The genus from the discriminant form, modulo 1** (J. H. Conway and N. J. A. Sloane, "Low-dimensional
lattices IV: the mass formula", 1988, §11, Lemma 4). Two positive definite integral lattices L and M of dimension n
(Gram matrices A and B) are in the same genus if and only if they have the same type and there is an isomorphism
L*/L ≅ M*/M of the discriminant groups preserving norms modulo 1 (`ConwaySloane.Mass.DiscIso 1 A B`). -/
theorem sameGenus_iff_discIso_one {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ} (hA : ConwaySloane.Mass.PosDefGram A)
    (hB : ConwaySloane.Mass.PosDefGram B) :
    Siegel.SameGenus (LocalDensity.ofMatrixZ A) (LocalDensity.ofMatrixZ B) ↔
      (ConwaySloane.Mass.gramType A = ConwaySloane.Mass.gramType B ∧ ConwaySloane.Mass.DiscIso 1 A B) := by
  sorry

end Classification

/-! ## Class numbers

Watson's theorem (1963): a genus of positive definite integer-valued forms in more than 11 variables is never a single
class. -/

section ClassNumbers

/-- **Watson's theorem: every genus in n > 11 variables has at least two classes** (G. L. Watson, "The
class-number of a positive quadratic form", Proc. London Math. Soc. (3) 13 (1963), 549–576, Theorem 1, the case
n ≥ 12 of (1.1); quoted without proof in J. W. S. Cassels, Rational Quadratic Forms, Appendix A, §3, p. 364). Let Q
be a positive definite integer-valued form in n > 11 variables (`QuadForm ℤ n`, the polynomial ∑_{i ≤ j} c_ij x_i x_j
with integer coefficients, and `IntQF.PosDef Q`). Then the genus of Q contains at least two GL_n(ℤ)-classes of forms
(`Siegel.genusClasses Q`, counted with Mathlib's `Set.encard`), and finitely many. Watson's other case of (1.1),
n = 11, is not part of this statement. -/
theorem watson_twoClasses {n : ℕ} (hn : 11 < n) (Q : QuadForm ℤ n) (hQ : IntQF.PosDef Q) :
    (2 : ℕ∞) ≤ (Siegel.genusClasses Q).encard ∧ (Siegel.genusClasses Q).Finite := by
  sorry

end ClassNumbers

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.

Tamagawa number and mass formula
* `Lattices.genusClasses Q L` (Lattices/Finite.lean): the classes L' in the genus of L (lattices in F^n up to isometry
  by the full O(Q), improper isometries included); `Lattices.LatClass.autCard Q c` (same file): |O(M)| =
  `Nat.card (autLat Q M)` for any lattice M in the class c. The mass ∑ 1/|O(L')| is written out in the statement
  (it is `Lattices.mass Q L`, same file).
* `Lattices.SameGenus Q L M`, `Lattices.autLat Q M` (Lattices/Genus.lean): M is in the genus of L; O(M).

Classical cases over ℚ
* `IntQF.PosDef Q` (Literature/Universal/Basic.lean): Q(x) > 0 for every nonzero x ∈ ℤ^n.
* `Siegel.genusClasses Q`, `Siegel.QClass.repNum`, `Siegel.QClass.autCard` (Siegel/Genus.lean): the
  GL_n(ℤ)-classes of forms in the genus of Q; r_{Q'}(m) and |Aut(Q')| for a form Q' in the class.

Exact mass formulas (paths in `Literature/`)
* `LocalDensity.ofMatrixZ A` (LocalDensity/JordanForm.lean, outside `Literature/`): the form xᵀAx of an integer
  matrix A. `Siegel.mass Q`, `Siegel.genusClasses Q` and `IntQF.PosDef Q` as in the classical cases over ℚ.

Classification of lattices and genera (paths in `Literature/`)
* `ConwaySloane.Theorem18Statement`, `ConwaySloane.IsRootVector` (ConwaySloane/Section9Theorem18.lean): Theorem 18;
  p-adic root vectors. `Lattices.localSpinorNormGroup` (OMeara/Sec101D.lean): θ(O⁺(L_𝔭)) as a subgroup of F_𝔭^×.
  `Lattices.SqClass.mk`, `Lattices.sqClassOf`, `Lattices.valProd` (Lattices/SpinorNorm.lean, Lattices/SpinorKernel.lean,
  outside `Literature/`): square classes; the product of the values Q(x) over a list of vectors.
* `OMeara.DyadicClassification` (OMeara/Sec93E.lean): 93:28; with `OMeara.fIdeal`, `OMeara.fundWeight`,
  `OMeara.SameFundamentalInvariants`, `OMeara.DiscQuotSqEquivMod`, `OMeara.SpanRepresents` (OMeara/Sec93E.lean),
  `OMeara.SqEquivMod` (OMeara/Sec93.lean), `OMeara.IsJordanSplitting` (OMeara/Sec91Jordan.lean), `OMeara.jordanChain`
  (OMeara/Sec91Chain.lean), `OMeara.scale`, `OMeara.normIdeal`, `OMeara.cls` (OMeara/Sec82.lean).
* `OMeara.TwoAdicClassification`, `OMeara.IsTwoAdic`, `OMeara.SameJordanInvariants` (OMeara/Sec93G.lean): 93:29.
* `ConwaySloane.Mass.PosDefGram`, `ConwaySloane.Mass.gramType`, `ConwaySloane.Mass.DiscIso`
  (ConwaySloane/Mass/GenusLemmas.lean): positive definite integral Gram matrices; the type (1 odd, 2 even); an
  isomorphism of discriminant groups preserving norms modulo T. `Siegel.SameGenus` (Siegel/Genus.lean, outside
  `Literature/`): equivalent over ℝ and over every ℤ_p.

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).
-/

end QuadFormsKB.Headlines
