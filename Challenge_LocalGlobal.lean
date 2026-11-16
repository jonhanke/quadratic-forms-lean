/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.FunctionField.RatFuncReciprocity
import QuadFormsKB.Literature.LocalGlobal.IsometricBaseChange

/-!
# Headline statements: Local–global principles and reciprocity

Hilbert reciprocity and the Hasse–Minkowski theorem over number fields and over ℚ, and the reciprocity laws over the rational function field 𝔽_q(t).

Every proof here is a deliberate `sorry`. `Solution_LocalGlobal.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/LocalGlobal.json`) checks that each theorem of
`Solution_LocalGlobal.lean` has exactly the statement given here and depends only on the axioms `propext`,
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

/-! ## Local–global principles over number fields

Setting: F any number field. `NFPlace F` is the set of places of F (infinite places and nonzero primes of 𝓞 F);
`NFPlace.Everywhere P` means P holds over the completion F_v for every place v. Forms are `QuadForm F n`. -/

section LocalGlobal

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Hilbert reciprocity.** For a, b ∈ F^×, the local Hilbert symbol (a, b)_v is -1 at only finitely many places
v, and at an even number of them; equivalently ∏_v (a, b)_v = 1. -/
theorem hilbertReciprocity_numberField (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard := by
  sorry

/-- **Hasse–Minkowski (isotropy).** A nondegenerate quadratic form Q over F is isotropic over F if and only if it is
isotropic over every completion F_v. -/
theorem hasseMinkowski_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  sorry

/-- **Representation is local–global.** A nondegenerate quadratic form Q over F represents c ∈ F^× over F if and only
if it represents c over every completion F_v. -/
theorem represents_iff_everywhere_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) (c : F) (hc : c ≠ 0) :
    Q.RepresentsIn F c ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.RepresentsIn K c := by
  sorry

/-- **Isometry is local–global.** Two nondegenerate quadratic forms Q, R over F in the same number of variables are
isometric over F if and only if they are isometric over every completion F_v. -/
theorem isometric_iff_everywhere_numberField (Q R : QuadForm F n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn F R ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsometricIn K R := by
  sorry

/-- **Hasse–Minkowski over ℚ.** A nondegenerate quadratic form Q over ℚ, in any number of variables, is isotropic over
ℚ if and only if it is isotropic over ℝ and over ℚ_p for every prime p. -/
theorem hasseMinkowski_rat (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ RatPlace.Everywhere fun K _ _ => Q.IsotropicIn K := by
  sorry

end LocalGlobal

/-! ## Reciprocity laws over the rational function field 𝔽_q(t)

Quadratic reciprocity in 𝔽_q[t] (Dedekind) and the Hilbert reciprocity law over 𝔽_q(t), q odd: the function field
counterparts of `hilbertReciprocity_numberField`. -/

section RationalFunctionField

/-- **Quadratic reciprocity in 𝔽_q[t]** (M. Rosen, *Number Theory in Function Fields*, Graduate Texts in Mathematics 210, Springer, 2002, Theorem 3.3, due to Dedekind). Let k be a finite
field with q elements, q odd, and P, P' distinct monic irreducible polynomials in k[t]. With the Legendre
symbol (a/P) (`RatFuncQR.legendreSym P a`: 0 if P divides a, 1 if a is a nonzero square modulo P, −1
otherwise), (P'/P)(P/P') = (−1)^{(q−1)/2 · deg P · deg P'}. -/
theorem quadraticReciprocity_polynomial {k : Type} [Field k] [Fintype k] [DecidableEq k] (hk : ringChar k ≠ 2)
    (P P' : Polynomial k) (hP : Irreducible P) (hPm : P.Monic) (hP' : Irreducible P') (hP'm : P'.Monic)
    (hne : P ≠ P') :
    RatFuncQR.legendreSym P P' * RatFuncQR.legendreSym P' P =
      (-1) ^ ((Fintype.card k - 1) / 2 * P.natDegree * P'.natDegree) := by
  sorry

/-- **Hilbert reciprocity over 𝔽_q(t)**, q odd (the function field case of O. T. O'Meara, *Introduction to Quadratic Forms*, Springer, 1963,
71:18, p. 199). Let k be a finite field of odd characteristic. The places of k(t) (`RatFuncPlace k`) are the
finite places, one for each nonzero prime ideal of k[t], and the place at infinity; `v.hilbert a b` is the
Hilbert symbol (a, b)_v over the completion k(t)_v (`hilbertSymbol`: 1 if z² = a x² + b y² has a nonzero
solution, −1 otherwise). For a, b ∈ k(t)^×, (a, b)_v = −1 at only finitely many places v, and at an even
number of them: ∏_v (a, b)_v = 1. -/
theorem hilbertReciprocity_ratFunc {k : Type} [Field k] [Fintype k] (hk : ringChar k ≠ 2) (a b : RatFunc k)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : RatFuncPlace k | v.hilbert a b = -1}.Finite ∧ Even {v : RatFuncPlace k | v.hilbert a b = -1}.ncard := by
  sorry

end RationalFunctionField

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.
* `QuadForm.Nondegenerate` (Defs/QuadForm.lean): det H ≠ 0.
* `QuadForm.IsotropicIn K` (Defs/QuadForm.lean): Q(x) = 0 for some nonzero x ∈ K^n.
* `QuadForm.RepresentsIn K c` (Defs/QuadForm.lean): Q(x) = c for some x ∈ K^n.
* `QuadForm.IsometricIn K Q R` (Defs/QuadForm.lean): Q(P x) = R(x) for all x, for some P ∈ GL_n(K).
* `RatPlace.Everywhere`, `RatPlace.atPlace` (Defs/Rational.lean): the property holds over ℝ and every ℚ_p.
* `NFPlace`, `NFPlace.atPlace`, `NFPlace.Everywhere` (Defs/NumberField.lean): places of F (infinite places,
  nonzero primes of 𝓞 F); the property holds over every completion (`w.Completion`, `v.adicCompletion F`).
* `NFPlace.hilbert` (Defs/NumberField.lean): (a, b)_v, the Hilbert symbol over the completion F_v.

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).

New in 0.5.1
* `RatFuncQR.legendreSym P a` (FunctionField/RatFuncQR.lean): the Legendre symbol (a/P) in k[t].
* `RatFuncPlace k`, `RatFuncPlace.hilbert` (FunctionField/RatFuncPlace.lean): the places of k(t) (a finite place
  for each height-one prime of k[t], and the place at infinity with completion k((1/t))) and the Hilbert symbol
  over the completion; `hilbertSymbol` as above.
-/

end QuadFormsKB.Headlines
