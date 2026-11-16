/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.FunctionField.RatFuncReciprocity
import QuadFormsKB.Literature.LocalGlobal.IsometricBaseChange

/-!
# Headline statements, proved: Local–global principles and reciprocity

The declarations of `Challenge_LocalGlobal.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/LocalGlobal.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_LocalGlobal.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
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
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard :=
  hilbert_reciprocity_nf a b ha hb

/-- **Hasse–Minkowski (isotropy).** A nondegenerate quadratic form Q over F is isotropic over F if and only if it is
isotropic over every completion F_v. -/
theorem hasseMinkowski_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_nf Q hQ

/-- **Representation is local–global.** A nondegenerate quadratic form Q over F represents c ∈ F^× over F if and only
if it represents c over every completion F_v. -/
theorem represents_iff_everywhere_numberField (Q : QuadForm F n) (hQ : Q.Nondegenerate) (c : F) (hc : c ≠ 0) :
    Q.RepresentsIn F c ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.RepresentsIn K c :=
  represents_iff_everywhere_nf Q hQ c hc

/-- **Isometry is local–global.** Two nondegenerate quadratic forms Q, R over F in the same number of variables are
isometric over F if and only if they are isometric over every completion F_v. -/
theorem isometric_iff_everywhere_numberField (Q R : QuadForm F n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn F R ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsometricIn K R :=
  isometricIn_iff_everywhere_nf Q R hQ hR

/-- **Hasse–Minkowski over ℚ.** A nondegenerate quadratic form Q over ℚ, in any number of variables, is isotropic over
ℚ if and only if it is isotropic over ℝ and over ℚ_p for every prime p. -/
theorem hasseMinkowski_rat (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ RatPlace.Everywhere fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski Q hQ

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
      (-1) ^ ((Fintype.card k - 1) / 2 * P.natDegree * P'.natDegree) :=
  QuadFormsKB.RatFuncQR.legendreSym_mul_legendreSym' hk P P' hP hPm hP' hP'm hne

/-- **Hilbert reciprocity over 𝔽_q(t)**, q odd (the function field case of O. T. O'Meara, *Introduction to Quadratic Forms*, Springer, 1963,
71:18, p. 199). Let k be a finite field of odd characteristic. The places of k(t) (`RatFuncPlace k`) are the
finite places, one for each nonzero prime ideal of k[t], and the place at infinity; `v.hilbert a b` is the
Hilbert symbol (a, b)_v over the completion k(t)_v (`hilbertSymbol`: 1 if z² = a x² + b y² has a nonzero
solution, −1 otherwise). For a, b ∈ k(t)^×, (a, b)_v = −1 at only finitely many places v, and at an even
number of them: ∏_v (a, b)_v = 1. -/
theorem hilbertReciprocity_ratFunc {k : Type} [Field k] [Fintype k] (hk : ringChar k ≠ 2) (a b : RatFunc k)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : RatFuncPlace k | v.hilbert a b = -1}.Finite ∧ Even {v : RatFuncPlace k | v.hilbert a b = -1}.ncard :=
  (QuadFormsKB.RatFuncPlace.hilbertReciprocity hk).reciprocity a b ha hb

end RationalFunctionField

end QuadFormsKB.Headlines
