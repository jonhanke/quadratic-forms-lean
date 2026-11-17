/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Voight.Wave11.MassSuperorder
import QuadFormsKB.Literature.Voight.Wave2.MainTheorem
import QuadFormsKB.Literature.Voight.Wave3.MaximalIff

/-!
# Headline statements, proved: J. Voight, Quaternion Algebras

The declarations of `Challenge_Voight.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/Voight.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_Voight.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## Quaternion orders

Theorems of J. Voight, *Quaternion Algebras* (2021): maximal orders and their discriminant, the correspondence between
ternary quadratic forms and quaternion orders, and the Eichler mass formula for maximal orders. -/

section QuaternionOrders

/-- **Maximal orders are the orders of discriminant equal to the discriminant of the algebra** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
Theorem 15.5.5, p. 249), over every number field F. Let a, b be nonzero elements of the ring of integers 𝓞_F,
B = (a, b)_F the quaternion algebra with i² = a, j² = b, ij = −ji (`QuatOrder.QuatF F a b`), and O an 𝓞_F-order
of B (`QuatOrder.IsOrder`: a finitely generated 𝓞_F-submodule and subring spanning B over F) that is free of
rank 4 as an 𝓞_F-module (automatic when 𝓞_F is a principal ideal domain). Then O is a maximal order
(`QuatOrder.IsMaximalOrder`: not properly contained in another order) if and only if its reduced discriminant
is the product of the finite primes at which B ramifies (`QuatOrder.ramFin`): `Voight.HasDiscrd O 𝔇` says that
for every 𝓞_F-basis e₀, …, e₃ of O the determinant det(trd(e_i e_j)) of the reduced trace form generates the
ideal 𝔇². -/
theorem voight_maximal_iff_discriminant {F : Type} [Field F] [NumberField F] (a b : 𝓞 F) (ha : a ≠ 0)
    (hb : b ≠ 0) (O : Subalgebra (𝓞 F) (QuatOrder.QuatF F a b)) (hO : QuatOrder.IsOrder (𝓞 F) F O)
    (hfree : Nonempty (Module.Basis (Fin 4) (𝓞 F) (Subalgebra.toSubmodule O))) :
    QuatOrder.IsMaximalOrder (𝓞 F) F O ↔
      Voight.HasDiscrd O (∏ v ∈ QuatOrder.ramFin ha hb, v.asIdeal) :=
  QuadFormsKB.Voight.Disc.maximalIffDiscriminant F a b ha hb O hO hfree

/-- **Ternary quadratic forms and quaternion orders** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021, Main Theorem 22.4.1, p. 364, due to
Gross and Lucianovic), for a principal ideal domain R whose fraction field F has 2 ≠ 0. For a ternary form
Q = ∑_{i ≤ j} c_ij x_i x_j over R (`QuadForm R 3`), `Voight.Clf0 Q` is its even Clifford algebra and
`Voight.ternaryDisc Q` its half-discriminant 4c₀₀c₁₁c₂₂ + c₁₂c₀₂c₀₁ − c₀₀c₁₂² − c₁₁c₀₂² − c₂₂c₀₁²; Q is
nondegenerate when this is nonzero. A quaternion R-order (`Voight.IsQuaternionOrder R F O`) is an R-algebra that
is finitely generated and torsion-free as an R-module and whose extension F ⊗_R O is a quaternion algebra over F.
Forms Q, Q' are similar (`Voight.Similar`) if Q' is isometric over R to u·Q for a unit u of R. The three
conjuncts: the even Clifford algebra of a nondegenerate form is a quaternion order; every quaternion order is
isomorphic to one of them; and two of them are isomorphic exactly when the forms are similar. Together:
Q ↦ Clf⁰(Q) is a bijection from similarity classes of nondegenerate ternary forms onto isomorphism classes of
quaternion R-orders. -/
theorem voight_evenClifford_correspondence (R F : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] (h2 : (2 : F) ≠ 0) :
    (∀ Q : QuadForm R 3, Voight.ternaryDisc Q ≠ 0 → Voight.IsQuaternionOrder R F (Voight.Clf0 Q)) ∧
    (∀ (O : Type) [Ring O] [Algebra R O], Voight.IsQuaternionOrder R F O →
      ∃ Q : QuadForm R 3, Voight.ternaryDisc Q ≠ 0 ∧ Nonempty (O ≃ₐ[R] Voight.Clf0 Q)) ∧
    (∀ Q Q' : QuadForm R 3, Voight.ternaryDisc Q ≠ 0 → Voight.ternaryDisc Q' ≠ 0 →
      (Nonempty (Voight.Clf0 Q ≃ₐ[R] Voight.Clf0 Q') ↔ Voight.Similar Q Q')) :=
  have h := QuadFormsKB.Voight.evenCliffordCorrespondence_of_two_ne_zero (R := R) h2
  ⟨h.isQuaternionOrder, fun O _ _ => h.exists_clf0 O, h.nonempty_equiv_iff_similar⟩

/-- **The Eichler mass formula for maximal orders over a totally real number field** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
Main Theorem 26.1.5 and Theorem 26.1.12 for level one, p. 432–433). Let F be a totally real number field of
degree n = [F : ℚ] whose ring of integers 𝓞_F is a principal ideal domain, a, b nonzero in 𝓞_F with
B = (a, b)_F totally definite (`QuatOrder.IsTotDefinite a b`: σ(a) < 0 and σ(b) < 0 for every real embedding σ),
and O a maximal order of B containing 𝓞_F⟨i, j⟩ (`QuatOrder.stdOrder F a b ≤ O`). Then
mass(O) = ∑_{[J]} 1/[O_R(J)^× : 𝓞_F^×] (`Voight.classMass O`: the sum over the classes of nonzero left
ideals J of O under J ~ Jβ, β ∈ B^×, of the inverse index of 𝓞_F^× in the unit group of the right order of J)
equals 2 ζ_F(2) (2π)^{−2n} |d_F|^{3/2} h_F ∏_{𝔭 | 𝔇} (N𝔭 − 1), with ζ_F the Dedekind zeta function
(`NFEuler.dedekindZetaR`), d_F the discriminant, h_F the class number and 𝔇 the product of the finite ramified
primes of B. Moreover (so that every term is meaningful) there are finitely many classes and every index is
finite. The containment O ⊇ 𝓞_F⟨i, j⟩ and the principal ideal domain hypothesis are restrictions of this
formalization; Voight's theorem holds for every maximal order and every class number. -/
theorem eichlerMass_totallyReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : QuatOrder.IsTotDefinite a b)
    {O : Subalgebra (𝓞 F) (QuatOrder.QuatF F a b)} (hO : QuatOrder.IsMaximalOrder (𝓞 F) F O)
    (hstd : QuatOrder.stdOrder F a b ≤ O) :
    Voight.classMass O = 2 * NFEuler.dedekindZetaR F 2 / (2 * Real.pi) ^ (2 * Module.finrank ℚ F) *
        |(NumberField.discr F : ℝ)| ^ (3 / 2 : ℝ) * (NumberField.classNumber F : ℝ) *
        ∏ v ∈ QuatOrder.ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1) ∧
      Finite (Quotient (QuatOrder.idealSetoid O)) ∧
      ∀ J : Ideal O, J ≠ ⊥ → (QuatOrder.centralUnitsIn (R := 𝓞 F) J).FiniteIndex :=
  ⟨QuadFormsKB.Voight.Wave3.classMass_eq_maximal ha hb hdef hO hstd,
    QuadFormsKB.QuatOrder.Gen.finite_classes ha hb hO
      (fun _ hx => QuadFormsKB.QuatOrder.eq_zero_of_nrd_eq_zero hdef hx),
    fun _ hJ => QuadFormsKB.QuatOrder.finiteIndex_centralUnitsIn hdef hO.1 hstd hJ⟩

/-- **The Eichler mass formula over ℚ** (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021, Theorem 25.1.1 = Theorem 25.3.15, p. 415 and 422).
Let a, b be nonzero integers (in 𝓞_ℚ) with B = (a, b)_ℚ definite (a < 0 and b < 0) and O a maximal order of B
containing ℤ⟨i, j⟩. Then mass(O) = ∑_{[J]} 1/[O_R(J)^× : {±1}] (`Voight.classMass O`, as in
`eichlerMass_totallyReal`) equals φ(D)/12 = (1/12) ∏_{p | D} (p − 1), the product over the primes at which B
ramifies; there are finitely many classes and every index is finite. The containment O ⊇ ℤ⟨i, j⟩ is a
restriction of this formalization. -/
theorem eichlerMass_rat {a b : 𝓞 ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : QuatOrder.IsTotDefinite a b)
    {O : Subalgebra (𝓞 ℚ) (QuatOrder.QuatF ℚ a b)} (hO : QuatOrder.IsMaximalOrder (𝓞 ℚ) ℚ O)
    (hstd : QuatOrder.stdOrder ℚ a b ≤ O) :
    Voight.classMass O = (∏ v ∈ QuatOrder.ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)) / 12 ∧
      Finite (Quotient (QuatOrder.idealSetoid O)) ∧
      ∀ J : Ideal O, J ≠ ⊥ → (QuatOrder.centralUnitsIn (R := 𝓞 ℚ) J).FiniteIndex :=
  ⟨QuadFormsKB.Voight.Wave3.classMass_eq_rat_maximal ha hb hdef hO hstd,
    QuadFormsKB.QuatOrder.Gen.finite_classes ha hb hO
      (fun _ hx => QuadFormsKB.QuatOrder.eq_zero_of_nrd_eq_zero hdef hx),
    fun _ hJ => QuadFormsKB.QuatOrder.finiteIndex_centralUnitsIn hdef hO.1 hstd hJ⟩

end QuaternionOrders

/-! ## Eichler's mass formula for Eichler orders over ℚ (new in 0.6.0)

J. Voight, *Quaternion Algebras* (2021), Theorem 25.3.18. Voight's Proposition 26.6.4, the step from a maximal order
to an Eichler order of every level, is proved in the library. -/

section EichlerOrders

theorem eichlerMass_eichlerOrders_rat : Voight.EichlerMassFormulaEichlerOrdersRat :=
  QuadFormsKB.Voight.Wave11.eichlerMassFormulaEichlerOrdersRat

end EichlerOrders

end QuadFormsKB.Headlines
