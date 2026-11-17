/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.HeadlineFactsWeil
import QuadFormsKB.Tamagawa.Measure.Weil.SpaceBinary

/-!
# Headline statements, proved: The Tamagawa number of SO(V) over every number field

The declarations of `Challenge_TamagawaSO.lean`, with the same names and statements, each proved by citing
library theorems. `lake comparator` (configured by `comparator/TamagawaSO.json`) checks that every theorem here has
exactly the statement of its counterpart in `Challenge_TamagawaSO.lean` and depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open NumberField IsDedekindDomain Module

noncomputable section

namespace QuadFormsKB.Headlines

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.SiegelSpace QuadFormsKB.HilbertModular
  QuadFormsKB.RegProd

/-! ## The Tamagawa number of SO(V) over every number field

Setting: F any number field (real and complex places allowed). For a nondegenerate quadratic form Q₀ in n variables
with coefficients in 𝓞 F, `SOAdele Q₀` is SO(V)(𝔸) = G_∞ × SO(V)(𝔸_f) (V = F^n with Q₀), `GammaSOAdele Q₀` is SO(V)(F)
embedded diagonally, and `muTam Q₀ hQ λ` is Weil's Tamagawa measure with convergence factors λ_v:
|d_F|^{-n(n-1)/4} · 2^{n(n-1)r₂/2} · μ_∞ × μ_f, where μ_∞ is the product of the gauge-form (Leray) measures at the
archimedean places, r₂ the number of complex places, and μ_f the Haar measure on SO(V)(𝔸_f) giving the stabilizer
SO(L̂) of L = 𝓞_F^n the mass ∏'_v μ_v(SO(L_v)), μ_v = `muLocSO v Q₀ λ_v` (so μ_v(SO(L_v)) = α_v(L, L)/λ_v, Siegel's
local density divided by λ_v). `covolume Γ G μ` is Mathlib's: the μ-measure of a fundamental domain of Γ in G, and 0 if
there is none; so a nonzero value also says that a fundamental domain exists.

**No hidden default values.** μ_f is defined through the real product ∏'_v μ_v(SO(L_v)) (a `tprod`, which is 1 when the
product does not converge), and some measures carry the factor L_F(1, χ)^{-1} (`LOne`, a limit): each statement
below also states that this product converges unconditionally and, where it occurs, that L_F(1, χ) exists and is
positive. -/

section TamagawaNumberField

set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

open MeasureTheory QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

/-- **τ(SO(V)) = 2 over every number field** (Weil). For every nondegenerate quadratic form Q₀ in n ≥ 3 variables
with coefficients in 𝓞 F (any signature at the real places, isotropic or not, F with complex places allowed), the
covolume of SO(V)(F) in SO(V)(𝔸) for Weil's Tamagawa measure with convergence factors λ_v = 1 is 2.
Moreover the product ∏'_v μ_v(SO(L_v)) in the measure converges unconditionally. -/
theorem tamagawa_two_numberField (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 ∧
      Multipliable fun v => (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨tauTwoAll_release_uncond n hn Q₀ hQ, multipliable_muLocSO_one Q₀ hQ (by omega) (by omega)⟩

/-- **τ(SO(V)) = 2 for quadratic spaces over every number field** (Weil). Let V be a vector space over F of
dimension n ≥ 3 and Q a nondegenerate quadratic form on V (Mathlib's `QuadraticForm F V`, nondegenerate polar form).
Then (V, Q) has an integral model (`IntegralModel Q`: a basis b of V, a nonzero d ∈ 𝓞 F and a form Q₀ over 𝓞 F with
Q₀ = d · Q in the coordinates of b), and for every integral model the form Q₀ is nondegenerate, the covolume of SO(V)(F)
in SO(V)(𝔸) for Weil's Tamagawa measure of Q₀ (λ_v = 1) is 2, and the product ∏'_v μ_v(SO(L_v)) converges
unconditionally. -/
theorem tamagawa_two_space {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : 3 ≤ finrank F V) (Q : QuadraticForm F V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : M.form.Nondegenerate,
      covolume (GammaSOAdele M.form) (SOAdele M.form) (muTam M.form hM fun _ => 1) = 2 ∧
      Multipliable fun v => (muLocSO v M.form 1 (soStabSO v M.form : Set (SOv v M.form))).toReal :=
  ⟨(tauTwo_space_uncond hV Q hQ).1, fun M =>
    let ⟨hM, h⟩ := (tauTwo_space_uncond hV Q hQ).2 M
    ⟨hM, h, multipliable_muLocSO_one M.form hM (by omega) (by omega)⟩⟩

/-- **τ(SO_1) = 1.** For every nondegenerate form Q₀ = ⟨c⟩ in one variable over 𝓞 F, the covolume of
SO(V)(F) in SO(V)(𝔸) for Weil's Tamagawa measure (λ_v = 1) is 1 (both groups are trivial; the value is the product
formula for 2c). Moreover the product ∏'_v μ_v(SO(L_v)) converges unconditionally. -/
theorem tamagawa_one_rankOne (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 1 ∧
      Multipliable fun v => (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨covolume_muTam_rankOne Q₀ hQ, multipliable_muLocSO_one Q₀ hQ one_ne_zero (by norm_num)⟩

/-- **τ(SO(V)) = 2 for anisotropic binary forms over every number field** (Weil; Ono's τ(R¹_{E/F} 𝔾_m) = 2).
Let Q₀ be a nondegenerate binary form over 𝓞 F that is anisotropic over F (any signature, complex places allowed),
and E a discriminant field of Q₀ (`IsDiscField Q₀ E`: [E : F] = 2 and E contains a square root of -det H, H the
Hessian of Q₀; such an E exists, `exists_isDiscField_of_anisotropicF`). For Weil's Tamagawa measure with the
convergence factors λ_v = L_v(1, χ_E)^{-1} = 1 - χ_E(v)/Nv and the global factor L_F(1, χ_E)^{-1} (`muTamBin`), the
covolume of SO(V)(F) in SO(V)(𝔸) is 2. Moreover L_F(1, χ_E) = lim_{s→1⁺} L_F(s, χ_E) exists and is positive, and the
product ∏'_v λ_v^{-1} μ_v(SO(L_v)) converges unconditionally (its factors are 1 for almost all v). -/
theorem tamagawa_two_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTamBin Q₀ hQ E) = 2 ∧
      HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) ∧
      Multipliable fun v => (muLocSO v Q₀ (lamL (chiE F E) v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨tauTwoBinaryAll_uncond F Q₀ hQ hA E hE, (hasLOne_chiE hE.finrank_eq_two).1, (hasLOne_chiE hE.finrank_eq_two).2,
    multipliable_muLocSO_lamL_chiE hQ hE⟩

/-- **τ(SO(V)) = 2 for anisotropic binary quadratic spaces over every number field.** Let V be a vector space
over F of dimension 2 and Q a nondegenerate anisotropic quadratic form on V. Then (V, Q) has an integral model, and
for every integral model the form Q₀ (read in 2 variables, `IntegralModel.form₂`) is nondegenerate and anisotropic
over F, and for every discriminant field E of Q₀ the conclusions of `tamagawa_two_binary` hold: the covolume for
`muTamBin` is 2, L_F(1, χ_E) exists and is positive, and the product of the local masses converges. -/
theorem tamagawa_two_space_binary {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V = 2) (Q : QuadraticForm F V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hA : Q.Anisotropic) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : (M.form₂ hV).Nondegenerate,
      AnisotropicF (M.form₂ hV) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E], IsDiscField (M.form₂ hV) E →
        covolume (GammaSOAdele (M.form₂ hV)) (SOAdele (M.form₂ hV)) (muTamBin (M.form₂ hV) hM E) = 2 ∧
        HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) ∧
        Multipliable fun v => (muLocSO v (M.form₂ hV) (lamL (chiE F E) v)
          (soStabSO v (M.form₂ hV) : Set (SOv v (M.form₂ hV)))).toReal :=
  ⟨(tauTwo_space_binary hV Q hQ hA).1, fun M =>
    let ⟨hM, hA', h⟩ := (tauTwo_space_binary hV Q hQ hA).2 M
    ⟨hM, hA', fun E _ _ _ hE => ⟨h E hE, (hasLOne_chiE hE.finrank_eq_two).1, (hasLOne_chiE hE.finrank_eq_two).2,
      multipliable_muLocSO_lamL_chiE hM hE⟩⟩⟩

/-- **τ(SO(V)) = 1 for isotropic binary forms over every number field** (Weil; Ono's τ(𝔾_m) = 1). Let Q₀ be a
nondegenerate binary form over 𝓞 F with an isotropic vector e ∈ F² (`IsIsoVec Q₀ e`: e ≠ 0, Q₀(e) = 0). Then
SO(V) ≅ 𝔾_m, and τ = vol(SO(V)(F)\SO(V)(𝔸)¹) = 1 for Weil's measure with the convergence factors
λ_v = 1 - N(v)^{-1} and the global factor ρ_F^{-1}, ρ_F the residue of ζ_F at 1 (`tauIso`: the covolume of SO(V)(F)
for this measure restricted to the shell 0 ≤ log |χ_e| < 1, which is the norm-one quotient measure; `muTamIso`).
Moreover the product ∏'_v λ_v^{-1} μ_v(SO(L_v)) in the measure converges unconditionally. -/
theorem tamagawa_one_binary_isotropic (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (e : Fin 2 → F)
    (he : IsIsoVec Q₀ e) :
    tauIso Q₀ hQ he = 1 ∧
      Multipliable fun v => (muLocSO v Q₀ (lamV v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal :=
  ⟨tauOne_binary_isotropic_uncond F Q₀ hQ ⟨e, he⟩ e he, multipliable_muLocSO_lamV_of_isotropicF hQ ⟨e, he⟩⟩

/-- **τ(SO(V)) = 1 for isotropic binary quadratic spaces over every number field.** Let V be a vector space
over F of dimension 2 and Q a nondegenerate quadratic form on V that is isotropic (not `QuadraticMap.Anisotropic`).
Then (V, Q) has an integral model, and for every integral model the form Q₀ (in 2 variables, `IntegralModel.form₂`)
is nondegenerate and isotropic over F, `tauIso` = 1 for every isotropic vector of Q₀, and the product of the local
masses converges unconditionally. -/
theorem tamagawa_one_space_binary_isotropic {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V = 2) (Q : QuadraticForm F V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hI : ¬ Q.Anisotropic) :
    Nonempty (IntegralModel Q) ∧ ∀ M : IntegralModel Q, ∃ hM : (M.form₂ hV).Nondegenerate,
      IsotropicF (M.form₂ hV) ∧
      (∀ (e : Fin 2 → F) (he : IsIsoVec (M.form₂ hV) e), tauIso (M.form₂ hV) hM he = 1) ∧
      Multipliable fun v => (muLocSO v (M.form₂ hV) (lamV v) (soStabSO v (M.form₂ hV) : Set (SOv v (M.form₂ hV)))).toReal :=
  ⟨(tauOne_space_binary_isotropic hV Q hQ hI).1, fun M =>
    let ⟨hM, hI', h⟩ := (tauOne_space_binary_isotropic hV Q hQ hI).2 M
    ⟨hM, hI', h, multipliable_muLocSO_lamV_of_isotropicF hM hI'⟩⟩

end TamagawaNumberField

end QuadFormsKB.Headlines
