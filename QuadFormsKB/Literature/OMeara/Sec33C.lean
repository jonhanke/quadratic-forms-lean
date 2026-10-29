/-
# O'Meara 33:2: the index of fractional ideals and the norm

**Setting.** $F$ a number field; $\mathcal O_F$-modules $\mathfrak b/\mathfrak a$ for fractional ideals
$\mathfrak a \subseteq \mathfrak b$ (the quotient of $\mathfrak b$ by $\mathfrak a$, written as in Mathlib's
`FractionalIdeal.quotientEquiv`).

**Proves** 33:2 `card_quotient_eq_absNorm_div`: $(\mathfrak b : \mathfrak a) = N\mathfrak a/N\mathfrak b$.

*Proof.* Mathlib's `quotientEquiv` (O'Meara's 22D, isomorphism 2) gives $\mathfrak b/\mathfrak a \cong 1/\mathfrak b^{-1}\mathfrak a$;
$\mathfrak b^{-1}\mathfrak a = I_0$ is integral and $1/I_0 \cong \mathcal O_F/I_0$ (`quotientOneEquiv`), of order $N I_0$.
-/
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.DedekindDomain.Factorization
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.OMeara

section Index

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- `R ⧸ I₀` is `R`-linearly equivalent to `1 ⧸ I₀` (the quotient of the fractional ideal `1` by the integral
ideal `I₀`). -/
def quotientOneEquiv (I₀ : Ideal R) :
    (R ⧸ I₀) ≃ₗ[R] ((1 : FractionalIdeal R⁰ K) ⧸
      (I₀ : FractionalIdeal R⁰ K).coeToSubmodule.comap (1 : FractionalIdeal R⁰ K).coeToSubmodule.subtype) := by
  let φ : R →ₗ[R] (1 : FractionalIdeal R⁰ K) :=
    LinearMap.codRestrict (1 : FractionalIdeal R⁰ K).coeToSubmodule (Algebra.linearMap R K)
      (fun r => (FractionalIdeal.mem_one_iff R⁰).2 ⟨r, rfl⟩)
  let Q := (1 : FractionalIdeal R⁰ K) ⧸
      (I₀ : FractionalIdeal R⁰ K).coeToSubmodule.comap (1 : FractionalIdeal R⁰ K).coeToSubmodule.subtype
  let ψ : R →ₗ[R] Q := (Submodule.mkQ _).comp φ
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff R⁰).1 hx
    exact ⟨r, rfl⟩
  have hker : LinearMap.ker ψ = I₀ := by
    ext r
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (p := (I₀ : FractionalIdeal R⁰ K).coeToSubmodule.comap
      (1 : FractionalIdeal R⁰ K).coeToSubmodule.subtype) (φ r) = 0 ↔ r ∈ I₀
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show algebraMap R K r ∈ (I₀ : FractionalIdeal R⁰ K) ↔ r ∈ I₀
    rw [FractionalIdeal.mem_coeIdeal R⁰]
    constructor
    · rintro ⟨x', hx', hx⟩
      rwa [← IsFractionRing.injective R K hx]
    · exact fun h => ⟨r, h, rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hψ)

end Index

variable (F : Type*) [Field F] [NumberField F]

/-- **O'Meara 33:2.** For nonzero fractional ideals $\mathfrak a \subseteq \mathfrak b$ of a number field, the
additive group index is $(\mathfrak b : \mathfrak a) = N\mathfrak a / N\mathfrak b$, where $N$ is the ideal norm
(Mathlib's `FractionalIdeal.absNorm`, equal to O'Meara's $N$ by 33:3). -/
@[kb "omeara1963" "§33C, 33:2, p. 67"]
theorem card_quotient_eq_absNorm_div {a b : FractionalIdeal (𝓞 F)⁰ F} (ha : a ≠ 0) (hab : a ≤ b) :
    (Nat.card (b ⧸ a.coeToSubmodule.comap b.coeToSubmodule.subtype) : ℚ) =
      FractionalIdeal.absNorm a / FractionalIdeal.absNorm b := by
  have hb : b ≠ 0 := fun h => ha (FractionalIdeal.le_zero_iff.mp (h ▸ hab))
  have hle : b⁻¹ * a ≤ 1 := by
    calc b⁻¹ * a ≤ b⁻¹ * b := mul_le_mul_right hab _
      _ = 1 := inv_mul_cancel₀ hb
  have hne : b⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero hb) ha
  obtain ⟨I₀, hI₀⟩ := (FractionalIdeal.le_one_iff_exists_coeIdeal).1 hle
  have H : b * (b⁻¹ * a) = 1 * a := by rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  have e := FractionalIdeal.quotientEquiv b a 1 (b⁻¹ * a) H hab hle hne hb
  have h1 : Nat.card (b ⧸ a.coeToSubmodule.comap b.coeToSubmodule.subtype) =
      Ideal.absNorm I₀ := by
    rw [Nat.card_congr e.toEquiv, ← hI₀, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (quotientOneEquiv F I₀).toEquiv).symm
  rw [h1]
  have h2 : FractionalIdeal.absNorm (b⁻¹ * a) = Ideal.absNorm I₀ := by
    rw [← hI₀, FractionalIdeal.coeIdeal_absNorm]
  rw [map_mul, map_inv₀] at h2
  have : FractionalIdeal.absNorm b ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact hb
  field_simp at h2 ⊢
  linarith
end QuadFormsKB.OMeara
