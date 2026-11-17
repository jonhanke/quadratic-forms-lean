/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.HeadlineFacts
import QuadFormsKB.Tamagawa.InputsFollowup

/-!
# Headline statements: The Tamagawa number and the mass formula over totally real number fields

τ(SO(Q)) = 2 and the Smith–Minkowski–Siegel mass formula over totally real number fields.

Every proof here is a deliberate `sorry`. `Solution_TamagawaTotallyReal.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/TamagawaTotallyReal.json`) checks that each theorem of
`Solution_TamagawaTotallyReal.lean` has exactly the statement given here and depends only on the axioms `propext`,
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

/-! ## The Tamagawa number and the mass formula over totally real number fields

Setting: F a totally real number field, Q₀ a quadratic form in n ≥ 4 variables with coefficients in 𝓞 F that is
totally positive definite over F; the last two statements are the case n = 3. (Ranks 1 and 2 are also
proved in the library; see `docs/results/`.) -/

section Tamagawa

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **τ(SO(Q)) = 2.** For Q₀ as above, the Tamagawa number of SO(Q₀) is 2. Here `tauSO Q₀` is
μ_Tam(K) · ∑_α 1/|Γ_α| (a Tamagawa volume times a double-coset mass); the library proves it equals the covolume of
SO(Q₀)(F) in SO(Q₀)(𝔸) for a Haar measure normalized as Weil's Tamagawa measure (`Measure.tauSO_eq_covolume`).
Moreover the product ∏_𝔭 α_𝔭(Q₀, Q₀) in μ_Tam(K) converges unconditionally, and the double-coset space
SO(Q₀)(F)\SO(Q₀)(𝔸_f)/SO(𝓞̂_F^n) in the mass is finite, with finite stabilizers Γ_α. -/
theorem tamagawa_two_totallyReal (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef (formF Q₀)) :
    tauSO Q₀ = 2 ∧
      (Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀) ∧
      Finite (MulAction.orbitRel.Quotient ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀)))
        (soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F n)).subgroupOf (soAf (formF Q₀)))) ∧
      ∀ x : soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F n)).subgroupOf (soAf (formF Q₀)),
        Finite (MulAction.stabilizer ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀))) x) := by
  sorry

/-- **The Smith–Minkowski–Siegel mass formula.** For Q₀ as above and L = 𝓞_F^n,
∑_{L' ∈ Gen(L)} 1/|O(L')| = ( |d_F|^{-n(n-1)/4} · ∏_σ vol(SO(Q₀^σ)) · ∏_𝔭 α_𝔭(Q₀, Q₀) )^{-1},
with σ running over the embeddings F → ℂ (all real), vol(SO(Q₀^σ)) the closed-form archimedean volume
(`archVolSO` at the Gram determinant `detGram Q₀ σ`), and α_𝔭(Q₀, Q₀) = (1/2) β_𝔭(Q₀, Q₀) Siegel's local density.
Moreover the genus of L has finitely many classes, every lattice in the genus has a finite automorphism group,
and the product ∏_𝔭 α_𝔭(Q₀, Q₀) converges unconditionally. -/
theorem massFormula_totallyReal (hn : 4 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : IsTotallyPosDef (formF Q₀)) :
    (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F n), ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) =
      (|(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) *
        ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹ ∧
      (genusClasses (formF Q₀) (stdLat F n)).Finite ∧
      (∀ M : Lat F n, SameGenus (formF Q₀) (stdLat F n).1 M.1 → Finite (autLat (formF Q₀) M.1)) ∧
      Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
  sorry

/-- **τ(SO(Q)) = 2, ternary forms.** As `tamagawa_two_totallyReal`, for a form Q₀ in 3 variables with coefficients
in 𝓞 F that is totally positive definite over F: the Tamagawa number `tauSO Q₀` of SO(Q₀) is 2. Moreover the
product ∏_𝔭 α_𝔭(Q₀, Q₀) in μ_Tam(K) converges unconditionally, and the double-coset space
SO(Q₀)(F)\SO(Q₀)(𝔸_f)/SO(𝓞̂_F^3) in the mass is finite, with finite stabilizers Γ_α. -/
theorem tamagawa_two_totallyReal_ternary (Q₀ : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef (formF Q₀)) :
    tauSO Q₀ = 2 ∧
      (Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀) ∧
      Finite (MulAction.orbitRel.Quotient ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀)))
        (soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F 3)).subgroupOf (soAf (formF Q₀)))) ∧
      ∀ x : soAf (formF Q₀) ⧸ (locStab (formF Q₀) (stdLat F 3)).subgroupOf (soAf (formF Q₀)),
        Finite (MulAction.stabilizer ((ratPoints (formF Q₀)).subgroupOf (soAf (formF Q₀))) x) := by
  sorry

/-- **The Smith–Minkowski–Siegel mass formula, ternary forms.** As `massFormula_totallyReal`, for a form Q₀ in
3 variables with coefficients in 𝓞 F that is totally positive definite over F, and L = 𝓞_F^3:
∑_{L' ∈ Gen(L)} 1/|O(L')| = ( |d_F|^{-3/2} · ∏_σ vol(SO(Q₀^σ)) · ∏_𝔭 α_𝔭(Q₀, Q₀) )^{-1}
(the exponent is -n(n-1)/4 at n = 3). Moreover the genus of L has finitely many classes, every lattice in the genus
has a finite automorphism group, and the product ∏_𝔭 α_𝔭(Q₀, Q₀) converges unconditionally. -/
theorem massFormula_totallyReal_ternary (Q₀ : QuadForm (𝓞 F) 3) (hQ : IsTotallyPosDef (formF Q₀)) :
    (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F 3), ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) =
      (|(discr F : ℝ)| ^ (-((3 : ℝ) * (3 - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 3 (detGram Q₀ σ)) *
        ∏' v : HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹ ∧
      (genusClasses (formF Q₀) (stdLat F 3)).Finite ∧
      (∀ M : Lat F 3, SameGenus (formF Q₀) (stdLat F 3).1 M.1 → Finite (autLat (formF Q₀) M.1)) ∧
      Multipliable fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
  sorry

end Tamagawa

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.

Siegel's theorem
* `SiegelSpace.LatClassV.autCard Q c` (Tamagawa/SiegelGenusV.lean): |O(M)| = `Nat.card (autLatV Q M)` for any
  lattice M in the class c, improper isometries included (independent of the representative).

Tamagawa number and mass formula
* `HilbertModular.formF Q₀` (HilbertModular/GenusTheta.lean): Q₀ with coefficients mapped into F.
* `Lattices.IsTotallyPosDef`, `Lattices.IsTotallyPos` (Lattices/Finite.lean): Q(x) totally positive for x ≠ 0.
* `Tamagawa.tauSO` (Tamagawa/MassFormula.lean): `tamagawaK Q₀ · dcMass (…)`; equal to the Tamagawa covolume by
  `Tamagawa.Measure.tauSO_eq_covolume` (Tamagawa/Measure/AdelicSO.lean).
* `Tamagawa.tamagawaK`, `Tamagawa.archVolSO`, `Tamagawa.detGram` (Tamagawa/MassFormula.lean): the Tamagawa volume of
  the stabilizer, the archimedean volume of SO(Q₀^σ), and |σ(det(H/2))|.
* `Lattices.genusClasses Q L` (Lattices/Finite.lean): the classes L' in the genus of L (lattices in F^n up to isometry
  by the full O(Q), improper isometries included); `Lattices.LatClass.autCard Q c` (same file): |O(M)| =
  `Nat.card (autLat Q M)` for any lattice M in the class c. The mass ∑ 1/|O(L')| is written out in the statement
  (it is `Lattices.mass Q L`, same file).
* `Lattices.SameGenus Q L M`, `Lattices.autLat Q M` (Lattices/Genus.lean): M is in the genus of L; O(M).
* `Lattices.OAf`, `Lattices.ratPoints`, `Lattices.locStab` (Lattices/ClassSet.lean): O(V)(𝔸_f), the diagonal
  O(V)(F) inside it, and the stabilizer O(L̂) of L; `Tamagawa.soAf` (Tamagawa/MassFormula.lean): SO(V)(𝔸_f).
* `Tamagawa.stdLat F n` (Tamagawa/MassFormula.lean): the lattice 𝓞_F^n in F^n.
* `LocalDensity.NF.siegelDensity v Q T` (LocalDensity/NFFormDensity.lean): α_𝔭(Q, T) = ε β_𝔭(Q, T), ε = 1/2 if
  T has the same rank as Q, with β_𝔭 = `localDensityForm` (same file).

Classical cases over ℚ
* `Siegel.genusClasses Q`, `Siegel.QClass.repNum`, `Siegel.QClass.autCard` (Siegel/Genus.lean): the
  GL_n(ℤ)-classes of forms in the genus of Q; r_{Q'}(m) and |Aut(Q')| for a form Q' in the class.

Exact mass formulas (paths in `Literature/`)
* `Lattices.IsTotallyPosDef` as in the Tamagawa section.

Class numbers
* `QuadForm ℤ n`, `IntQF.PosDef Q` and `Siegel.genusClasses Q` as in the classical cases over ℚ; `Set.encard`
  (Mathlib): the cardinality of a set in ℕ∞ (⊤ for an infinite set).
-/

end QuadFormsKB.Headlines
