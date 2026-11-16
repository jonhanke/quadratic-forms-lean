/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.FrameSiegelAll
import QuadFormsKB.Tamagawa.HeadlineFacts
import QuadFormsKB.Tamagawa.HeadlineFactsWeil

/-!
# Headline statements: Siegel's theorem over totally real number fields

Siegel's formula for totally positive definite lattices over totally real number fields, for numbers and for forms represented by forms.

Every proof here is a deliberate `sorry`. `Solution_SiegelTotallyReal.lean` declares the same theorems and proves each
by citing library theorems; `lake comparator` (configured by `comparator/SiegelTotallyReal.json`) checks that each theorem of
`Solution_SiegelTotallyReal.lean` has exactly the statement given here and depends only on the axioms `propext`,
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

/-! ## Siegel's theorem over totally real number fields

Setting: F a totally real number field, (V, Q) a totally positive definite quadratic space over F of dimension n,
L an 𝓞 F-lattice in V (of any Steinitz class, so not necessarily free) on which Q is integral, and m ∈ 𝓞 F totally
positive. In the statements, n is local notation for `finrank F V`. In each formula the left side is

  ∑ over classes L' in Gen(L) of r_{L'}(m)/|O(L')|

(in Lean: `∑ᶠ c ∈ genusClassesV Q L` of `LatClassV.repCount Q c m / LatClassV.autCard Q c`), and the right side
starts with the mass ∑ over classes L' in Gen(L) of 1/|O(L')| (the `∑ᶠ` of `(LatClassV.autCard Q c)⁻¹`). On the right,
d_F is the discriminant of F, N𝔡(L) the norm of the discriminant ideal of L, β_σ(m) = π^{n/2}/Γ(n/2) · σ(m)^{(n-2)/2}
the real density at the embedding σ, and β_𝔭(L, m) the classical local density of L at the prime 𝔭 (all named in
"Definitions used"). -/

section Siegel

-- `IsScalarTower (𝓞 F) F V` says the two scalar actions on V agree: (a • c) • v = a • (c • v) for a ∈ 𝓞 F, c ∈ F.
-- So the 𝓞 F-module structure (needed for lattices L ⊆ V) is the restriction of the F-vector-space structure.
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {V : Type*} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
  {L : Submodule (𝓞 F) V} [L.IsLattice F]

-- In this section `n` is notation for the dimension `finrank F V` of V over F (pure syntax: it unfolds to
-- `finrank F V` when the statement is elaborated). Its scope ends with the section, so the later `{n : ℕ}` variables
-- are unaffected.
set_option hygiene false in
local notation "n" => finrank F V

/-- **Siegel's theorem, rank n ≥ 4.** With the setting above,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-(n-1)/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · ∏_𝔭 β_𝔭(L, m).
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
and the product ∏_𝔭 β_𝔭(L, m) converges unconditionally. -/
theorem siegel_totallyReal (hn : 4 ≤ n) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((n : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity n ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        ∏' v, intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      Multipliable fun v => intrinsicBetaV v Q L m := by
  sorry

/-- **Siegel's theorem, rank 3** (Euler product regularized by L(1, χ_m)). With the setting above and n = 3,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1} · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)
  · L_F(1, χ_m) · ∏_𝔭 β_𝔭(L, m) (1 - χ_m(𝔭)/N𝔭),
where χ_m is the quadratic character of F(√(-2m·det H))/F, H the Hessian of Q in a basis of V (this version
uses the basis `finBasisOfFinrankEq`; see the next theorem for a basis-free character).
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
the limit L_F(1, χ_m) = lim_{s→1⁺} L_F(s, χ_m) exists and is positive, and the corrected product
∏_𝔭 β_𝔭(L, m) (1 - χ_m(𝔭)/N𝔭) converges unconditionally. -/
theorem siegel_totallyReal_rank3 (h : n = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m) 1 fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m)
        (LOne (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m)) ∧
      0 < LOne (spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m) ∧
      Multipliable fun v => intrinsicBetaV v Q L m *
        (1 - spaceChar3 (coordForm Q (finBasisOfFinrankEq F V h)) m v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 3, basis-free character.** As `siegel_totallyReal_rank3`, with χ_m the character of
F(√(-2m·disc Q))/F defined without choosing a basis, and the same extra conjuncts. -/
theorem siegel_totallyReal_rank3' (h : n = 3) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3V Q m) 1 fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar3V Q m) (LOne (spaceChar3V Q m)) ∧ 0 < LOne (spaceChar3V Q m) ∧
      Multipliable fun v => intrinsicBetaV v Q L m * (1 - spaceChar3V Q m v / (NFEuler.normP v : ℝ)) ^ (1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 2** (factor 1/2; Euler product regularized by L(1, χ_Q)^{-1}). With the setting above
and n = 2,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (1/2) · (∑_{L' ∈ Gen(L)} 1/|O(L')|) · |d_F|^{-1/2} · N𝔡(L)^{-1/2}
  · ∏_σ β_σ(m) · L_F(1, χ_Q)^{-1} · ∏_𝔭 β_𝔭(L, m) (1 - χ_Q(𝔭)/N𝔭)^{-1},
where χ_Q is the quadratic character of F(√(-det H))/F, H the Hessian of Q in the basis `finBasisOfFinrankEq`.
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
the limit L_F(1, χ_Q) = lim_{s→1⁺} L_F(s, χ_Q) exists and is positive, and the corrected product
∏_𝔭 β_𝔭(L, m) (1 - χ_Q(𝔭)/N𝔭)^{-1} converges unconditionally. -/
theorem siegel_totallyReal_rank2 (h : n = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (1 / 2 : ℝ) * (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h))) (-1) fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h)))
        (LOne (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h)))) ∧
      0 < LOne (spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h))) ∧
      Multipliable fun v => intrinsicBetaV v Q L m *
        (1 - spaceChar2 (coordForm Q (finBasisOfFinrankEq F V h)) v / (NFEuler.normP v : ℝ)) ^ (-1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 2, basis-free character.** As `siegel_totallyReal_rank2`, with χ_Q the character of
F(√(-disc Q))/F defined without choosing a basis, and the same extra conjuncts. -/
theorem siegel_totallyReal_rank2' (h : n = 2) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (1 / 2 : ℝ) * (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2V Q) (-1) fun v => intrinsicBetaV v Q L m) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      HasLOne (spaceChar2V Q) (LOne (spaceChar2V Q)) ∧ 0 < LOne (spaceChar2V Q) ∧
      Multipliable fun v => intrinsicBetaV v Q L m * (1 - spaceChar2V Q v / (NFEuler.normP v : ℝ)) ^ (-1 : ℤ) := by
  sorry

/-- **Siegel's theorem, rank 1** (factor 1/2 at every place). With the setting above and n = 1,
∑_{L' ∈ Gen(L)} r_{L'}(m)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · 2 · N𝔡(L)^{-1/2} · ∏_σ β_σ(m)/2
  · ∏_𝔭 β_𝔭(L, m)/2.
Moreover the genus of L has finitely many classes, every lattice M in the genus has a finite automorphism group
O(M) and finitely many x ∈ M with Q(x) = m (so the sums and counts above are finite and every |O(M)| ≥ 1),
and the product ∏_𝔭 β_𝔭(L, m)/2 converges unconditionally. -/
theorem siegel_totallyReal_rank1 (h : n = 1) (hQ : IsTotallyPosDefV Q) (hL : IsIntegralLattice Q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    (∑ᶠ c ∈ genusClassesV Q L, (LatClassV.repCount Q c (algebraMap (𝓞 F) F m) : ℝ) / LatClassV.autCard Q c) =
      (∑ᶠ c ∈ genusClassesV Q L, ((LatClassV.autCard Q c : ℝ))⁻¹) *
      (2 * (discNormV Q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ 1 / 2) *
        ∏' v, intrinsicBetaV v Q L m / 2)) ∧
      (genusClassesV Q L).Finite ∧
      (∀ (M : Submodule (𝓞 F) V) [M.IsLattice F], SameGenusV Q L M →
        Finite (autLatV Q M) ∧ Finite {x : V // x ∈ M ∧ Q x = algebraMap (𝓞 F) F m}) ∧
      Multipliable fun v => intrinsicBetaV v Q L m / 2 := by
  sorry

end Siegel

/-! ## Representations of forms by forms over totally real number fields

Setting: F a totally real number field, Q₀ a quadratic form over 𝓞 F in N variables and T₀ one in r variables,
1 ≤ r ≤ N, both totally positive definite over F, L = 𝓞_F^N. r_M(T) is the number of frames X ∈ M^r (columns in M) with
Q ∘ X = T (`LatClass.repCountT`, a `Nat.card`). The case stated here is N ≥ 3 and N - r ≠ 2 (the product of the local
densities converges absolutely); the library also proves the other cases (`Frames.siegelForms_all_ranks`: N - r = 2
regularized by L_F(1, χ), N = 2, N = 1). -/

section SiegelForms

set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open QuadFormsKB.Tamagawa.Frames QuadFormsKB.LocalDensity

/-- **Siegel's formula for representations of forms by forms** (Siegel 1935, Hauptsatz; over F: Siegel
1937). With the setting above,
∑_{L' ∈ Gen(L)} r_{L'}(T₀)/|O(L')| = (∑_{L' ∈ Gen(L)} 1/|O(L')|) · S(Q₀, T₀),
S(Q₀, T₀) = ε' |d_F|^{-r(2N-r-1)/4} ∏_σ ε β_σ(Q₀, T₀) ∏_𝔭 α_𝔭(Q₀, T₀) (`siegelProductT`; ε = 1/2 at every place if
r = N, ε' = 1/2 if r = N - 1). Moreover the product ∏_𝔭 α_𝔭(Q₀, T₀) converges unconditionally, the genus of L has
finitely many classes, and every lattice M in the genus has a finite automorphism group O(M) and finitely many frames
X ∈ M^r with Q₀ ∘ X = T₀. -/
theorem siegelForms_totallyReal {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) (hN : 3 ≤ N) (h2 : N ≠ r + 2)
    (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hpd : IsTotallyPosDef (formF Q₀))
    (hpdT : IsTotallyPosDef (formF T₀)) :
    (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F N),
        (LatClass.repCountT (formF Q₀) c (formF T₀) : ℝ) / LatClass.autCard (formF Q₀) c) =
      (∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F N), ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹) *
        siegelProductT Q₀ T₀ ∧
      (Multipliable fun v => NF.siegelDensity v Q₀ T₀) ∧
      (genusClasses (formF Q₀) (stdLat F N)).Finite ∧
      ∀ M : Lat F N, SameGenus (formF Q₀) (stdLat F N).1 M.1 →
        Finite (autLat (formF Q₀) M.1) ∧
        Finite {X : Matrix (Fin N) (Fin r) F // (∀ j, (fun i => X i j) ∈ M.1) ∧ (formF Q₀).compMat X = formF T₀} := by
  sorry

end SiegelForms

/-! ## Definitions used

The statements above use the following library definitions (all in namespace `QuadFormsKB`; paths relative to
`QuadFormsKB/`), besides those named in the docstrings of the 0.6.0 headlines. Everything else is Mathlib.

Forms and local–global predicates
* `QuadForm R n` (Defs/QuadForm.lean): a form ∑_{i ≤ j} c_ij x_i x_j, by its upper-triangular coefficient matrix.

Siegel's theorem
* `HilbertModular.realEmb F v` (HilbertModular/Congruence.lean): the real embedding F → ℝ of the place v.
* `Lattices.IsIntegralLattice Q L` (Lattices/Basic.lean): Q(x) ∈ 𝓞 F for all x ∈ L, where F is the number field of Q
  (an implicit argument, read off the type of Q) and 𝓞 F is Mathlib's ring of integers of F
  (`NumberField.RingOfIntegers F`).
* `SiegelSpace.IsTotallyPosDefV Q` (Tamagawa/SiegelQuadSpace.lean): Q(x) is totally positive (positive under every
  real embedding of F, the number field of Q, read off its type) for every x ≠ 0.
* `SiegelSpace.LatClassV Q` (Tamagawa/SiegelGenusV.lean): the classes of lattices of (V, Q), i.e. 𝓞 F-lattices in V
  up to isometry by the full O(V, Q) (improper isometries included).
* `SiegelSpace.genusClassesV Q L` (Tamagawa/SiegelGenusV.lean): the set of classes of the lattices M with
  `SameGenusV Q L M`, i.e. the classes L' in Gen(L); `SiegelSpace.SameGenusV Q L M` (same file): M is in the genus
  of L (locally isometric to L at every prime of 𝓞 F).
* `SiegelSpace.LatClassV.repCount Q c t` (Tamagawa/SiegelGenusV.lean): r_M(t) = #{x ∈ M : Q(x) = t} for any lattice
  M in the class c (a `Nat.card`; independent of the representative).
* `SiegelSpace.LatClassV.autCard Q c` (Tamagawa/SiegelGenusV.lean): |O(M)| = `Nat.card (autLatV Q M)` for any
  lattice M in the class c, improper isometries included (independent of the representative).
* `Lattices.autLatV Q M` (Lattices/Basic.lean): O(M), the isometries of (V, Q) mapping M onto M.
* `SiegelSpace.discNormV Q L` (Tamagawa/SiegelClassical.lean): N𝔡(L), the absolute norm of the discriminant ideal of
  L (an ideal of 𝓞 F).
* `SiegelSpace.intrinsicBetaV v Q L m` (Tamagawa/SiegelClassical.lean): for v = 𝔭 a nonzero prime of 𝓞 F
  (`HeightOneSpectrum (𝓞 F)`; the product ∏' v runs over these), β_𝔭(L, m) =
  lim_k #{x ∈ L_𝔭/𝔭^k L_𝔭 : Q(x) ≡ m mod 𝔭^k} / N𝔭^{k(n-1)}, via `SiegelSpace.intrinsicBeta` (same file)
  in the coordinates of `Module.finBasis`.
* `Tamagawa.archRepDensity n a d` (Tamagawa/MassInduction.lean): π^{n/2}/Γ(n/2) · a^{(n-2)/2} · d^{-1/2}.
* `RegProd.regProd χ e f` (Siegel/RegProd.lean): L_F(1, χ)^e · ∏'_𝔭 f(𝔭)(1 - χ(𝔭)/N𝔭)^e, with `RegProd.LOne`
  = lim_{s→1+} L_F(s, χ) and `RegProd.HasLOne χ c` (same file): L_F(s, χ) → c as s → 1⁺;
  `NFEuler.normP 𝔭` (Analysis/NFEulerProduct.lean): N𝔭, the absolute norm of 𝔭.
* `SiegelSpace.spaceChar3`, `SiegelSpace.spaceChar2` (Tamagawa/SiegelSpace.lean): χ(𝔭) = `sqChar` of
  -2m·det H, resp. -det H; `SiegelSpace.sqChar` (same file): the quadratic symbol at 𝔭 (0 at 𝔭 | 2 and at non-units).
* `SiegelSpace.spaceChar3V`, `SiegelSpace.spaceChar2V` (Tamagawa/SiegelSpaceChars.lean): the same with the
  basis-free `sqClassChar` and `hessDetV`.
* `Lattices.coordForm Q e` (Lattices/Basic.lean): the form Q in the basis e (a `Basis (Fin k) F V`), as a `QuadForm F k`
  (F the field of Q; k = 3 or 2 in the statements, from `finBasisOfFinrankEq F V h`).

Tamagawa number and mass formula
* `HilbertModular.formF Q₀` (HilbertModular/GenusTheta.lean): Q₀ with coefficients mapped into F.
* `Lattices.IsTotallyPosDef`, `Lattices.IsTotallyPos` (Lattices/Finite.lean): Q(x) totally positive for x ≠ 0.
* `Lattices.genusClasses Q L` (Lattices/Finite.lean): the classes L' in the genus of L (lattices in F^n up to isometry
  by the full O(Q), improper isometries included); `Lattices.LatClass.autCard Q c` (same file): |O(M)| =
  `Nat.card (autLat Q M)` for any lattice M in the class c. The mass ∑ 1/|O(L')| is written out in the statement
  (it is `Lattices.mass Q L`, same file).
* `Lattices.SameGenus Q L M`, `Lattices.autLat Q M` (Lattices/Genus.lean): M is in the genus of L; O(M).
* `Tamagawa.stdLat F n` (Tamagawa/MassFormula.lean): the lattice 𝓞_F^n in F^n.
* `LocalDensity.NF.siegelDensity v Q T` (LocalDensity/NFFormDensity.lean): α_𝔭(Q, T) = ε β_𝔭(Q, T), ε = 1/2 if
  T has the same rank as Q, with β_𝔭 = `localDensityForm` (same file).

`Tamagawa/Measure/`)
* `RegProd.LOne`, `RegProd.HasLOne` (Siegel/RegProd.lean, as above).

Siegel's formula for indefinite forms (namespace `Tamagawa.Indefinite` unless stated; paths in `Tamagawa/Indefinite/`)
* `Indefinite.repCount Q₀ T₀ i` (CorankOneCount.lean): #(Γ_i\R(M_i, T₀)) in [0, ∞], R(M_i, T₀) = `repsT`.

Forms by forms (namespace `Tamagawa.Frames`; paths in `Tamagawa/`)
* `LatClass.repCountT Q c T`, `repCountT` (FrameRepMass.lean): r_M(T) = #{X ∈ M^r : Q ∘ X = T} for M in the class c.
* `siegelProductT Q₀ T₀`, `epsNR`, `epsCodimOne`, `archDensityForm` (FrameSiegel.lean): Siegel's product S(Q₀, T₀).

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
