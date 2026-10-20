/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelSpaceFormula
import QuadFormsKB.Lattices.Basic

/-!
# Siegel's formula for an abstract quadratic space over a totally real number field (gv)

**Layer:** $F$ a totally real number field; $(V, q)$ a finite-dimensional quadratic space over $F$ given by Mathlib's
`q : QuadraticForm F V`, totally positive definite ($\sigma(q(x)) > 0$ for every nonzero $x \in V$ and every real embedding
$\sigma$, `IsTotallyPosDefV`); $L \subseteq V$ an $\mathcal O_F$-lattice (Mathlib's `Submodule.IsLattice F L`: finitely generated,
spanning $V$ over $F$; any Steinitz class) with $q$ integral on $L$ (`IsIntegralLattice q L`); $m \in \mathcal O_F$ totally positive.

**Definitions (via any coordinate system, proved independent of it).** For an $F$-basis $e$ of $V$ (indexed by
$\mathrm{Fin}\,n$), `coordForm q e` is the form $y \mapsto q(\sum_i y_i e_i)$ on $F^n$ and `coordLat e L` the lattice of coordinate
vectors of $L$. The intrinsic objects `massV`, `repMassV`, `siegelProductV`, `siegelProduct3V`, `siegelProduct2RegV`,
`siegelProductOneV` are the SiegelSpace objects of $(\mathtt{coordForm}\ q\ e, \mathtt{coordLat}\ e\ L)$ for the canonical basis
`Module.finBasis` (resp. `Module.finBasisOfFinrankEq`); the theorems `massV_eq_basis`, `repMassV_eq_basis`,
`siegelProductV_eq_basis`, … show that **every** basis $e$ gives the same value. Two bases differ by $g \in \mathrm{GL}_n(F)$
(`basisChange`), which acts by $(Q, L) \mapsto (Q\circ g, g^{-1}L)$ (`coordForm_basis_change`, `coordLat_basis_change`); the
SiegelSpace basis-independence theorems (`siegelProduct*Space_compMat`, `repMass_compMat`, `mass_similar`) do the rest.

**Proves** (unconditional):
* **`siegelFormula_quadraticSpace_totallyReal`** ($\dim V \ge 4$): $\mathrm{repMass}(L, m) = \mathrm{Mass}(L)\cdot S(L, m)$.
* **`siegelFormula3_quadraticSpace_totallyReal`**, **`siegelFormula2_quadraticSpace_totallyReal`** ($\varepsilon = \tfrac12$),
  **`siegelFormula1_quadraticSpace_totallyReal`**, with the same regularizations as SiegelSpace.
* Natural order (given `NaturalOrderEulerOne` of the character, in any basis): `siegelFormula3_quadraticSpace_natural`,
  `siegelFormula2_quadraticSpace_natural`.
* Consistency: for $V = F^N$ and $q$ from a `QuadForm F N`, every intrinsic object is the SiegelSpace one
  (`massV_pi`, `repMassV_pi`, `siegelProductV_pi`, …).

The local densities $\beta_\mathfrak p$ and the archimedean factors individually depend on the Haar measure on $V_\mathfrak p$, i.e. on the
basis (`spaceBeta_compMat`, `detGramF_compMat`); only the products are intrinsic, so the natural-order statements quote the
densities in a chosen basis $e$.

Source: Siegel 1935, Hauptsatz; Siegel 1937 (over number fields) [unverified locators].

-/

open NumberField IsDedekindDomain Filter Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open Matrix
open QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm QuadFormsKB.HilbertModular QuadFormsKB.NFEuler
open QuadFormsKB.RegProd QuadFormsKB.Tamagawa.SiegelLat LatChange

variable {F : Type} [Field F] [NumberField F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]

/-! ### Coordinates of a lattice and change of basis -/

section Coords

variable {n : ℕ}

/-- **Total positive definiteness of an abstract quadratic space:** $\sigma(q(x)) > 0$ for every nonzero $x \in V$ and every
embedding $\sigma : F \to \mathbb C$ (so $F$ totally real makes this positive definiteness at every real place). -/
@[kb "omeara1963" "§66 (positive definite at each real place) [unverified]"]
def IsTotallyPosDefV (q : QuadraticForm F V) : Prop := ∀ x : V, x ≠ 0 → IsTotallyPos (q x)

/-- **The coordinate vectors of $L$** in the basis $e$: $\{e^*(x) : x \in L\} \subseteq F^n$. -/
def coordLatSub (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) : Submodule (𝓞 F) (Fin n → F) :=
  L.map (e.equivFun.toLinearMap.restrictScalars (𝓞 F))

theorem coordLatSub_isLattice (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) [hL : L.IsLattice F] :
    (coordLatSub e L).IsLattice F where
  fg := hL.fg.map _
  span_eq_top := by
    rw [coordLatSub, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hL.span_eq_top,
      Submodule.map_top, LinearMap.range_eq_top]
    exact e.equivFun.surjective

/-- **The coordinate lattice** $e^*(L) \in$ `Lat F n` of a lattice $L \subseteq V$. -/
def coordLat (e : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] : Lat F n :=
  ⟨coordLatSub e L, coordLatSub_isLattice e L⟩

theorem eval_coordForm (q : QuadraticForm F V) (e : Basis (Fin n) F V) (y : Fin n → F) :
    (coordForm q e).eval y = q (e.equivFun.symm y) := by
  rw [coordForm, eval_ofQuadraticForm, QuadraticMap.comp_apply, LinearEquiv.coe_coe]

theorem isTotallyPosDef_coordForm {q : QuadraticForm F V} (hq : IsTotallyPosDefV q) (e : Basis (Fin n) F V) :
    IsTotallyPosDef (coordForm q e) := fun y hy => by
  rw [eval_coordForm]
  exact hq _ fun h => hy ((LinearEquiv.map_eq_zero_iff _).mp h)

theorem isIntegral_coordLat {q : QuadraticForm F V} {L : Submodule (𝓞 F) V} [L.IsLattice F]
    (hLi : IsIntegralLattice q L) (e : Basis (Fin n) F V) : Lattices.IsIntegral (coordForm q e) (coordLat e L).1 := by
  rintro _ ⟨x, hx, rfl⟩
  have h := eval_coordForm q e (e.equivFun x)
  simp only [LinearEquiv.symm_apply_apply] at h
  change (coordForm q e).eval (e.equivFun x) ∈ _
  rw [h]
  exact hLi x hx

/-- **The change-of-basis matrix** $g = [e]_{e'}$ (columns: the $e$-coordinates of $e'_j$), so that $g\,e'^*(x) = e^*(x)$. -/
def basisChange (e e' : Basis (Fin n) F V) : GL (Fin n) F :=
  ⟨e.toMatrix e', e'.toMatrix e, e.toMatrix_mul_toMatrix_flip e', e'.toMatrix_mul_toMatrix_flip e⟩

theorem basisChange_mulVec (e e' : Basis (Fin n) F V) (x : V) :
    (basisChange e e').val *ᵥ e'.equivFun x = e.equivFun x := by
  simp only [basisChange, Basis.equivFun_apply]
  exact e'.toMatrix_mulVec_repr e x

theorem basisChange_inv_mulVec (e e' : Basis (Fin n) F V) (x : V) :
    (basisChange e e')⁻¹.val *ᵥ e.equivFun x = e'.equivFun x := by
  rw [← basisChange_mulVec e e' x, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

/-- **Change of basis on the form:** $q_{e'} = q_e \circ g$ with $g$ = `basisChange e e'`. -/
theorem coordForm_basis_change (q : QuadraticForm F V) (e e' : Basis (Fin n) F V) :
    coordForm q e' = (coordForm q e).compMat (basisChange e e').val := by
  refine QuadForm.ext_eval fun y => ?_
  obtain ⟨x, rfl⟩ := e'.equivFun.surjective y
  rw [eval_compMat, basisChange_mulVec, eval_coordForm, eval_coordForm]
  simp only [LinearEquiv.symm_apply_apply]

/-- **Change of basis on the lattice:** $e'^*(L) = g^{-1}\,e^*(L)$ with $g$ = `basisChange e e'`. -/
theorem coordLat_basis_change (e e' : Basis (Fin n) F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] :
    coordLat e' L = Lat.image (basisChange e e')⁻¹ (coordLat e L) := by
  apply Subtype.ext
  change coordLatSub e' L = glImage _ (coordLatSub e L)
  rw [coordLatSub, coordLatSub, glImage, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun x => ?_
  exact (basisChange_inv_mulVec e e' x).symm

theorem lat_image_image_inv' (γ : GL (Fin n) F) (M : Lat F n) : Lat.image γ (Lat.image γ⁻¹ M) = M :=
  Subtype.ext (by
    change glImage γ (glImage γ⁻¹ M.1) = M.1
    rw [← glImage_mul, mul_inv_cancel, glImage_one])

/-- Two bases of $V$ indexed by $\mathrm{Fin}\,n$ and $\mathrm{Fin}\,n'$ have $n = n'$. -/
theorem basis_card_eq {n' : ℕ} (e : Basis (Fin n) F V) (e' : Basis (Fin n') F V) : n = n' := by
  have h1 := finrank_eq_card_basis e
  have h2 := finrank_eq_card_basis e'
  simp only [Fintype.card_fin] at h1 h2
  rw [← h1, ← h2]

end Coords

/-! ### Basis independence -/

section Indep

variable {n : ℕ} (q : QuadraticForm F V) (L : Submodule (𝓞 F) V) [L.IsLattice F]

/-- **The mass does not depend on the basis.** -/
theorem mass_coord_indep {n' : ℕ} (e : Basis (Fin n) F V) (e' : Basis (Fin n') F V) :
    mass (coordForm q e) (coordLat e L) = mass (coordForm q e') (coordLat e' L) := by
  obtain rfl := basis_card_eq e e'
  have h1 : (1 : F) • (coordForm q e).compMat (basisChange e e').val =
      (coordForm q e).compMat (basisChange e e').val := by ext i j; simp
  rw [coordForm_basis_change q e e', coordLat_basis_change e e', ← h1, mass_similar _ one_ne_zero,
    lat_image_image_inv']

variable {q L}

/-- **The weighted representation number of the genus does not depend on the basis.** -/
theorem repMass_coord_indep (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {n' : ℕ} (e : Basis (Fin n) F V)
    (e' : Basis (Fin n') F V) (t : F) :
    repMass (coordForm q e) (coordLat e L) t = repMass (coordForm q e') (coordLat e' L) t := by
  obtain rfl := basis_card_eq e e'
  rw [coordForm_basis_change q e e', coordLat_basis_change e e',
    repMass_compMat _ _ (isTotallyPosDef_coordForm hq e) (isIntegral_coordLat hLi e)]

variable [IsTotallyReal F]

/-- **$S(L, m)$ does not depend on the basis** ($\dim V \ge 4$). -/
theorem siegelProductSpace_coord_indep (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {n' : ℕ}
    (hn : 4 ≤ n) (e : Basis (Fin n) F V) (e' : Basis (Fin n') F V) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductSpace (coordForm q e) (coordLat e L) m = siegelProductSpace (coordForm q e') (coordLat e' L) m := by
  obtain rfl := basis_card_eq e e'
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [coordForm_basis_change q e e', coordLat_basis_change e e',
    siegelProductSpace_compMat (by omega) _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) _ hm]

/-- **$S_3(L, m)$ does not depend on the basis.** -/
theorem siegelProduct3Space_coord_indep (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L)
    (e e' : Basis (Fin 3) F V) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct3Space (coordForm q e) (coordLat e L) m = siegelProduct3Space (coordForm q e') (coordLat e' L) m := by
  rw [coordForm_basis_change q e e', coordLat_basis_change e e',
    siegelProduct3Space_compMat _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) _ hm]

/-- **$S^{\mathrm{reg}}_2(L, m)$ does not depend on the basis.** -/
theorem siegelProduct2RegSpace_coord_indep (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L)
    (e e' : Basis (Fin 2) F V) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct2RegSpace (coordForm q e) (coordLat e L) m =
      siegelProduct2RegSpace (coordForm q e') (coordLat e' L) m := by
  rw [coordForm_basis_change q e e', coordLat_basis_change e e',
    siegelProduct2RegSpace_compMat _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) _ hm]

/-- **$\mathcal S_1(L, m)$ does not depend on the basis.** -/
theorem siegelProductOneSpace_coord_indep (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L)
    (e e' : Basis (Fin 1) F V) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductOneSpace (coordForm q e) (coordLat e L) m =
      siegelProductOneSpace (coordForm q e') (coordLat e' L) m := by
  rw [coordForm_basis_change q e e', coordLat_basis_change e e',
    siegelProductOneSpace_compMat _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) _ hm]

end Indep

/-! ### The intrinsic objects -/

section Intrinsic

variable [FiniteDimensional F V] (q : QuadraticForm F V) (L : Submodule (𝓞 F) V) [L.IsLattice F]

/-- **The mass of the genus of $L$ in $(V, q)$**, $\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)} 1/|O(M)|$, computed in the coordinates of
`Module.finBasis`; any basis gives the same value (`massV_eq_basis`). -/
@[kb "siegel1935" "§1 (mass of a genus) [unverified]"]
def massV : ℝ := mass (coordForm q (finBasis F V)) (coordLat (finBasis F V) L)

/-- **The weighted representation number** $\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)} r_M(t)/|O(M)|$ of the genus of $L$ in $(V, q)$,
computed in the coordinates of `Module.finBasis`; any basis gives the same value (`repMassV_eq_basis`). -/
@[kb "siegel1935" "§1 (genus average) [unverified]"]
def repMassV (t : F) : ℝ := repMass (coordForm q (finBasis F V)) (coordLat (finBasis F V) L) t

/-- **Siegel's product** $S(L, m) = |d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma\prod_\mathfrak p\beta_\mathfrak p$ of $(V, q, L)$ ($N = \dim V$),
computed in the coordinates of `Module.finBasis`; any basis gives the same value (`siegelProductV_eq_basis`, $N \ge 4$). -/
@[kb "siegel1935" "Hauptsatz (Siegel product) [unverified]"]
def siegelProductV (m : 𝓞 F) : ℝ := siegelProductSpace (coordForm q (finBasis F V)) (coordLat (finBasis F V) L) m

/-- **The regularized ternary Siegel product** of $(V, q, L)$ ($\dim V = 3$), in the coordinates of
`Module.finBasisOfFinrankEq`; any basis gives the same value (`siegelProduct3V_eq_basis`). -/
def siegelProduct3V (h : finrank F V = 3) (m : 𝓞 F) : ℝ :=
  siegelProduct3Space (coordForm q (finBasisOfFinrankEq F V h)) (coordLat (finBasisOfFinrankEq F V h) L) m

/-- **The regularized binary Siegel product** of $(V, q, L)$ ($\dim V = 2$); basis independent (`siegelProduct2RegV_eq_basis`). -/
def siegelProduct2RegV (h : finrank F V = 2) (m : 𝓞 F) : ℝ :=
  siegelProduct2RegSpace (coordForm q (finBasisOfFinrankEq F V h)) (coordLat (finBasisOfFinrankEq F V h) L) m

/-- **The unary Siegel product** of $(V, q, L)$ ($\dim V = 1$); basis independent (`siegelProductOneV_eq_basis`). -/
def siegelProductOneV (h : finrank F V = 1) (m : 𝓞 F) : ℝ :=
  siegelProductOneSpace (coordForm q (finBasisOfFinrankEq F V h)) (coordLat (finBasisOfFinrankEq F V h) L) m

variable {n : ℕ}

theorem massV_eq_basis (e : Basis (Fin n) F V) : massV q L = mass (coordForm q e) (coordLat e L) :=
  mass_coord_indep q L _ e

variable {q L}

theorem repMassV_eq_basis (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) (e : Basis (Fin n) F V) (t : F) :
    repMassV q L t = repMass (coordForm q e) (coordLat e L) t :=
  repMass_coord_indep hq hLi _ e t

variable [IsTotallyReal F]

theorem siegelProductV_eq_basis (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) (hN : 4 ≤ finrank F V)
    (e : Basis (Fin n) F V) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductV q L m = siegelProductSpace (coordForm q e) (coordLat e L) m :=
  siegelProductSpace_coord_indep hq hLi hN _ e hm

theorem siegelProduct3V_eq_basis (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) (h : finrank F V = 3)
    (e : Basis (Fin 3) F V) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct3V q L h m = siegelProduct3Space (coordForm q e) (coordLat e L) m :=
  siegelProduct3Space_coord_indep hq hLi _ e hm

theorem siegelProduct2RegV_eq_basis (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) (h : finrank F V = 2)
    (e : Basis (Fin 2) F V) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct2RegV q L h m = siegelProduct2RegSpace (coordForm q e) (coordLat e L) m :=
  siegelProduct2RegSpace_coord_indep hq hLi _ e hm

theorem siegelProductOneV_eq_basis (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) (h : finrank F V = 1)
    (e : Basis (Fin 1) F V) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductOneV q L h m = siegelProductOneSpace (coordForm q e) (coordLat e L) m :=
  siegelProductOneSpace_coord_indep hq hLi _ e hm

end Intrinsic

/-! ### The headlines -/

section Headlines

variable [IsTotallyReal F] [FiniteDimensional F V] {q : QuadraticForm F V} {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **Siegel's formula for an abstract quadratic space over a totally real number field, $\dim V \ge 4$** (unconditional;
Siegel 1935, Hauptsatz; over $F$: Siegel 1937 [unverified]): for every totally positive definite quadratic space $(V, q)$
over $F$ of dimension $N \ge 4$, every $\mathcal O_F$-lattice $L \subseteq V$ with $q$ integral on $L$ and every totally positive
$m \in \mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot S(L, m).$$
Every term is defined in some coordinate system of $V$ and proved independent of it (`massV_eq_basis`, …). -/
@[kb "siegel1935" "Hauptsatz, abstract quadratic space over a totally real field, every genus [unverified for F]"]
theorem siegelFormula_quadraticSpace_totallyReal (hN : 4 ≤ finrank F V) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassV q L (algebraMap (𝓞 F) F m) = massV q L * siegelProductV q L m :=
  siegelFormula_space_totallyReal hN _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm

/-- **Siegel's formula for an abstract ternary quadratic space over a totally real number field** (unconditional; regularized
with $\chi_m$): $\mathrm{repMass}(L, m) = \mathrm{Mass}(L)\cdot S_3(L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 3, abstract quadratic space over a totally real field, every genus [unverified for F]"]
theorem siegelFormula3_quadraticSpace_totallyReal (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassV q L (algebraMap (𝓞 F) F m) = massV q L * siegelProduct3V q L h m := by
  rw [repMassV_eq_basis hq hLi (finBasisOfFinrankEq F V h), massV_eq_basis q L (finBasisOfFinrankEq F V h)]
  exact siegelFormula3_space_totallyReal _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm

/-- **Siegel's formula for an abstract binary quadratic space over a totally real number field** (unconditional;
$\varepsilon = \tfrac12$, regularized with $\chi_q$): $\mathrm{repMass}(L, m) = \tfrac12\,\mathrm{Mass}(L)\cdot S^{\mathrm{reg}}_2(L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2), abstract quadratic space over a totally real field [unverified for F]"]
theorem siegelFormula2_quadraticSpace_totallyReal (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massV q L * siegelProduct2RegV q L h m := by
  rw [repMassV_eq_basis hq hLi (finBasisOfFinrankEq F V h), massV_eq_basis q L (finBasisOfFinrankEq F V h)]
  exact siegelFormula2_space_totallyReal _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm

/-- **Siegel's formula for an abstract unary quadratic space over a totally real number field** (unconditional;
$\varepsilon = \tfrac12$): $\mathrm{repMass}(L, m) = \mathrm{Mass}(L)\cdot 2\,\mathcal S_1(L, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2), abstract quadratic space over a totally real field [unverified for F]"]
theorem siegelFormula1_quadraticSpace_totallyReal (h : finrank F V = 1) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassV q L (algebraMap (𝓞 F) F m) = massV q L * (2 * siegelProductOneV q L h m) := by
  rw [repMassV_eq_basis hq hLi (finBasisOfFinrankEq F V h), massV_eq_basis q L (finBasisOfFinrankEq F V h)]
  exact siegelFormula1_space_totallyReal _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm

/-- **Ternary, natural order** (Hanke 2004, (5.3), p. 368, over $F$): in any basis $e$ of $V$, given
`NaturalOrderEulerOne` of the character $\chi_m$ (convention input), $\lim_X\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ is the
regularized value, and Siegel's formula holds with the intrinsic product. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), abstract quadratic space over a totally real field"]
theorem siegelFormula3_quadraticSpace_natural (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (e : Basis (Fin 3) F V) (hN : NaturalOrderEulerOne (spaceChar3 (coordForm q e) m)) :
    HasProd (fun v => spaceBeta v (coordForm q e) (coordLat e L) m)
        (regProd (spaceChar3 (coordForm q e) m) 1 fun v => spaceBeta v (coordForm q e) (coordLat e L) m) (normOrder F) ∧
      repMassV q L (algebraMap (𝓞 F) F m) = massV q L * siegelProduct3V q L h m :=
  ⟨(siegelFormula3_space_natural _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) hm hN).1,
    siegelFormula3_quadraticSpace_totallyReal h hq hLi hm⟩

/-- **Binary, natural order**: in any basis $e$ of $V$, given `NaturalOrderEulerOne` of $\chi_q$,
$\lim_X\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L, m)$ is the regularized value, and Siegel's formula holds with the intrinsic product. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), abstract quadratic space over a totally real field [unverified]"]
theorem siegelFormula2_quadraticSpace_natural (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (e : Basis (Fin 2) F V) (hN : NaturalOrderEulerOne (spaceChar2 (coordForm q e))) :
    HasProd (fun v => spaceBeta v (coordForm q e) (coordLat e L) m)
        (regProd (spaceChar2 (coordForm q e)) (-1) fun v => spaceBeta v (coordForm q e) (coordLat e L) m)
        (normOrder F) ∧
      repMassV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massV q L * siegelProduct2RegV q L h m :=
  ⟨(siegelFormula2_space_natural _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) hm hN).1,
    siegelFormula2_quadraticSpace_totallyReal h hq hLi hm⟩

end Headlines

/-! ### Consistency with SiegelSpace ($V = F^N$) -/

section Pi

variable {N : ℕ} (Q : QuadForm F N) (L : Submodule (𝓞 F) (Fin N → F)) [L.IsLattice F]

theorem coordForm_basisFun : coordForm Q.toQuadraticForm (Pi.basisFun F (Fin N)) = Q :=
  QuadForm.ext_eval fun y => by
    rw [eval_coordForm, Pi.basisFun_equivFun, toQuadraticForm_apply]; rfl

theorem coordLat_basisFun : coordLat (Pi.basisFun F (Fin N)) L = ⟨L, inferInstance⟩ := by
  apply Subtype.ext
  change L.map _ = L
  rw [Pi.basisFun_equivFun]
  exact Submodule.map_id L

theorem isTotallyPosDefV_toQuadraticForm {Q : QuadForm F N} (hpd : IsTotallyPosDef Q) :
    IsTotallyPosDefV Q.toQuadraticForm := fun x hx => by rw [toQuadraticForm_apply]; exact hpd x hx

theorem isIntegralLattice_toQuadraticForm {Q : QuadForm F N} (hLi : Lattices.IsIntegral Q L) :
    IsIntegralLattice Q.toQuadraticForm L := fun x hx => by rw [toQuadraticForm_apply]; exact hLi x hx

/-- On $V = F^N$ the intrinsic mass is SiegelSpace's `mass`. -/
theorem massV_pi : massV Q.toQuadraticForm L = mass Q ⟨L, inferInstance⟩ := by
  rw [massV_eq_basis _ _ (Pi.basisFun F (Fin N)), coordForm_basisFun, coordLat_basisFun]

variable {Q L}

/-- On $V = F^N$ the intrinsic `repMassV` is SiegelSpace's `repMass`. -/
theorem repMassV_pi (hpd : IsTotallyPosDef Q) (hLi : Lattices.IsIntegral Q L) (t : F) :
    repMassV Q.toQuadraticForm L t = repMass Q ⟨L, inferInstance⟩ t := by
  rw [repMassV_eq_basis (isTotallyPosDefV_toQuadraticForm hpd) (isIntegralLattice_toQuadraticForm L hLi)
    (Pi.basisFun F (Fin N)), coordForm_basisFun, coordLat_basisFun]

variable [IsTotallyReal F]

/-- On $V = F^N$ the intrinsic `siegelProductV` is `siegelProductSpace` ($N \ge 4$). -/
theorem siegelProductV_pi (hpd : IsTotallyPosDef Q) (hLi : Lattices.IsIntegral Q L) (hN : 4 ≤ N) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductV Q.toQuadraticForm L m = siegelProductSpace Q ⟨L, inferInstance⟩ m := by
  rw [siegelProductV_eq_basis (isTotallyPosDefV_toQuadraticForm hpd) (isIntegralLattice_toQuadraticForm L hLi)
    (by simpa using hN) (Pi.basisFun F (Fin N)) hm, coordForm_basisFun, coordLat_basisFun]

theorem siegelProduct3V_pi {Q : QuadForm F 3} {L : Submodule (𝓞 F) (Fin 3 → F)} [L.IsLattice F]
    (hpd : IsTotallyPosDef Q) (hLi : Lattices.IsIntegral Q L) (h : finrank F (Fin 3 → F) = 3) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct3V Q.toQuadraticForm L h m = siegelProduct3Space Q ⟨L, inferInstance⟩ m := by
  rw [siegelProduct3V_eq_basis (isTotallyPosDefV_toQuadraticForm hpd) (isIntegralLattice_toQuadraticForm L hLi) h
    (Pi.basisFun F (Fin 3)) hm, coordForm_basisFun, coordLat_basisFun]

theorem siegelProduct2RegV_pi {Q : QuadForm F 2} {L : Submodule (𝓞 F) (Fin 2 → F)} [L.IsLattice F]
    (hpd : IsTotallyPosDef Q) (hLi : Lattices.IsIntegral Q L) (h : finrank F (Fin 2 → F) = 2) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct2RegV Q.toQuadraticForm L h m = siegelProduct2RegSpace Q ⟨L, inferInstance⟩ m := by
  rw [siegelProduct2RegV_eq_basis (isTotallyPosDefV_toQuadraticForm hpd) (isIntegralLattice_toQuadraticForm L hLi) h
    (Pi.basisFun F (Fin 2)) hm, coordForm_basisFun, coordLat_basisFun]

theorem siegelProductOneV_pi {Q : QuadForm F 1} {L : Submodule (𝓞 F) (Fin 1 → F)} [L.IsLattice F]
    (hpd : IsTotallyPosDef Q) (hLi : Lattices.IsIntegral Q L) (h : finrank F (Fin 1 → F) = 1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductOneV Q.toQuadraticForm L h m = siegelProductOneSpace Q ⟨L, inferInstance⟩ m := by
  rw [siegelProductOneV_eq_basis (isTotallyPosDefV_toQuadraticForm hpd) (isIntegralLattice_toQuadraticForm L hLi) h
    (Pi.basisFun F (Fin 1)) hm, coordForm_basisFun, coordLat_basisFun]

end Pi

end QuadFormsKB.Tamagawa.SiegelSpace
