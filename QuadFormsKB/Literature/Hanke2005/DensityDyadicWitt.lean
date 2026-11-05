/-
# Hanke 2005, §3: the Hensel link `DyadicWittLink` (proved)

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Proves** the named input `DyadicWittLink` (`DensityDyadicSelfDual.lean`): at a dyadic place with a unimodular Hessian and
$n=2m$, the reduction $\bar Q_0$ over $\mathcal O/\mathfrak p$ has Witt index $m$ iff the anisotropic kernel of $Q_0$ over
$F_\mathfrak p$ is $0$.

*Route (no Hensel lifting of isotropic subspaces is needed).* Both sides are the same square-class condition on
$\Delta=(-1)^m\det H$:
1. (`arfSignQ_eq_one_iff_wittIndex`) The Arf sign $\varepsilon=\mathrm{arfSignQ}(Q,\pi)$ (defined by the number of
   solutions of $Q\equiv0\pmod\pi$) equals $+1$ iff the Witt index of $\bar Q$ is $m$: the zero count of a nonsingular
   quadratic form over $\mathbb F_q$, $q$ even, is $q^{2m-1}+\varepsilon'(q^m-q^{m-1})$ with $\varepsilon'=+1$ iff the Witt
   index is $m$ (`zeros_and_card`).
2. (`DVR.arfSignQ_eq_one_iff_isSquare_frac`, O'Meara 93:15 and §93D) $\varepsilon=+1$ iff $\Delta$ is a square in $F_\mathfrak p$.
3. (`anisoDim_eq_two_iff`, `anisoDim_le_two_of_dualIndexAt_eq_one`, parity) $\Delta$ is a square in $F_\mathfrak p$ iff the
   anisotropic kernel has dimension $0$ (it has dimension $0$ or $2$).
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicFinite
import QuadFormsKB.Literature.Hanke2005.LocalTypes
import QuadFormsKB.Siegel.NFDyadicGood
import QuadFormsKB.Literature.Hanke2005.DensityOddWitt

open NumberField IsDedekindDomain QuadraticMap QuadraticForm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB QuadFormsKB.LocalDensity

/-- Evaluation commutes with change of rings (any commutative rings). -/
theorem eval_map_apply' {A B : Type*} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (Q : QuadForm A n)
    (x : Fin n → A) : (Q.map φ).eval (fun i => φ (x i)) = φ (Q.eval x) := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, map_sum, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

section Residue

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The solution count of $Q\equiv0\pmod\pi$ is the number of zeros of the reduction $\bar Q$ over the residue field.** -/
theorem repCount_zero_eq_card_zeros {π : R} (hπ : Irreducible π) {n : ℕ} (Q : QuadForm R n) :
    DVR.repCount Q π 1 0 =
      Nat.card {x : Fin n → IsLocalRing.ResidueField R // (Q.map (IsLocalRing.residue R)).toQuadraticForm x = 0} := by
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  let φ : (R ⧸ Ideal.span {π ^ 1}) ≃+* IsLocalRing.ResidueField R :=
    Ideal.quotEquivOfEq (by rw [pow_one, ← hmax])
  have hφ : ∀ r : R, φ (Ideal.Quotient.mk _ r) = IsLocalRing.residue R r := fun r => rfl
  have h1 : Q.map (IsLocalRing.residue R) = (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))).map φ.toRingHom := by
    apply QuadForm.ext
    ext i j
    simp [QuadForm.map, hφ]
  unfold DVR.repCount
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => φ.toEquiv) (fun x => ?_))
  rw [QuadForm.toQuadraticForm_apply, h1]
  have h3 := eval_map_apply' φ.toRingHom (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))) x
  have h4 : Q.evalIn (R ⧸ Ideal.span {π ^ 1}) x = (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))).eval x := by
    simp [QuadForm.evalIn, QuadForm.map]
  have h5 : (fun i => φ (x i)) = (Equiv.piCongrRight fun _ => φ.toEquiv) x := rfl
  have h3' : ((Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))).map φ.toRingHom).eval
      ((Equiv.piCongrRight fun _ => φ.toEquiv) x) = φ ((Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))).eval x) := h3
  rw [h3', h4]
  constructor
  · intro h; rw [h]; simp
  · intro h
    have : φ ((Ideal.Quotient.mk (Ideal.span {π ^ 1})) 0) = φ ((Q.map (Ideal.Quotient.mk (Ideal.span {π ^ 1}))).eval x) := by
      simpa using h.symm
    exact (φ.injective this).symm

/-- **The Arf sign is $+1$ iff the reduction has maximal Witt index** ($\pi\mid2$, unimodular Hessian, $2m$ variables):
the number of zeros of $\bar Q$ is $q^{2m-1}+\varepsilon'(q^m-q^{m-1})$ (`zeros_and_card`), where $\varepsilon'=+1$ iff the Witt
index of $\bar Q$ is $m$, and $\varepsilon=+1$ iff this exceeds $q^{2m-1}$. -/
@[kb "omeara1963" "93:15, 93:16--93:18 (Arf sign of an even unimodular lattice = Witt type of the reduction)"]
theorem arfSignQ_eq_one_iff_wittIndex [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (h2 : π ∣ 2)
    {j : ℕ} (Q : QuadForm R (2 * (j + 1))) (hdet : IsUnit Q.hessian.det) :
    DVR.arfSignQ Q π = 1 ↔
      QuadraticForm.wittIndex (Q.map (IsLocalRing.residue R)).toQuadraticForm = j + 1 := by
  classical
  have : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  have h20 : (2 : IsLocalRing.ResidueField R) = 0 := by
    have : (IsLocalRing.residue R) 2 = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]; exact h2
    exact (map_ofNat (IsLocalRing.residue R) 2).symm.trans this
  have : CharP (IsLocalRing.ResidueField R) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h20
  have hdet' : (Q.map (IsLocalRing.residue R)).hessian.det ≠ 0 := by
    have : (Q.map (IsLocalRing.residue R)).hessian = Q.hessian.map (IsLocalRing.residue R) := by
      simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
    rw [this, show (Q.hessian.map (IsLocalRing.residue R)).det = IsLocalRing.residue R Q.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (hdet.map _).ne_zero
  have hnd := nondegenerate_toQuadraticForm _ hdet'
  have hz := (zeros_and_card (K := IsLocalRing.ResidueField R) j (Fin (2 * (j + 1)) → IsLocalRing.ResidueField R)
    (Q.map (IsLocalRing.residue R)).toQuadraticForm hnd (by simp)).1
  rw [← repCount_zero_eq_card_zeros hπ Q] at hz
  have hq : DVR.q R = Fintype.card (IsLocalRing.ResidueField R) := Nat.card_eq_fintype_card
  have hq2 : 2 ≤ Fintype.card (IsLocalRing.ResidueField R) := Fintype.one_lt_card_iff_nontrivial.2 inferInstance
  unfold DVR.arfSignQ
  rw [hq, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
  generalize Fintype.card (IsLocalRing.ResidueField R) = X at *
  have hlt : (X : ℤ) ^ j < (X : ℤ) ^ (j + 1) := by
    rw [pow_succ]
    have : (0 : ℤ) < (X : ℤ) ^ j := by positivity
    nlinarith
  by_cases hw : QuadraticForm.wittIndex (Q.map (IsLocalRing.residue R)).toQuadraticForm = j + 1
  · rw [if_pos hw] at hz
    simp only [hw, iff_true]
    rw [if_pos]
    have : ((X ^ (2 * j + 1) : ℕ) : ℤ) < (DVR.repCount Q π 1 0 : ℤ) := by
      rw [hz]; push_cast; linarith
    exact_mod_cast this
  · rw [if_neg hw] at hz
    simp only [hw, iff_false]
    rw [if_neg]
    · simp
    · intro hlt'
      have : ((X ^ (2 * j + 1) : ℕ) : ℤ) < (DVR.repCount Q π 1 0 : ℤ) := by exact_mod_cast hlt'
      rw [hz] at this; push_cast at this; linarith

end Residue

variable {F : Type} [Field F] [NumberField F]

/-- **`DyadicWittLink` is a theorem** (O'Meara 93:15, 93:16--93:18; Hanke thesis, §3, p. 8): at a dyadic place with
$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]=1$ and $n=2m$, the reduction $\bar Q_0$ has Witt index $m$ iff the
anisotropic kernel of $Q_0$ over $F_\mathfrak p$ is $0$. Both are equivalent to $(-1)^m\det H$ being a square in
$F_\mathfrak p$ (`arfSignQ_eq_one_iff_wittIndex`, `DVR.arfSignQ_eq_one_iff_isSquare_frac`, `anisoDim_eq_two_iff`). -/
@[kb "omeara1963" "93:15, 93:16--93:18 (even unimodular lattices: reduction hyperbolic iff the space is hyperbolic)"]
theorem dyadicWittLink (F : Type) [Field F] [NumberField F] : DyadicWittLink F := by
  refine ⟨fun {m} hm Q₀ hQ v h2 h1 => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hπ := NF.irreducible_π v
  have hπ2 : NF.π v ∣ 2 := by
    by_contra hd
    exact h2 (DVR.dvr_isUnit_of_not_dvd hπ hd)
  have hdet := isUnit_det_of_dualIndexAt_eq_one v Q₀ h1
  rw [← arfSignQ_eq_one_iff_wittIndex hπ hπ2 (NF.Qp v Q₀) hdet]
  have hL := isLocalLevel_zero_of_isUnit_det (NF.Qp v Q₀) (NF.π v) hdet
  rw [DVR.arfSignQ_eq_one_iff_isSquare_frac (v.adicCompletion F) (NF.Qp v Q₀) hπ hπ2 (NF.two_ne_zero' v) hL
    (by omega)]
  have hev : Even (2 * (j + 1)) := ⟨j + 1, by ring⟩
  have e : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)
      ((-1) ^ (2 * (j + 1) / 2) * (NF.Qp v Q₀).hessian.det) =
      (-1) ^ (2 * (j + 1) / 2) * (Qf v Q₀).hessian.det := by
    have hQf : Qf v Q₀ = (NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) :=
      (QV_eq_Qf v Q₀).symm
    rw [hQf, SelfDualD.hessian_det_map]
    simp [map_mul, map_pow, map_neg, map_one]
  rw [e, ← isSquare_algebraMap_discK_iff v Q₀ hev]
  have h2' := anisoDim_eq_two_iff v Q₀ hQ hev
  have hle := anisoDim_le_two_of_dualIndexAt_eq_one v Q₀ hQ h1
  have hpar := anisoDim_parity v Q₀ hQ
  constructor
  · intro hs
    by_contra hne
    have : anisoDim v Q₀ = 2 := by omega
    exact (h2'.1 this) hs
  · intro h0
    by_contra hs
    have := h2'.2 hs
    omega

/-- **`DyadicOrthogonalOrder` unconditionally**: the group order `evenOrthogonalOrderChar2` with the Hensel link
`dyadicWittLink`, both now proved. -/
@[kb "omeara1963" "93:15, 93:16--93:18 (order of the orthogonal group of the reduction; unconditional)"]
theorem dyadicOrthogonalOrder_uncond (F : Type) [Field F] [NumberField F] : DyadicOrthogonalOrder F :=
  dyadicOrthogonalOrder_of_wittLink (dyadicWittLink F)

/-- **Shimura's (3.3) at a dyadic place with $\widetilde\Lambda_\mathfrak p = \Lambda_\mathfrak p$, unconditionally**
(`shimuraDensityDyadicSelfDual_of_orderCount` with `dyadicOrthogonalOrder_uncond`). -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p = Λ_p)"]
theorem shimuraDensityDyadicSelfDual (F : Type) [Field F] [NumberField F] : ShimuraDensityDyadicSelfDual F :=
  shimuraDensityDyadicSelfDual_of_orderCount (dyadicOrthogonalOrder_uncond F)

/-- **The places of Shimura's (3.3) not proved directly, from the dyadic places with
$\widetilde\Lambda_\mathfrak p \ne \Lambda_\mathfrak p$ alone**: `shimuraMaximalDensityRest_of_split` with the odd
ramified places (`shimuraDensityOddRamified`) and the dyadic self-dual places (`shimuraDensityDyadicSelfDual`) proved;
the only named input left is `ShimuraDensityDyadicBad`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (places p | 2e)"]
theorem shimuraMaximalDensityRest_of_dyadicBad {F : Type} [Field F] [NumberField F]
    (I : ShimuraDensityDyadicBad F) : ShimuraMaximalDensityRest F :=
  shimuraMaximalDensityRest_of_split (shimuraDensityOddRamified F) (shimuraDensityDyadicSelfDual F) I

end QuadFormsKB.Hanke2005
