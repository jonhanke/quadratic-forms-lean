/-
# Covolumes of presented lattices, for every class number
**Layer:** $F$ a number field (any class number), $n \in \mathbb N$. A *presented lattice* is
$$L(P,\mathfrak a) = \{P\xi : \xi_i \in \mathfrak a_i\} \subset F^n,\qquad P \in \mathrm{GL}_n(F),\ \mathfrak a_1,\dots,\mathfrak a_n\ \text{fractional ideals}$$
(every $\mathcal O_F$-lattice has such a presentation, by Steinitz). Its *covolume* relative to $\mathcal O_F^n$ is
$\operatorname{covol}(P,\mathfrak a) = |N_{F/\mathbb Q}(\det P)|\prod_iN(\mathfrak a_i)$ (`covol`).

* **`relIndex_presGrp`**: for presented lattices $L \subseteq L'$, $[L':L]\cdot\operatorname{covol}(L') = \operatorname{covol}(L)$
  (as ℤ-lattices in the ℚ-space $F^n$: a ℚ-basis of $F^n$ spanning $L$ over ℤ is $P\,(\beta^{(i)}_k e_i)$, $\beta^{(i)}$ a ℤ-basis of $\mathfrak a_i$;
  its determinant against $(\omega_ke_i)$, $\omega$ an integral basis, is $N(\det P)\prod_i\det(\beta^{(i)}/\omega)$, `det_presBasis`,
  and $|\det(\beta^{(i)}/\omega)| = N(\mathfrak a_i)$, Mathlib's `det_basisOfFractionalIdeal_eq_absNorm`).
* **`latConst_mul_covol`**: the lattice constant of $L(P,\mathfrak a)$ with Gram matrix $P^{\mathsf T}A_0P$ times
  $\operatorname{covol}(P,\mathfrak a)$ is the
  lattice constant of $(\mathcal O_F^n, A_0)$; hence **`latConst_eq_mul_relIndex`**: $c_{L'} = c_L\,[L':L]$ for $L \subseteq L'$.

No basis of an $\mathcal O_F$-module is chosen: only ℤ-bases of fractional ideals (always free over ℤ) and ℚ-bases.

Source: standard (the index of ℤ-lattices is the absolute value of the determinant, Mathlib's `AddSubgroup.relIndex_eq_abs_det`;
$\det_{\mathbb Q}(P) = N_{F/\mathbb Q}(\det_FP)$, `LinearMap.det_restrictScalars`).
-/
import QuadFormsKB.Tamagawa.QuatEichlerMass
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Norm.Transitivity

open NumberField Module Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LatCovol

open QuadFormsKB.SphericalUnfold QuadFormsKB.IdeleClass QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "ιF" => Free.ChooseBasisIndex ℤ (𝓞 F)

/-! ### A ℚ-basis of $F$ spanning a fractional ideal -/

/-- The index type of a ℤ-basis of a fractional ideal has the cardinality of that of $\mathcal O_F$. -/
def idealIdx (𝔞 : FracIdeal F) : ιF ≃ Free.ChooseBasisIndex ℤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
  Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
      NumberField.fractionalIdeal_rank])

/-- **A ℚ-basis of $F$ spanning $\mathfrak a$ over ℤ**, indexed like the integral basis. -/
def idealBasis (𝔞 : FracIdeal F) : Basis ιF ℚ F :=
  (basisOfFractionalIdeal F 𝔞).reindex (idealIdx 𝔞).symm

theorem mem_span_idealBasis (𝔞 : FracIdeal F) {x : F} :
    x ∈ Submodule.span ℤ (Set.range (idealBasis 𝔞)) ↔ x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) : Set F) := by
  rw [idealBasis, Basis.range_reindex]
  exact mem_span_basisOfFractionalIdeal F

theorem abs_det_idealBasis (𝔞 : FracIdeal F) :
    |(integralBasis F).det (idealBasis 𝔞)| = FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
  det_basisOfFractionalIdeal_eq_absNorm F 𝔞 (idealIdx 𝔞)

/-! ### The ℚ-bases of $F^n$ -/

/-- The standard ℚ-basis $(\omega_ke_i)$ of $F^n$. -/
def stdBasis : Basis (Σ _ : Fin n, ιF) ℚ (Fin n → F) := Pi.basis fun _ => integralBasis F

/-- The ℚ-basis $(\beta^{(i)}_ke_i)$ of $F^n$ spanning $\bigoplus_i\mathfrak a_i$ over ℤ. -/
def latBasis (𝔞 : Fin n → FracIdeal F) : Basis (Σ _ : Fin n, ιF) ℚ (Fin n → F) :=
  Pi.basis fun i => idealBasis (𝔞 i)

/-- $P$ as a ℚ-linear automorphism of $F^n$. -/
def matEquiv (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) : (Fin n → F) ≃ₗ[ℚ] (Fin n → F) :=
  letI : Invertible P.det := invertibleOfNonzero hP
  letI : Invertible P := P.invertibleOfDetInvertible
  (Matrix.toLinearEquiv' P this).restrictScalars ℚ

theorem matEquiv_apply (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) (x : Fin n → F) :
    matEquiv P hP x = P *ᵥ x := rfl

/-- The ℚ-basis $P(\beta^{(i)}_ke_i)$ spanning the presented lattice $L(P,\mathfrak a)$ over ℤ. -/
def presBasis (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) (𝔞 : Fin n → FracIdeal F) :
    Basis (Σ _ : Fin n, ιF) ℚ (Fin n → F) :=
  (latBasis 𝔞).map (matEquiv P hP)

theorem det_latBasis (𝔞 : Fin n → FracIdeal F) :
    (stdBasis (F := F) (n := n)).det (latBasis 𝔞) = ∏ i, (integralBasis F).det (idealBasis (𝔞 i)) := by
  classical
  let e : (Σ _ : Fin n, ιF) ≃ ιF × Fin n := (Equiv.sigmaEquivProd (Fin n) ιF).trans (Equiv.prodComm _ _)
  rw [Basis.det_apply]
  have h : (stdBasis (F := F) (n := n)).toMatrix (latBasis 𝔞) =
      (Matrix.blockDiagonal fun i => (integralBasis F).toMatrix (idealBasis (𝔞 i))).submatrix e e := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [Basis.toMatrix_apply, stdBasis, latBasis, Pi.basis_repr, Pi.basis_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal_apply, e, Equiv.trans_apply, Equiv.sigmaEquivProd_apply, Equiv.prodComm_apply,
      Prod.swap_prod_mk]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Pi.single_eq_of_ne hij]; simp [hij]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  simp only [Basis.det_apply]

theorem det_matEquiv (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) :
    LinearMap.det (matEquiv P hP : (Fin n → F) →ₗ[ℚ] (Fin n → F)) = Algebra.norm ℚ P.det := by
  have : (matEquiv P hP : (Fin n → F) →ₗ[ℚ] (Fin n → F)) = (Matrix.toLin' P).restrictScalars ℚ := by
    ext x; rfl
  rw [this, LinearMap.det_restrictScalars, LinearMap.det_toLin']

/-- **The determinant of the presented basis**: $N(\det P)\prod_i\det(\beta^{(i)}/\omega)$. -/
theorem det_presBasis (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) (𝔞 : Fin n → FracIdeal F) :
    (stdBasis (F := F) (n := n)).det (presBasis P hP 𝔞) =
      Algebra.norm ℚ P.det * ∏ i, (integralBasis F).det (idealBasis (𝔞 i)) := by
  rw [presBasis, Basis.coe_map, show (⇑(matEquiv P hP) ∘ ⇑(latBasis 𝔞)) =
    ⇑(matEquiv P hP : (Fin n → F) →ₗ[ℚ] (Fin n → F)) ∘ ⇑(latBasis 𝔞) from rfl, Basis.det_comp, det_matEquiv,
    det_latBasis]

/-! ### Presented lattices -/

/-- **The presented lattice** $L(P,\mathfrak a) = \{P\xi : \xi_i \in \mathfrak a_i\}$, as an additive subgroup of $F^n$. -/
def presGrp (P : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → FracIdeal F) : AddSubgroup (Fin n → F) where
  carrier := {y | ∃ ξ, LatMem 𝔞 ξ ∧ y = P *ᵥ ξ}
  add_mem' := by
    rintro _ _ ⟨ξ, hξ, rfl⟩ ⟨η, hη, rfl⟩
    exact ⟨ξ + η, fun i => Submodule.add_mem _ (hξ i) (hη i), (Matrix.mulVec_add _ _ _).symm⟩
  zero_mem' := ⟨0, fun i => Submodule.zero_mem _, (Matrix.mulVec_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨ξ, hξ, rfl⟩
    exact ⟨-ξ, fun i => Submodule.neg_mem _ (hξ i), (Matrix.mulVec_neg _ _).symm⟩

theorem mem_presGrp {P : Matrix (Fin n) (Fin n) F} {𝔞 : Fin n → FracIdeal F} {y : Fin n → F} :
    y ∈ presGrp P 𝔞 ↔ ∃ ξ, LatMem 𝔞 ξ ∧ y = P *ᵥ ξ := Iff.rfl

theorem span_latBasis (𝔞 : Fin n → FracIdeal F) {ξ : Fin n → F} :
    ξ ∈ Submodule.span ℤ (Set.range (latBasis 𝔞)) ↔ LatMem 𝔞 ξ := by
  classical
  constructor
  · intro h
    let S : Submodule ℤ (Fin n → F) :=
      { carrier := {ξ | LatMem 𝔞 ξ}
        add_mem' := fun hξ hη i => Submodule.add_mem _ (hξ i) (hη i)
        zero_mem' := fun i => Submodule.zero_mem _
        smul_mem' := fun c ξ hξ i => by
          have : ((c : 𝓞 F) • ξ i) = c • ξ i := by
            rw [Algebra.smul_def, zsmul_eq_mul]; simp
          show c • ξ i ∈ _
          rw [← this]; exact Submodule.smul_mem _ _ (hξ i) }
    have hle : Submodule.span ℤ (Set.range (latBasis 𝔞)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨i, k⟩, rfl⟩ j
      simp only [latBasis, Pi.basis_apply]
      by_cases hij : j = i
      · subst hij
        rw [Pi.single_eq_same]
        exact (mem_span_idealBasis (𝔞 j)).1 (Submodule.subset_span ⟨k, rfl⟩)
      · rw [Pi.single_eq_of_ne hij]; exact Submodule.zero_mem _
    exact hle h
  · intro h
    have hξ : ξ = ∑ i, Pi.single i (ξ i) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hξ]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi := (mem_span_idealBasis (𝔞 i)).2 (h i)
    have hmap : Submodule.map (LinearMap.single ℤ (fun _ : Fin n => F) i)
        (Submodule.span ℤ (Set.range (idealBasis (𝔞 i)))) ≤ Submodule.span ℤ (Set.range (latBasis 𝔞)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨⟨i, k⟩, by simp [latBasis]⟩
    exact hmap ⟨ξ i, hi, rfl⟩

theorem presGrp_eq_closure (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) (𝔞 : Fin n → FracIdeal F) :
    presGrp P 𝔞 = AddSubgroup.closure (Set.range (presBasis P hP 𝔞)) := by
  ext y
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, mem_presGrp, presBasis,
    Basis.coe_map, Set.range_comp]
  have : Submodule.span ℤ (⇑(matEquiv P hP) '' Set.range (latBasis 𝔞)) =
      Submodule.map ((matEquiv P hP : (Fin n → F) →ₗ[ℚ] (Fin n → F)).restrictScalars ℤ)
        (Submodule.span ℤ (Set.range (latBasis 𝔞))) := by
    rw [Submodule.map_span]; rfl
  rw [this]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨ξ, (span_latBasis 𝔞).2 hξ, rfl⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨ξ, (span_latBasis 𝔞).1 hξ, rfl⟩

/-- **The covolume** $|N(\det P)|\prod_iN(\mathfrak a_i)$ of $L(P,\mathfrak a)$ relative to $\mathcal O_F^n$. -/
def covol (P : Matrix (Fin n) (Fin n) F) (𝔞 : Fin n → FracIdeal F) : ℝ :=
  |((Algebra.norm ℚ P.det : ℚ) : ℝ)| * ∏ i, idealNorm F (𝔞 i)

theorem abs_det_presBasis (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) (𝔞 : Fin n → FracIdeal F) :
    (|(stdBasis (F := F) (n := n)).det (presBasis P hP 𝔞)| : ℝ) = covol P 𝔞 := by
  rw [det_presBasis, covol]
  push_cast
  rw [abs_mul, Finset.abs_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [idealNorm, ← abs_det_idealBasis (𝔞 i)]
  push_cast; rfl

theorem covol_pos (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) (𝔞 : Fin n → FracIdeal F) : 0 < covol P 𝔞 := by
  refine mul_pos (abs_pos.2 ?_) (Finset.prod_pos fun i _ => idealNorm_pos F _)
  exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hP

/-- **The index of presented lattices**: for $L(P,\mathfrak a) \subseteq L(P',\mathfrak a')$,
$[L(P',\mathfrak a') : L(P,\mathfrak a)]\cdot\operatorname{covol}(P',\mathfrak a') = \operatorname{covol}(P,\mathfrak a)$. -/
theorem relIndex_presGrp {P P' : Matrix (Fin n) (Fin n) F} (hP : P.det ≠ 0) (hP' : P'.det ≠ 0)
    {𝔞 𝔞' : Fin n → FracIdeal F} (hle : presGrp P 𝔞 ≤ presGrp P' 𝔞') :
    ((presGrp P 𝔞).relIndex (presGrp P' 𝔞') : ℝ) * covol P' 𝔞' = covol P 𝔞 := by
  classical
  have h := AddSubgroup.relIndex_eq_abs_det (presGrp P 𝔞) (presGrp P' 𝔞') hle (presBasis P hP 𝔞)
    (presBasis P' hP' 𝔞') (presGrp_eq_closure P hP 𝔞) (presGrp_eq_closure P' hP' 𝔞')
  have hm := Basis.toMatrix_mul_toMatrix (stdBasis (F := F) (n := n)) (presBasis P' hP' 𝔞') (presBasis P hP 𝔞)
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, ← Basis.det_apply, ← Basis.det_apply, ← Basis.det_apply] at hd
  have h' : ((presGrp P 𝔞).relIndex (presGrp P' 𝔞') : ℝ) =
      ((|(presBasis P' hP' 𝔞').det (presBasis P hP 𝔞)| : ℚ) : ℝ) := by exact_mod_cast h
  rw [h', ← abs_det_presBasis P' hP' 𝔞', ← abs_det_presBasis P hP 𝔞, ← hd]
  push_cast
  rw [abs_mul, mul_comm]

/-! ### The lattice constant of a presented lattice -/

variable [IsTotallyReal F]

/-- **The lattice constant times the covolume** is that of the standard lattice: for $A = P^{\mathsf T}A_0P$,
$c_{(A,\mathfrak a)}\cdot\operatorname{covol}(P,\mathfrak a) = c_{(A_0,\mathcal O_F^n)}$. -/
theorem latConst_mul_covol {A₀ : Matrix (Fin n) (Fin n) F} (hA₀ : IsTotPosGram A₀) (P : Matrix (Fin n) (Fin n) F)
    (hP : P.det ≠ 0) (𝔞 : Fin n → FracIdeal F) :
    AdditiveZeta.latConst (Pᵀ * A₀ * P) 𝔞 * covol P 𝔞 = AdditiveZeta.latConst A₀ (fun _ => 1) := by
  have hsq : ∀ v : InfinitePlace F, Real.sqrt ((Pᵀ * A₀ * P).map (realEmb F v)).det =
      |realEmb F v P.det| * Real.sqrt (A₀.map (realEmb F v)).det := by
    intro v
    have h1 : ((Pᵀ * A₀ * P).map (realEmb F v)).det = (realEmb F v P.det) ^ 2 * (A₀.map (realEmb F v)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul]; ring
    rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hP0 : 0 < ∏ v : InfinitePlace F, Real.sqrt (A₀.map (realEmb F v)).det :=
    Finset.prod_pos fun v _ => Real.sqrt_pos.2 (hA₀ v).det_pos
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  have hsd : 0 < Real.sqrt (NumberField.discr F : ℝ) := Real.sqrt_pos.2 hd
  have hemb : ∀ i, embDet (𝔞 i) = idealNorm F (𝔞 i) * Real.sqrt (NumberField.discr F) := fun i => by
    rw [AdditiveZeta.embDet_eq]; rfl
  have hemb1 : embDet (1 : FracIdeal F) = Real.sqrt (NumberField.discr F) := by
    rw [AdditiveZeta.embDet_eq]; simp
  have hN : 0 < |((Algebra.norm ℚ P.det : ℚ) : ℝ)| := abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hP)
  have hI : 0 < ∏ i, idealNorm F (𝔞 i) := Finset.prod_pos fun i _ => idealNorm_pos F _
  unfold AdditiveZeta.latConst covol
  rw [Finset.prod_congr rfl fun v _ => hsq v, Finset.prod_mul_distrib, QuatOrder.prod_abs_realEmb_eq,
    Finset.prod_congr rfl fun i _ => hemb i, Finset.prod_mul_distrib]
  simp only [hemb1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hs : 0 < Real.sqrt (NumberField.discr F : ℝ) ^ n := pow_pos hsd n
  field_simp

/-- **The lattice constant grows with the index**: for presented lattices $L(P,\mathfrak a) \subseteq L(P',\mathfrak a')$ with Gram matrices
$P^{\mathsf T}A_0P$, $P'^{\mathsf T}A_0P'$: $c_{L'} = c_L\,[L':L]$. -/
theorem latConst_eq_mul_relIndex {A₀ : Matrix (Fin n) (Fin n) F} (hA₀ : IsTotPosGram A₀)
    {P P' : Matrix (Fin n) (Fin n) F} (hP : P.det ≠ 0) (hP' : P'.det ≠ 0)
    {𝔞 𝔞' : Fin n → FracIdeal F} (hle : presGrp P 𝔞 ≤ presGrp P' 𝔞') :
    AdditiveZeta.latConst (P'ᵀ * A₀ * P') 𝔞' =
      AdditiveZeta.latConst (Pᵀ * A₀ * P) 𝔞 * ((presGrp P 𝔞).relIndex (presGrp P' 𝔞') : ℝ) := by
  have h1 := latConst_mul_covol hA₀ P hP 𝔞
  have h2 := latConst_mul_covol hA₀ P' hP' 𝔞'
  have h3 := relIndex_presGrp hP hP' hle
  have hc := covol_pos P' hP' 𝔞'
  have hc' := covol_pos P hP 𝔞
  rw [← h3] at h1
  have : AdditiveZeta.latConst (P'ᵀ * A₀ * P') 𝔞' * covol P' 𝔞' =
      AdditiveZeta.latConst (Pᵀ * A₀ * P) 𝔞 * ((presGrp P 𝔞).relIndex (presGrp P' 𝔞') : ℝ) * covol P' 𝔞' := by
    rw [h2, ← h1]; ring
  exact mul_right_cancel₀ hc.ne' this

end QuadFormsKB.LatCovol
