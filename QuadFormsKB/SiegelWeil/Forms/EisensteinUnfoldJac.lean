/-
# The Jacobian of the unfolding coordinates
**Layer:** archimedean, over a totally real number field $F$ of degree $d$ with discriminant $d_F$.

**Statement.** Let $\Phi = $ `phiR F r` $:\mathbb R^J\to(\mathbb R^{\mathrm{SymIdx}_r})^{d}$, $t\mapsto(X_w(t))_w$, where the $p$-th
entry of $X(t)$ is $\sum_j t_{p,j}\,\sigma(b_j)\in\mathbb R^d$ for the $\mathbb Z$-basis $(b_j)$ of $\mathcal O_F$ behind `oBasis F`.
Then
$$|\det\Phi| = \big(\sqrt{|d_F|}\big)^{\#\mathrm{SymIdx}_r},\qquad\text{i.e. `phiDetR F r`}=\sqrt{|d_F|}^{\,r(r+1)/2}.$$

*Proof.* The unit cube of $\mathbb R^J$ is carried by $\Phi$ onto $\{x:\ \forall p,\ x_{\bullet p}\in P\}$, $P=$ the parallelepiped of `oBasis F`.
After the measure-preserving coordinate swap this is a product of $\#\mathrm{SymIdx}_r$ copies of $P$, and
$\mathrm{vol}(P)=\mathrm{covol}(\sigma(\mathcal O_F))=\sqrt{|d_F|}$ (Mathlib's `covolume_idealLattice` for the unit ideal, via the
measure-preserving identification `mixedEquiv` of $F\otimes\mathbb R$ with $\mathbb R^d$).

Sources: Neukirch, *Algebraic Number Theory*, Ch. I, Prop. 5.2 (covolume of the Minkowski lattice) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldArchProd
import QuadFormsKB.Analysis.MinkowskiPoissonPi
open Matrix NumberField MeasureTheory NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors
open IsDedekindDomain
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus
set_option linter.unusedSectionVars false
noncomputable section
namespace QuadFormsKB.SiegelWeil.Forms
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

/-- The coordinate swap $(\mathbb R^{\kappa})^{\iota}\simeq(\mathbb R^{\iota})^{\kappa}$ as a linear equivalence. -/
def swapL (ι κ : Type) : (ι → κ → ℝ) ≃ₗ[ℝ] (κ → ι → ℝ) where
  toFun x p w := x w p
  invFun y w p := y p w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Lebesgue measure on $\mathbb R^{\iota\times\kappa}$ (nested form) is an additive Haar measure. -/
instance instAddHaarNested (ι κ : Type) [Fintype ι] [Fintype κ] :
    (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := by
  rw [volume_pi]
  infer_instance

/-- The unit cube of $\iota\to\kappa\to\mathbb R$ has volume $1$. -/
lemma volume_Icc_nested (ι κ : Type) [Fintype ι] [Fintype κ] :
    (volume : Measure (ι → κ → ℝ)) (Set.Icc 0 1) = 1 := by
  have : (Set.Icc (0 : ι → κ → ℝ) 1) = Set.univ.pi fun _ => Set.Icc (0 : κ → ℝ) 1 := by
    ext x; simp [Pi.le_def]
  rw [this, volume_pi_pi]
  simp [Real.volume_Icc_pi]

/-- The coordinate swap preserves Lebesgue measure. -/
lemma volume_swapL_preimage (ι κ : Type) [Fintype ι] [Fintype κ] (A : Set (κ → ι → ℝ)) :
    (volume : Measure (ι → κ → ℝ)) (swapL ι κ ⁻¹' A) = volume A := by
  let e : (ι → κ → ℝ) ≃ᵐ (κ → ι → ℝ) :=
    (swapL ι κ).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hH : ((volume : Measure (ι → κ → ℝ)).map (swapL ι κ)).IsAddHaarMeasure :=
    Measure.MapLinearEquiv.isAddHaarMeasure (𝕜 := ℝ) (volume : Measure (ι → κ → ℝ)) (swapL ι κ)
  have hmap := Measure.isAddLeftInvariant_eq_smul
    ((volume : Measure (ι → κ → ℝ)).map (swapL ι κ)) (volume : Measure (κ → ι → ℝ))
  set k := Measure.addHaarScalarFactor ((volume : Measure (ι → κ → ℝ)).map (swapL ι κ))
    (volume : Measure (κ → ι → ℝ)) with hk
  have hmapA : ∀ B : Set (κ → ι → ℝ),
      ((volume : Measure (ι → κ → ℝ)).map (swapL ι κ)) B = volume (swapL ι κ ⁻¹' B) :=
    fun B => e.map_apply B
  have hK : swapL ι κ ⁻¹' (Set.Icc (0 : κ → ι → ℝ) 1) = Set.Icc 0 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, Pi.le_def]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i j => h1 j i, fun i j => h2 j i⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i j => h1 j i, fun i j => h2 j i⟩
  have h1 : (1 : ENNReal) = k := by
    have := hmapA (Set.Icc 0 1)
    rw [hmap, hK, volume_Icc_nested, Measure.smul_apply, volume_Icc_nested] at this
    simpa using this.symm
  have hk1 : k = 1 := by exact_mod_cast h1.symm
  rw [← hmapA, hmap, hk1, one_smul]

variable (F) in
/-- The real-coordinate fundamental parallelepiped $P$ of `oBasis F` in $\mathbb R^d$. -/
abbrev parOBasis : Set (InfinitePlace F → ℝ) := parallelepiped (⇑(oBasis F))

/-- `mixedEquiv` as a measurable equivalence. -/
def mixedMEquiv : mixedSpace F ≃ᵐ (InfinitePlace F → ℝ) :=
  (mixedEquiv (F := F)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- `mixedEquiv` preserves Lebesgue measure (the complex factor is empty). -/
lemma measurePreserving_mixedMEquiv :
    MeasurePreserving (mixedMEquiv (F := F)) volume volume := by
  classical
  let f : {w : InfinitePlace F // w.IsReal} ≃ InfinitePlace F :=
    Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v
  have : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)) := by
    rw [volume_pi, Measure.pi_of_empty]
    infer_instance
  have h1 : MeasurePreserving (Prod.fst : mixedSpace F → ({w : InfinitePlace F // w.IsReal} → ℝ))
      volume volume := measurePreserving_fst
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℝ) f).comp h1
  have hfun : (⇑(mixedMEquiv (F := F))) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : InfinitePlace F => ℝ) f) ∘ Prod.fst := by
    funext y v
    obtain ⟨u, rfl⟩ := f.surjective v
    rw [Function.comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  rw [hfun]
  exact h2

/-- The volume of the parallelepiped of `oBasis F` is $\sqrt{|d_F|}$. -/
lemma volume_parOBasis : (volume : Measure (InfinitePlace F → ℝ)) (parOBasis F) =
    ENNReal.ofReal (Real.sqrt |(NumberField.discr F : ℝ)|) := by
  have h1 : parOBasis F = mixedMEquiv '' (parallelepiped (⇑(QuadFormsKB.Analysis.bR (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)))) := by
    have := image_parallelepiped (mixedEquiv (F := F)).toLinearMap
      (⇑(QuadFormsKB.Analysis.bR (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)))
    exact this.symm
  have h2 : (volume : Measure (InfinitePlace F → ℝ)) (parOBasis F) =
      (volume : Measure (mixedSpace F))
        (parallelepiped (⇑(QuadFormsKB.Analysis.bR (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)))) := by
    rw [h1, MeasurableEquiv.image_eq_preimage_symm]
    exact (measurePreserving_mixedMEquiv (F := F)).symm.measure_preimage_equiv _
  rw [h2, ← Module.Basis.coe_parallelepiped, QuadFormsKB.Analysis.volume_parallelepiped_bR,
    covolume_idealLattice]
  simp

/-- The preimage of the cube $\{x:\forall p,\ x_{\bullet p}\in P\}$ under `phiR` is the unit cube of $\mathbb R^J$. -/
lemma phiR_preimage_cube :
    phiR F r ⁻¹' {x : InfinitePlace F → SymIdx r → ℝ | ∀ p, (fun w => x w p) ∈ parOBasis F} =
      Set.Icc (0 : JR F r → ℝ) 1 := by
  ext t
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
  have key : ∀ p, (fun w => phiR F r t w p) ∈ parOBasis F ↔
      (∀ j, 0 ≤ t (p, j)) ∧ ∀ j, t (p, j) ≤ 1 := by
    intro p
    have hp : (fun w => phiR F r t w p) = (oBasis F).equivFun.symm (fun j => t (p, j)) := rfl
    rw [hp, parOBasis, mem_parallelepiped_iff]
    constructor
    · rintro ⟨s, ⟨hs0, hs1⟩, hs⟩
      have : (fun j => t (p, j)) = s := by
        apply (oBasis F).equivFun.symm.injective
        rw [hs, Module.Basis.equivFun_symm_apply]
      subst this
      exact ⟨fun j => hs0 j, fun j => hs1 j⟩
    · rintro ⟨h0, h1⟩
      exact ⟨fun j => t (p, j), ⟨fun j => h0 j, fun j => h1 j⟩,
        (Module.Basis.equivFun_symm_apply _ _)⟩
  simp_rw [key]
  constructor
  · intro h
    exact ⟨fun q => (h q.1).1 q.2, fun q => (h q.1).2 q.2⟩
  · rintro ⟨h1, h2⟩ p
    exact ⟨fun j => h1 (p, j), fun j => h2 (p, j)⟩

/-- **The Jacobian of the unfolding coordinates:** $|\det\Phi| = \sqrt{|d_F|}^{\,\#\mathrm{SymIdx}_r}$. -/
theorem phiDetR_eq :
    phiDetR F r = Real.sqrt |(NumberField.discr F : ℝ)| ^ Fintype.card (SymIdx r) := by
  have hH : ((volume : Measure (JR F r → ℝ)).map (phiR F r)).IsAddHaarMeasure := inferInstance
  have hmap := Measure.isAddLeftInvariant_eq_smul
    ((volume : Measure (JR F r → ℝ)).map (phiR F r))
    (volume : Measure (InfinitePlace F → SymIdx r → ℝ))
  set c := Measure.addHaarScalarFactor ((volume : Measure (JR F r → ℝ)).map (phiR F r))
    (volume : Measure (InfinitePlace F → SymIdx r → ℝ)) with hc
  let e : (JR F r → ℝ) ≃ᵐ (InfinitePlace F → SymIdx r → ℝ) :=
    (phiR F r).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  set S : Set (InfinitePlace F → SymIdx r → ℝ) :=
    {x | ∀ p, (fun w => x w p) ∈ parOBasis F} with hS
  have hL : ((volume : Measure (JR F r → ℝ)).map (phiR F r)) S = 1 := by
    have : ((volume : Measure (JR F r → ℝ)).map (phiR F r)) S = volume (phiR F r ⁻¹' S) :=
      e.map_apply S
    rw [this, hS, phiR_preimage_cube, Real.volume_Icc_pi]
    simp
  have hS' : S = swapL (InfinitePlace F) (SymIdx r) ⁻¹'
      (Set.univ.pi fun _ : SymIdx r => parOBasis F) := by
    ext x; simp [hS, swapL]
  have hvS : (volume : Measure (InfinitePlace F → SymIdx r → ℝ)) S =
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr F : ℝ)|)) ^ Fintype.card (SymIdx r) := by
    rw [hS', volume_swapL_preimage, volume_pi_pi, volume_parOBasis]
    simp
  have hpos : 0 < Real.sqrt |(NumberField.discr F : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F))
  have h1 : (1 : ENNReal) = (c : ENNReal) *
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr F : ℝ)|)) ^ Fintype.card (SymIdx r) := by
    rw [← hvS, ← hL, hmap, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [← ENNReal.ofReal_pow hpos.le] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hpos.le _)] at h2
  simp only [ENNReal.toReal_one, ENNReal.coe_toReal] at h2
  have hcne : (c : ℝ) ≠ 0 := by
    intro h; rw [h] at h2; simp at h2
  rw [phiDetR]
  exact (eq_inv_of_mul_eq_one_right h2.symm).symm

end QuadFormsKB.SiegelWeil.Forms