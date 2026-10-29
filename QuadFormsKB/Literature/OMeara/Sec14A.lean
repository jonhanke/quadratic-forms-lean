/-
# O'Meara §11H, §14: prolongation of a complete valuation to a finite extension (11:18, 11:18a, 14:1)

**Setting.** $K$ is a complete field with a non-trivial non-archimedean valuation (Mathlib `NontriviallyNormedField K`,
`CompleteSpace K`, `IsUltrametricDist K`; the valuation is the norm), and $L/K$ a finite extension.

**Special case.** O'Meara's theorems cover every complete valuation, including the archimedean ones (via 12:4) and the
trivial one. We prove only the complete, non-trivial, non-archimedean case, which is what Mathlib's spectral norm gives.

**Proves**
* `spectralAbs`: the spectral norm of $L/K$ as an `AbsoluteValue L ℝ`; `prolongation_formula` (**14:1**): it extends
  the valuation of $K$, equals $\lVert N_{L/K}(a)\rVert^{1/n}$ with $n = [L:K]$, is complete, and is the only extension;
* `extension_unique`, `extension_complete` (**11:18**): any valuation of $L$ extending that of $K$ is unique and $L$ is
  complete under it;
* `isEquiv_spectralAbs_of_isEquiv_on_base` (**11:18a**): a valuation $u\circ\psi$ of $L$ pulled back along a ring
  homomorphism $\psi$ that is topological on $K$ is equivalent to the extension, i.e. $\psi$ is topological on $L$.

Proof: Mathlib's `spectralNorm_unique_field_norm_ext`, `spectralNorm.completeSpace`, and the norm formula via
`Algebra.norm_eq_norm_adjoin` and `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`.
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.RingTheory.Norm.Transitivity
import QuadFormsKB.Literature.OMeara.Sec11A

open Filter Topology IntermediateField

namespace QuadFormsKB.OMeara

section Spectral

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The spectral norm of the finite extension $L/K$ as a real absolute value of $L$ (Mathlib's `spectralNorm`). By
`prolongation_formula` it is the unique extension of the valuation of $K$. -/
noncomputable def spectralAbs : AbsoluteValue L ℝ :=
  @NormedField.toAbsoluteValue L (spectralNorm.normedField K L)

/-- Unfolding of `spectralAbs`. -/
theorem spectralAbs_apply (x : L) : spectralAbs (K := K) x = spectralNorm K L x := rfl

/-- The spectral absolute value extends the valuation of $K$. -/
theorem spectralAbs_extends (x : K) : spectralAbs (K := K) (algebraMap K L x) = ‖x‖ :=
  spectralNorm_extends x

/-- Any absolute value of $L$ extending the valuation of $K$ is the spectral one. -/
theorem eq_spectralAbs_of_extends (w : AbsoluteValue L ℝ)
    (hw : ∀ x : K, w (algebraMap K L x) = ‖x‖) : w = spectralAbs (K := K) := by
  ext x
  exact spectralNorm_unique_field_norm_ext hw x

/-- $L$ is complete under the spectral absolute value. -/
theorem completeSpace_spectralAbs : CompleteSpace (WithAbs (spectralAbs (K := K) (L := L))) := by
  let _ := spectralNorm.normedField K L
  have h : Isometry (WithAbs.equiv (spectralAbs (K := K) (L := L))) :=
    AddMonoidHomClass.isometry_of_norm _ (fun x => rfl)
  have hc : CompleteSpace L := spectralNorm.completeSpace K L
  exact (h.isUniformInducing.completeSpace_congr (WithAbs.equiv _).surjective).2 hc

/-- $|a|_{sp} = \\lVert N_{L/K}(a)\\rVert^{1/[L:K]}$. -/
theorem spectralNorm_eq_norm_rpow (x : L) :
    spectralNorm K L x = ‖Algebra.norm K x‖ ^ (1 / (Module.finrank K L : ℝ)) := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hd : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hx
  rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow]
  rw [Algebra.norm_eq_norm_adjoin K x]
  have h1 : ‖Algebra.norm K (IntermediateField.AdjoinSimple.gen K x)‖ =
      ‖(minpoly K x).coeff 0‖ := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_gen] at this
    rw [this, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have : minpoly K (IntermediateField.AdjoinSimple.gen K x) = minpoly K x := by
      rw [← minpoly.algebraMap_eq (algebraMap K⟮x⟯ L).injective]
      simp
    rw [this]
  have h2 : Module.finrank K K⟮x⟯ = (minpoly K x).natDegree :=
    IntermediateField.adjoin.finrank hx
  have h3 := Module.finrank_mul_finrank K K⟮x⟯ L
  rw [h2] at h3
  rw [norm_pow, h1, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  have hm : 0 < Module.finrank K⟮x⟯ L := Module.finrank_pos
  rw [← h3]
  push_cast
  field_simp

/-- **11:18 (2).** For a finite extension $L/K$ of a complete non-trivial non-archimedean valued field, there is at
most one valuation of $L$ extending that of $K$ (so at most one spot of $L$ divides that of $K$). -/
@[kb "omeara1963" "§11H, 11:18 (2), p. 13"]
theorem extension_unique (w w' : AbsoluteValue L ℝ) (hw : ∀ x : K, w (algebraMap K L x) = ‖x‖)
    (hw' : ∀ x : K, w' (algebraMap K L x) = ‖x‖) : w = w' :=
  (eq_spectralAbs_of_extends w hw).trans (eq_spectralAbs_of_extends w' hw').symm

/-- **11:18 (1).** $L$ is complete under any valuation extending that of $K$. -/
@[kb "omeara1963" "§11H, 11:18 (1), p. 13"]
theorem extension_complete (w : AbsoluteValue L ℝ) (hw : ∀ x : K, w (algebraMap K L x) = ‖x‖) :
    CompleteSpace (WithAbs w) := by
  rw [eq_spectralAbs_of_extends (K := K) w hw]
  exact completeSpace_spectralAbs

/-- **14:1** (complete non-trivial non-archimedean case). The valuation of $K$ has a prolongation to $L$, namely
$|a| = |N_{L/K}(a)|^{1/n}$ with $n = [L:K]$; it is complete and is the unique prolongation. -/
@[kb "omeara1963" "§14, 14:1, p. 28"]
theorem prolongation_formula :
    (∀ x : K, spectralAbs (K := K) (L := L) (algebraMap K L x) = ‖x‖) ∧
    (∀ a : L, spectralAbs (K := K) (L := L) a = ‖Algebra.norm K a‖ ^ (1 / (Module.finrank K L : ℝ))) ∧
    CompleteSpace (WithAbs (spectralAbs (K := K) (L := L))) ∧
    ∀ w : AbsoluteValue L ℝ, (∀ x : K, w (algebraMap K L x) = ‖x‖) → w = spectralAbs (K := K) :=
  ⟨spectralAbs_extends, spectralNorm_eq_norm_rpow, completeSpace_spectralAbs,
    eq_spectralAbs_of_extends⟩

/-- The power $w^c$ ($c > 0$) of a non-archimedean absolute value is again an absolute value. -/
noncomputable def rpowAbs {M : Type*} [Field M] (w : AbsoluteValue M ℝ) (hw : IsNonarchimedean w)
    (c : ℝ) (hc : 0 < c) : AbsoluteValue M ℝ where
  toFun x := w x ^ c
  map_mul' x y := by simp [Real.mul_rpow, w.nonneg]
  nonneg' x := Real.rpow_nonneg (w.nonneg x) c
  eq_zero' x := by
    constructor
    · intro h
      have := (Real.rpow_eq_zero (w.nonneg x) hc.ne').1 h
      exact (AbsoluteValue.eq_zero w).1 this
    · rintro rfl
      simp [Real.zero_rpow hc.ne']
  add_le' x y := by
    have h1 : w (x + y) ^ c ≤ max (w x ^ c) (w y ^ c) := by
      rcases le_max_iff.1 (hw x y) with h | h
      · exact (Real.rpow_le_rpow (w.nonneg _) h hc.le).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow (w.nonneg _) h hc.le).trans (le_max_right _ _)
    have h2 : 0 ≤ w x ^ c := Real.rpow_nonneg (w.nonneg x) c
    have h3 : 0 ≤ w y ^ c := Real.rpow_nonneg (w.nonneg y) c
    exact h1.trans (max_le (by linarith) (by linarith))

/-- **11:18a.** Let $\psi\colon L \to G$ be a ring homomorphism into a field with valuation $u$, such that $\psi$ is
topological on $K$ (the pullback of $u$ to $K$ is equivalent to the valuation of $K$). Then $\psi$ is topological on
$L$: the pullback of $u$ to $L$ is equivalent to the extended valuation. -/
@[kb "omeara1963" "§11H, 11:18a, p. 13"]
theorem isEquiv_spectralAbs_of_isEquiv_on_base {G : Type*} [Field G] (ψ : L →+* G)
    (u : AbsoluteValue G ℝ)
    (h : ((u.comp ψ.injective).comp (algebraMap K L).injective).IsEquiv
      (NormedField.toAbsoluteValue K)) :
    (u.comp ψ.injective).IsEquiv (spectralAbs (K := K) (L := L)) := by
  set w1 := u.comp ψ.injective with hw1
  obtain ⟨c, hc, hvc⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h.symm
  have hext : ∀ x : K, w1 (algebraMap K L x) = ‖x‖ ^ c := fun x => (congrFun hvc x).symm
  have hna1 : IsNonarchimedean w1 := by
    refine (isNonarchimedean_iff_natCast_bounded w1).2 ⟨1, fun n => ?_⟩
    have : (n : L) = algebraMap K L (n : K) := by simp
    rw [this, hext]
    have hn : ‖(n : K)‖ ≤ 1 :=
      (IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.1 inferInstance).apply_natCast_le_one
        (by simp) (by simp)
    exact Real.rpow_le_one (norm_nonneg _) hn hc.le
  let w2 := rpowAbs w1 hna1 (1 / c) (by positivity)
  have hw2 : ∀ x : K, w2 (algebraMap K L x) = ‖x‖ := by
    intro x
    show w1 (algebraMap K L x) ^ (1 / c) = ‖x‖
    rw [hext, ← Real.rpow_mul (norm_nonneg _)]
    field_simp
    simp
  have heq := eq_spectralAbs_of_extends (K := K) w2 hw2
  refine AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨1 / c, by positivity, ?_⟩
  rw [← heq]
  rfl

end Spectral

end QuadFormsKB.OMeara
