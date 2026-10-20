import QuadFormsKB.Tamagawa.Measure.OrbitalComplex

/-!
# The stabilizer of $e_0$ in $SO(Q)(\mathbb C)$

The complex analogue of `OrbitalReal.exists_iota_eq_of_mulVec_e₀`: for $Q = \langle c\rangle \perp Q'$ with
$c \ne 0$, every $g \in SO(Q)(\mathbb C)$ with $g e_0 = e_0$ is $\iota(h) = \mathrm{diag}(1, h)$ for a (unique)
$h \in SO(Q')(\mathbb C)$. With `OrbitalComplex.exists_mulVec_e₀_eqC` this identifies $S_c \cong SO(Q)/SO(Q')$, so
`orbC s` is a bijection $S_c \times SO(Q') \to SO(Q)$ (`orbC_bijective`).
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.OrbitalComplex

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC

variable {m : ℕ} {c : ℂ} {Q' : QuadForm ℂ m}

/-- The lower-right $m \times m$ block of an $(m+1)\times(m+1)$ matrix. -/
def blockSubC (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : Matrix (Fin m) (Fin m) ℂ := X.submatrix Fin.succ Fin.succ

theorem iotaC_mulVec_e₀ (h : ArchSOC Q') :
    ArchSOC.mat _ (iotaC c Q' h) *ᵥ (e₀ : Fin (m + 1) → ℂ) = e₀ := by
  rw [mat_iotaC, cornerMat_mulVec]; simp

theorem shape_of_mulVec_e₀C (hc : c ≠ 0) (g : ArchSOC (splitForm c Q'))
    (hg : ArchSOC.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℂ) = e₀) :
    ArchSOC.mat _ g = cornerMat 1 (blockSubC (ArchSOC.mat _ g)) := by
  set G := ArchSOC.mat _ g
  have hcol : ∀ i, G i 0 = (e₀ : Fin (m + 1) → ℂ) i := fun i => by
    have := congrFun hg i
    rw [← this]; simp [mulVec, dotProduct, Fin.sum_univ_succ, G]
  have hiso := ArchSOC.isometry _ g
  rw [gramC_splitForm] at hiso
  have hrow : ∀ j : Fin m, G 0 j.succ = 0 := by
    intro j
    have := congrFun (congrFun hiso 0) j.succ
    simp only [Matrix.mul_apply, transpose_apply, cornerMat_zero_succ] at this
    have hsum : ∑ x, (∑ x_1, G x_1 0 * cornerMat c (gramC Q') x_1 x) * G x j.succ = c * G 0 j.succ := by
      rw [Fin.sum_univ_succ]
      simp only [hcol, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, cornerMat_zero_zero,
        cornerMat_zero_succ, cornerMat_succ_zero, zero_mul, mul_zero, add_zero, Finset.sum_const_zero, one_mul]
    rw [hsum] at this
    exact (mul_eq_zero.mp this).resolve_left hc
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hcol 0
  · simpa using hrow j
  · simpa using hcol i.succ
  · rfl

/-- **The stabilizer of $e_0$ in $SO(Q)(\mathbb C)$ is $\iota(SO(Q')(\mathbb C))$** ($Q = \langle c\rangle \perp Q'$,
$c \ne 0$). The complex analogue of `OrbitalReal.exists_iota_eq_of_mulVec_e₀`. -/
@[kb "weil1982" "§3.4 (stabilizer of a vector is O(ξ^⊥)) [unverified]"]
theorem exists_iotaC_eq_of_mulVec_e₀ (hc : c ≠ 0) (g : ArchSOC (splitForm c Q'))
    (hg : ArchSOC.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℂ) = e₀) : ∃ h : ArchSOC Q', iotaC c Q' h = g := by
  have hgi : ArchSOC.mat _ g⁻¹ *ᵥ (e₀ : Fin (m + 1) → ℂ) = e₀ := by
    conv_lhs => rw [← hg]
    rw [mulVec_mulVec, ArchSOC.mat_inv_mul, one_mulVec]
  have e1 := shape_of_mulVec_e₀C hc g hg
  have e2 := shape_of_mulVec_e₀C hc g⁻¹ hgi
  set G' := blockSubC (ArchSOC.mat _ g)
  set Gi' := blockSubC (ArchSOC.mat _ g⁻¹)
  have h1 : G' * Gi' = 1 := by
    have := ArchSOC.mat_mul_inv g
    rw [e1, e2, cornerMat_mul, ← cornerMat_one] at this
    exact cornerMat_injective_right this
  have h2 : Gi' * G' = 1 := by
    have := ArchSOC.mat_inv_mul g
    rw [e1, e2, cornerMat_mul, ← cornerMat_one] at this
    exact cornerMat_injective_right this
  let u : GL (Fin m) ℂ := ⟨G', Gi', h1, h2⟩
  have hmem : u ∈ soC Q' := by
    rw [mem_soC_iff]
    have hiso := ArchSOC.isometry _ g
    have hdet := ArchSOC.det_mat _ g
    rw [e1, gramC_splitForm, cornerMat_transpose, cornerMat_mul, cornerMat_mul] at hiso
    rw [e1, det_cornerMat, one_mul] at hdet
    exact ⟨cornerMat_injective_right hiso, hdet⟩
  refine ⟨ArchSOC.mk _ u hmem, ?_⟩
  apply Subtype.ext; apply Units.ext
  show cornerMat 1 G' = ArchSOC.mat _ g
  exact e1.symm

theorem iotaC_injective : Function.Injective (iotaC c Q') := by
  intro a b h
  have := congrArg (ArchSOC.mat _) h
  rw [mat_iotaC, mat_iotaC] at this
  apply Subtype.ext; apply Units.ext
  exact cornerMat_injective_right this

/-- **`orbC s` is a bijection** $S_c \times SO(Q')(\mathbb C) \to SO(Q)(\mathbb C)$ for every section $s$. -/
theorem orbC_bijective (hc : c ≠ 0) (s : SphSectionC c Q') : Function.Bijective (orbC s) := by
  constructor
  · rintro ⟨x, h⟩ ⟨x', h'⟩ he
    have hx : (x : Fin (m + 1) → ℂ) = x' := by
      have := congrArg (fun g => ArchSOC.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℂ)) he
      simp only [orbC, ArchSOC.mat_mul, ← mulVec_mulVec, iotaC_mulVec_e₀, s.spec] at this
      exact this
    have hx' : x = x' := Subtype.ext hx
    subst hx'
    simp only [orbC, mul_right_inj] at he
    rw [iotaC_injective he]
  · intro g
    have hmem : (splitForm c Q').eval (ArchSOC.mat _ g *ᵥ (e₀ : Fin (m + 1) → ℂ)) = c := eval_mat_e₀ g
    set x : SphC (splitForm c Q') c := ⟨_, hmem⟩
    have hst : ArchSOC.mat _ ((s.toFun x)⁻¹ * g) *ᵥ (e₀ : Fin (m + 1) → ℂ) = e₀ := by
      have h1 := s.spec x
      have h2 : ArchSOC.mat _ (s.toFun x)⁻¹ *ᵥ (x : Fin (m + 1) → ℂ) = e₀ := by
        rw [← h1, mulVec_mulVec, ArchSOC.mat_inv_mul, one_mulVec]
      rw [ArchSOC.mat_mul, ← mulVec_mulVec]; exact h2
    obtain ⟨h, hh⟩ := exists_iotaC_eq_of_mulVec_e₀ hc _ hst
    refine ⟨(x, h), ?_⟩
    simp only [orbC, hh, mul_inv_cancel_left]

end QuadFormsKB.Tamagawa.Measure.OrbitalComplex
