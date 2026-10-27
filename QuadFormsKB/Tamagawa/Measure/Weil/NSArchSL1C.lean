import QuadFormsKB.Tamagawa.Measure.Weil.NSArchCayleyC
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchHaar
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchComplex

/-!
# The complex norm-one quaternions: Haar measure

**Layer:** one complex place, $D = \mathbb H[\mathbb C,A,B]$ ($A,B\ne0$), $S_1 = \{N = 1\}$ (`SphC (normForm A B) 1`) with the
quaternion product, $\sigma = $ `sigC (normForm A B) 1`, $Q' = \langle-A,-B,AB\rangle$ (`pureForm A B`). Complex analogue of `NSArchSL1R.lean`.

* `SphC (normForm A B) 1` is a locally compact second countable group; **`isHaarMeasure_sigC`** (the instance
  `(sigC (normForm A B) 1).IsHaarMeasure`): $\sigma$ is a left Haar measure (left multiplication is the isometry `lmat` of
  determinant $1$; positivity from the Cayley density `tendsto_nuC_cayBallC`).
* **`conjSC`**: the conjugation $x\mapsto c_x\in SO(Q')(\mathbb C)$, a continuous homomorphism (`continuous_conjSC`).
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLerayC QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.Leray

variable {A B : ℂ}

/-! ### The group structure on the sphere -/

instance : Group (SphC (normForm A B) 1) := inferInstanceAs (Group (NormOne ℂ A B))

instance : IsTopologicalGroup (SphC (normForm A B) 1) := inferInstanceAs (IsTopologicalGroup (NormOne ℂ A B))

instance : LocallyCompactSpace (SphC (normForm A B) 1) :=
  (isClosed_sphC (normForm A B) 1).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sphC_mul_val (x y : SphC (normForm A B) 1) :
    ((x * y : SphC (normForm A B) 1) : Fin 4 → ℂ) =
      qVec (vecQ (x : Fin 4 → ℂ) * vecQ (y : Fin 4 → ℂ) : ℍ[ℂ,A,B]) :=
  rfl

theorem sphC_one_val : ((1 : SphC (normForm A B) 1) : Fin 4 → ℂ) = qVec (1 : ℍ[ℂ,A,B]) := rfl

theorem nrd_sphC (x : SphC (normForm A B) 1) : nrd (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]) = 1 := by
  rw [← eval_normForm]; exact x.2

theorem gramC_normForm : gramC (normForm A B) = nDiag A B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gramC, normForm, nDiag, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

theorem lmat_gramC (x : SphC (normForm A B) 1) :
    (lmat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]))ᵀ * gramC (normForm A B) *
        lmat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]) =
      gramC (normForm A B) := by
  rw [gramC_normForm, lmat_isometry, nrd_sphC, one_smul]

theorem mul_eq_sphMapC (x y : SphC (normForm A B) 1) :
    x * y = sphMapC (normForm A B) 1 (lmat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B])) (lmat_gramC x) y := by
  apply Subtype.ext
  show qVec (vecQ (x : Fin 4 → ℂ) * vecQ (y : Fin 4 → ℂ) : ℍ[ℂ,A,B]) = lmat _ *ᵥ (y : Fin 4 → ℂ)
  rw [lmat_mulVec]

instance : (sigC (normForm A B) 1).IsMulLeftInvariant := by
  refine ⟨fun x => ?_⟩
  have e : (fun y : SphC (normForm A B) 1 => x * y) = sphMapC (normForm A B) 1
      (lmat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]))
      (lmat_gramC x) := funext (mul_eq_sphMapC x)
  rw [e, map_sphMapC_sigC one_ne_zero]
  rw [det_lmat, nrd_sphC, one_pow, norm_one]

theorem norm_le_of_isCompactC {K : Set (SphC (normForm A B) 1)} (hK : IsCompact K) :
    ∃ R : ℝ, K ⊆ {x | ‖(x : Fin 4 → ℂ)‖ ≤ R} := by
  obtain ⟨R, hR⟩ := (hK.image continuous_subtype_val).isBounded.subset_closedBall 0
  exact ⟨R, fun x hx => by simpa using hR ⟨x, hx, rfl⟩⟩

instance : IsFiniteMeasureOnCompacts (sigC (normForm A B) 1) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := norm_le_of_isCompactC hK
  refine lt_of_le_of_lt (measure_mono hR) ?_
  rw [sigC, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (nuC_ballS_lt_top one_ne_zero (by norm_num) R)

theorem norm_cayC_le {z : Fin 3 → ℂ} (hz : ‖z‖ < radC A B) : ‖cayC A B z‖ ≤ 2 := by
  have hp := one_add_qPure_ne_zeroC hz
  have hz1 : ‖z‖ ≤ 1 := hz.le.trans (radC_le_one A B)
  have hq : ‖qPure A B z‖ ≤ 1 / 2 := (norm_qPure_lt_one hz).le
  have hb : 1 / 2 ≤ ‖1 + qPure A B z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(qPure A B z))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this
    linarith
  have hbpos : 0 < ‖1 + qPure A B z‖ := by linarith
  have hc2 : ‖(1 + qPure A B z) ^ (-(1 / 2 : ℂ))‖ ^ 2 ≤ 2 := by
    rw [← norm_pow, sq_cpow_neg_half hp, norm_inv]
    calc ‖1 + qPure A B z‖⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) hb
      _ = 2 := by norm_num
  have hc : ‖(1 + qPure A B z) ^ (-(1 / 2 : ℂ))‖ ≤ 2 := by
    nlinarith [norm_nonneg ((1 + qPure A B z) ^ (-(1 / 2 : ℂ)))]
  have hv : ‖(Fin.cons 1 z : Fin 4 → ℂ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using (norm_le_pi_norm z i).trans hz1
  rw [cayC, norm_smul]
  nlinarith [norm_nonneg (Fin.cons 1 z : Fin 4 → ℂ), norm_nonneg ((1 + qPure A B z) ^ (-(1 / 2 : ℂ)))]

theorem cayBallC_subset {δ : ℝ} (hδ : δ ≤ radC A B) :
    cayBallC A B δ ⊆ {x : SphC (normForm A B) 1 | ‖(x : Fin 4 → ℂ)‖ ≤ 2} := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := (mem_cayBallC_iff hδ x).1 hx
  show ‖(x : Fin 4 → ℂ)‖ ≤ 2
  rw [hxz]; exact norm_cayC_le (lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ)

theorem isCompact_normLeC (R : ℝ) : IsCompact {x : SphC (normForm A B) 1 | ‖(x : Fin 4 → ℂ)‖ ≤ R} :=
  isCompact_ballS (Q := normForm A B) (c := 1) R

theorem eventually_nuC_cayBallC_pos :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < (nuC (normForm A B) 1 (cayBallC A B δ)).toReal := by
  have h := (tendsto_nuC_cayBallC (A := A) (B := B)).eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  filter_upwards [h, self_mem_nhdsWithin] with δ hδ (hδ0 : 0 < δ)
  have hv : 0 < (volume (ball (0 : Fin 3 → ℂ) δ)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume _ hδ0).ne' measure_ball_lt_top.ne
  have : 1 / 2 * (volume (ball (0 : Fin 3 → ℂ) δ)).toReal <
      (nuC (normForm A B) 1 (cayBallC A B δ)).toReal := by
    rwa [lt_div_iff₀ hv] at hδ
  linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hv]

instance : (sigC (normForm A B) 1).IsOpenPosMeasure := by
  obtain ⟨δ, hδ, hδr⟩ := ((eventually_nuC_cayBallC_pos (A := A) (B := B)).and
    (nhdsWithin_le_nhds (Iic_mem_nhds (radC_pos A B)))).exists
  refine isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_normLeC (A := A) (B := B) 2) ?_
  intro h0
  have hle := measure_mono_null (cayBallC_subset hδr) h0
  rw [sigC, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hle
  rcases hle with h | h
  · simp at h
  · rw [h] at hδ; simp at hδ

/-- **`isHaarMeasure_sigC`**: $\sigma$ is a left Haar measure on $\mathrm{SL}_1(\mathbb H[\mathbb C,A,B])$. -/
instance isHaarMeasure_sigC : (sigC (normForm A B) 1).IsHaarMeasure := {}

/-! ### Conjugation -/

/-- A point of $S_1$ as a unit. -/
def toUnitC (x : SphC (normForm A B) 1) : (ℍ[ℂ,A,B])ˣ where
  val := vecQ (x : Fin 4 → ℂ)
  inv := star (vecQ (x : Fin 4 → ℂ))
  val_inv := by rw [mul_star_eq_nrd, nrd_sphC]; rfl
  inv_val := by rw [star_mul_eq_nrd, nrd_sphC]; rfl

theorem toUnitC_mul (x y : SphC (normForm A B) 1) : toUnitC (x * y) = toUnitC x * toUnitC y := by
  apply Units.ext
  show vecQ (qVec (vecQ (x : Fin 4 → ℂ) * vecQ (y : Fin 4 → ℂ) : ℍ[ℂ,A,B])) = _
  rw [vecQ_qVec]; rfl

theorem toUnitC_one : toUnitC (1 : SphC (normForm A B) 1) = 1 := by
  apply Units.ext
  show vecQ (qVec (1 : ℍ[ℂ,A,B])) = 1
  rw [vecQ_qVec]

theorem conjGL_mem_soC (u : (ℍ[ℂ,A,B])ˣ) : conjGL u ∈ soC (pureForm A B) := by
  rw [mem_soC_iff, gramC]
  have := (mem_SO_iff_hessian (two_ne_zero (α := ℂ))).1 (conjGL_mem u)
  refine ⟨?_, this.1⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, this.2]

/-- **The conjugation $S_1\to SO(\langle-A,-B,AB\rangle)(\mathbb C)$**, $x\mapsto(y\mapsto xyx^{-1})$. -/
def conjSC : SphC (normForm A B) 1 →* ArchSOC (pureForm A B) where
  toFun x := ArchSOC.mk _ (conjGL (toUnitC x)) (conjGL_mem_soC _)
  map_one' := by
    apply Subtype.ext
    show conjGL (toUnitC 1) = 1
    rw [toUnitC_one]; exact congrArg Subtype.val (map_one conjSO)
  map_mul' x y := by
    apply Subtype.ext
    show conjGL (toUnitC (x * y)) = conjGL (toUnitC x) * conjGL (toUnitC y)
    rw [toUnitC_mul]; exact congrArg Subtype.val (map_mul conjSO _ _)

theorem mat_conjSC (x : SphC (normForm A B) 1) :
    ArchSOC.mat _ (conjSC x) = nMat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]) := by
  change ((conjGL (toUnitC x) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = _
  rw [conjGL_val]
  have : nrd (((toUnitC x)⁻¹ : (ℍ[ℂ,A,B])ˣ) : ℍ[ℂ,A,B]) = 1 := by
    show nrd (star (vecQ (x : Fin 4 → ℂ))) = 1
    rw [nrd_star, nrd_sphC]
  rw [this, one_smul]; rfl

theorem continuous_nMat_vecQC : Continuous fun v : Fin 4 → ℂ => nMat (vecQ v : ℍ[ℂ,A,B]) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nMat, imv, Quat.pure, vecQ, Pi.single_apply] <;> fun_prop

theorem continuous_conjSC : Continuous (conjSC (A := A) (B := B)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ x : SphC (normForm A B) 1, ((ArchSOC.incl _ (conjSC x) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
        nMat (vecQ (x : Fin 4 → ℂ) : ℍ[ℂ,A,B]) := mat_conjSC
    exact (continuous_congr e).2 (continuous_nMat_vecQC.comp continuous_subtype_val)
  · have e : ∀ x : SphC (normForm A B) 1, (((ArchSOC.incl _ (conjSC x) : GL (Fin 3) ℂ))⁻¹ : GL (Fin 3) ℂ).val =
        nMat (vecQ ((x⁻¹ : SphC (normForm A B) 1) : Fin 4 → ℂ) : ℍ[ℂ,A,B]) := fun x => by
      rw [← mat_conjSC, map_inv]; rfl
    exact (continuous_congr e).2 (continuous_nMat_vecQC.comp (continuous_subtype_val.comp continuous_inv))

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
