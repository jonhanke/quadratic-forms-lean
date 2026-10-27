import QuadFormsKB.Tamagawa.Measure.Weil.NSArchCayleyR
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchHaar
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchTamagawa

/-!
# The real norm-one quaternions: Haar measure, and the local ratio of $\mathrm{SL}_1\to SO_3$

**Layer:** one real place, $D = \mathbb H[\mathbb R,A,B]$ ($A,B\ne0$, any signs), $S_1 = \{N = 1\}$ (`Sph (normForm A B) 1`) with the
quaternion product, $\sigma$ = `sig (normForm A B) 1`, $Q' = \langle-A,-B,AB\rangle$ (`pureForm A B`), $\mu_{Q'}$ its Leray measure.

* `Sph (normForm A B) 1` is a locally compact second countable group; **`isHaarMeasure_sig`**: $\sigma$ is a left Haar measure
  (left multiplication is the isometry `lmat` of determinant $1$; positivity from the Cayley density, `tendsto_nu_cayBall`).
* **`conjS`**: the conjugation $x\mapsto c_x\in SO(Q')(\mathbb R)$, a continuous homomorphism with kernel $\pm1$ (locally injective).
* **`leray_conjS_image`**: $\mu_{Q'}(c(Y)) = \dfrac{1}{4|A|^3|B|^3}\,\sigma(Y)$ for every measurable $Y\subseteq S_1$ on which $c$ is injective.
  *Proof:* Haar uniqueness along $c$ (`measure_image_eq_smul`), and the constant from the Cayley chart: $c(\mathrm{cayBall}_\delta)$ is
  the chart neighbourhood `ARq A B δ` with $\mu_{Q'}(\mathrm{ARq}_\delta)/\mathrm{vol}(B_\delta)\to1/(8|A|^3|B|^3)$
  (`tendsto_leray_quatBall`), while $\sigma(\mathrm{cayBall}_\delta)/\mathrm{vol}(B_\delta)\to\tfrac12$.
-/

open MeasureTheory Measure Set Filter Topology Metric Matrix
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil.NSArch

open QuadFormsKB.Quat QuadFormsKB.Tamagawa.Measure.Weil SphereLeray QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.Leray

variable {A B : ℝ}

/-! ### The group structure on the sphere -/

instance : Group (Sph (normForm A B) 1) := inferInstanceAs (Group (NormOne ℝ A B))

instance : IsTopologicalGroup (Sph (normForm A B) 1) := inferInstanceAs (IsTopologicalGroup (NormOne ℝ A B))

instance : LocallyCompactSpace (Sph (normForm A B) 1) :=
  (isClosed_sph (normForm A B) 1).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sph_mul_val (x y : Sph (normForm A B) 1) :
    ((x * y : Sph (normForm A B) 1) : Fin 4 → ℝ) = qVec (vecQ (x : Fin 4 → ℝ) * vecQ (y : Fin 4 → ℝ) : ℍ[ℝ,A,B]) :=
  rfl

theorem sph_one_val : ((1 : Sph (normForm A B) 1) : Fin 4 → ℝ) = qVec (1 : ℍ[ℝ,A,B]) := rfl

theorem nrd_sph (x : Sph (normForm A B) 1) : nrd (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]) = 1 := by
  rw [← eval_normForm]; exact x.2

theorem gramMatrixR_normForm : gramMatrixR (normForm A B) = nDiag A B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [gramMatrixR, normForm, nDiag, QuadForm.hessian, QuadForm.diag, Matrix.diagonal] <;> ring

theorem lmat_gram (x : Sph (normForm A B) 1) :
    (lmat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]))ᵀ * gramMatrixR (normForm A B) *
        lmat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]) =
      gramMatrixR (normForm A B) := by
  rw [gramMatrixR_normForm, lmat_isometry, nrd_sph, one_smul]

theorem mul_eq_sphMap (x y : Sph (normForm A B) 1) :
    x * y = sphMap (normForm A B) 1 (lmat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B])) (lmat_gram x) y := by
  apply Subtype.ext
  show qVec (vecQ (x : Fin 4 → ℝ) * vecQ (y : Fin 4 → ℝ) : ℍ[ℝ,A,B]) = lmat _ *ᵥ (y : Fin 4 → ℝ)
  rw [lmat_mulVec]

instance : (sig (normForm A B) 1).IsMulLeftInvariant := by
  refine ⟨fun x => ?_⟩
  have e : (fun y : Sph (normForm A B) 1 => x * y) = sphMap (normForm A B) 1
      (lmat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]))
      (lmat_gram x) := funext (mul_eq_sphMap x)
  rw [e, map_sphMap_sig one_ne_zero, ]
  rw [det_lmat, nrd_sph, one_pow, abs_one]

theorem norm_le_of_isCompact {K : Set (Sph (normForm A B) 1)} (hK : IsCompact K) :
    ∃ R : ℝ, K ⊆ {x | ‖(x : Fin 4 → ℝ)‖ ≤ R} := by
  obtain ⟨R, hR⟩ := (hK.image continuous_subtype_val).isBounded.subset_closedBall 0
  exact ⟨R, fun x hx => by simpa using hR ⟨x, hx, rfl⟩⟩

instance : IsFiniteMeasureOnCompacts (sig (normForm A B) 1) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := norm_le_of_isCompact hK
  refine lt_of_le_of_lt (measure_mono hR) ?_
  rw [sig, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (nu_bounded_lt_top one_ne_zero R)

theorem norm_cay_le {z : Fin 3 → ℝ} (hz : ‖z‖ < radR A B) : ‖cay A B z‖ ≤ 2 := by
  have hp := one_add_qPure_pos hz
  have hz1 : ‖z‖ ≤ 1 := hz.le.trans (radR_le_one A B)
  have hq : (1 : ℝ) / 2 ≤ 1 + qPure A B z := by
    have hc : 0 < 1 + ‖A‖ + ‖B‖ + ‖A * B‖ := by positivity
    have hz2 : ‖z‖ < 1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) := hz.trans_le (min_le_right _ _)
    have hle := norm_qPure_le A B z
    have hsq : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
    have h3 : (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ < 1 / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc (1 + ‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ * 2 = ‖z‖ * (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) := by ring
        _ < 1 / (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) * (2 * (1 + ‖A‖ + ‖B‖ + ‖A * B‖)) :=
            mul_lt_mul_of_pos_right hz2 (by positivity)
        _ = 1 := by field_simp
    have h4 : (‖A‖ + ‖B‖ + ‖A * B‖) * ‖z‖ ^ 2 < 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ ‖A‖ + ‖B‖ + ‖A * B‖)]
    have := (Real.norm_eq_abs _ ▸ hle : |qPure A B z| ≤ _)
    linarith [neg_abs_le (qPure A B z)]
  have hr : (1 + qPure A B z) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
    rw [Real.rpow_neg hp.le, inv_le_comm₀ (Real.rpow_pos_of_pos hp _) (by norm_num)]
    calc (2 : ℝ)⁻¹ ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = Real.sqrt (1 / 4) by
            rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num]
          exact Real.sqrt_le_sqrt (by norm_num)
      _ ≤ (1 + qPure A B z) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hq (by norm_num)
  have hc : ‖(Fin.cons 1 z : Fin 4 → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using (norm_le_pi_norm z i).trans hz1
  rw [cay, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  nlinarith [norm_nonneg (Fin.cons 1 z : Fin 4 → ℝ), Real.rpow_pos_of_pos hp (-(1 / 2 : ℝ))]

theorem cayBall_subset {δ : ℝ} (hδ : δ ≤ radR A B) :
    cayBall A B δ ⊆ {x : Sph (normForm A B) 1 | ‖(x : Fin 4 → ℝ)‖ ≤ 2} := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := (mem_cayBall_iff hδ x).1 hx
  show ‖(x : Fin 4 → ℝ)‖ ≤ 2
  rw [hxz]; exact norm_cay_le (lt_of_lt_of_le (mem_ball_zero_iff.1 hz) hδ)

theorem isCompact_normLe (R : ℝ) : IsCompact {x : Sph (normForm A B) 1 | ‖(x : Fin 4 → ℝ)‖ ≤ R} := by
  have e : {x : Sph (normForm A B) 1 | ‖(x : Fin 4 → ℝ)‖ ≤ R} =
      Subtype.val ⁻¹' closedBall (0 : Fin 4 → ℝ) R := by
    ext x; simp
  rw [e]
  exact (isClosed_sph (normForm A B) 1).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_closedBall _ _)

theorem eventually_nu_cayBall_pos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < (nu (normForm A B) 1 (cayBall A B δ)).toReal := by
  have h := (tendsto_nu_cayBall (A := A) (B := B)).eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  filter_upwards [h, self_mem_nhdsWithin] with δ hδ (hδ0 : 0 < δ)
  have hv : 0 < (volume (ball (0 : Fin 3 → ℝ) δ)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume _ hδ0).ne' measure_ball_lt_top.ne
  have : 1 / 2 * (volume (ball (0 : Fin 3 → ℝ) δ)).toReal < (nu (normForm A B) 1 (cayBall A B δ)).toReal := by
    rwa [lt_div_iff₀ hv] at hδ
  linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hv]

instance : (sig (normForm A B) 1).IsOpenPosMeasure := by
  obtain ⟨δ, hδ, hδr⟩ := ((eventually_nu_cayBall_pos (A := A) (B := B)).and
    (nhdsWithin_le_nhds (Iic_mem_nhds (radR_pos A B)))).exists
  refine isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_normLe (A := A) (B := B) 2) ?_
  intro h0
  have hle := measure_mono_null (cayBall_subset hδr) h0
  rw [sig, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hle
  rcases hle with h | h
  · simp at h
  · rw [h] at hδ; simp at hδ

instance : (sig (normForm A B) 1).IsHaarMeasure := {}

/-! ### Conjugation -/

/-- A point of $S_1$ as a unit. -/
def toUnit (x : Sph (normForm A B) 1) : (ℍ[ℝ,A,B])ˣ where
  val := vecQ (x : Fin 4 → ℝ)
  inv := star (vecQ (x : Fin 4 → ℝ))
  val_inv := by rw [mul_star_eq_nrd, nrd_sph]; rfl
  inv_val := by rw [star_mul_eq_nrd, nrd_sph]; rfl

theorem toUnit_mul (x y : Sph (normForm A B) 1) : toUnit (x * y) = toUnit x * toUnit y := by
  apply Units.ext
  show vecQ (qVec (vecQ (x : Fin 4 → ℝ) * vecQ (y : Fin 4 → ℝ) : ℍ[ℝ,A,B])) = _
  rw [vecQ_qVec]; rfl

theorem toUnit_one : toUnit (1 : Sph (normForm A B) 1) = 1 := by
  apply Units.ext
  show vecQ (qVec (1 : ℍ[ℝ,A,B])) = 1
  rw [vecQ_qVec]

theorem conjGL_mem_soReal (u : (ℍ[ℝ,A,B])ˣ) : conjGL u ∈ soReal (pureForm A B) := by
  rw [mem_soReal_iff]
  have := (mem_SO_iff_hessian (two_ne_zero (α := ℝ))).1 (conjGL_mem u)
  exact ⟨this.2, this.1⟩

/-- **The conjugation $S_1\to SO(\langle-A,-B,AB\rangle)(\mathbb R)$**, $x\mapsto(y\mapsto xyx^{-1})$. -/
def conjS : Sph (normForm A B) 1 →* ArchSO (pureForm A B) where
  toFun x := ⟨conjGL (toUnit x), conjGL_mem_soReal _⟩
  map_one' := by
    apply Subtype.ext
    show conjGL (toUnit 1) = 1
    rw [toUnit_one]; exact congrArg Subtype.val (map_one conjSO)
  map_mul' x y := by
    apply Subtype.ext
    show conjGL (toUnit (x * y)) = conjGL (toUnit x) * conjGL (toUnit y)
    rw [toUnit_mul]; exact congrArg Subtype.val (map_mul conjSO _ _)

theorem mat_conjS (x : Sph (normForm A B) 1) :
    ArchSOInst.mat _ (conjS x) = nMat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]) := by
  change ((conjGL (toUnit x) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = _
  rw [conjGL_val]
  have : nrd (((toUnit x)⁻¹ : (ℍ[ℝ,A,B])ˣ) : ℍ[ℝ,A,B]) = 1 := by
    show nrd (star (vecQ (x : Fin 4 → ℝ))) = 1
    rw [nrd_star, nrd_sph]
  rw [this, one_smul]; rfl

theorem continuous_nMat_vecQ : Continuous fun v : Fin 4 → ℝ => nMat (vecQ v : ℍ[ℝ,A,B]) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [nMat, imv, Quat.pure, vecQ, Pi.single_apply] <;> fun_prop

theorem continuous_conjS : Continuous (conjS (A := A) (B := B)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ x : Sph (normForm A B) 1, ((ArchSO.incl _ (conjS x) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
        nMat (vecQ (x : Fin 4 → ℝ) : ℍ[ℝ,A,B]) := mat_conjS
    exact (continuous_congr e).2 (continuous_nMat_vecQ.comp continuous_subtype_val)
  · have e : ∀ x : Sph (normForm A B) 1, (((ArchSO.incl _ (conjS x) : GL (Fin 3) ℝ))⁻¹ : GL (Fin 3) ℝ).val =
        nMat (vecQ ((x⁻¹ : Sph (normForm A B) 1) : Fin 4 → ℝ) : ℍ[ℝ,A,B]) := fun x => by
      rw [← mat_conjS, map_inv]; rfl
    exact (continuous_congr e).2 (continuous_nMat_vecQ.comp (continuous_subtype_val.comp continuous_inv))

end QuadFormsKB.Tamagawa.Measure.Weil.NSArch

end
