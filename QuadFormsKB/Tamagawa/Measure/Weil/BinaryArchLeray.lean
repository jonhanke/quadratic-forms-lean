import QuadFormsKB.Tamagawa.Measure.OrbitImage
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchReal
import QuadFormsKB.Tamagawa.BinaryNormOne

/-!
# The Leray measure of $SO(\langle1,D\rangle)(\mathbb R)$ on rotations
**Layer:** one real place. $D\in\mathbb R\setminus0$ of either sign, $Q = \langle1,D\rangle = x_0^2 + Dx_1^2$
(`QuadForm.diag ![1, D]`), $S_1 = \{Q = 1\}$ (`Sph Q 1`), $\sigma_1$ its Leray measure (`sig Q 1`). Every
$u = (u_0,u_1)\in S_1$ is the first column of the rotation $\rho(u) = \begin{pmatrix}u_0&-Du_1\\u_1&u_0\end{pmatrix}\in SO(Q)(\mathbb R)$
(multiplication by $u_0 + u_1\omega$, $\omega^2 = -D$; `BinaryNormOne.rotMat`).

**Proves**
* `lerayMeasure_diag_one_univ`: the Leray measure of the trivial group $SO(\langle c\rangle)(\mathbb R)$ is $1/(2|c|)$, for
  $c$ of either sign (`lerayMeasure_univ` for $c>0$, the similarity $\langle c\rangle\sim\langle-c\rangle$ of
  `map_lerayMeasure_conjSO'` for $c<0$);
* **`lerayMeasure_rotSec_image`**: $\mu_Q(\rho(A)) = \dfrac{1}{4|D|}\,\sigma_1(A)$ for every measurable $A\subseteq S_1$ (the orbital
  identity `lerayMeasure_image_sec` with $Q = \langle1\rangle\perp\langle D\rangle$).
-/

open MeasureTheory Measure Set Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray

/-! ### Rank one -/

section RankOne

theorem hessian_diag_one (c : ℝ) : (QuadForm.diag ![c]).hessian = !![2 * c] := by
  ext i j; fin_cases i; fin_cases j; simp [QuadForm.hessian, QuadForm.diag]; ring

theorem gramDetR_diag_one (c : ℝ) : gramDetR (QuadForm.diag ![c]) = c := by
  rw [gramDetR, hessian_diag_one, Matrix.det_fin_one_of]; ring

theorem gramDetR_diag_one_ne_zero {c : ℝ} (hc : c ≠ 0) : gramDetR (QuadForm.diag ![c]) ≠ 0 := by
  rwa [gramDetR_diag_one]

theorem isPosDefR_diag_one {c : ℝ} (hc : 0 < c) : IsPosDefR (QuadForm.diag ![c]) := by
  intro x hx
  have hx0 : x 0 ≠ 0 := fun h => hx (funext fun i => by fin_cases i; exact h)
  have : (QuadForm.diag ![c]).eval x = c * x 0 ^ 2 := by
    simp [QuadForm.evalIn, QuadForm.diag]; ring
  rw [this]; positivity

/-- $\mathrm{archVolSO}\ 1\ c = 1/(2c)$. -/
theorem archVolSO_one (c : ℝ) : archVolSO 1 c = 1 / (2 * c) := by
  rw [archVolSO]
  simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, zero_add, Nat.cast_one]
  have hg : Real.Gamma (1 / 2) = Real.pi ^ ((1 : ℝ) / 2) := by
    rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow]
  rw [hg, div_self (by positivity), show -((1 : ℝ) + 1) / 2 = -1 by norm_num, Real.rpow_neg_one]
  norm_num
  ring

/-- **The Leray measure of $SO(\langle c\rangle)(\mathbb R) = \{1\}$** is $1/(2|c|)$, for every $c\ne0$. -/
theorem lerayMeasure_diag_one_univ {c : ℝ} (hc : c ≠ 0) :
    lerayMeasure (QuadForm.diag ![c]) (gramDetR_diag_one_ne_zero hc) univ = ENNReal.ofReal (1 / (2 * |c|)) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · -- similarity ⟨c⟩ ↦ ⟨-c⟩ = (-1)·⟨c⟩
    have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
    have hH : (QuadForm.diag ![-c]).hessian = (-1 : ℝ) • (((1 : GL (Fin 1) ℝ) : Matrix (Fin 1) (Fin 1) ℝ)ᵀ *
        (QuadForm.diag ![c]).hessian * ((1 : GL (Fin 1) ℝ) : Matrix (Fin 1) (Fin 1) ℝ)) := by
      rw [hessian_diag_one, hessian_diag_one]
      ext i j; fin_cases i; fin_cases j; simp
    have hmap := map_lerayMeasure_conjSO' (Q := QuadForm.diag ![c]) (Q' := QuadForm.diag ![-c]) 1 (-1) hH
      (by norm_num) (gramDetR_diag_one_ne_zero hc) (gramDetR_diag_one_ne_zero hc')
    have hpd : Fact (IsPosDefR (QuadForm.diag ![-c])) := ⟨isPosDefR_diag_one (by linarith)⟩
    calc lerayMeasure (QuadForm.diag ![c]) (gramDetR_diag_one_ne_zero hc) univ
        = ((lerayMeasure (QuadForm.diag ![c]) (gramDetR_diag_one_ne_zero hc)).map
            (conjSO 1 (-1) hH (by norm_num))) univ := by
          rw [Measure.map_apply (map_continuous (conjSO 1 (-1) hH (by norm_num))).measurable MeasurableSet.univ,
            preimage_univ]
      _ = _ := by
          rw [hmap, Measure.smul_apply, lerayMeasure_univ _ le_rfl, gramDetR_diag_one, archVolSO_one,
            abs_of_neg hneg]
          simp
  · have hpd : Fact (IsPosDefR (QuadForm.diag ![c])) := ⟨isPosDefR_diag_one hpos⟩
    rw [lerayMeasure_univ _ le_rfl, gramDetR_diag_one, archVolSO_one, abs_of_pos hpos]

end RankOne

/-! ### The binary form $\langle1,D\rangle$ and its rotations -/

section Binary

variable {D : ℝ}

theorem diag_one_D_eq_splitForm (D : ℝ) :
    QuadForm.diag ![1, D] = splitForm 1 (QuadForm.diag ![D]) := by
  have h : (QuadForm.diag ![1, D]).coeff = (splitForm (1 : ℝ) (QuadForm.diag ![D])).coeff := by
    rw [splitForm_coeff]
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  cases h' : QuadForm.diag ![1, D]
  cases h'' : splitForm (1 : ℝ) (QuadForm.diag ![D])
  rw [h', h''] at h
  simp only at h
  subst h
  rfl

theorem hessian_diag_one_D (D : ℝ) : (QuadForm.diag ![1, D]).hessian = BinaryNormOne.hessD D := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, QuadForm.diag, BinaryNormOne.hessD] <;> ring

theorem eval_diag_one_D (D : ℝ) (x : Fin 2 → ℝ) : (QuadForm.diag ![1, D]).eval x = x 0 ^ 2 + D * x 1 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two]; ring

theorem gramDetR_diag_one_D (D : ℝ) : gramDetR (QuadForm.diag ![1, D]) = D := by
  rw [gramDetR, hessian_diag_one_D, BinaryNormOne.hessD, Matrix.det_fin_two_of]; ring

theorem gramDetR_diag_one_D_ne_zero (hD : D ≠ 0) : gramDetR (QuadForm.diag ![1, D]) ≠ 0 := by
  rwa [gramDetR_diag_one_D]

theorem norm_one_of_sph (u : Sph (QuadForm.diag ![1, D]) 1) :
    (u : Fin 2 → ℝ) 0 ^ 2 + D * (u : Fin 2 → ℝ) 1 ^ 2 = 1 := by
  have h : (QuadForm.diag ![1, D]).eval (u : Fin 2 → ℝ) = 1 := u.2
  rwa [eval_diag_one_D] at h

/-- The rotation $\rho(u)$ with first column $u\in S_1$, as an element of $GL_2(\mathbb R)$. -/
def rotGLR (D : ℝ) (u : Sph (QuadForm.diag ![1, D]) 1) : GL (Fin 2) ℝ :=
  ⟨BinaryNormOne.rotMat D ((u : Fin 2 → ℝ) 0) ((u : Fin 2 → ℝ) 1) 1,
    BinaryNormOne.rotMatInv D ((u : Fin 2 → ℝ) 0) ((u : Fin 2 → ℝ) 1) 1,
    BinaryNormOne.rotMat_mul_rotMatInv (norm_one_of_sph u) (by norm_num),
    BinaryNormOne.rotMatInv_mul_rotMat (norm_one_of_sph u) (by norm_num)⟩

theorem rotGLR_mem (u : Sph (QuadForm.diag ![1, D]) 1) : rotGLR D u ∈ soReal (QuadForm.diag ![1, D]) := by
  rw [mem_soReal_iff]
  refine ⟨?_, ?_⟩
  · rw [hessian_diag_one_D]
    exact BinaryNormOne.rotMat_isometry (norm_one_of_sph u) (by norm_num)
  · exact BinaryNormOne.det_rotMat (norm_one_of_sph u)

/-- **The rotation section** $S_1\to SO(\langle1,D\rangle)(\mathbb R)$, $u\mapsto\rho(u)$. -/
def rotSec (D : ℝ) (u : Sph (QuadForm.diag ![1, D]) 1) : ArchSO (QuadForm.diag ![1, D]) :=
  ⟨rotGLR D u, rotGLR_mem u⟩

theorem mat_rotSec (u : Sph (QuadForm.diag ![1, D]) 1) :
    ArchSOInst.mat _ (rotSec D u) = BinaryNormOne.rotMat D ((u : Fin 2 → ℝ) 0) ((u : Fin 2 → ℝ) 1) 1 := rfl

theorem continuous_rotSec : Continuous (rotSec D) := by
  have h0 : Continuous fun u : Sph (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℝ) 0 :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun u : Sph (QuadForm.diag ![1, D]) 1 => (u : Fin 2 → ℝ) 1 :=
    (continuous_apply 1).comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · change Continuous fun u : Sph (QuadForm.diag ![1, D]) 1 =>
      BinaryNormOne.rotMat D ((u : Fin 2 → ℝ) 0) ((u : Fin 2 → ℝ) 1) 1
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [BinaryNormOne.rotMat] <;>
      first | exact h0 | exact h1 | exact (continuous_const.mul h1).neg
  · change Continuous fun u : Sph (QuadForm.diag ![1, D]) 1 =>
      BinaryNormOne.rotMatInv D ((u : Fin 2 → ℝ) 0) ((u : Fin 2 → ℝ) 1) 1
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [BinaryNormOne.rotMatInv] <;>
      first | exact h0 | exact h1.neg | exact continuous_const.mul h1

theorem rotSec_spec (u : Sph (QuadForm.diag ![1, D]) 1) :
    ArchSOInst.mat _ (rotSec D u) *ᵥ (e₀ : Fin 2 → ℝ) = (u : Fin 2 → ℝ) := by
  rw [mat_rotSec]
  funext i; fin_cases i <;> simp [BinaryNormOne.rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, e₀]

/-- The embedding $SO(\langle D\rangle)\to SO(\langle1,D\rangle)$, $h\mapsto\mathrm{diag}(1,h)$. -/
def iotaR1 (D : ℝ) (h : ArchSO (QuadForm.diag ![D])) : ArchSO (QuadForm.diag ![1, D]) :=
  ⟨blockGL (ArchSO.incl _ h), by
    rw [diag_one_D_eq_splitForm]; exact OrbitalReal.blockGL_mem_soReal 1 _ h.2⟩

theorem mat_iotaR1 (h : ArchSO (QuadForm.diag ![D])) :
    ArchSOInst.mat _ (iotaR1 D h) = cornerMat 1 (ArchSOInst.mat _ h) := by
  change ((blockGL (ArchSO.incl _ h) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [blockGL_val]; rfl

/-- $SO(\langle D\rangle)(\mathbb R)$ is trivial. -/
theorem archSO_one_eq_one (h : ArchSO (QuadForm.diag ![D])) : ArchSOInst.mat _ h = 1 := by
  have hm := (mem_soReal_iff _ _).1 h.2
  have hdet := hm.2
  rw [Matrix.det_fin_one] at hdet
  ext i j; fin_cases i; fin_cases j
  exact hdet

theorem iotaR1_eq_one (h : ArchSO (QuadForm.diag ![D])) : iotaR1 D h = 1 := by
  apply Subtype.ext; apply Units.ext
  change ArchSOInst.mat _ (iotaR1 D h) = 1
  rw [mat_iotaR1, archSO_one_eq_one, cornerMat_one]

/-- **The Leray measure of the rotations by $A\subseteq S_1$**: $\mu_{\langle1,D\rangle}(\rho(A)) = \sigma_1(A)/(4|D|)$. -/
theorem lerayMeasure_rotSec_image (hD : D ≠ 0) {A : Set (Sph (QuadForm.diag ![1, D]) 1)} (hA : MeasurableSet A) :
    lerayMeasure (QuadForm.diag ![1, D]) (gramDetR_diag_one_D_ne_zero hD) (rotSec D '' A) =
      ENNReal.ofReal (1 / (4 * |D|)) * sig (QuadForm.diag ![1, D]) 1 A := by
  have h := lerayMeasure_image_sec (m := 1) one_ne_zero (gramDetR_diag_one_ne_zero hD) (QuadForm.diag ![1, D])
    (diag_one_D_eq_splitForm D) (gramDetR_diag_one_D_ne_zero hD) (rotSec D) continuous_rotSec.measurable
    rotSec_spec (iotaR1 D) mat_iotaR1 hA MeasurableSet.univ
  have himg : (fun p : Sph (QuadForm.diag ![1, D]) 1 × ArchSO (QuadForm.diag ![D]) => rotSec D p.1 * iotaR1 D p.2) ''
      (A ×ˢ univ) = rotSec D '' A := by
    ext g
    constructor
    · rintro ⟨⟨u, h⟩, ⟨hu, -⟩, rfl⟩
      exact ⟨u, hu, by simp [iotaR1_eq_one]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(u, 1), ⟨hu, mem_univ _⟩, by simp [iotaR1_eq_one]⟩
  rw [himg, lerayMeasure_diag_one_univ hD] at h
  rw [h, mul_comm (sig _ _ A), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [mul_one, pow_one, abs_two]
  field_simp
  ring

theorem isPosDefR_diag_one_D {D : ℝ} (hD : 0 < D) : IsPosDefR (QuadForm.diag ![1, D]) := by
  intro x hx
  rw [eval_diag_one_D]
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := fun h1 => hx (funext fun i => by fin_cases i <;> simp [h0, h1])
    rw [h0]; positivity
  · positivity

/-- **The compact case** $D > 0$: $\mu_{\langle1,D\rangle}(SO(2)) = \pi/(4D^{3/2})$. -/
theorem lerayMeasure_diag_one_D_univ {D : ℝ} (hD : 0 < D) :
    lerayMeasure (QuadForm.diag ![1, D]) (gramDetR_diag_one_D_ne_zero hD.ne') univ =
      ENNReal.ofReal (Real.pi / (4 * D ^ ((3 : ℝ) / 2))) := by
  have : Fact (IsPosDefR (QuadForm.diag ![1, D])) := ⟨isPosDefR_diag_one_D hD⟩
  rw [lerayMeasure_univ _ (by norm_num), gramDetR_diag_one_D]
  congr 1
  rw [archVolSO]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.cast_zero, Nat.cast_one, zero_add]
  have hg : Real.Gamma (1 / 2) = Real.pi ^ ((1 : ℝ) / 2) := by
    rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow]
  have h2 : Real.Gamma ((1 + 1) / 2) = 1 := by norm_num
  rw [hg, h2, div_self (by positivity), show -((2 : ℕ) + (1 : ℝ)) / 2 = -((3 : ℝ) / 2) by norm_num,
    Real.rpow_neg hD.le]
  norm_num
  ring

end Binary

end QuadFormsKB.Tamagawa.Measure.Weil
