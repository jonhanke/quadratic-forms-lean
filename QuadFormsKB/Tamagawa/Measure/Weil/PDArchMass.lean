import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The archimedean quotient mass of $\mathbb H_w^\times/\mathbb R^\times$ for a definite quaternion algebra

At a real place $w$ where $D_w = (A,B)_{\mathbb R}$ is definite ($A, B < 0$), Weil's measure on
$PD^\times(\mathbb R) = D_w^\times/\mathbb R^\times$ is the quotient of $\omega_w = \operatorname{nrd}(x)^{-2}dx$ (coordinates
$1,i,j,k$, Lebesgue $dx$) by $dt/|t|$ on $\mathbb R^\times$. Its total mass is computed on the fundamental shell
$\{1 \le \operatorname{nrd} < e^2\}$ for $t \mapsto tx$ (`cArch`):
$$\mathrm{vol}(D_w^\times/\mathbb R^\times) = \frac{\int_{1\le\operatorname{nrd}x<e^2}\operatorname{nrd}(x)^{-2}dx}
  {\int_{1\le|t|<e}|t|^{-1}dt} = \frac{2\pi^2/(AB)}{2} = \frac{\pi^2}{AB}\qquad(\texttt{cArch\_eq}).$$
*Proof:* the diagonal change of variables $x = Ly$, $L = \mathrm{diag}(1, (-A)^{-1/2}, (-B)^{-1/2}, (AB)^{-1/2})$
turns $\operatorname{nrd}$ into $|y|^2$ (Mathlib's `map_linearMap_addHaar_eq_smul_addHaar`, $\det L = 1/(AB)$), and the
polar formula `integral_fun_norm_addHaar` with `EuclideanSpace.volume_ball` ($\mathrm{vol}(B^4) = \pi^2/2$) gives
$\int_{1\le|y|<e}|y|^{-4}dy = 4\cdot\frac{\pi^2}2\int_1^e\frac{dr}r = 2\pi^2$.
-/

open MeasureTheory Real Set

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

/-- The reduced norm of $x_0 + x_1i + x_2j + x_3k \in (A,B)_{\mathbb R}$. -/
def nrdR (A B : ℝ) (x : Fin 4 → ℝ) : ℝ := x 0 ^ 2 - A * x 1 ^ 2 - B * x 2 ^ 2 + A * B * x 3 ^ 2

/-- The fundamental shell $\{1 \le \operatorname{nrd} < e^2\}$ for the scalar action of $\mathbb R_{>0}$. -/
def shellR (A B : ℝ) : Set (Fin 4 → ℝ) := {x | 1 ≤ nrdR A B x ∧ nrdR A B x < Real.exp 2}

/-- The fundamental shell $\{1 \le |t| < e\}$ in $\mathbb R^\times$. -/
def shellT : Set ℝ := {t | 1 ≤ |t| ∧ |t| < Real.exp 1}

/-- **Weil's quotient mass of $D_w^\times/\mathbb R^\times$** at a real place:
$\int_{1\le\operatorname{nrd}<e^2}\operatorname{nrd}^{-2}dx \,/\, \int_{1\le|t|<e}|t|^{-1}dt$. -/
def cArch (A B : ℝ) : ℝ := (∫ x in shellR A B, (nrdR A B x ^ 2)⁻¹) / ∫ t in shellT, |t|⁻¹

theorem measurable_nrdR (A B : ℝ) : Measurable (nrdR A B) := by
  unfold nrdR; fun_prop

theorem measurableSet_shellR (A B : ℝ) : MeasurableSet (shellR A B) :=
  (measurableSet_le measurable_const (measurable_nrdR A B)).inter
    (measurableSet_lt (measurable_nrdR A B) measurable_const)

/-- $\int_{1\le|t|<e}|t|^{-1}dt = 2$. -/
theorem integral_shellT : ∫ t in shellT, |t|⁻¹ = 2 := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hsplit : shellT = Ioc (-Real.exp 1) (-1) ∪ Ico 1 (Real.exp 1) := by
    ext t
    simp only [shellT, mem_ofPred_eq, mem_union, mem_Ioc, mem_Ico]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]; constructor
      · intro h; right; exact h
      · rintro (h | h)
        · linarith [h.2]
        · exact h
    · rw [abs_of_neg ht]; constructor
      · rintro ⟨h1, h2⟩; left; constructor <;> linarith
      · rintro (h | h)
        · constructor <;> linarith [h.1, h.2]
        · linarith [h.1]
  have hdisj : Disjoint (Ioc (-Real.exp 1) (-1)) (Ico 1 (Real.exp 1)) := by
    rw [Set.disjoint_left]; intro t h1 h2; linarith [h1.2, h2.1]
  have hint : ∀ {u w : ℝ}, (0 : ℝ) ∉ Icc u w → IntegrableOn (fun t : ℝ => |t|⁻¹) (Icc u w) := by
    intro u w h0
    refine ContinuousOn.integrableOn_Icc (ContinuousOn.inv₀ continuous_abs.continuousOn fun t ht => ?_)
    rw [abs_ne_zero]; rintro rfl; exact h0 ht
  rw [hsplit, setIntegral_union hdisj measurableSet_Ico
    ((hint (u := -Real.exp 1) (w := -1) (by simp only [mem_Icc, not_and, not_le]; intro; norm_num)).mono_set
      Ioc_subset_Icc_self)
    ((hint (u := 1) (w := Real.exp 1) (by simp only [mem_Icc, not_and, not_le]; intro h; linarith)).mono_set
      Ico_subset_Icc_self)]
  have h1 : ∫ t in Ioc (-Real.exp 1) (-1), |t|⁻¹ = 1 := by
    rw [← intervalIntegral.integral_of_le (by linarith)]
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => -t⁻¹) fun t ht => by
      rw [uIcc_of_le (by linarith)] at ht
      simp only [abs_of_neg (show t < 0 by linarith [ht.2]), inv_neg]]
    rw [intervalIntegral.integral_neg, integral_inv (by
      rw [uIcc_of_le (by linarith)]; simp only [mem_Icc, not_and, not_le]; intro; norm_num)]
    rw [show (-1 : ℝ) / -Real.exp 1 = (Real.exp 1)⁻¹ by field_simp, Real.log_inv, Real.log_exp]; ring
  have h2 : ∫ t in Ico 1 (Real.exp 1), |t|⁻¹ = 1 := by
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le he.le]
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => t⁻¹) fun t ht => by
      rw [uIcc_of_le he.le] at ht
      simp only [abs_of_pos (show 0 < t by linarith [ht.1])]]
    rw [integral_inv_of_pos one_pos (by linarith), div_one, Real.log_exp]
  rw [h1, h2]; norm_num

theorem volume_real_ball_four :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real (Metric.ball 0 1) = π ^ 2 / 2 := by
  rw [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity)]
  rw [show ((4 : ℕ) : ℝ) / 2 + 1 = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  rw [show Real.sqrt π ^ 4 = (Real.sqrt π ^ 2) ^ 2 by ring, Real.sq_sqrt Real.pi_pos.le]
  norm_num [Nat.factorial]

/-- The radial profile $f(r) = r^{-4}$ on $[1, e)$, $0$ elsewhere. -/
def radialF (r : ℝ) : ℝ := if 1 ≤ r ∧ r < Real.exp 1 then (r ^ 4)⁻¹ else 0

/-- $\int_{\mathbb R^4} f(|y|)\,dy = 2\pi^2$ for the profile $f(r) = r^{-4}\mathbf 1_{[1,e)}(r)$. -/
theorem integral_radialF : ∫ z : EuclideanSpace ℝ (Fin 4), radialF ‖z‖ = 2 * π ^ 2 := by
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  rw [integral_fun_norm_addHaar volume radialF, volume_real_ball_four, finrank_euclideanSpace, Fintype.card_fin]
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (4 - 1) • radialF y = 1 := by
    have hcongr : ∀ y ∈ Ioi (0 : ℝ), y ^ (4 - 1) • radialF y = (Ico 1 (Real.exp 1)).indicator (fun t => t⁻¹) y := by
      intro y hy
      simp only [radialF, smul_eq_mul, indicator, mem_Ico]
      split_ifs with h
      · have hy0 : y ≠ 0 := (mem_Ioi.mp hy).ne'
        field_simp
      · simp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_indicator measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico, inter_eq_left.mpr (fun t ht => mem_Ioi.mpr (by linarith [ht.1])),
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le he.le, integral_inv_of_pos one_pos
        (by linarith), div_one, Real.log_exp]
  rw [hI]; simp only [smul_eq_mul, nsmul_eq_mul]; push_cast; ring

/-- **The shell integral:** for $A, B < 0$, $\int_{1\le\operatorname{nrd}x<e^2}\operatorname{nrd}(x)^{-2}dx = 2\pi^2/(AB)$. -/
theorem integral_shellR {A B : ℝ} (hA : A < 0) (hB : B < 0) :
    ∫ x in shellR A B, (nrdR A B x ^ 2)⁻¹ = 2 * π ^ 2 / (A * B) := by
  have hAB : 0 < A * B := mul_pos_of_neg_of_neg hA hB
  set d : Fin 4 → ℝ := ![1, (Real.sqrt (-A))⁻¹, (Real.sqrt (-B))⁻¹, (Real.sqrt (A * B))⁻¹]
  set L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := Matrix.toLin' (Matrix.diagonal d)
  have hsA : Real.sqrt (-A) ^ 2 = -A := Real.sq_sqrt (by linarith)
  have hsB : Real.sqrt (-B) ^ 2 = -B := Real.sq_sqrt (by linarith)
  have hsAB : Real.sqrt (A * B) ^ 2 = A * B := Real.sq_sqrt hAB.le
  have hsA0 : Real.sqrt (-A) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsB0 : Real.sqrt (-B) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsAB0 : Real.sqrt (A * B) ≠ 0 := (Real.sqrt_pos.mpr hAB).ne'
  have hd0 : d 0 = 1 := rfl
  have hd1 : d 1 = (Real.sqrt (-A))⁻¹ := rfl
  have hd2 : d 2 = (Real.sqrt (-B))⁻¹ := rfl
  have hd3 : d 3 = (Real.sqrt (A * B))⁻¹ := rfl
  have hdet : LinearMap.det L = (A * B)⁻¹ := by
    rw [LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_four, hd0, hd1, hd2, hd3, one_mul,
      ← mul_inv, ← mul_inv, ← Real.sqrt_mul (by linarith), show -A * -B = A * B by ring,
      ← pow_two, hsAB]
  have hL : ∀ y, L y = fun i => d i * y i := fun y => by
    funext i; simp [L, Matrix.mulVec_diagonal]
  have hnrd : ∀ y, nrdR A B (L y) = ∑ i, y i ^ 2 := by
    intro y
    have hA0 : A ≠ 0 := hA.ne
    have hB0 : B ≠ 0 := hB.ne
    rw [hL, nrdR, Fin.sum_univ_four]
    simp only [hd0, hd1, hd2, hd3, one_mul, mul_pow, inv_pow, hsA, hsB, hsAB]
    field_simp
    ring
  set g : (Fin 4 → ℝ) → ℝ := (shellR A B).indicator fun x => (nrdR A B x ^ 2)⁻¹
  have hgm : Measurable g :=
    (((measurable_nrdR A B).pow_const 2).inv).indicator (measurableSet_shellR A B)
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact inv_ne_zero hAB.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin 4 → ℝ)) hdet0
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hcomp : ∫ y, g (L y) = (A * B) * ∫ x, g x := by
    rw [← integral_map hLm.aemeasurable hgm.aestronglyMeasurable, hmap, integral_smul_measure, hdet, inv_inv,
      abs_of_pos hAB, ENNReal.toReal_ofReal hAB.le, smul_eq_mul]
  have hrad : ∫ y, g (L y) = ∫ z : EuclideanSpace ℝ (Fin 4), radialF ‖z‖ := by
    rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 4)).integral_comp'
      (fun y => g (L y))]
    congr 1
    funext z
    have hn : ‖z‖ ^ 2 = ∑ i, ((MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm z i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]; rfl
    have hn0 : 0 ≤ ‖z‖ := norm_nonneg z
    have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    simp only [g, indicator, shellR, mem_ofPred_eq, hnrd, ← hn, radialF, he2]
    have h1 : (1 ≤ ‖z‖ ^ 2) ↔ 1 ≤ ‖z‖ := by
      constructor
      · intro h; nlinarith
      · intro h; nlinarith
    have h2 : (‖z‖ ^ 2 < Real.exp 1 ^ 2) ↔ ‖z‖ < Real.exp 1 :=
      pow_lt_pow_iff_left₀ hn0 (Real.exp_pos 1).le two_ne_zero
    by_cases hc : 1 ≤ ‖z‖ ∧ ‖z‖ < Real.exp 1
    · rw [if_pos (⟨h1.mpr hc.1, h2.mpr hc.2⟩ : 1 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < Real.exp 1 ^ 2), if_pos hc]; ring
    · rw [if_neg (fun h : 1 ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < Real.exp 1 ^ 2 => hc ⟨h1.mp h.1, h2.mp h.2⟩), if_neg hc]
  rw [integral_indicator (measurableSet_shellR A B)] at *
  have := hcomp.symm.trans (hrad.trans integral_radialF)
  rw [eq_div_iff hAB.ne', mul_comm]
  exact this

/-- **The archimedean local mass:** $\mathrm{vol}(D_w^\times/\mathbb R^\times) = \pi^2/(AB)$ for $A, B < 0$. -/
theorem cArch_eq {A B : ℝ} (hA : A < 0) (hB : B < 0) : cArch A B = π ^ 2 / (A * B) := by
  rw [cArch, integral_shellR hA hB, integral_shellT]
  ring

end QuadFormsKB.Tamagawa.Measure.Weil
