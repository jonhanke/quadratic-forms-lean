/-
# The archimedean Tamagawa masses of $SO(\langle1,-a,-b,ab\rangle)$ and $SO(\langle-a,-b,ab\rangle)$

**Layer:** a totally real number field $F$, $a, b\in\mathcal O_F$ negative at every real place ($D$ totally definite).

* `archVolSO_four`: $\mathrm{vol}(SO_4(\mathbb R), d) = \pi^4/(64\,d^2\sqrt d)$ (`archVolSO`, $\Gamma(1/2) = \sqrt\pi$,
  $\Gamma(3/2) = \sqrt\pi/2$);
* **`muArchTamSO_qSq_univ_toReal`**: $\mu^{\mathrm{Tam}}_\infty(G_\infty) = c_F(4)\prod_w\pi^4/(64\,\sigma_w(ab)^4|\sigma_w(ab)|)$;
* **`muArchTam_sq_eq`**: $\mu^{(3)}_\infty(G^{(3)}_\infty)^2 = \mu^{(4)}_\infty(G^{(4)}_\infty)\cdot\prod_w|\sigma_w(ab)|^{-3}$.

Source: Weil 1982, §2.2 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqSOLocal
import QuadFormsKB.Tamagawa.Measure.Weil.PDTamagawa

open MeasureTheory Set NumberField NumberField.InfinitePlace
open scoped ENNReal ComplexOrder

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayArch

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

theorem archVolSO_four {d : ℝ} (hd : 0 < d) :
    QuadFormsKB.Tamagawa.archVolSO 4 d = Real.pi ^ 4 / (64 * (d ^ 2 * Real.sqrt d)) := by
  unfold QuadFormsKB.Tamagawa.archVolSO
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num
  have h1 : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have h3 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), h1]; ring
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one, mul_one]
  have hp1 : Real.pi ^ (1 / 2 : ℝ) = Real.sqrt Real.pi := (Real.sqrt_eq_rpow Real.pi).symm
  have hp3 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos, Real.rpow_one, hp1]
  have hd52 : d ^ (-(5 / 2) : ℝ) = (d ^ 2 * Real.sqrt d)⁻¹ := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_neg hd.le, Real.rpow_add hd,
      ← Real.sqrt_eq_rpow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  try rw [hp1]
  try rw [h1]
  try rw [hp3]
  try rw [h3]
  try rw [h2]
  rw [hd52]
  have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsd : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  field_simp
  nlinarith [hsq, Real.pi_pos]

open scoped Classical in
theorem eval_QRe_qSq (w : {w : InfinitePlace F // w.IsReal}) (x : Fin 4 → ℝ) :
    (QRe (qSq a b) w).eval x = x 0 ^ 2 + sigW w (-(a : F)) * x 1 ^ 2 + sigW w (-(b : F)) * x 2 ^ 2 +
      sigW w ((a : F) * b) * x 3 ^ 2 := by
  simp [QRe, QuadForm.eval, QuadForm.evalIn, QuadForm.map, qSq, QuadForm.diag, Matrix.diagonal,
    Fin.sum_univ_four]
  ring

theorem gramDetR_QRe_qSq (w : {w : InfinitePlace F // w.IsReal}) :
    gramDetR (QRe (qSq a b) w) = (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 := by
  rw [gramDetR, QRe, QuadForm.hessian_map, QuadForm.hessian_map, hessian_qSq, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_map (map_zero _), Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, map_mul, map_neg, map_ofNat]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  simp only [map_ofNat]
  ring

section TR

open scoped Classical

variable [IsTotallyReal F]

theorem diag_map' {n : ℕ} (c : Fin n → 𝓞 F) :
    (QuadForm.diag c).map (algebraMap (𝓞 F) F) = QuadForm.diag (fun i => algebraMap (𝓞 F) F (c i)) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- A diagonal form with totally positive coefficients is totally positive definite (totally real $F$). -/
theorem isTotallyPosDef_formF_diag {n : ℕ} (c : Fin n → 𝓞 F) (hc : ∀ i, IsTotallyPos (c i : F)) :
    IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (QuadForm.diag c)) := by
  intro x hx σ
  rw [QuadFormsKB.HilbertModular.formF, diag_map', QuadFormsKB.Tamagawa.eval_diag_gen, map_sum]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
  · by_cases hj : x j = 0
    · rw [hj]; simp
    · rw [map_mul]; exact (mul_pos (hc j σ) (QuadFormsKB.Tamagawa.isTotallyPos_sq_nf hj σ)).le
  · rw [map_mul]; exact mul_pos (hc i σ) (QuadFormsKB.Tamagawa.isTotallyPos_sq_nf hi σ)

theorem hpd_pureFormO (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) :
    IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (QuatZeta.pureFormO a b)) := by
  rw [QuatZeta.pureFormO]
  refine isTotallyPosDef_formF_diag _ fun i => ?_
  fin_cases i
  · simpa using hna
  · simpa using hnb
  · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hna hnb
    simpa [neg_mul_neg] using this

theorem hpd_qSq (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) :
    IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (qSq a b)) := by
  rw [qSq]
  refine isTotallyPosDef_formF_diag _ fun i => ?_
  fin_cases i
  · intro σ; show 0 < σ ((1 : 𝓞 F) : F); simp only [algebraMap.coe_one, map_one]
    exact (zero_lt_one : (0 : ℂ) < 1)
  · simpa using hna
  · simpa using hnb
  · have := QuadFormsKB.Tamagawa.LatChange.isTotallyPos_mul hna hnb
    simpa [neg_mul_neg] using this

/-- **The total Tamagawa mass of $G_\infty$ for $\langle1,-a,-b,ab\rangle$** (definite). -/
theorem muArchTamSO_qSq_univ (hQ : (qSq a b).Nondegenerate)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (qSq a b))) :
    muArchTamSO (qSq a b) hQ Set.univ =
      ENNReal.ofReal (cF F 4) * ∏ w : {w : InfinitePlace F // w.IsReal},
        ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO 4 (gramDetR (QRe (qSq a b) w))) := by
  have : ∀ w, Fact (IsPosDefR (QRe (qSq a b) w)) := fun w => ⟨isPosDefR_QRe (qSq a b) hQ hpd w⟩
  have hC : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe (qSq a b) w) (gramDetR_QRe_ne_zero (qSq a b) hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero (qSq a b) hQ w); infer_instance
  have hsfC : ∀ i : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (LerayComplex.lerayMeasureC (QCx (qSq a b) i) (gramDetC_QCx_ne_zero (qSq a b) hQ i)) :=
    fun i => isEmptyElim i
  rw [muArchTamSO_of_isTotallyReal, Measure.smul_apply, smul_eq_mul, muArchNF, muArchLeray, ← Set.univ_prod_univ,
    Measure.prod_prod, Measure.pi_univ, Measure.pi_univ,
    Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty, mul_one]
  congr 1
  exact Finset.prod_congr rfl fun w _ => lerayMeasure_univ _ (by norm_num)

end TR

end QuadFormsKB.Tamagawa.Measure.Weil
