/-
# Hanke 2005, (2.9) and §4.3 for an arbitrary complex form: transport to the sum of squares

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

For a nondegenerate complex form $Q$ in $n$ variables (Gram matrix $A$), the normal form (2.9) is the sum of squares
(`exists_normalForm_complex`). The conjugation $g\mapsto G^{-1}gG$ identifies $SO(Q)(\mathbb C)$ with $SO_n(\mathbb C)$
(`transC`) and carries the Leray measure to $|\det G|^{2(n+1)} = |\det A|^{-(n+1)}$ times the Leray measure of the
sum of squares (`map_transC`; Lemma 2.2 at the complex places, from `map_lerayMeasureC_conjSOC'`). With
$F_Q = F_{\mathbb C}\circ$`transC` the fibration of `ArchFibrationComplex` transports to $Q$ (`map_FCQ`), and $F_Q$ is
equivariant for the transported action (`FCQ_mul`).
-/
import QuadFormsKB.Literature.Hanke2005.ArchNormalForm
import QuadFormsKB.Literature.Hanke2005.ArchActionComplex
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchComplex

open MeasureTheory Measure Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.LerayComplex

/-- **Normal form data** (Hanke thesis, (2.9)) of a nondegenerate complex form $Q$: the sum of squares
$=\,{}^tG\,Q\,G$ (on Hessians). -/
structure NFDataC {n : ℕ} (Q : QuadForm ℂ n) where
  /-- the change of basis -/
  G : GL (Fin n) ℂ
  /-- the Hessian identity, with $c = 1$ -/
  hH : (sumSqC n).hessian = (1 : ℂ) • ((G : Matrix (Fin n) (Fin n) ℂ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℂ))

/-- The normal form data given by `exists_normalForm_complex`. -/
def NFDataC.ofExists {n : ℕ} (Q : QuadForm ℂ n) (hQ : gramDetC Q ≠ 0) : NFDataC Q :=
  ⟨(exists_normalForm_complex Q hQ).choose, by
    rw [one_smul]; exact (exists_normalForm_complex Q hQ).choose_spec⟩

variable {n : ℕ} {Q : QuadForm ℂ n} (D : NFDataC Q)

/-- **The transport** $SO(Q)(\mathbb C)\cong SO_n(\mathbb C)$, $g\mapsto G^{-1}gG$ (Hanke thesis, (2.9)). -/
def transC : ArchSOC Q ≃ₜ* ArchSOC (sumSqC n) := conjSOC D.G 1 D.hH one_ne_zero

/-- **Lemma 2.2 at a complex place**: the transport carries $\mu_Q$ to $|\det G|^{2(n+1)}\mu_{\mathrm{sumSq}}$. -/
theorem map_transC (hQ : gramDetC Q ≠ 0) :
    (lerayMeasureC Q hQ).map (transC D) =
      ENNReal.ofReal (‖(D.G : Matrix (Fin n) (Fin n) ℂ).det‖ ^ (2 * (n + 1))) •
        lerayMeasureC (sumSqC n) gramDetC_sumSqC_ne_zero := by
  have h1 := map_lerayMeasureC_conjSOC' D.G 1 D.hH one_ne_zero hQ (gramDetC_sumSqC_ne_zero (n := n))
  rw [norm_one, one_pow, one_mul] at h1
  exact h1

/-- $\det(G)^2\det A = 1$, $A$ the Gram matrix of $Q$, so $\|\det G\|^2\|\det A\| = 1$. -/
theorem sq_norm_det_G : ‖(D.G : Matrix (Fin n) (Fin n) ℂ).det‖ ^ 2 * ‖gramDetC Q‖ = 1 := by
  have h := congrArg Matrix.det D.hH
  have hH : Q.hessian = (2 : ℂ) • gramC Q := by
    rw [gramC, smul_smul]; norm_num
  have e : (sumSqC n).hessian = diagonal fun _ : Fin n => 2 * (1 : ℂ) :=
    hessian_diag_field (fun _ : Fin n => (1 : ℂ))
  rw [one_smul, det_mul, det_mul, det_transpose, hH, det_smul, Fintype.card_fin] at h
  rw [e, det_diagonal] at h
  have h2 : (∏ i : Fin n, 2 * (1 : ℂ)) = 2 ^ n := by simp
  rw [h2] at h
  have h3 : (D.G : Matrix (Fin n) (Fin n) ℂ).det ^ 2 * gramDetC Q = 1 := by
    have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    apply mul_left_cancel₀ h2n
    rw [gramDetC]
    linear_combination -h
  have h4 := congrArg norm h3
  rwa [norm_mul, norm_pow, norm_one] at h4

theorem norm_det_G_pow (hQ : gramDetC Q ≠ 0) :
    ‖(D.G : Matrix (Fin n) (Fin n) ℂ).det‖ ^ (2 * (n + 1)) = (‖gramDetC Q‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  set s := ‖(D.G : Matrix (Fin n) (Fin n) ℂ).det‖ with hs
  have hg : 0 < ‖gramDetC Q‖ := norm_pos_iff.mpr hQ
  have h := sq_norm_det_G D
  rw [← hs] at h
  have hs0 : 0 < s := by
    have hne : s ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  have hgn : ‖gramDetC Q‖ = (s ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
  have e : (‖gramDetC Q‖ ^ 2) = (s ^ 4)⁻¹ := by rw [hgn]; field_simp
  rw [e, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
    show -(-((n : ℝ) + 1) / 2) = ((n : ℝ) + 1) / 2 by ring,
    show (s ^ 4 : ℝ) = s ^ (4 : ℝ) by norm_num, ← Real.rpow_mul hs0.le, ← Real.rpow_natCast]
  congr 1; push_cast; ring

/-- Measurability of $F_{\mathbb C}$ on $SO_n(\mathbb C)$. -/
theorem measurable_FCG : Measurable (FCG : ArchSOC (sumSqC n) → LIdx n → ℝ) := by
  have hre : Continuous fun g : ArchSOC (sumSqC n) => reM (ArchSOC.mat _ g) :=
    continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_re.comp ((continuous_apply j).comp ((continuous_apply i).comp (ArchSOC.continuous_mat _)))
  have him : Continuous fun g : ArchSOC (sumSqC n) => -imM (ArchSOC.mat _ g) :=
    (continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_im.comp ((continuous_apply j).comp ((continuous_apply i).comp
        (ArchSOC.continuous_mat _)))).neg
  have hm : Measurable fun g : ArchSOC (sumSqC n) => actC (ArchSOC.mat _ g) 0 := by
    have : (fun g : ArchSOC (sumSqC n) => actC (ArchSOC.mat _ g) 0) =
        fun g => (-imM (ArchSOC.mat _ g)) * (reM (ArchSOC.mat _ g))⁻¹ := by
      funext g; rw [actC_zero]
    rw [this]
    exact measurable_matMul him.measurable (measurable_matInv hre.measurable)
  refine measurable_pi_iff.mpr fun p => ?_
  exact (measurable_pi_apply p.1.2).comp ((measurable_pi_apply p.1.1).comp hm)

/-- **$F_{\mathbb C}$ for $Q$**: $F_Q = F_{\mathbb C}\circ$`transC`. -/
def FCQ (g : ArchSOC Q) : LIdx n → ℝ := FCG (transC D g)

theorem measurable_FCQ : Measurable (FCQ D) := measurable_FCG.comp (transC D).continuous.measurable

/-- **Equivariance of $F_Q$** for the action transported along `transC`: $F_Q(gh) = \mathrm{transC}(g)\cdot F_Q(h)$. -/
theorem FCQ_mul (g h : ArchSOC Q) : FCQ D (g * h) = transC D g • FCQ D h := by
  unfold FCQ
  rw [map_mul, FCG_mul]

/-- **The fibration at a complex place, for an arbitrary nondegenerate form** (Hanke thesis, §4.3 with (2.9) and
Lemma 2.2), conditional on the named statement `ArchFibrationComplex n`:
$(F_Q)_*\big(2^{3n(n-1)/2}\mu_Q\big) = |\det A|^{-(n+1)}\,\mathrm{vol}_C(C_{\mathbb C})\,\omega_Z$. -/
@[kb "hanke2005crelle" "§4.3, pp. 14–15; (2.9), p. 6; Lemma 2.2, p. 6"]
theorem map_FCQ (hC : ArchFibrationComplex n) (hQ : gramDetC Q ≠ 0) :
    (ENNReal.ofReal ((2 : ℝ) ^ (3 * (n * (n - 1) / 2))) • lerayMeasureC Q hQ).map (FCQ D) =
      ENNReal.ofReal ((‖gramDetC Q‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * volCComplex n) • muZC n := by
  have hm : Measurable (transC D : ArchSOC Q → ArchSOC (sumSqC n)) := (transC D).continuous.measurable
  rw [Measure.map_smul _ (measurable_FCQ D).aemeasurable,
    show FCQ D = FCG ∘ (transC D : ArchSOC Q → ArchSOC (sumSqC n)) from rfl,
    ← Measure.map_map measurable_FCG hm, map_transC D hQ, Measure.map_smul _ measurable_FCG.aemeasurable,
    smul_smul]
  have hH := hC.map_eq
  rw [hankeHaarC, Measure.map_smul _ measurable_FCG.aemeasurable] at hH
  rw [mul_comm, ← smul_smul, hH, smul_smul, ← ENNReal.ofReal_mul (by positivity), norm_det_G_pow D hQ]

end QuadFormsKB.Hanke2005.ArchCx
