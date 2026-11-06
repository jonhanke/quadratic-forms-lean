/-
# Hanke 2005, (2.9) and §4.2 for an arbitrary real form: transport to the normal form

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

For a nondegenerate real form $Q$ in $n$ variables (Gram matrix $A$), Hanke's normal form (2.9) is
$Q\cong c\cdot\mathrm{diag}[1_q, -1_r]$, $c = \pm1$, $q = r + t\ge r$, $r$ the Witt index (`exists_normalForm_real`). The
conjugation $g\mapsto G^{-1}gG$ identifies $SO(Q)(\mathbb R)$ with $SO(\varphi_v)$ (`transR`) and carries the Leray measure to
$|\det G|^{n+1} = |\det A|^{-(n+1)/2}$ times the Leray measure of $\varphi_v$ (`map_transR`; this is Lemma 2.2 at the real
places, from `LerayReal.map_lerayMeasure_conjSO'`). With $F_Q = F_{\mathbb R}\circ$`transR` this gives the fibration for $Q$
(`map_FRQ`): $(F_Q)_*\widetilde\omega_{G} = |\det A|^{-(n+1)/2}\mathrm{vol}_C(C_{\mathbb R})\,\omega_Z$, i.e. Hanke's
$\mathrm{vol}_C(C_v)$ for the matrix $\psi$ (`volCAt`).
-/
import QuadFormsKB.Literature.Hanke2005.ArchNormalForm
import QuadFormsKB.Literature.Hanke2005.ArchActionReal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchReal

open MeasureTheory Measure Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal

theorem hessian_phiQn (m r : ℕ) :
    (phiQn m r).hessian = diagonal fun i : Fin m => 2 * (if (i : ℕ) < m - r then (1 : ℝ) else -1) := by
  ext i j
  simp only [phiQn, QuadForm.hessian, QuadForm.diag, Matrix.add_apply, Matrix.transpose_apply, diagonal_apply]
  by_cases h : i = j
  · subst h; simp; split_ifs <;> norm_num
  · simp [h, Ne.symm h]

theorem gramDetR_phiQn_ne_zero (m r : ℕ) : gramDetR (phiQn m r) ≠ 0 := by
  rw [gramDetR, hessian_phiQn, det_diagonal]
  refine div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (by positivity)
  split_ifs <;> norm_num

/-- The identification $SO(\mathrm{diag}[1_{m-r},-1_r]) = SO(\mathrm{diag}[1_{m'-r},-1_r])$ along $m = m'$. -/
def castPhi (r : ℕ) {m m' : ℕ} (h : m = m') : ArchSO (phiQn m r) ≃ₜ* ArchSO (phiQn m' r) := by
  subst h; exact ContinuousMulEquiv.refl _

theorem map_castPhi (r : ℕ) {m m' : ℕ} (h : m = m') :
    (lerayMeasure (phiQn m r) (gramDetR_phiQn_ne_zero m r)).map (castPhi r h) =
      lerayMeasure (phiQn m' r) (gramDetR_phiQn_ne_zero m' r) := by
  subst h
  simp [castPhi]

theorem hessian_phiQ_eq (r t : ℕ) :
    (phiQ r t).hessian = (1 : ℝ) • (((1 : GL (Fin (r + t + r)) ℝ) : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)ᵀ *
      (phiQn (r + t + r) r).hessian * ((1 : GL (Fin (r + t + r)) ℝ) : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)) := by
  rw [one_smul, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one, hessian_phiQn]
  ext i j
  simp only [phiQ, QuadForm.hessian, QuadForm.diag, Matrix.add_apply, Matrix.transpose_apply, diagonal_apply]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have : ((Fin.castAdd r a : Fin (r + t + r)) : ℕ) < r + t + r - r := by simp
      simp [signVec, this]; ring
    · have : ¬ ((Fin.natAdd (r + t) b : Fin (r + t + r)) : ℕ) < r + t + r - r := by simp
      simp [signVec, this]; ring
  · simp [h, Ne.symm h]

/-- $SO(\mathrm{diag}[1_{r+t},-1_r]) \cong SO(\varphi_v)$ (the same form, two presentations). -/
def toPhiQ (r t : ℕ) : ArchSO (phiQn (r + t + r) r) ≃ₜ* ArchSO (phiQ r t) :=
  conjSO 1 1 (hessian_phiQ_eq r t) one_ne_zero

theorem map_toPhiQ (r t : ℕ) :
    (lerayMeasure (phiQn (r + t + r) r) (gramDetR_phiQn_ne_zero _ r)).map (toPhiQ r t) =
      lerayMeasure (phiQ r t) gramDetR_phiQ_ne_zero := by
  rw [toPhiQ, map_lerayMeasure_conjSO' _ _ _ _ _ gramDetR_phiQ_ne_zero]
  simp

/-- **Normal form data** (Hanke thesis, (2.9)) of a nondegenerate real form $Q$: $c\cdot\mathrm{diag}[1_{n-r},-1_r]
= c\cdot{}^tG\,Q\,G$, $c = \pm1$, $r$ the Witt index. -/
structure NFData {n : ℕ} (Q : QuadForm ℝ n) where
  /-- the Witt index -/
  r : ℕ
  /-- the change of basis -/
  G : GL (Fin n) ℝ
  /-- the sign -/
  c : ℝ
  hr : 2 * r ≤ n
  hc : c = 1 ∨ c = -1
  hH : (phiQn n r).hessian = c • ((G : Matrix (Fin n) (Fin n) ℝ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℝ))
  hw : r = QuadraticForm.wittIndex (QuadForm.toQuadraticForm Q)

/-- The normal form data given by `exists_normalForm_real`. -/
def NFData.ofExists {n : ℕ} (Q : QuadForm ℝ n) (hQ : gramDetR Q ≠ 0) : NFData Q :=
  let h := exists_normalForm_real Q hQ
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose, h.choose_spec.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.choose_spec.2.2.1,
    h.choose_spec.choose_spec.choose_spec.2.2.2⟩

variable {n : ℕ} {Q : QuadForm ℝ n} (D : NFData Q)

/-- $t = n - 2r$. -/
def NFData.t : ℕ := n - 2 * D.r

theorem NFData.hn : D.r + D.t + D.r = n := by unfold NFData.t; have := D.hr; omega

theorem NFData.c_ne_zero : D.c ≠ 0 := by rcases D.hc with h | h <;> rw [h] <;> norm_num

theorem NFData.abs_c : |D.c| = 1 := by rcases D.hc with h | h <;> rw [h] <;> norm_num

/-- **The transport** $SO(Q)(\mathbb R)\cong SO(\varphi_v)$, $g\mapsto G^{-1}gG$ (Hanke thesis, (2.9)). -/
def transR : ArchSO Q ≃ₜ* ArchSO (phiQ D.r D.t) :=
  (conjSO D.G D.c D.hH D.c_ne_zero).trans ((castPhi D.r D.hn.symm).trans (toPhiQ D.r D.t))

/-- **Lemma 2.2 at a real place**: the transport carries $\mu_Q$ to $|\det G|^{n+1}\mu_{\varphi_v}$. -/
theorem map_transR (hQ : gramDetR Q ≠ 0) :
    (lerayMeasure Q hQ).map (transR D) =
      ENNReal.ofReal (|(D.G : Matrix (Fin n) (Fin n) ℝ).det| ^ (n + 1)) • lerayMeasure (phiQ D.r D.t) gramDetR_phiQ_ne_zero := by
  have h1 := map_lerayMeasure_conjSO' D.G D.c D.hH D.c_ne_zero hQ (gramDetR_phiQn_ne_zero n D.r)
  rw [D.abs_c, one_pow, one_mul] at h1
  have hm1 : Measurable (conjSO D.G D.c D.hH D.c_ne_zero) := (conjSO D.G D.c D.hH D.c_ne_zero).continuous.measurable
  have hm2 : Measurable (castPhi D.r D.hn.symm) := (castPhi D.r D.hn.symm).continuous.measurable
  have hm3 : Measurable (toPhiQ D.r D.t) := (toPhiQ D.r D.t).continuous.measurable
  rw [transR, ContinuousMulEquiv.coe_trans, ContinuousMulEquiv.coe_trans, ← Measure.map_map (hm3.comp hm2) hm1, h1,
    Measure.map_smul _ (hm3.comp hm2).aemeasurable, ← Measure.map_map hm3 hm2, map_castPhi, map_toPhiQ]

/-- $|\det G|^2\,|\det A| = 1$, $A$ the Gram matrix of $Q$. -/
theorem sq_abs_det_G : |(D.G : Matrix (Fin n) (Fin n) ℝ).det| ^ 2 * |gramDetR Q| = 1 := by
  have h := congrArg Matrix.det D.hH
  rw [det_smul, det_mul, det_mul, det_transpose, hessian_phiQn, det_diagonal, Fintype.card_fin] at h
  have h2 : |∏ i : Fin n, 2 * (if (i : ℕ) < n - D.r then (1 : ℝ) else -1)| = 2 ^ n := by
    have : ∀ i : Fin n, |2 * (if (i : ℕ) < n - D.r then (1 : ℝ) else -1)| = 2 := fun i => by split_ifs <;> norm_num
    rw [Finset.abs_prod, Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h3 := congrArg abs h
  rw [h2, abs_mul, abs_mul, abs_mul, abs_pow, D.abs_c, one_pow, one_mul] at h3
  rw [gramDetR, abs_div, abs_pow, abs_two]
  field_simp
  nlinarith [h3, abs_nonneg (D.G : Matrix (Fin n) (Fin n) ℝ).det]

theorem abs_det_G_pow (hQ : gramDetR Q ≠ 0) :
    |(D.G : Matrix (Fin n) (Fin n) ℝ).det| ^ (n + 1) = |gramDetR Q| ^ (-((n : ℝ) + 1) / 2) := by
  have hpos : 0 < |gramDetR Q| := abs_pos.mpr hQ
  have h := sq_abs_det_G D
  have hG : |(D.G : Matrix (Fin n) (Fin n) ℝ).det| = |gramDetR Q| ^ (-(1 / 2 : ℝ)) := by
    have hG0 : 0 ≤ |(D.G : Matrix (Fin n) (Fin n) ℝ).det| := abs_nonneg _
    have : |(D.G : Matrix (Fin n) (Fin n) ℝ).det| ^ 2 = |gramDetR Q|⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, ← this, Real.sqrt_sq hG0]
  rw [hG, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  congr 1; push_cast; ring

/-- **$F_{\mathbb R}$ for $Q$**: $F_Q = F_{\mathbb R}\circ$`transR`. -/
def FRQ (g : ArchSO Q) : Fin (D.r + D.t) → Fin D.r → ℝ := FRG (transR D g)

theorem measurable_FRQ : Measurable (FRQ D) := measurable_FRG.comp (transR D).continuous.measurable

/-- **The fibration at a real place, for an arbitrary nondegenerate form** (Hanke thesis, §4.2 with (2.9) and
Lemma 2.2): $(F_Q)_*\big(2^{n(n-1)/2}\mu_Q\big) = |\det A|^{-(n+1)/2}\,\mathrm{vol}_C(C_{\mathbb R})\,\omega_Z$. -/
@[kb "hanke2005crelle" "§4.2, pp. 12–13; (2.9), p. 6; Lemma 2.2, p. 6"]
theorem map_FRQ (hQ : gramDetR Q ≠ 0) (hn : 1 ≤ n) :
    (ENNReal.ofReal ((2 : ℝ) ^ (n * (n - 1) / 2)) • lerayMeasure Q hQ).map (FRQ D) =
      ENNReal.ofReal (|gramDetR Q| ^ (-((n : ℝ) + 1) / 2) * volCReal (D.r + D.t) D.r) • muZR D.r D.t := by
  have hm : Measurable (transR D : ArchSO Q → ArchSO (phiQ D.r D.t)) := (transR D).continuous.measurable
  have hrt : 1 ≤ D.r + D.t := by have := D.hn; omega
  rw [Measure.map_smul _ (measurable_FRQ D).aemeasurable,
    show FRQ D = FRG ∘ (transR D : ArchSO Q → ArchSO (phiQ D.r D.t)) from rfl,
    ← Measure.map_map measurable_FRG hm, map_transR D hQ, Measure.map_smul _ measurable_FRG.aemeasurable, smul_smul]
  have hH := map_FR_hankeHaar (r := D.r) (t := D.t) hrt
  have e : (2 : ℝ) ^ ((D.r + D.t + D.r) * (D.r + D.t + D.r - 1) / 2) = 2 ^ (n * (n - 1) / 2) := by rw [D.hn]
  rw [hankeHaarR, Measure.map_smul _ measurable_FRG.aemeasurable, e] at hH
  -- hH : ofReal 2^N • map = ofReal vol • muZR
  rw [mul_comm, ← smul_smul, hH, smul_smul, ← ENNReal.ofReal_mul (by positivity), abs_det_G_pow D hQ]

end QuadFormsKB.Hanke2005.ArchReal
