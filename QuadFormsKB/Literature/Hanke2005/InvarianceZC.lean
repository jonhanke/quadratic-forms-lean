/-
# Hanke 2005, (4.3.9): $\omega_Z$ is $SO_n(\mathbb C)$-invariant

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

For $\alpha = a + bi\in SO_n(\mathbb C)$ and a skew-symmetric $z$ put $\mu_\alpha(z) = a + bz$, $\nu_\alpha(z) = az - b$,
so that $\alpha z = \nu_\alpha(z)\mu_\alpha(z)^{-1}$ (`actC`). Algebraic identities (all for skew $z$ with $\mu_\alpha(z)$
invertible): ${}^t\mu_\alpha(w)(\alpha z-\alpha w)\mu_\alpha(z) = z - w$ (`fdiff`) and
$\delta(\alpha z) = \det\mu_\alpha(z)^{-2}\delta(z)$ (`delta_actC`).
-/
import QuadFormsKB.Literature.Hanke2005.ArchActionComplex
import QuadFormsKB.Literature.Hanke2005.Jacobians

open MeasureTheory Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchCx

open QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {n : ℕ}

/-- $\mu_\alpha(z) = a + bz$ for $\alpha = a + bi$. -/
def muC (α : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  reM α + imM α * z

/-- $\nu_\alpha(z) = az - b$ for $\alpha = a + bi$. -/
def nuC (α : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  reM α * z - imM α

theorem actC_eq (α : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin n) (Fin n) ℝ) :
    actC α z = nuC α z * (muC α z)⁻¹ := rfl

section Algebra

variable {α : Matrix (Fin n) (Fin n) ℂ} {z w : Matrix (Fin n) (Fin n) ℝ}

/-- $\mu^{\mathsf T}\nu = -\nu^{\mathsf T}\mu$ for $\alpha\in SO_n(\mathbb C)$ and skew $z$. -/
theorem muT_nu (hα : α ∈ SOC n) (hz : zᵀ = -z) :
    (muC α z)ᵀ * nuC α z = -((nuC α z)ᵀ * muC α z) := by
  obtain ⟨h1, h2⟩ := soc_re_im hα
  have k2 := key_id2 (reM α) (imM α) z h1 h2 hz
  exact eq_neg_of_add_eq_zero_left k2

/-- $\alpha z$ is skew-symmetric for skew $z$ with $\mu_\alpha(z)$ invertible. -/
theorem actC_skew (hα : α ∈ SOC n) (hz : zᵀ = -z) (hu : IsUnit (muC α z).det) :
    (actC α z)ᵀ = -actC α z := by
  have h3 := muT_nu hα hz
  rw [actC_eq]
  set μ := muC α z
  set ν := nuC α z
  have hIr : μ * μ⁻¹ = 1 := mul_nonsing_inv _ hu
  have hT : (μ⁻¹)ᵀ * μᵀ = 1 := by rw [← transpose_mul, hIr, transpose_one]
  have hνt : νᵀ = -(μᵀ * ν * μ⁻¹) := by
    have h4 : νᵀ * μ = -(μᵀ * ν) := by rw [h3]; simp
    calc νᵀ = νᵀ * (μ * μ⁻¹) := by rw [hIr, mul_one]
      _ = (νᵀ * μ) * μ⁻¹ := by rw [mul_assoc]
      _ = _ := by rw [h4]; simp
  calc (ν * μ⁻¹)ᵀ = (μ⁻¹)ᵀ * νᵀ := transpose_mul _ _
    _ = (μ⁻¹)ᵀ * (-(μᵀ * ν * μ⁻¹)) := by rw [← hνt]
    _ = -(((μ⁻¹)ᵀ * μᵀ) * ν * μ⁻¹) := by noncomm_ring
    _ = -(ν * μ⁻¹) := by rw [hT]; simp

/-- ${}^t\mu_\alpha(z)\,(\alpha z) = -{}^t\nu_\alpha(z)$. -/
theorem muT_actC (hα : α ∈ SOC n) (hz : zᵀ = -z) (hu : IsUnit (muC α z).det) :
    (muC α z)ᵀ * actC α z = -(nuC α z)ᵀ := by
  have h3 := muT_nu hα hz
  rw [actC_eq, ← Matrix.mul_assoc, h3, Matrix.neg_mul, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]

/-- $\alpha z\cdot\mu_\alpha(z) = \nu_\alpha(z)$. -/
theorem actC_mul_mu (hu : IsUnit (muC α z).det) : actC α z * muC α z = nuC α z := by
  rw [actC_eq, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

/-- **Hanke's identity** (thesis, p. 14): ${}^t\mu_\alpha(w)\,(\alpha z - \alpha w)\,\mu_\alpha(z) = z - w$. -/
theorem fdiff_aux (hα : α ∈ SOC n) (hz : zᵀ = -z) (hw : wᵀ = -w) (huz : IsUnit (muC α z).det)
    (huw : IsUnit (muC α w).det) :
    (muC α w)ᵀ * (actC α z - actC α w) * muC α z = z - w := by
  obtain ⟨h1, h2⟩ := soc_re_im hα
  have e1 : (muC α w)ᵀ * (actC α z - actC α w) * muC α z =
      (muC α w)ᵀ * nuC α z + (nuC α w)ᵀ * muC α z := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, actC_mul_mu huz, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (actC α w), muT_actC hα hw huw]
    simp [sub_eq_add_neg]
  rw [e1]
  have e2 : (muC α w)ᵀ * nuC α z + (nuC α w)ᵀ * muC α z =
      ((reM α)ᵀ * reM α - (imM α)ᵀ * imM α) * z - w * ((reM α)ᵀ * reM α - (imM α)ᵀ * imM α)
        - ((reM α)ᵀ * imM α + (imM α)ᵀ * reM α)
        - w * ((imM α)ᵀ * reM α + (reM α)ᵀ * imM α) * z := by
    simp only [muC, nuC, transpose_add, transpose_mul, transpose_sub, hw]
    noncomm_ring
  rw [e2, h1, h2]
  have h2' : (imM α)ᵀ * reM α + (reM α)ᵀ * imM α = 0 := by rw [add_comm]; exact h2
  rw [h2']
  simp

/-- $\alpha z - \alpha w = ({}^t\mu_\alpha(w))^{-1}(z-w)\mu_\alpha(z)^{-1}$ (the differential of the action, in
exact form). -/
theorem fdiff (hα : α ∈ SOC n) (hz : zᵀ = -z) (hw : wᵀ = -w) (huz : IsUnit (muC α z).det)
    (huw : IsUnit (muC α w).det) :
    actC α z - actC α w = ((muC α w)ᵀ)⁻¹ * (z - w) * (muC α z)⁻¹ := by
  have h := fdiff_aux hα hz hw huz huw
  have hdT : IsUnit ((muC α w)ᵀ).det := by rwa [det_transpose]
  have hz' : (muC α z) * (muC α z)⁻¹ = 1 := mul_nonsing_inv _ huz
  have hw' : ((muC α w)ᵀ)⁻¹ * (muC α w)ᵀ = 1 := nonsing_inv_mul _ hdT
  calc actC α z - actC α w
      = ((muC α w)ᵀ)⁻¹ * ((muC α w)ᵀ * (actC α z - actC α w) * muC α z) * (muC α z)⁻¹ := by
        simp only [Matrix.mul_assoc, hz', Matrix.mul_one]
        rw [← Matrix.mul_assoc, hw', Matrix.one_mul]
    _ = _ := by rw [h]

/-- $\delta(\alpha z) = \det\mu_\alpha(z)^{-2}\,\delta(z)$ (Hanke thesis, p. 14). -/
theorem delta_actC (hα : α ∈ SOC n) (hz : zᵀ = -z) (hu : IsUnit (muC α z).det) :
    deltaC (actC α z) = ((muC α z).det)⁻¹ ^ 2 * deltaC z := by
  obtain ⟨h1, h2⟩ := soc_re_im hα
  have k1 := key_id (reM α) (imM α) z h1 h2 hz
  set μ := muC α z with hμ
  set ν := nuC α z with hν
  have k1' : μᵀ * μ = νᵀ * ν + (1 - zᵀ * z) := k1
  have hIr : μ * μ⁻¹ = 1 := mul_nonsing_inv _ hu
  have hT : (μ⁻¹)ᵀ * μᵀ = 1 := by rw [← transpose_mul, hIr, transpose_one]
  have e : (1 : Matrix (Fin n) (Fin n) ℝ) - zᵀ * z = μᵀ * μ - νᵀ * ν := by rw [k1']; abel
  have e2 : (1 : Matrix (Fin n) (Fin n) ℝ) - (ν * μ⁻¹)ᵀ * (ν * μ⁻¹) = (μ⁻¹)ᵀ * (1 - zᵀ * z) * μ⁻¹ := by
    rw [e]
    have : (μ⁻¹)ᵀ * (μᵀ * μ - νᵀ * ν) * μ⁻¹ =
        ((μ⁻¹)ᵀ * μᵀ) * (μ * μ⁻¹) - (μ⁻¹)ᵀ * νᵀ * ν * μ⁻¹ := by noncomm_ring
    rw [this, hT, hIr, transpose_mul]
    noncomm_ring
  unfold deltaC
  rw [actC_eq, e2, det_mul, det_mul, det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  ring

end Algebra

variable {α : Matrix (Fin n) (Fin n) ℂ}

/-! ### The differential of the action -/

/-- $\mathrm{skewOf}$ as a linear map. -/
def skewLin : (LIdx n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := skewOf
  map_add' y z := by
    ext i k
    simp only [skewOf, of_apply, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c y := by
    ext i k
    simp only [skewOf, of_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- $\mathrm{lowerOf}$ as a linear map. -/
def lowerLin : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (LIdx n → ℝ) where
  toFun := lowerOf
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear map $h\mapsto{}^ta\,\mathrm{skew}(h)\,a$ in the coordinates $z_{ik}$, $i>k$. -/
def dAct (a : Matrix (Fin n) (Fin n) ℝ) : (LIdx n → ℝ) →ₗ[ℝ] (LIdx n → ℝ) :=
  lowerLin ∘ₗ ((LinearMap.mulLeft ℝ aᵀ) ∘ₗ (LinearMap.mulRight ℝ a)) ∘ₗ skewLin

theorem dAct_apply (a : Matrix (Fin n) (Fin n) ℝ) (h : LIdx n → ℝ) :
    dAct a h = lowerOf (aᵀ * skewOf h * a) := by
  simp [dAct, lowerLin, skewLin, Matrix.mul_assoc]
  rfl

/-- **Lemma A4 in coordinates**: $\det(h\mapsto{}^ta\,\mathrm{skew}(h)\,a) = \det(a)^{n-1}$. -/
theorem det_dAct (a : Matrix (Fin n) (Fin n) ℝ) : LinearMap.det (dAct a) = a.det ^ (n - 1) := by
  rw [← det_congrSkew a]
  symm
  refine det_eq_of_intertwine (congrSkew a) (LinearEquiv.ofBijective skewCoord skewCoord_bijective)
    (dAct a) ?_
  intro t
  have ht : (t : Matrix (Fin n) (Fin n) ℝ)ᵀ = -(t : Matrix (Fin n) (Fin n) ℝ) := t.2
  have hs : skewOf (skewCoord t : LIdx n → ℝ) = (t : Matrix (Fin n) (Fin n) ℝ) :=
    skewOf_lowerOf ht
  show skewCoord (congrSkew a t) = dAct a (skewCoord t)
  rw [dAct_apply, hs]
  rfl

/-- A bilinear bound: $\|\mathrm{low}(P\,\mathrm{skew}(h)\,E)\|\le C\|h\|\|E\|$. -/
theorem exists_bilinear_bound (P : Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : LIdx n → ℝ) (E : Fin n → Fin n → ℝ),
      ‖lowerOf (P * skewOf h * (Matrix.of E))‖ ≤ C * ‖h‖ * ‖E‖ := by
  let B₀ : (LIdx n → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℝ) →ₗ[ℝ] (LIdx n → ℝ) :=
    LinearMap.mk₂ ℝ (fun h E => lowerOf (P * skewOf h * (Matrix.of E)))
      (fun h h' E => by
        have e : skewOf (h + h') = skewOf h + skewOf h' := skewLin.map_add h h'
        funext p; simp [lowerOf, e, Matrix.mul_add, Matrix.add_mul])
      (fun c h E => by
        have e : skewOf (c • h) = c • skewOf h := skewLin.map_smul c h
        funext p; simp [lowerOf, e])
      (fun h E E' => by
        have e : (Matrix.of (E + E') : Matrix (Fin n) (Fin n) ℝ) = Matrix.of E + Matrix.of E' := rfl
        funext p
        show lowerOf (P * skewOf h * Matrix.of (E + E')) p = (lowerOf (P * skewOf h * Matrix.of E) + lowerOf (P * skewOf h * Matrix.of E')) p
        rw [e, Matrix.mul_add]; rfl)
      (fun c h E => by
        have e : (Matrix.of (c • E) : Matrix (Fin n) (Fin n) ℝ) = c • Matrix.of E := rfl
        funext p
        show lowerOf (P * skewOf h * Matrix.of (c • E)) p = (c • lowerOf (P * skewOf h * Matrix.of E)) p
        rw [e, Matrix.mul_smul]; rfl)
  let B1 : (LIdx n → ℝ) →ₗ[ℝ] ((Fin n → Fin n → ℝ) →L[ℝ] (LIdx n → ℝ)) :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin n → Fin n → ℝ) (F' := LIdx n → ℝ)).toLinearMap ∘ₗ B₀
  let Bcl : (LIdx n → ℝ) →L[ℝ] ((Fin n → Fin n → ℝ) →L[ℝ] (LIdx n → ℝ)) := LinearMap.toContinuousLinearMap B1
  refine ⟨‖Bcl‖, ContinuousLinearMap.opNorm_nonneg _, fun h E => ?_⟩
  have := Bcl.le_opNorm₂ h E
  exact this

/-- $F_\alpha(v) = \alpha\cdot z(v)$ in the coordinates $z_{ik}$ (without the case distinction of `actZC`). -/
def Fa (α : Matrix (Fin n) (Fin n) ℂ) (v : LIdx n → ℝ) : LIdx n → ℝ := lowerOf (actC α (skewOf v))

theorem continuous_muC (α : Matrix (Fin n) (Fin n) ℂ) : Continuous fun v : LIdx n → ℝ => muC α (skewOf v) := by
  unfold muC
  exact continuous_const.add (continuous_const.matrix_mul continuous_skewOf)

theorem continuousAt_muInv (α : Matrix (Fin n) (Fin n) ℂ) {v : LIdx n → ℝ}
    (hu : (muC α (skewOf v)).det ≠ 0) :
    ContinuousAt (fun u : LIdx n → ℝ => (muC α (skewOf u))⁻¹) v := by
  have hc := continuous_muC (n := n) α
  have hdet : ContinuousAt (fun u : LIdx n → ℝ => (muC α (skewOf u)).det) v :=
    (Continuous.matrix_det hc).continuousAt
  have hadj : Continuous fun u : LIdx n → ℝ => (muC α (skewOf u)).adjugate := Continuous.matrix_adjugate hc
  have : (fun u : LIdx n → ℝ => (muC α (skewOf u))⁻¹) =
      fun u => ((muC α (skewOf u)).det)⁻¹ • (muC α (skewOf u)).adjugate := by
    funext u; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (hdet.inv₀ hu).smul hadj.continuousAt

/-- **The differential of the action** (Hanke thesis, p. 14): at $v$ with $\mu_\alpha(z(v))$ invertible,
$d(\alpha z) = {}^t\mu^{-1}\,dz\,\mu^{-1}$ in the coordinates $z_{ik}$, $i>k$. -/
theorem hasFDerivAt_Fa (hα : α ∈ SOC n) {v : LIdx n → ℝ} (hu : IsUnit (muC α (skewOf v)).det) :
    HasFDerivAt (Fa α) (LinearMap.toContinuousLinearMap (dAct ((muC α (skewOf v))⁻¹))) v := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set Mi := (muC α (skewOf v))⁻¹ with hMi
  obtain ⟨C, hC0, hC⟩ := exists_bilinear_bound (Miᵀ)
  have hne : (muC α (skewOf v)).det ≠ 0 := hu.ne_zero
  have hcont : ContinuousAt (fun h : LIdx n → ℝ => (muC α (skewOf (v + h)))⁻¹) 0 := by
    have := continuousAt_muInv α hne
    have h2 : ContinuousAt (fun h : LIdx n → ℝ => v + h) 0 := (continuous_const.add continuous_id).continuousAt
    exact this.comp_of_eq h2 (by simp)
  have hEcont : ContinuousAt (fun h : LIdx n → ℝ => ‖fun i j => ((muC α (skewOf (v + h)))⁻¹ - Mi) i j‖) 0 := by
    refine ContinuousAt.norm ?_
    refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
    exact ((continuousAt_pi.mp (continuousAt_pi.mp hcont i) j).sub continuousAt_const)
  have hE0 : ‖fun i j => ((muC α (skewOf (v + 0)))⁻¹ - Mi) i j‖ = 0 := by
    have : (fun i j => ((muC α (skewOf (v + 0)))⁻¹ - Mi) i j) = 0 := by
      funext i j; simp [hMi]
    rw [this, norm_zero]
  have hsmall : ∀ᶠ h in nhds (0 : LIdx n → ℝ), ‖fun i j => ((muC α (skewOf (v + h)))⁻¹ - Mi) i j‖ < c / (C + 1) :=
    hEcont.eventually_lt continuousAt_const (by rw [hE0]; positivity)
  have hdet : ContinuousAt (fun h : LIdx n → ℝ => (muC α (skewOf (v + h))).det) 0 :=
    (Continuous.matrix_det ((continuous_muC α).comp (continuous_const.add continuous_id))).continuousAt
  have hunit : ∀ᶠ h in nhds (0 : LIdx n → ℝ), (muC α (skewOf (v + h))).det ≠ 0 :=
    hdet.eventually_ne (by simpa using hne)
  filter_upwards [hsmall, hunit] with h hs hd
  have hz : (skewOf (v + h))ᵀ = -skewOf (v + h) := skewOf_transpose _
  have hw : (skewOf v)ᵀ = -skewOf v := skewOf_transpose _
  have hfd := fdiff hα hz hw (isUnit_iff_ne_zero.mpr hd) hu
  have hsk : skewOf (v + h) - skewOf v = skewOf h := by
    have : skewOf (v + h) = skewOf v + skewOf h := skewLin.map_add v h
    rw [this]; abel
  rw [hsk, ← Matrix.transpose_nonsing_inv] at hfd
  have key : Fa α (v + h) - Fa α v - (LinearMap.toContinuousLinearMap (dAct Mi)) h =
      lowerOf (Miᵀ * skewOf h * (Matrix.of fun i j => ((muC α (skewOf (v + h)))⁻¹ - Mi) i j)) := by
    rw [LinearMap.coe_toContinuousLinearMap', dAct_apply]
    funext p
    have := congrFun (congrFun hfd p.1.1) p.1.2
    simp only [Fa, lowerOf, Pi.sub_apply]
    rw [← Matrix.sub_apply, hfd, ← Matrix.sub_apply, ← Matrix.mul_sub]
    rfl
  rw [key]
  refine (hC h _).trans ?_
  have hCn : 0 ≤ C * ‖h‖ := mul_nonneg hC0 (norm_nonneg _)
  calc C * ‖h‖ * ‖fun i j => ((muC α (skewOf (v + h)))⁻¹ - Mi) i j‖
      ≤ C * ‖h‖ * (c / (C + 1)) := by gcongr
    _ ≤ c * ‖h‖ := by
      rw [mul_comm c, mul_assoc]
      have : C * (c / (C + 1)) ≤ c := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
      nlinarith [norm_nonneg h]

/-! ### The invariance -/

theorem real_identity (D δ : ℝ) (hD : D ≠ 0) (hδ : 0 < δ) (m : ℕ) :
    |(D⁻¹) ^ m| * ((D⁻¹ ^ 2 * δ) ^ ((1 - (((m + 1 : ℕ)) : ℝ)) / 2)) =
      δ ^ ((1 - (((m + 1 : ℕ)) : ℝ)) / 2) := by
  have hq : 0 < |D| := abs_pos.mpr hD
  have e1 : D⁻¹ ^ 2 = (|D|⁻¹) ^ 2 := by rw [inv_pow, inv_pow, sq_abs]
  have e2 : |(D⁻¹) ^ m| = (|D|⁻¹) ^ m := by rw [abs_pow, abs_inv]
  have e3 : ((|D|⁻¹) ^ 2) ^ ((1 - (((m + 1 : ℕ)) : ℝ)) / 2) = |D| ^ m := by
    have h0 : (0 : ℝ) ≤ |D|⁻¹ := by positivity
    rw [← Real.rpow_two, ← Real.rpow_mul h0, show (2 : ℝ) * ((1 - (((m + 1 : ℕ)) : ℝ)) / 2) = -(m : ℝ) by
      push_cast; ring, Real.rpow_neg h0, Real.rpow_natCast, inv_pow, inv_inv]
  rw [e1, e2, Real.mul_rpow (by positivity) hδ.le, e3, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hq.ne',
    one_pow, one_mul]

variable (g : ArchSOC (sumSqC n))

theorem skewOf_smul_mem {v : LIdx n → ℝ} (hv : skewOf v ∈ ZC n) : skewOf (g • v) ∈ ZC n := by
  rw [smul_def, skewOf_actZC g hv]; exact (actC_mem (mat_mem_SOC g) hv).2

theorem smul_eq_Fa {v : LIdx n → ℝ} (hv : skewOf v ∈ ZC n) : g • v = Fa (ArchSOC.mat _ g) v := by
  rw [smul_def, actZC_of_mem g hv]; rfl

/-- The derivative of $v\mapsto g\cdot v$ at $v$. -/
def jacSmul (v : LIdx n → ℝ) : (LIdx n → ℝ) →L[ℝ] (LIdx n → ℝ) :=
  LinearMap.toContinuousLinearMap (dAct ((muC (ArchSOC.mat _ g) (skewOf v))⁻¹))

theorem hasFDerivWithinAt_smul {v : LIdx n → ℝ} (hv : skewOf v ∈ ZC n) :
    HasFDerivWithinAt (fun u : LIdx n → ℝ => g • u) (jacSmul g v) (skewOf ⁻¹' ZC n) v :=
  (hasFDerivAt_Fa (mat_mem_SOC g) (actC_mem (mat_mem_SOC g) hv).1).hasFDerivWithinAt.congr
    (fun u hu => smul_eq_Fa g hu) (smul_eq_Fa g hv)

theorem jac_density {m : ℕ} (hn : n = m + 1) {v : LIdx n → ℝ} (hv : skewOf v ∈ ZC n) :
    ENNReal.ofReal |(jacSmul g v).det| * ENNReal.ofReal (deltaC (skewOf (g • v)) ^ ((1 - (n : ℝ)) / 2)) =
      ENNReal.ofReal (deltaC (skewOf v) ^ ((1 - (n : ℝ)) / 2)) := by
  subst hn
  have hα := mat_mem_SOC g
  have hu := (actC_mem hα hv).1
  have hz := skewOf_transpose v
  have hδ : 0 < deltaC (skewOf v) := hv.2.det_pos
  have hdet : (jacSmul g v).det = ((muC (ArchSOC.mat _ g) (skewOf v)).det)⁻¹ ^ m := by
    have : (jacSmul g v).det = LinearMap.det (dAct ((muC (ArchSOC.mat _ g) (skewOf v))⁻¹)) := rfl
    rw [this, det_dAct, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp
  have hd2 : deltaC (skewOf (g • v)) = ((muC (ArchSOC.mat _ g) (skewOf v)).det)⁻¹ ^ 2 * deltaC (skewOf v) := by
    rw [smul_eq_Fa g hv, Fa, skewOf_lowerOf (actC_skew hα hz hu), delta_actC hα hz hu]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), hdet, hd2]
  congr 1
  exact real_identity _ _ hu.ne_zero hδ m

theorem measurable_rhoZC (n : ℕ) :
    Measurable fun v : LIdx n → ℝ => ENNReal.ofReal (deltaC (skewOf v) ^ ((1 - (n : ℝ)) / 2)) := by
  refine ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ _)
  unfold deltaC
  exact (Continuous.matrix_det (continuous_const.sub
    (continuous_skewOf.matrix_transpose.matrix_mul continuous_skewOf))).measurable

/-- **$\omega_Z$ is $SO_n(\mathbb C)$-invariant** (Hanke thesis, (4.3.9), p. 14): Shimura's measure
$\omega_Z = \delta(z)^{(1-n)/2}\bigwedge_{i>k}dz_{ik}$ on $Z_{\mathbb C}$ is invariant under $g\in SO_n(\mathbb C)$.
Proof: the Jacobian of $z\mapsto\alpha z$ in the coordinates $z_{ik}$ is $\det\mu_\alpha(z)^{-(n-1)}$ (Lemma A4,
`det_dAct`) and $\delta(\alpha z) = \det\mu_\alpha(z)^{-2}\delta(z)$ (`delta_actC`); the change of variables formula
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` then gives the claim. -/
@[kb "hanke2005crelle" "(4.3.9), p. 14 (ω_Z is G_C-invariant)"]
theorem map_smul_muZC (g : ArchSOC (sumSqC n)) : (muZC n).map (fun v : LIdx n → ℝ => g • v) = muZC n := by
  cases n with
  | zero =>
    have : IsEmpty (LIdx 0) := ⟨fun p => p.1.1.elim0⟩
    have : (fun v : LIdx 0 → ℝ => g • v) = id := funext fun v => Subsingleton.elim _ _
    rw [this, Measure.map_id]
  | succ m =>
    have hT : Measurable (fun v : LIdx (m + 1) → ℝ => g • v) := measurable_const_smul g
    have hU : MeasurableSet (skewOf ⁻¹' ZC (m + 1) : Set (LIdx (m + 1) → ℝ)) := measurableSet_skewOf_ZC
    have hρ := measurable_rhoZC (m + 1)
    have himg : (fun u : LIdx (m + 1) → ℝ => g • u) '' (skewOf ⁻¹' ZC (m + 1)) = skewOf ⁻¹' ZC (m + 1) := by
      ext w
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact skewOf_smul_mem g hv
      · intro hw
        exact ⟨g⁻¹ • w, skewOf_smul_mem g⁻¹ hw, smul_inv_smul g w⟩
    have hinj : Set.InjOn (fun u : LIdx (m + 1) → ℝ => g • u) (skewOf ⁻¹' ZC (m + 1)) :=
      fun a _ b _ h => MulAction.injective g h
    have key : ∀ φ : (LIdx (m + 1) → ℝ) → ℝ≥0∞, Measurable φ →
        ∫⁻ v, φ (g • v) ∂(muZC (m + 1)) = ∫⁻ v, φ v ∂(muZC (m + 1)) := by
      intro φ hφ
      have hmu : muZC (m + 1) = ((volume : Measure (LIdx (m + 1) → ℝ)).restrict (skewOf ⁻¹' ZC (m + 1))).withDensity
          (fun v => ENNReal.ofReal (deltaC (skewOf v) ^ ((1 - ((m + 1 : ℕ) : ℝ)) / 2))) := rfl
      rw [hmu, lintegral_withDensity_eq_lintegral_mul _ hρ (show Measurable (fun v => φ (g • v)) from hφ.comp hT),
        lintegral_withDensity_eq_lintegral_mul _ hρ hφ]
      simp only [Pi.mul_apply]
      have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure (LIdx (m + 1) → ℝ)))
        hU (fun v hv => hasFDerivWithinAt_smul g hv) hinj
        (fun w => ENNReal.ofReal (deltaC (skewOf w) ^ ((1 - ((m + 1 : ℕ) : ℝ)) / 2)) * φ w)
      rw [himg] at hcv
      rw [hcv]
      refine setLIntegral_congr_fun hU (fun v hv => ?_)
      rw [← mul_assoc, jac_density g rfl hv]
    refine Measure.ext fun B hB => ?_
    rw [Measure.map_apply hT hB, ← lintegral_indicator_one (hT hB), ← lintegral_indicator_one hB]
    have := key (B.indicator 1) (measurable_one.indicator hB)
    rw [← this]
    refine lintegral_congr fun v => ?_
    by_cases h : g • v ∈ B <;> simp [Set.indicator, h]

end QuadFormsKB.Hanke2005.ArchCx
