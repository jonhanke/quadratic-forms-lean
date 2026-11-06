import QuadFormsKB.Literature.Hanke2005.ArchVolumeReal
import QuadFormsKB.Citation

open MeasureTheory Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.ArchSOMeasure

variable {r t : ℕ}

/-! ### The action of $O(\varphi_v)$ on $Z_{\mathbb R}$ at the level of matrices -/

/-- For ${}^tg\varphi_vg = \varphi_v$: ${}^t(gP(z))\,\varphi_v\,(gP(z)) = -\xi(z)$. -/
theorem gram_mul_frameOf {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (z : Fin (r + t) → Fin r → ℝ) :
    (g * frameOf z 1)ᵀ * phiR r t * (g * frameOf z 1) = -(xiR z) := by
  have h1 : (g * frameOf z 1)ᵀ * phiR r t * (g * frameOf z 1) =
      (frameOf z 1)ᵀ * (gᵀ * phiR r t * g) * frameOf z 1 := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [h1, hg, transpose_frameOf_mul]; simp

theorem negGram_posDef {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) {z : Fin (r + t) → Fin r → ℝ} (hz : z ∈ ZR r t) :
    (-((g * frameOf z 1)ᵀ * phiR r t * (g * frameOf z 1))).PosDef := by
  rw [gram_mul_frameOf hg, neg_neg]; exact hz

/-- $O(\varphi_v)$ preserves $Z_{\mathbb R}$. -/
theorem actR_mem_ZR {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) {z : Fin (r + t) → Fin r → ℝ} (hz : z ∈ ZR r t) :
    actR g z ∈ ZR r t :=
  zOf_mem_ZR (negGram_posDef hg hz)

/-- $gP(z) = P(gz)\,m$ with $m$ invertible. -/
theorem exists_frameOf_actR {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) {z : Fin (r + t) → Fin r → ℝ} (hz : z ∈ ZR r t) :
    ∃ m : Matrix (Fin r) (Fin r) ℝ, IsUnit m.det ∧ g * frameOf z 1 = frameOf (actR g z) 1 * m := by
  have hU : IsUnit (wBlk (g * frameOf z 1) + cBlk (g * frameOf z 1)).det :=
    isUnit_iff_ne_zero.mpr (det_wc_ne_zero (negGram_posDef hg hz))
  have h3 := frameOf_zOf hU
  refine ⟨_, hU, ?_⟩
  rw [← frameOf_eq_mul]; exact h3.symm

/-- $\alpha\mapsto(z\mapsto\alpha z)$ is compatible with products: $(gh)z = g(hz)$ for $h\in O(\varphi_v)$,
$z\in Z_{\mathbb R}$. -/
theorem actR_mul (g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)
    {h : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ} (hh : hᵀ * phiR r t * h = phiR r t)
    {z : Fin (r + t) → Fin r → ℝ} (hz : z ∈ ZR r t) :
    actR (g * h) z = actR g (actR h z) := by
  obtain ⟨m, hm, hmeq⟩ := exists_frameOf_actR hh hz
  show zOf (g * h * frameOf z 1) = zOf (g * frameOf (actR h z) 1)
  rw [Matrix.mul_assoc, hmeq, ← Matrix.mul_assoc, zOf_mul_right _ hm]

theorem actR_one (z : Fin (r + t) → Fin r → ℝ) : actR (1 : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) z = z := by
  rw [actR, Matrix.one_mul]
  exact zOf_frameOf z (m := 1) (by simp)

theorem lastCols_gram_act {β : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hβ : βᵀ * phiR r t * β = phiR r t) :
    (lastCols β)ᵀ * phiR r t * lastCols β = -1 := by
  have h : (lastCols β)ᵀ * phiR r t * lastCols β =
      (βᵀ * phiR r t * β).submatrix (Fin.natAdd (r + t)) (Fin.natAdd (r + t)) := by
    ext i j; simp [lastCols, Matrix.mul_apply]
  rw [h, hβ]
  ext i j
  simp [phiR, diagonal_apply, signVec, one_apply, Fin.natAdd_inj]
  split_ifs <;> simp

/-- $F_{\mathbb R}(\beta)\in Z_{\mathbb R}$ for $\beta\in O(\varphi_v)$. -/
theorem FR_mem_ZR' {β : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hβ : βᵀ * phiR r t * β = phiR r t) : FR β ∈ ZR r t := by
  refine zOf_mem_ZR ?_
  rw [lastCols_gram_act hβ, neg_neg]; exact PosDef.one

/-! ### The action of $SO(\varphi_v)$ on `Fin (r + t) → Fin r → ℝ` -/

theorem orth_mat (g : ArchSO (phiQ r t)) :
    (ArchSOInst.mat _ g)ᵀ * phiR r t * ArchSOInst.mat _ g = phiR r t := by
  have := ArchSOInst.isometry (phiQ r t) g
  rwa [gramMatrixR_phiQ] at this

theorem mat_one' : ArchSOInst.mat (phiQ r t) (1 : ArchSO (phiQ r t)) = 1 := by
  simp [ArchSOInst.mat]

/-- **Hanke's action** (4.2.1)–(4.2.2) of $SO(\varphi_v)$ on $Z_{\mathbb R}$, extended by the identity off
$Z_{\mathbb R}$: $g\cdot z = \mathrm{zOf}(g\,P(z))$ for $z\in Z_{\mathbb R}$ and $g\cdot z = z$ otherwise. -/
@[kb "hanke2005crelle" "(4.2.1)–(4.2.2), p. 11 (the G_R-action on Z_R)"]
def actZR (g : ArchSO (phiQ r t)) (z : Fin (r + t) → Fin r → ℝ) : Fin (r + t) → Fin r → ℝ :=
  open Classical in if z ∈ ZR r t then actR (ArchSOInst.mat _ g) z else z

theorem actZR_of_mem (g : ArchSO (phiQ r t)) {z : Fin (r + t) → Fin r → ℝ} (hz : z ∈ ZR r t) :
    actZR g z = actR (ArchSOInst.mat _ g) z := by
  unfold actZR; rw [if_pos hz]

theorem actZR_of_not_mem (g : ArchSO (phiQ r t)) {z : Fin (r + t) → Fin r → ℝ} (hz : z ∉ ZR r t) :
    actZR g z = z := by
  unfold actZR; rw [if_neg hz]

/-- $SO(\varphi_v)$ preserves $Z_{\mathbb R}$. -/
@[kb "hanke2005crelle" "(4.2.1)–(4.2.2), p. 11 (the G_R-action on Z_R)"]
theorem actZR_mem (g : ArchSO (phiQ r t)) {z : Fin (r + t) → Fin r → ℝ} (hz : z ∈ ZR r t) :
    actZR g z ∈ ZR r t := by
  unfold actZR
  rw [if_pos hz]
  exact actR_mem_ZR (orth_mat g) hz

@[kb "hanke2005crelle" "(4.2.1)–(4.2.2), p. 11 (the G_R-action on Z_R)"]
instance actZRSMul : SMul (ArchSO (phiQ r t)) (Fin (r + t) → Fin r → ℝ) := ⟨actZR⟩

theorem smul_def (g : ArchSO (phiQ r t)) (z : Fin (r + t) → Fin r → ℝ) : g • z = actZR g z := rfl

/-- **$SO(\varphi_v)$ acts on $\mathbb R^{q\times r}$** by Hanke's action on $Z_{\mathbb R}$ (identity outside). -/
@[kb "hanke2005crelle" "(4.2.1)–(4.2.2), p. 11 (the G_R-action on Z_R)"]
instance actZRMulAction : MulAction (ArchSO (phiQ r t)) (Fin (r + t) → Fin r → ℝ) where
  one_smul z := by
    rw [smul_def, actZR]
    by_cases hz : z ∈ ZR r t
    · rw [if_pos hz, mat_one']; exact actR_one z
    · rw [if_neg hz]
  mul_smul g h z := by
    simp only [smul_def]
    by_cases hz : z ∈ ZR r t
    · rw [actZR_of_mem _ hz, actZR_of_mem h hz, actZR_of_mem g (actR_mem_ZR (orth_mat h) hz),
        ArchSOInst.mat_mul]
      exact actR_mul _ (orth_mat h) hz
    · rw [actZR_of_not_mem _ hz, actZR_of_not_mem h hz, actZR_of_not_mem g hz]

/-- $F_{\mathbb R}(g)\in Z_{\mathbb R}$ for $g\in SO(\varphi_v)$. -/
@[kb "hanke2005crelle" "(4.2.3), p. 11 (F_R)"]
theorem FR_mem_ZR_G (g : ArchSO (phiQ r t)) : FRG g ∈ ZR r t :=
  FR_mem_ZR' (orth_mat g)

/-- **Equivariance** $F_{\mathbb R}(gh) = g\,F_{\mathbb R}(h)$ for $g,h\in SO(\varphi_v)$ ((4.2.2)–(4.2.3)). -/
@[kb "hanke2005crelle" "(4.2.2)–(4.2.3), p. 11"]
theorem FRG_mul (g h : ArchSO (phiQ r t)) : FRG (g * h) = g • FRG h := by
  rw [smul_def, actZR_of_mem g (FR_mem_ZR_G h)]
  show FR (ArchSOInst.mat _ (g * h)) = actR (ArchSOInst.mat _ g) (FR (ArchSOInst.mat _ h))
  rw [ArchSOInst.mat_mul]
  exact FR_mul _ (orth_mat h)

theorem measurable_actR_const (A : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) :
    Measurable fun z : Fin (r + t) → Fin r → ℝ => actR A z := by
  have hc : Continuous fun z : Fin (r + t) → Fin r → ℝ => (frameOf z 1 : Matrix (Fin (r + t + r)) (Fin r) ℝ) :=
    by
    have h2 : Continuous fun z : Fin (r + t) → Fin r → ℝ =>
        ((z, (1 : Matrix (Fin r) (Fin r) ℝ)) : (Fin (r + t) → Fin r → ℝ) × Matrix (Fin r) (Fin r) ℝ) :=
      continuous_id.prodMk continuous_const
    have := (continuous_frameOf (r := r) (t := t)).comp h2
    simpa only [Function.comp_def] using this
  exact measurable_zOf.comp (continuous_const.matrix_mul hc).measurable

/-- The maps $z\mapsto g\cdot z$ are measurable. -/
instance : MeasurableConstSMul (ArchSO (phiQ r t)) (Fin (r + t) → Fin r → ℝ) where
  measurable_const_smul g := by
    classical
    have : (fun z : Fin (r + t) → Fin r → ℝ => g • z) =
        fun z => if z ∈ ZR r t then actR (ArchSOInst.mat _ g) z else z := by
      funext z; rw [smul_def, actZR]
    rw [this]
    exact Measurable.ite measurableSet_ZR (measurable_actR_const _) measurable_id

end QuadFormsKB.Hanke2005.ArchReal
