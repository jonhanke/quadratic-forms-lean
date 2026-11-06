/-
# Hanke 2005, §4.2: the change of variables $u = P(z)m$ on frames

Measure-theoretic input for the archimedean volume computation: `lintegral_frames` expresses a Lebesgue integral
over $n\times r$ matrices $u$ (blocks $c, f, w$) in the coordinates $(z, m)$, $u = P(z)m$, $m = w + c$,
$z = \begin{bmatrix}x\\y\end{bmatrix}$ (`frameOf`).

**Proves** (unconditional)
* `measurePreserving_swapPi`: transposition of $\mathbb R^{k\times r}$ is measure preserving;
* `lintegral_pi_affine`: row-wise affine change of variables $z_i\mapsto P_iz_i+b_i$;
* `lintegral_frames`: $\int G(u)\,du = 2^{-r^2}2^{-tr/2}\int_z\int_m|\det m|^{r+t}G(P(z)m)$.
-/
import QuadFormsKB.Literature.Hanke2005.ArchSymmetricReal
import QuadFormsKB.Literature.Hanke2005.ArchMeasAux
import QuadFormsKB.Tamagawa.ArchVolume
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace QuadFormsKB.Hanke2005.ArchReal

/-- Transposition $(x_{ij})\mapsto(x_{ji})$, $\mathbb R^{k\times r}\to\mathbb R^{r\times k}$, preserves Lebesgue
measure (Haar uniqueness, normalised on the unit cube). -/
theorem measurePreserving_swapPi (k r : ℕ) :
    MeasurePreserving (fun (x : Fin k → Fin r → ℝ) (j : Fin r) (i : Fin k) => x i j) volume volume := by
  let e : (Fin k → Fin r → ℝ) ≃+ (Fin r → Fin k → ℝ) :=
    { Equiv.piComm (fun (_ : Fin k) (_ : Fin r) => ℝ) with map_add' := fun _ _ => rfl }
  have hc : Continuous e :=
    continuous_pi fun j => continuous_pi fun i => (continuous_apply j).comp (continuous_apply i)
  have hc' : Continuous e.symm :=
    continuous_pi fun j => continuous_pi fun i => (continuous_apply j).comp (continuous_apply i)
  have hV : ∀ a b : ℕ, (volume : Measure (Fin a → Fin b → ℝ)).IsAddHaarMeasure := fun a b =>
    MeasureTheory.Measure.pi.isAddHaarMeasure (fun _ : Fin a => (volume : Measure (Fin b → ℝ)))
  have := hV k r
  have := hV r k
  have : (Measure.map e (volume : Measure (Fin k → Fin r → ℝ))).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume hc hc'
  have hm : Measurable e := hc.measurable
  refine ⟨hm, ?_⟩
  have h1 := Measure.isAddLeftInvariant_eq_smul (Measure.map e (volume : Measure (Fin k → Fin r → ℝ)))
    (volume : Measure (Fin r → Fin k → ℝ))
  set Q : Set (Fin r → Fin k → ℝ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 with hQ
  have hQ1 : (volume : Measure (Fin r → Fin k → ℝ)) Q = 1 := by
    simp only [hQ, volume_pi, Measure.pi_pi, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      Finset.prod_const_one]
  have hQ2 : (Measure.map e (volume : Measure (Fin k → Fin r → ℝ))) Q = 1 := by
    rw [Measure.map_apply hm (MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
    have : (e ⁻¹' Q) = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1 := by
      ext x
      simp only [hQ, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
      rw [forall_comm]; rfl
    rw [this]
    simp only [volume_pi, Measure.pi_pi, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      Finset.prod_const_one]
  rw [h1] at hQ2
  show Measure.map e (volume : Measure (Fin k → Fin r → ℝ)) = volume
  rw [h1]
  rw [Measure.smul_apply, hQ1] at hQ2
  simp only [ENNReal.smul_def, smul_eq_mul, mul_one] at hQ2
  rw [ENNReal.coe_eq_one.mp hQ2, one_smul]

/-- **Row-wise affine change of variables**: for invertible $P_i$,
$\int H = \prod_i|\det P_i|\int H\big((P_iz_i+b_i)_i\big)\,dz$ on $(\mathbb R^r)^k$. -/
theorem lintegral_pi_affine {k r : ℕ} (P : Fin k → Matrix (Fin r) (Fin r) ℝ) (hP : ∀ i, (P i).det ≠ 0)
    (b : Fin k → Fin r → ℝ) {H : (Fin k → Fin r → ℝ) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ y, H y = ENNReal.ofReal (∏ i, |(P i).det|) *
      ∫⁻ z : Fin k → Fin r → ℝ, H (fun i => P i *ᵥ z i + b i) := by
  have hmeas0 : ∀ i, Measurable fun y : Fin r → ℝ => P i *ᵥ y := fun i =>
    (Matrix.toLin' (P i)).continuous_of_finiteDimensional.measurable
  have hmeas : ∀ i, Measurable fun y : Fin r → ℝ => P i *ᵥ y + b i := fun i => (hmeas0 i).add_const _
  set c : Fin k → NNReal := fun i => Real.toNNReal (|(P i).det|⁻¹) with hc
  have h1 : ∀ i, Measure.map (fun y : Fin r → ℝ => P i *ᵥ y + b i) volume =
      c i • (volume : Measure (Fin r → ℝ)) := by
    intro i
    have hl := Real.map_matrix_volume_pi_eq_smul_volume_pi (hP i)
    rw [abs_inv] at hl
    rw [show (fun y : Fin r → ℝ => P i *ᵥ y + b i) = (fun y => y + b i) ∘ (fun y => P i *ᵥ y) from rfl,
      ← Measure.map_map (measurable_add_const _) (hmeas0 i)]
    have hl' : Measure.map (fun y : Fin r → ℝ => P i *ᵥ y) volume =
        c i • (volume : Measure (Fin r → ℝ)) := by
      rw [ENNReal.smul_def]; exact hl
    rw [hl', Measure.map_smul, map_add_right_eq_self]
    exact (measurable_add_const _).aemeasurable
  have hmap : Measure.map (fun (z : Fin k → Fin r → ℝ) i => P i *ᵥ z i + b i) volume =
      (∏ i, c i) • (volume : Measure (Fin k → Fin r → ℝ)) := by
    rw [volume_pi, Measure.pi_map_pi (hμ := fun i => by rw [h1]; infer_instance)
      (fun i => (hmeas i).aemeasurable)]
    simp only [h1]
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
      ENNReal.ofNNReal_finsetProd]
  have hT : Measurable (fun (z : Fin k → Fin r → ℝ) i => P i *ᵥ z i + b i) :=
    measurable_pi_iff.mpr fun i => (hmeas i).comp (measurable_pi_apply i)
  have hcc : ((∏ i, c i : NNReal) : ℝ≥0∞) = ENNReal.ofReal (∏ i, |(P i).det|⁻¹) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), ENNReal.ofNNReal_finsetProd]; rfl
  have h2 : ∫⁻ z : Fin k → Fin r → ℝ, H (fun i => P i *ᵥ z i + b i) =
      ENNReal.ofReal (∏ i, |(P i).det|⁻¹) * ∫⁻ y, H y := by
    rw [← lintegral_map hH hT, hmap, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul, hcc]
  rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => abs_nonneg _),
    Finset.prod_inv_distrib, mul_inv_cancel₀, ENNReal.ofReal_one, one_mul]
  exact (Finset.prod_pos fun i _ => abs_pos.mpr (hP i)).ne'

section Frames

variable {r t : ℕ}

/-- Row scalars: $-\tfrac12$ on the $x$-rows, $1/\sqrt2$ on the $y$-rows. -/
def frmSgn (r t : ℕ) : Fin (r + t) → ℝ := fun i =>
  Fin.addCases (motive := fun _ => ℝ) (fun _ => -(1 / 2 : ℝ)) (fun _ => (Real.sqrt 2)⁻¹) i

/-- Translation part: $\tfrac12 m$ on the $x$-rows, $0$ on the $y$-rows. -/
def frmShift (m : Matrix (Fin r) (Fin r) ℝ) : Fin (r + t) → Fin r → ℝ := fun i =>
  Fin.addCases (motive := fun _ => Fin r → ℝ) (fun i₁ => fun j => (1 / 2 : ℝ) * m i₁ j) (fun _ => 0) i

/-- The row-wise affine map $z\mapsto (P_i z_i + b_i)_i$ with $P_i = s_i\,{}^tm$ (rows of $[c; f]$). -/
def frmAff (m : Matrix (Fin r) (Fin r) ℝ) (z : Fin (r + t) → Fin r → ℝ) : Fin (r + t) → Fin r → ℝ :=
  fun i => (frmSgn r t i • mᵀ) *ᵥ z i + frmShift m i

/-- The $x$-part $C$ of a column-stacked $[c;f]$ (`a j` = column $j$). -/
def frmC (a : Fin r → Fin (r + t) → ℝ) : Fin r → Fin r → ℝ := fun j i => a j (Fin.castAdd t i)

theorem frmAff_frame (z : Fin (r + t) → Fin r → ℝ) (M : Fin r → Fin r → ℝ) :
    (Matrix.of fun i j => Fin.append (fun i' => frmAff (Matrix.of fun i j => M j i) z i' j)
        ((M - frmC (r := r) (t := t) fun j i' => frmAff (Matrix.of fun i j => M j i) z i' j) j) i :
      Matrix (Fin (r + t + r)) (Fin r) ℝ) = frameOf z (Matrix.of fun i j => M j i) := by
  have hsum : ∀ (c : ℝ) (f g : Fin r → ℝ), ∑ x, c * f x * g x = c * ∑ x, g x * f x := by
    intro c f g; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  ext i j
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun b => ?_) a
    · simp [frameOf, frmAff, frmSgn, frmShift, xBlk, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Matrix.sub_mul, hsum]
      ring
    · simp [frameOf, frmAff, frmSgn, frmShift, yBlk, Matrix.mulVec, dotProduct, Matrix.mul_apply, hsum]
  · simp [frameOf, frmAff, frmSgn, frmShift, frmC, xBlk, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.add_mul, hsum, Matrix.one_apply, mul_add]
    ring

theorem frmSgn_ne_zero (i : Fin (r + t)) : frmSgn r t i ≠ 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simp [frmSgn]
  · simp [frmSgn]

theorem det_frmSgn_smul (m : Matrix (Fin r) (Fin r) ℝ) (i : Fin (r + t)) :
    (frmSgn r t i • mᵀ).det = frmSgn r t i ^ r * m.det := by
  rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]

/-- The Jacobian: $\prod_i|\det(s_i\,{}^tm)| = 2^{-r^2}2^{-tr/2}|\det m|^{r+t}$. -/
theorem prod_det_frmAff (m : Matrix (Fin r) (Fin r) ℝ) :
    ∏ i : Fin (r + t), |(frmSgn r t i • mᵀ).det| =
      (2 : ℝ) ^ (-((r : ℝ) ^ 2)) * (2 : ℝ) ^ (-((t : ℝ) * r) / 2) * |m.det| ^ (r + t) := by
  simp only [det_frmSgn_smul]
  rw [Fin.prod_univ_add]
  simp only [frmSgn, Fin.addCases_left, Fin.addCases_right, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, abs_mul, abs_pow]
  have h1 : (2 : ℝ) ^ (-((r : ℝ) ^ 2)) = (|(-(1 / 2 : ℝ))| ^ r) ^ r := by
    rw [Real.rpow_neg (by norm_num), show ((r : ℝ) ^ 2) = ((r * r : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← pow_mul, one_div, inv_pow]
  have h2 : (2 : ℝ) ^ (-((t : ℝ) * r) / 2) = (|(Real.sqrt 2)⁻¹| ^ r) ^ t := by
    have : (2 : ℝ) ^ (-((t : ℝ) * r) / 2) = ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (t * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
    rw [this, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, abs_of_pos (by positivity), ← pow_mul,
      mul_comm r t]
  rw [h1, h2]
  ring

theorem measurable_frmAppend :
    Measurable (fun p : (Fin r → Fin (r + t) → ℝ) × (Fin r → Fin r → ℝ) =>
      (fun j => Fin.append (p.1 j) (p.2 j) : Fin r → Fin (r + t + r) → ℝ)) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have : (fun p : (Fin r → Fin (r + t) → ℝ) × (Fin r → Fin r → ℝ) => Fin.append (p.1 j) (p.2 j)) =
      fun p => finAppendEquiv (r + t) r ℝ (p.1 j, p.2 j) := by
    funext p; rw [finAppendEquiv_apply]
  rw [this]
  exact (finAppendEquiv _ _ _).measurable.comp
    (((measurable_pi_apply j).comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd))

theorem measurable_frmC : Measurable (frmC : (Fin r → Fin (r + t) → ℝ) → Fin r → Fin r → ℝ) :=
  measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun _ =>
    (measurable_pi_apply _).comp (measurable_pi_apply j)

theorem measurable_frmTrans {n : ℕ} : Measurable (fun X2 : Fin r → Fin n → ℝ =>
    (Matrix.of fun i j => X2 j i : Matrix (Fin n) (Fin r) ℝ)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply i).comp (measurable_pi_apply j)

theorem continuous_frameOf :
    Continuous (fun p : (Fin (r + t) → Fin r → ℝ) × Matrix (Fin r) (Fin r) ℝ => frameOf p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (fun a₁ => ?_) (fun b => ?_) a
    · simp only [frameOf, Matrix.of_apply, Fin.addCases_left, xBlk, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
      fun_prop
    · simp only [frameOf, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, yBlk, Matrix.smul_apply,
        Matrix.mul_apply, smul_eq_mul]
      fun_prop
  · simp only [frameOf, Matrix.of_apply, Fin.addCases_right, xBlk, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    fun_prop

theorem wBlk_add_cBlk_frmAppend (a : Fin r → Fin (r + t) → ℝ) (M : Fin r → Fin r → ℝ) :
    wBlk (Matrix.of fun i j => Fin.append (a j) ((M - frmC a) j) i : Matrix (Fin (r + t + r)) (Fin r) ℝ) +
      cBlk (Matrix.of fun i j => Fin.append (a j) ((M - frmC a) j) i : Matrix (Fin (r + t + r)) (Fin r) ℝ) =
      Matrix.of fun i j => M j i := by
  ext i j
  simp [wBlk, cBlk, frmC]

/-- The inner integral over the $[c;f]$-columns $a$ for fixed $w + c = m$ (columns `M j`). -/
theorem lintegral_frames_fixed {G : Matrix (Fin (r + t + r)) (Fin r) ℝ → ℝ≥0∞} (hG : Measurable G)
    (hG0 : ∀ u, (wBlk u + cBlk u).det = 0 → G u = 0) (M : Fin r → Fin r → ℝ) :
    ∫⁻ a : Fin r → Fin (r + t) → ℝ, G (Matrix.of fun i j => Fin.append (a j) ((M - frmC a) j) i) =
      ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) ^ 2)) * (2 : ℝ) ^ (-((t : ℝ) * r) / 2)) *
        ∫⁻ z : Fin (r + t) → Fin r → ℝ, ENNReal.ofReal (|(Matrix.of fun i j => M j i).det| ^ (r + t)) *
          G (frameOf z (Matrix.of fun i j => M j i)) := by
  set m : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => M j i with hm
  by_cases hd : m.det = 0
  · have h1 : ∀ a : Fin r → Fin (r + t) → ℝ,
        G (Matrix.of fun i j => Fin.append (a j) ((M - frmC a) j) i) = 0 := fun a =>
      hG0 _ (by rw [wBlk_add_cBlk_frmAppend]; exact hd)
    have h2 : ∀ z : Fin (r + t) → Fin r → ℝ, G (frameOf z m) = 0 := fun z =>
      hG0 _ (by rw [wBlk_add_cBlk_frameOf]; exact hd)
    simp only [h1, h2, mul_zero, lintegral_zero]
  · have hP : ∀ i : Fin (r + t), (frmSgn r t i • mᵀ).det ≠ 0 := fun i => by
      rw [det_frmSgn_smul]; exact mul_ne_zero (pow_ne_zero _ (frmSgn_ne_zero i)) hd
    have hΨ : Measurable fun a : Fin r → Fin (r + t) → ℝ =>
        G (Matrix.of fun i j => Fin.append (a j) ((M - frmC a) j) i) := by
      refine hG.comp ?_
      have : Measurable fun a : Fin r → Fin (r + t) → ℝ =>
          (fun j => Fin.append (a j) ((M - frmC a) j) : Fin r → Fin (r + t + r) → ℝ) :=
        measurable_frmAppend.comp (measurable_id.prodMk (measurable_const.sub measurable_frmC))
      exact measurable_frmTrans.comp this
    have hτ := measurePreserving_swapPi (r + t) r
    set Ψ : (Fin r → Fin (r + t) → ℝ) → ℝ≥0∞ :=
      fun a => G (Matrix.of fun i j => Fin.append (a j) ((M - frmC a) j) i) with hΨdef
    have e1 : ∫⁻ a, Ψ a = ∫⁻ y : Fin (r + t) → Fin r → ℝ, Ψ (fun j i => y i j) :=
      (hτ.lintegral_comp hΨ).symm
    have e2 := lintegral_pi_affine (fun i => frmSgn r t i • mᵀ) hP (frmShift m)
      (H := fun y : Fin (r + t) → Fin r → ℝ => Ψ (fun j i => y i j)) (hΨ.comp hτ.measurable)
    have h3 : ∀ z : Fin (r + t) → Fin r → ℝ,
        Ψ (fun j i => ((fun i => (frmSgn r t i • mᵀ) *ᵥ z i + frmShift m i) :
          Fin (r + t) → Fin r → ℝ) i j) = G (frameOf z m) := fun z => congrArg G (frmAff_frame z M)
    rw [e1, e2, lintegral_congr h3]
    have h4 : ∏ i : Fin (r + t), |(frmSgn r t i • mᵀ).det| =
        (2 : ℝ) ^ (-((r : ℝ) ^ 2)) * (2 : ℝ) ^ (-((t : ℝ) * r) / 2) * |m.det| ^ (r + t) :=
      prod_det_frmAff m
    rw [h4, ENNReal.ofReal_mul (by positivity), mul_assoc,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem measurable_frmTransSq : Measurable fun p : (Fin r → Fin r → ℝ) × (Fin (r + t) → Fin r → ℝ) =>
    (Matrix.of fun i j => p.1 j i : Matrix (Fin r) (Fin r) ℝ) := measurable_frmTrans.comp measurable_fst

theorem measurable_frmDet : Measurable fun p : (Fin r → Fin r → ℝ) × (Fin (r + t) → Fin r → ℝ) =>
    ENNReal.ofReal (|(Matrix.of fun i j => p.1 j i : Matrix (Fin r) (Fin r) ℝ).det| ^ (r + t)) :=
  ENNReal.measurable_ofReal.comp (Measurable.pow_const
    ((Continuous.matrix_det continuous_id).measurable.comp (measurable_frmTransSq (r := r) (t := t))).abs _)

theorem measurable_frmFrame : Measurable fun p : (Fin r → Fin r → ℝ) × (Fin (r + t) → Fin r → ℝ) =>
    (frameOf p.2 (Matrix.of fun i j => p.1 j i) : Matrix (Fin (r + t + r)) (Fin r) ℝ) := by
  have hc : Continuous fun p : (Fin r → Fin r → ℝ) × (Fin (r + t) → Fin r → ℝ) =>
      (Matrix.of fun i j => p.1 j i : Matrix (Fin r) (Fin r) ℝ) :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply i).comp ((continuous_apply j).comp continuous_fst)
  have hc2 : Continuous fun p : (Fin r → Fin r → ℝ) × (Fin (r + t) → Fin r → ℝ) =>
      (p.2, (Matrix.of fun i j => p.1 j i : Matrix (Fin r) (Fin r) ℝ)) := continuous_snd.prodMk hc
  exact (continuous_frameOf.comp hc2).measurable

theorem measurable_frmAppendA {G : Matrix (Fin (r + t + r)) (Fin r) ℝ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun p : (Fin r → Fin r → ℝ) × (Fin r → Fin (r + t) → ℝ) =>
      G (Matrix.of fun i j => Fin.append (p.2 j) (p.1 j) i)) := by
  have : Measurable fun p : (Fin r → Fin r → ℝ) × (Fin r → Fin (r + t) → ℝ) =>
      (fun j => Fin.append (p.2 j) (p.1 j) : Fin r → Fin (r + t + r) → ℝ) :=
    measurable_frmAppend.comp measurable_swap
  exact hG.comp (measurable_frmTrans.comp this)

theorem measurable_frmAppendB {G : Matrix (Fin (r + t + r)) (Fin r) ℝ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun p : (Fin r → Fin (r + t) → ℝ) × (Fin r → Fin r → ℝ) =>
      G (Matrix.of fun i j => Fin.append (p.1 j) ((p.2 - frmC p.1) j) i)) := by
  have : Measurable fun p : (Fin r → Fin (r + t) → ℝ) × (Fin r → Fin r → ℝ) =>
      (fun j => Fin.append (p.1 j) ((p.2 - frmC p.1) j) : Fin r → Fin (r + t + r) → ℝ) :=
    measurable_frmAppend.comp
      (measurable_fst.prodMk (measurable_snd.sub (measurable_frmC.comp measurable_fst)))
  exact hG.comp (measurable_frmTrans.comp this)

end Frames

/-- **Frames in the coordinates $(z, m)$** (Hanke 2005, §4.2): writing a frame as $u = P(z)m$ with
$P(z)=\begin{bmatrix}(1-x)/2\\ y/\sqrt2\\ (1+x)/2\end{bmatrix}$ (`frameOf z m`), Lebesgue measure on
$\mathbb R^{n\times r}$ ($n = r+t+r$; `X2 j` is column $j$ of $u$) becomes
$2^{-r^2}2^{-tr/2}\,|\det m|^{r+t}\,dz\,dm$, for $G$ vanishing where $\det(w+c)=0$. -/
theorem lintegral_frames {r t : ℕ} {G : Matrix (Fin (r + t + r)) (Fin r) ℝ → ℝ≥0∞} (hG : Measurable G)
    (hG0 : ∀ u, (wBlk u + cBlk u).det = 0 → G u = 0) :
    ∫⁻ X2 : Fin r → Fin (r + t + r) → ℝ, G (Matrix.of fun i j => X2 j i) =
      ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) ^ 2)) * (2 : ℝ) ^ (-((t : ℝ) * r) / 2)) *
        ∫⁻ z : Fin (r + t) → Fin r → ℝ, ∫⁻ Y : Fin r → Fin r → ℝ,
          ENNReal.ofReal (|(Matrix.of fun i j => Y j i).det| ^ (r + t)) *
            G (frameOf z (Matrix.of fun i j => Y j i)) := by
  have hGm : Measurable (fun X2 : Fin r → Fin (r + t + r) → ℝ => G (Matrix.of fun i j => X2 j i)) :=
    hG.comp measurable_frmTrans
  rw [lintegral_pi_finAppend hGm]
  rw [lintegral_lintegral_swap (measurable_frmAppendA hG).aemeasurable]
  have e1 : ∀ a : Fin r → Fin (r + t) → ℝ,
      ∫⁻ W : Fin r → Fin r → ℝ, G (Matrix.of fun i j => Fin.append (a j) (W j) i) =
        ∫⁻ M : Fin r → Fin r → ℝ, G (Matrix.of fun i j => Fin.append (a j) ((M - frmC a) j) i) :=
    fun a => (lintegral_sub_right_eq_self
      (fun W : Fin r → Fin r → ℝ => G (Matrix.of fun i j => Fin.append (a j) (W j) i)) (frmC a)).symm
  rw [lintegral_congr e1]
  rw [lintegral_lintegral_swap (measurable_frmAppendB hG).aemeasurable,
    lintegral_congr (lintegral_frames_fixed hG hG0), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_lintegral_swap
    ((measurable_frmDet (r := r) (t := t)).mul
      (hG.comp (measurable_frmFrame (r := r) (t := t)))).aemeasurable

end QuadFormsKB.Hanke2005.ArchReal
