import QuadFormsKB.Tamagawa.ArchVolume
import QuadFormsKB.Citation
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace QuadFormsKB.Hanke2005.ArchReal
open QuadFormsKB.Tamagawa.ArchVol

/-- $\int G(PX_1,\dots,PX_k)\,dX = |\det P|^{-k}\int G$ on $(\mathbb R^r)^k$
($P$ acting on each of the $k$ vectors). -/
theorem lintegral_comp_mulVec_rect {k r : ℕ} (P : Matrix (Fin r) (Fin r) ℝ) (hP : P.det ≠ 0)
    {G : (Fin k → Fin r → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ X : Fin k → Fin r → ℝ, G (fun j => P *ᵥ X j) =
      ENNReal.ofReal (|P.det|⁻¹) ^ k * ∫⁻ Y, G Y := by
  have hmeas : Measurable fun y : Fin r → ℝ => P *ᵥ y :=
    (Matrix.toLin' P).continuous_of_finiteDimensional.measurable
  set c : NNReal := Real.toNNReal (|P.det|⁻¹)
  have h1 : Measure.map (fun y : Fin r → ℝ => P *ᵥ y) volume = c • (volume : Measure (Fin r → ℝ)) := by
    have := Real.map_matrix_volume_pi_eq_smul_volume_pi hP
    rw [abs_inv] at this
    rw [ENNReal.smul_def]
    exact this
  have hmap : Measure.map (fun (X : Fin k → Fin r → ℝ) j => P *ᵥ X j) volume =
      ENNReal.ofReal (|P.det|⁻¹) ^ k • (volume : Measure (Fin k → Fin r → ℝ)) := by
    rw [volume_pi, Measure.pi_map_pi (hμ := fun _ => by rw [h1]; infer_instance)
      (fun _ => hmeas.aemeasurable)]
    simp only [h1]
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_congr rfl
      (fun i _ => Measure.smul_apply _ _ _), Finset.prod_congr rfl (fun i _ => ENNReal.smul_def _ _),
      Finset.prod_congr rfl (fun i _ => smul_eq_mul _ _),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  rw [← lintegral_map hG (g := fun (X : Fin k → Fin r → ℝ) j => P *ᵥ X j)
    (measurable_pi_iff.mpr fun j => hmeas.comp (measurable_pi_apply j)), hmap,
    lintegral_smul_measure, smul_eq_mul]

/-- Upper coordinates of the Gram matrix of the vectors `B j` for the inner product given by `H`. -/
def gramH {k m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (B : Fin k → Fin m → ℝ) : UIdx k → ℝ :=
  fun p => B p.1.1 ⬝ᵥ (H *ᵥ B p.1.2)

/-- A positive definite $H = P^{\mathsf T}P$ (as bilinear forms) with $|\det P| = \sqrt{\det H}$. -/
theorem exists_factor_posDef {k : ℕ} {H : Matrix (Fin k) (Fin k) ℝ} (hH : H.PosDef) :
    ∃ P : Matrix (Fin k) (Fin k) ℝ, (∀ x y, x ⬝ᵥ (H *ᵥ y) = (P *ᵥ x) ⬝ᵥ (P *ᵥ y)) ∧
      0 < H.det ∧ |P.det| = Real.sqrt H.det := by
  have hherm : H.IsHermitian := hH.isHermitian
  have hsymm : ∀ x y : Fin k → ℝ, x ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ x) := by
    intro x y
    have hT : Hᵀ = H := by simpa using hherm.eq
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  obtain ⟨P, hP, hpos, hdet⟩ := QuadFormsKB.Siegel.exists_sqrt_factor H hherm
    (fun x hx => by simpa using hH.dotProduct_mulVec_pos hx)
  refine ⟨P, fun x y => ?_, hpos, hdet⟩
  have hd : ∀ z, z ⬝ᵥ (H *ᵥ z) = (P *ᵥ z) ⬝ᵥ (P *ᵥ z) := fun z => by
    rw [hP]; simp only [dotProduct, sq]
  have e := hd (x + y)
  simp only [mulVec_add, dotProduct_add, add_dotProduct] at e
  rw [hsymm y x, hd x, hd y, dotProduct_comm (P *ᵥ y) (P *ᵥ x)] at e
  linarith

theorem gramH_eq_gramU {k : ℕ} {H P : Matrix (Fin k) (Fin k) ℝ}
    (hP : ∀ x y, x ⬝ᵥ (H *ᵥ y) = (P *ᵥ x) ⬝ᵥ (P *ᵥ y)) (B : Fin k → Fin k → ℝ) :
    gramH H B = gramU (fun j => P *ᵥ B j) := by
  funext p; exact hP _ _

/-- **Weighted Gram co-area formula:** for positive definite $H$,
$\int f(\mathrm{Gram}_H(B))\,dB = (\det H)^{-k/2}\int \rho_k(t) f(t)\,dt$. -/
theorem lintegral_gramH {k : ℕ} {H : Matrix (Fin k) (Fin k) ℝ} (hH : H.PosDef)
    {f : (UIdx k → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ B : Fin k → Fin k → ℝ, f (gramH H B) =
      ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2)) * ∫⁻ t, densR k t * f t := by
  obtain ⟨P, hP, hd, hdP⟩ := exists_factor_posDef hH
  have hP0 : P.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hdP; exact (Real.sqrt_pos.2 hd).ne' hdP.symm
  have hfg : Measurable fun Y : Fin k → Fin k → ℝ => f (gramU Y) :=
    hf.comp continuous_gramU.measurable
  have : ∀ B : Fin k → Fin k → ℝ, f (gramH H B) = f (gramU (fun j => P *ᵥ B j)) := fun B => by
    rw [gramH_eq_gramU hP]
  have key : ENNReal.ofReal (|P.det|⁻¹) ^ k = ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [hdP, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hd.le]
    congr 1; ring
  simp_rw [this]
  rw [lintegral_comp_mulVec_rect P hP0 (G := fun Y => f (gramU Y)) hfg, lintegral_gram k hf, key]

/-- An $H$-reflection: $R$ with $\det R = -1$ and $(Rx)^{\mathsf T}H(Ry) = x^{\mathsf T}Hy$
($H$ positive definite, $k \ge 1$). -/
theorem exists_reflection_posDef {k : ℕ} (hk : 1 ≤ k) {H : Matrix (Fin k) (Fin k) ℝ} (hH : H.PosDef) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, R.det = -1 ∧
      ∀ x y, (R *ᵥ x) ⬝ᵥ (H *ᵥ (R *ᵥ y)) = x ⬝ᵥ (H *ᵥ y) := by
  obtain ⟨P, hP, hd, hdP⟩ := exists_factor_posDef hH
  have hP0 : IsUnit P.det := by
    rw [isUnit_iff_ne_zero]
    intro h; rw [h, abs_zero] at hdP; exact (Real.sqrt_pos.2 hd).ne' hdP.symm
  set i0 : Fin k := ⟨0, hk⟩
  set d : Fin k → ℝ := fun i => if i = i0 then -1 else 1
  set D : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal d
  have hDdet : D.det = -1 := by
    simp [D, d, det_diagonal]
  have hDdot : ∀ x y, (D *ᵥ x) ⬝ᵥ (D *ᵥ y) = x ⬝ᵥ y := by
    intro x y
    simp only [D, mulVec_diagonal, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i = i0 <;> simp [d, h]
  have hPR : P * (P⁻¹ * D * P) = D * P := by
    rw [← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hP0, one_mul]
  refine ⟨P⁻¹ * D * P, ?_, fun x y => ?_⟩
  · have h1 : P.det * (P⁻¹).det = 1 := by
      rw [← det_mul, mul_nonsing_inv _ hP0, det_one]
    rw [det_mul, det_mul, hDdet]
    calc (P⁻¹).det * -1 * P.det = -(P.det * (P⁻¹).det) := by ring
      _ = -1 := by rw [h1]
  · have e : ∀ z, P *ᵥ ((P⁻¹ * D * P) *ᵥ z) = D *ᵥ (P *ᵥ z) := fun z => by
      rw [mulVec_mulVec, hPR, ← mulVec_mulVec]
    rw [hP, hP, e, e, hDdot]

/-- **Signed half of the weighted Gram co-area formula** ($k \ge 1$, $s \ne 0$): restricting to
$\{B : s\det B > 0\}$ gives half of `lintegral_gramH`. -/
theorem lintegral_gramH_det_pos {k : ℕ} (hk : 1 ≤ k) {H : Matrix (Fin k) (Fin k) ℝ} (hH : H.PosDef)
    {s : ℝ} (hs : s ≠ 0)
    {f : (UIdx k → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ B : Fin k → Fin k → ℝ, {B : Fin k → Fin k → ℝ | 0 < s * (Matrix.of B).det}.indicator
        (fun B => f (gramH H B)) B =
      ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2) / 2) * ∫⁻ t, densR k t * f t := by
  obtain ⟨R, hRdet, hR⟩ := exists_reflection_posDef hk hH
  obtain ⟨P, hP, hd, hdP⟩ := exists_factor_posDef hH
  have hmp : MeasurePreserving (fun (X : Fin k → Fin k → ℝ) j => R *ᵥ X j) volume volume :=
    measurePreserving_pi _ _ fun _ => measurePreserving_mulVec R (by rw [hRdet]; norm_num)
  have hdetc : Continuous fun X : Fin k → Fin k → ℝ => (Matrix.of X).det :=
    Continuous.matrix_det (continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i))
  have hmS : MeasurableSet {B : Fin k → Fin k → ℝ | 0 < s * (Matrix.of B).det} :=
    measurableSet_lt measurable_const (measurable_const.mul hdetc.measurable)
  have hmN : MeasurableSet {B : Fin k → Fin k → ℝ | s * (Matrix.of B).det < 0} :=
    measurableSet_lt (measurable_const.mul hdetc.measurable) measurable_const
  have hmg : Measurable fun B : Fin k → Fin k → ℝ => f (gramH H B) := by
    have : (fun B : Fin k → Fin k → ℝ => f (gramH H B)) = fun B => f (gramU (fun j => P *ᵥ B j)) :=
      funext fun B => by rw [gramH_eq_gramU hP]
    rw [this]
    refine hf.comp (continuous_gramU.measurable.comp ?_)
    exact measurable_pi_iff.mpr fun j =>
      ((Matrix.toLin' P).continuous_of_finiteDimensional.measurable).comp (measurable_pi_apply j)
  set g : (Fin k → Fin k → ℝ) → ℝ≥0∞ := fun B => f (gramH H B) with hg
  set S := {B : Fin k → Fin k → ℝ | 0 < s * (Matrix.of B).det}
  set N := {B : Fin k → Fin k → ℝ | s * (Matrix.of B).det < 0}
  have hgR : ∀ B, g (fun j => R *ᵥ B j) = g B := fun B => by
    simp only [g]
    congr 1
    funext p
    exact hR _ _
  -- the two halves are equal
  have hSN : ∫⁻ B, S.indicator g B = ∫⁻ B, N.indicator g B := by
    rw [← hmp.lintegral_comp (hmg.indicator hmN)]
    refine lintegral_congr fun B => ?_
    have hiff : (fun j => R *ᵥ B j) ∈ N ↔ B ∈ S := by
      simp only [N, S, Set.mem_setOf_eq, det_of_mulVec, hRdet]
      constructor <;> intro h <;> linarith
    by_cases h : B ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h), hgR]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.1 h'))]
  -- the halves add up to the whole integral
  have hsum : ∫⁻ B, g B = (∫⁻ B, S.indicator g B) + ∫⁻ B, N.indicator g B := by
    rw [← lintegral_add_left (μ := volume) (hmg.indicator hmS) (N.indicator g)]
    refine lintegral_congr_ae ?_
    have hnull := volume_det_eq_zero (n := k)
    have : ∀ᵐ B : Fin k → Fin k → ℝ, (Matrix.of B).det ≠ 0 := by
      rw [ae_iff]; simpa using hnull
    filter_upwards [this] with B hB
    rcases lt_or_gt_of_ne (mul_ne_zero hs hB) with h | h
    · have : B ∉ S := fun h' => by simp only [S, Set.mem_setOf_eq] at h'; linarith
      rw [Set.indicator_of_notMem this, Set.indicator_of_mem (show B ∈ N from h), zero_add]
    · have : B ∉ N := fun h' => by simp only [N, Set.mem_setOf_eq] at h'; linarith
      rw [Set.indicator_of_notMem this, Set.indicator_of_mem (show B ∈ S from h), add_zero]
  have hfull : ∫⁻ B, g B = ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2)) * ∫⁻ t, densR k t * f t :=
    lintegral_gramH hH hf
  have hc : 0 ≤ H.det ^ (-(k : ℝ) / 2) := (Real.rpow_pos_of_pos hd _).le
  have hcc : ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2)) =
      ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2) / 2) + ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2) / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have h2 : 2 * ∫⁻ B, S.indicator g B =
      2 * (ENNReal.ofReal (H.det ^ (-(k : ℝ) / 2) / 2) * ∫⁻ t, densR k t * f t) := by
    rw [← two_mul] at hcc
    calc 2 * ∫⁻ B, S.indicator g B = (∫⁻ B, S.indicator g B) + ∫⁻ B, S.indicator g B := by rw [two_mul]
      _ = ∫⁻ B, g B := by rw [hsum, ← hSN]
      _ = _ := by rw [hfull, hcc, mul_assoc]
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 h2

end QuadFormsKB.Hanke2005.ArchReal
