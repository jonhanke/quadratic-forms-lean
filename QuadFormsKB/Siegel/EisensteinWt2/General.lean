/-
# Weight-2 Eisenstein series for $\Gamma(N)$ with an arbitrary residue weight

For $W : (\mathbb{Z}/N)^2 \to \mathbb{C}$ define
$$E_W(z) = \sum_{c \in \mathbb{Z}}\ \sum_{d \in \mathbb{Z}} W(c, d)\,(cz + d)^{-2}$$
(iterated sum, $c$ outer; the term $(c, d) = (0, 0)$ is $0$ by Lean's convention $0^{-1} = 0$). When the total mass
$\sum_{a, b}W(a, b)$ vanishes, *Hecke's trick* applies (`tendsto_heckeSum`): the absolutely convergent series
$H_W(z, s) = \sum W(c,d)(cz+d)^{-2}|cz+d|^{-2s}$ tends to $E_W(z)$ as $s \to 0^+$. Since $H_W(\cdot, s)$ transforms exactly
under $\mathrm{SL}_2(\mathbb{Z})$ (`heckeSum_smul`), so does $E_W$ (`eis2_slash`):
$$E_W\,|_2\,\gamma = E_{W\cdot\gamma}, \qquad (W\cdot\gamma)(a, b) = W\bigl((a, b)\gamma^{-1}\bigr).$$
(Diamond–Shurman §4.6 / Miyake §7.2 [unverified locators]; the vanishing of the total mass removes the
non-holomorphic correction $-\pi/(N^2\operatorname{Im}z)\sum W$ of the general case.)
-/
import QuadFormsKB.Siegel.EisensteinWt2.Lattice
import Mathlib.NumberTheory.ModularForms.SlashActions

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups

namespace QuadFormsKB.Siegel.EisensteinWt2

variable {N : ℕ} [NeZero N]

/-- Summing over $0 \le r < N$ is summing over $\mathbb{Z}/N$. -/
lemma sum_range_zmod (f : ZMod N → ℂ) : ∑ r ∈ Finset.range N, f (r : ℤ) = ∑ b, f b := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [← Fin.sum_univ_eq_sum_range (fun r => f ((r : ℤ) : ZMod (n + 1))) (n + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Int.cast_natCast]
  exact Fin.cast_val_eq_self i

/-- The weight on $\mathbb{Z}^2$ attached to $W$. -/
def wt (W : ZMod N → ZMod N → ℂ) (c d : ℤ) : ℂ := W c d

/-- The **total mass** $\sum_{a, b \in \mathbb{Z}/N}W(a, b)$. -/
def totalSum (W : ZMod N → ZMod N → ℂ) : ℂ := ∑ a, ∑ b, W a b

/-- A bound for $|W|$. -/
noncomputable def wtBound (W : ZMod N → ZMod N → ℂ) : ℝ := ∑ a, ∑ b, ‖W a b‖

lemma norm_wt_le (W : ZMod N → ZMod N → ℂ) (c d : ℤ) : ‖wt W c d‖ ≤ wtBound W := by
  unfold wt wtBound
  calc ‖W c d‖ ≤ ∑ b, ‖W c b‖ :=
        Finset.single_le_sum (f := fun b => ‖W c b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    _ ≤ ∑ a, ∑ b, ‖W a b‖ :=
        Finset.single_le_sum (f := fun a => ∑ b, ‖W a b‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ _)

omit [NeZero N] in
lemma wt_add_N_right (W : ZMod N → ZMod N → ℂ) (c d : ℤ) : wt W c (d + N) = wt W c d := by
  simp [wt]

omit [NeZero N] in
lemma wt_add_N_left (W : ZMod N → ZMod N → ℂ) (c d : ℤ) : wt W (c + N) d = wt W c d := by
  simp [wt]

/-- The **Hecke-regularized series** $H_W(z, s) = \sum_{(c,d)} W(c, d)\,(cz+d)^{-2}|cz+d|^{-2s}$. -/
noncomputable def heckeSum (W : ZMod N → ZMod N → ℂ) (s : ℝ) (z : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ, wt W p.1 p.2 * fs s (p.1 * z + p.2)

/-- **The weight-2 Eisenstein series with residue weight $W$** (iterated sum, $c$ outer):
$E_W(z) = \sum_c\sum_d W(c, d)(cz+d)^{-2}$. -/
noncomputable def eis2 (W : ZMod N → ZMod N → ℂ) (z : ℍ) : ℂ :=
  ∑' c : ℤ, ∑' d : ℤ, wt W c d * (((c : ℂ) * z + d) ^ 2)⁻¹

omit [NeZero N] in
lemma eis2_eq_fs (W : ZMod N → ZMod N → ℂ) (z : ℍ) :
    eis2 W z = ∑' c : ℤ, ∑' d : ℤ, wt W c d * fs 0 ((c : ℂ) * z + d) := by
  simp [eis2, fs_zero_left]

/-- The row mean $\frac1N\sum_b W(a, b)$. -/
noncomputable def rowMean (W : ZMod N → ZMod N → ℂ) (a : ZMod N) : ℂ := (N : ℂ)⁻¹ * ∑ b, W a b

/-- The row-mean-zero part $W^0 = W - \text{rowMean}$. -/
noncomputable def rowZero (W : ZMod N → ZMod N → ℂ) (a b : ZMod N) : ℂ := W a b - rowMean W a

lemma sum_rowZero (W : ZMod N → ZMod N → ℂ) (a : ZMod N) : ∑ b, rowZero W a b = 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [rowZero, Finset.sum_sub_distrib, rowMean, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  field_simp
  ring

lemma sum_rowMean (W : ZMod N → ZMod N → ℂ) : ∑ a, rowMean W a = (N : ℂ)⁻¹ * totalSum W := by
  simp [rowMean, totalSum, Finset.mul_sum]

lemma heckeSum_summable (W : ZMod N → ZMod N → ℂ) {s : ℝ} (hs : 0 < s) (z : ℍ) :
    Summable fun p : ℤ × ℤ => wt W p.1 p.2 * fs s (p.1 * (z : ℂ) + p.2) :=
  Summable.of_norm_bounded ((summable_lat_rpow z (t := 2 + 2 * s) (by linarith)).mul_left (wtBound W))
    fun p => by
      rw [norm_mul]
      exact mul_le_mul (norm_wt_le W _ _) (norm_fs_le_rpow hs.le _) (norm_nonneg _)
        ((norm_nonneg _).trans (norm_wt_le W 0 0))

/-- The split $\sum_d W(c,d)f_s(cz+d) = \sum_d W^0(c,d)f_s(cz+d) + \mathrm{rowMean}(c)\,R_s(c)$. -/
lemma row_split (W : ZMod N → ZMod N → ℂ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : ℍ) (c : ℤ) :
    ∑' d : ℤ, wt W c d * fs s ((c : ℂ) * z + d) =
      ∑' d : ℤ, wt (rowZero W) c d * fs s ((c : ℂ) * z + d) + rowMean W c * rowSum z s c := by
  have h1 := (rowSystem_lat z).summable_fs (v := wt (rowZero W)) hs0 hs1 c
    (fun i j => norm_wt_le _ i j)
  have h2 := (rowSystem_lat z).summable_fs (v := fun _ _ => rowMean W c) hs0 hs1 c
    (fun _ _ => le_refl ‖rowMean W c‖)
  rw [rowSum, ← tsum_mul_left, ← h1.tsum_add h2]
  refine tsum_congr fun d => ?_
  simp only [wt, rowZero]
  ring

/-- Outer summability of the row-mean-zero part. -/
lemma summable_rowZero_rows (W : ZMod N → ZMod N → ℂ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (z : ℍ) :
    Summable fun c : ℤ => ∑' d : ℤ, wt (rowZero W) c d * fs s ((c : ℂ) * z + d) :=
  (rowSystem_lat z).summable_rows (N := N) (fun i j => wt_add_N_right _ i j)
    (fun i => by simp only [wt]; rw [sum_range_zmod (fun b => rowZero W i b)]; exact sum_rowZero W _)
    (fun i j => norm_wt_le _ i j) hs0 hs1

lemma summable_rowMean_rowSum (W : ZMod N → ZMod N → ℂ) {s : ℝ} (hs : s = 0 ∨ 0 < s) (z : ℍ) :
    Summable fun c : ℤ => rowMean W c * rowSum z s c := by
  have hg : Summable (rowSum z s) := by
    rcases hs with rfl | hs
    · exact summable_rowSum_zero z
    · exact summable_rowSum z hs
  refine Summable.of_norm_bounded (hg.norm.mul_left (wtBound (fun a _ => rowMean W a))) fun c => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_wt_le (fun a _ => rowMean W a) c 0) (norm_nonneg _)

lemma rows_split (W : ZMod N → ZMod N → ℂ) {s : ℝ} (hs : s = 0 ∨ 0 < s) (hs1 : s ≤ 1) (z : ℍ) :
    ∑' c : ℤ, ∑' d : ℤ, wt W c d * fs s ((c : ℂ) * z + d) =
      ∑' c : ℤ, ∑' d : ℤ, wt (rowZero W) c d * fs s ((c : ℂ) * z + d) +
        ∑' c : ℤ, rowMean W c * rowSum z s c := by
  have hs0 : 0 ≤ s := by rcases hs with rfl | hs <;> linarith
  rw [← (summable_rowZero_rows W hs0 hs1 z).tsum_add (summable_rowMean_rowSum W hs z)]
  exact tsum_congr fun c => row_split W hs0 hs1 z c

/-- **Hecke's trick** (total mass zero): $H_W(z, s) \to E_W(z)$ as $s \to 0^+$. -/
theorem tendsto_heckeSum (W : ZMod N → ZMod N → ℂ) (hW : totalSum W = 0) (z : ℍ) :
    Tendsto (fun s => heckeSum W s z) (𝓝[>] 0) (𝓝 (eis2 W z)) := by
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact ⟨hs.1, hs.2.le⟩
  rw [eis2_eq_fs, rows_split W (Or.inl rfl) zero_le_one z]
  have hA := (rowSystem_lat z).tendsto (N := N) (v := wt (rowZero W))
    (fun i j => wt_add_N_right _ i j)
    (fun i => by simp only [wt]; rw [sum_range_zmod (fun b => rowZero W i b)]; exact sum_rowZero W _)
    (fun i j => norm_wt_le _ i j)
  have hB := tendsto_outer z (N := N) (a := fun c : ℤ => rowMean W c)
    (fun c => by simp) (by rw [sum_range_zmod (rowMean W), sum_rowMean, hW, mul_zero])
    (fun c => norm_wt_le (fun a _ => rowMean W a) c 0)
  refine (hA.add hB).congr' ?_
  filter_upwards [hev] with s hs
  rw [heckeSum, (heckeSum_summable W hs.1 z).tsum_prod, rows_split W (Or.inr hs.1) hs.2 z]

/-! ### The transformation law -/

/-- The right action of $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ on weights: $(W\cdot\gamma)(a, b) = W((a, b)\gamma^{-1})$,
$\gamma^{-1} = \begin{pmatrix}\gamma_{11}&-\gamma_{01}\\-\gamma_{10}&\gamma_{00}\end{pmatrix}$. -/
def slashW (W : ZMod N → ZMod N → ℂ) (γ : SL(2, ℤ)) (a b : ZMod N) : ℂ :=
  W (a * (γ 1 1 : ℤ) - b * (γ 1 0 : ℤ)) (-(a * (γ 0 1 : ℤ)) + b * (γ 0 0 : ℤ))

lemma det_SL (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rw [Matrix.det_fin_two] at this; exact this

/-- The action permutes $(\mathbb{Z}/N)^2$, so it preserves the total mass. -/
lemma totalSum_slashW (W : ZMod N → ZMod N → ℂ) (γ : SL(2, ℤ)) : totalSum (slashW W γ) = totalSum W := by
  have hdet : ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    exact_mod_cast congr_arg (Int.cast : ℤ → ZMod N) (det_SL γ)
  let e : ZMod N × ZMod N ≃ ZMod N × ZMod N :=
    { toFun := fun p => (p.1 * (γ 1 1 : ℤ) - p.2 * (γ 1 0 : ℤ), -(p.1 * (γ 0 1 : ℤ)) + p.2 * (γ 0 0 : ℤ))
      invFun := fun q => (q.1 * (γ 0 0 : ℤ) + q.2 * (γ 1 0 : ℤ), q.1 * (γ 0 1 : ℤ) + q.2 * (γ 1 1 : ℤ))
      left_inv := fun p => by
        ext
        · simp only; linear_combination p.1 * hdet
        · simp only; linear_combination p.2 * hdet
      right_inv := fun q => by
        ext
        · simp only; linear_combination q.1 * hdet
        · simp only; linear_combination q.2 * hdet }
  simp only [totalSum, slashW, ← Fintype.sum_prod_type']
  exact e.sum_comp (fun p => W p.1 p.2)

lemma fs_div {s : ℝ} (L j : ℂ) (hj : j ≠ 0) :
    fs s (L / j) = j ^ 2 * ((‖j‖ ^ (2 * s) : ℝ) : ℂ) * fs s L := by
  have hj0 : 0 < ‖j‖ := norm_pos_iff.mpr hj
  simp only [fs, norm_div]
  rw [Real.div_rpow (norm_nonneg _) hj0.le, show -2 * s = -(2 * s) by ring,
    Real.rpow_neg hj0.le (2 * s)]
  have : (‖j‖ ^ (2 * s) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hj0 _).ne'
  rw [div_inv_eq_mul]
  push_cast
  field_simp

omit [NeZero N] in
/-- **Exact transformation of $H_W$** for $s > 0$: with $j = \gamma_{10}z + \gamma_{11}$,
$H_W(\gamma z, s) = j^2|j|^{2s}H_{W\cdot\gamma}(z, s)$. -/
theorem heckeSum_smul (W : ZMod N → ZMod N → ℂ) (γ : SL(2, ℤ)) (s : ℝ) (z : ℍ) :
    heckeSum W s ((γ • z : ℍ) : ℂ) =
      (((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)) ^ 2 *
        ((‖((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)‖ ^ (2 * s) : ℝ) : ℂ) * heckeSum (slashW W γ) s z := by
  set j : ℂ := ((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ) with hjdef
  have hj : j ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
    simpa [UpperHalfPlane.denom, hjdef] using this
  have hdet := det_SL γ
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 * γ 0 0 + p.2 * γ 1 0, p.1 * γ 0 1 + p.2 * γ 1 1)
      invFun := fun q => (q.1 * γ 1 1 - q.2 * γ 1 0, -(q.1 * γ 0 1) + q.2 * γ 0 0)
      left_inv := fun p => by
        ext
        · simp only; linear_combination p.1 * hdet
        · simp only; linear_combination p.2 * hdet
      right_inv := fun q => by
        ext
        · simp only; linear_combination q.1 * hdet
        · simp only; linear_combination q.2 * hdet }
  have hterm : ∀ p : ℤ × ℤ, wt W p.1 p.2 * fs s (p.1 * ((γ • z : ℍ) : ℂ) + p.2) =
      j ^ 2 * ((‖j‖ ^ (2 * s) : ℝ) : ℂ) *
        (wt (slashW W γ) (e p).1 (e p).2 * fs s ((e p).1 * (z : ℂ) + (e p).2)) := by
    intro p
    have hL : (p.1 : ℂ) * ((γ • z : ℍ) : ℂ) + p.2 =
        (((e p).1 : ℤ) * (z : ℂ) + ((e p).2 : ℤ)) / j := by
      have hj3 : (z : ℂ) * ((γ 1 0 : ℤ) : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by rw [mul_comm]; exact hj
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp only [algebraMap_int_eq, eq_intCast, ofReal_intCast, e, Equiv.coe_fn_mk]
      rw [eq_div_iff hj, hjdef]
      field_simp
      push_cast
      ring
    have hw : wt (slashW W γ) (e p).1 (e p).2 = wt W p.1 p.2 := by
      simp only [wt, slashW, e, Equiv.coe_fn_mk]
      have hd : ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
        exact_mod_cast congr_arg (Int.cast : ℤ → ZMod N) hdet
      congr 1
      · push_cast; linear_combination (p.1 : ZMod N) * hd
      · push_cast; linear_combination (p.2 : ZMod N) * hd
    rw [hL, fs_div _ _ hj, hw]
    ring
  rw [heckeSum, heckeSum, tsum_congr hterm, tsum_mul_left]
  congr 1
  exact e.tsum_eq (fun q => wt (slashW W γ) q.1 q.2 * fs s (q.1 * (z : ℂ) + q.2))

/-- **The transformation law of $E_W$** (total mass zero): $E_W\,|_2\,\gamma = E_{W\cdot\gamma}$ for every
$\gamma \in \mathrm{SL}_2(\mathbb{Z})$. -/
theorem eis2_slash (W : ZMod N → ZMod N → ℂ) (hW : totalSum W = 0) (γ : SL(2, ℤ)) :
    (eis2 W) ∣[(2 : ℤ)] γ = eis2 (slashW W γ) := by
  ext z
  set j : ℂ := ((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ) with hjdef
  have hj : j ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
    simpa [UpperHalfPlane.denom, hjdef] using this
  have h1 := tendsto_heckeSum W hW (γ • z)
  have h2 := tendsto_heckeSum (slashW W γ) (by rw [totalSum_slashW, hW]) z
  have hc : Tendsto (fun s : ℝ => j ^ 2 * ((‖j‖ ^ (2 * s) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (j ^ 2)) := by
    have : ContinuousAt (fun s : ℝ => ‖j‖ ^ (2 * s)) 0 :=
      (Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hj)).comp
        (continuous_const.mul continuous_id).continuousAt
    have h := ((continuous_ofReal.tendsto _).comp this).const_mul (j ^ 2)
    simp only [Function.comp_def, mul_zero, Real.rpow_zero, ofReal_one, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h3 := hc.mul h2
  have heq : eis2 W (γ • z) = j ^ 2 * eis2 (slashW W γ) z := by
    refine tendsto_nhds_unique h1 (h3.congr fun s => ?_)
    rw [heckeSum_smul W γ s z]
  rw [ModularForm.SL_slash_apply, heq]
  have hden : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) = j := by
    simp [UpperHalfPlane.denom, hjdef]
  rw [hden, zpow_neg, zpow_two]
  field_simp

end QuadFormsKB.Siegel.EisensteinWt2
