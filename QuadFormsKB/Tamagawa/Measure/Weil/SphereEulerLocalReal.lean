import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerGauss
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalReal
import QuadFormsKB.Tamagawa.SphericalZeta

/-!
# The local spherical identity at a real place

$Q$ a real quadratic form in $N\ge1$ variables, $c\ne0$, $\sigma_c$ = the Leray measure on the sphere
$S_c = \{Q = c\}$ (`SphereLeray.sig`), $G(x) = e^{-\pi\sum_ix_i^2}$ (`gaussRe`), $a = N + 2s$. The archimedean factor of
the adelic spherical integral is
$$\int_{S_c}\int_{\mathbb R}|t|^{a-1}G(ty)\,dt\,d\sigma_c(y) = |c|^{-1-s}\int_{cQ>0}|Q(x)|^sG(x)\,dx$$
(**`lintegral_archMellin_sig`**; polar coordinates `lintegral_posSet_pol`, $\sigma_c = \nu_c/(2|c|)$, $G$ even), hence
(**`lintegral_archMellin_sigR`**) it equals $Z_w(s,\rho)/(|2\rho|_w|\rho|_w^s)$, $Z_w$ = `sphArchAt` with $\Phi_w = G$.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace QuadFormsKB.Tamagawa.Measure.SphereLeray

/-- **The Gaussian** $G(x) = e^{-\pi\sum_ix_i^2}$ on $\mathbb R^n$, real valued (`gaussRe` is its `ofReal`). -/
def gaussFn {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.exp (-Real.pi * ∑ i, x i ^ 2)

theorem ofReal_gaussFn {n : ℕ} (x : Fin n → ℝ) : ENNReal.ofReal (gaussFn x) = gaussRe x := rfl

/-- **The archimedean Mellin transform of the Gaussian** $M_a(y) = \int_{\mathbb R}|t|^{a}|t|^{-1}G(ty)\,dt$. -/
def archMellin {n : ℕ} (a : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ENNReal.ofReal (|t| ^ a * |t|⁻¹) * gaussRe (t • y)

theorem measurable_archMellin {n : ℕ} (a : ℝ) : Measurable (archMellin (n := n) a) := by
  unfold archMellin
  refine Measurable.lintegral_prod_left' (μ := (volume : Measure ℝ)) (f := fun p : ℝ × (Fin n → ℝ) =>
    ENNReal.ofReal (|p.1| ^ a * |p.1|⁻¹) * gaussRe (p.1 • p.2)) ?_
  refine Measurable.mul ?_ (measurable_gaussRe.comp (measurable_fst.smul measurable_snd))
  exact ENNReal.measurable_ofReal.comp (((measurable_fst.abs).pow_const a).mul measurable_fst.abs.inv)

/-- $G(-z) = G(z)$. -/
theorem gaussRe_neg {n : ℕ} (z : Fin n → ℝ) : gaussRe (-z) = gaussRe z := by
  simp [gaussRe]

/-- **Halving the Mellin transform**: $M_a(y) = 2\int_{\mathbb R}e^{au}G(e^uy)\,du$. -/
theorem archMellin_eq {n : ℕ} (a : ℝ) (y : Fin n → ℝ) :
    archMellin a y = 2 * ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (a * u)) * gaussRe (Real.exp u • y) := by
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (|t| ^ a * |t|⁻¹) * gaussRe (t • y) with hg
  have hgm : Measurable g := by
    refine Measurable.mul ?_ (measurable_gaussRe.comp (measurable_id.smul measurable_const))
    exact ENNReal.measurable_ofReal.comp (((measurable_id.abs).pow_const a).mul measurable_id.abs.inv)
  have hpos : ∫⁻ t in Ioi 0, g t = ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (a * u)) * gaussRe (Real.exp u • y) := by
    have himg : Real.exp '' (univ : Set ℝ) = Ioi 0 := by rw [image_univ, Real.range_exp]
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ (f' := Real.exp)
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn, Measure.restrict_univ]
    refine lintegral_congr fun u => ?_
    simp only [hg]
    rw [abs_of_pos (Real.exp_pos u), ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos u).le,
      ← Real.exp_mul, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 3
    ring
  have hneg : ∫⁻ t in Iic 0, g t = ∫⁻ t in Ioi 0, g t := by
    rw [setLIntegral_congr Iio_ae_eq_Iic.symm]
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
      (Homeomorph.neg ℝ).measurableEmbedding g (Ioi 0)
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by ext t; simp
    rw [hpre] at h
    rw [← h]
    refine setLIntegral_congr_fun measurableSet_Iio fun t _ => ?_
    simp only [hg, abs_neg, neg_smul, gaussRe_neg]
  have hsplit : ∫⁻ t, g t = (∫⁻ t in Ioi 0, g t) + ∫⁻ t in (Ioi (0 : ℝ))ᶜ, g t :=
    (lintegral_add_compl (μ := volume) g (measurableSet_Ioi (a := (0 : ℝ)))).symm
  rw [compl_Ioi] at hsplit
  show ∫⁻ t, g t = _
  rw [hsplit, hneg, hpos, two_mul]

/-- **Polar coordinates for the Mellin transform**:
$\int_{S_c}M_{N+2s}\,d\sigma_c = |c|^{-1-s}\int_{cQ>0}|Q|^sG\,dx$. -/
theorem lintegral_archMellin_sig {N : ℕ} (Q : QuadForm ℝ N) {c : ℝ} (hc : c ≠ 0) (hN : 1 ≤ N) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ y, archMellin ((N : ℝ) + 2 * s) (y : Fin N → ℝ) ∂sig Q c =
      ENNReal.ofReal (|c| ^ (-(1 + s))) * ∫⁻ x in posSet Q c, ENNReal.ofReal (|Q.eval x| ^ s) * gaussRe x := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hnu : nu Q c = ENNReal.ofReal (2 * |c|) • sig Q c := by
    rw [sig, smul_smul, ← ENNReal.ofReal_mul (by positivity)]
    rw [show 2 * |c| * (1 / (2 * |c|)) = 1 by field_simp]
    simp
  set a : ℝ := (N : ℝ) + 2 * s with ha
  set f : (Fin N → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (|Q.eval x| ^ s) * gaussRe x with hf
  have hfm : Measurable f := by
    refine Measurable.mul (ENNReal.measurable_ofReal.comp ?_) measurable_gaussRe
    exact ((Siegel.continuous_eval_real Q).measurable.abs).pow_const s
  rw [lintegral_posSet_pol hc hN hfm]
  have key : ∀ t : ℝ, ENNReal.ofReal (Real.exp (N * t)) * ∫⁻ x, f (Real.exp t • (x : Fin N → ℝ)) ∂nu Q c =
      ENNReal.ofReal (|c| ^ s) * (ENNReal.ofReal (2 * |c|) *
        ∫⁻ x : Sph Q c, ENNReal.ofReal (Real.exp (a * t)) * gaussRe (Real.exp t • (x : Fin N → ℝ)) ∂sig Q c) := by
    intro t
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have : ∀ x : Sph Q c, ENNReal.ofReal (Real.exp (N * t)) * f (Real.exp t • (x : Fin N → ℝ)) =
        ENNReal.ofReal (|c| ^ s) * (ENNReal.ofReal (Real.exp (a * t)) * gaussRe (Real.exp t • (x : Fin N → ℝ))) := by
      intro x
      have h1 : Q.eval (Real.exp t • (x : Fin N → ℝ)) = Real.exp (2 * t) * c := eval_pol Q c (t, x)
      simp only [hf]
      rw [h1, abs_mul, abs_of_pos (Real.exp_pos _), Real.mul_rpow (Real.exp_pos _).le (abs_nonneg _),
        ← Real.exp_mul]
      have e1 : ENNReal.ofReal (Real.exp (N * t)) * ENNReal.ofReal (Real.exp (2 * t * s) * |c| ^ s) =
          ENNReal.ofReal (|c| ^ s) * ENNReal.ofReal (Real.exp (a * t)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [ha, show ((N : ℝ) + 2 * s) * t = N * t + 2 * t * s by ring, Real.exp_add]
        ring
      rw [← mul_assoc, e1, mul_assoc]
    simp_rw [this]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hnu, lintegral_smul_measure]
    rfl
  simp_rw [key]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmeas : Measurable (fun p : ℝ × Sph Q c => ENNReal.ofReal (Real.exp (a * p.1)) * gaussRe (Real.exp p.1 • (p.2 : Fin N → ℝ))) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_fst))).mul
      (measurable_gaussRe.comp (continuous_pol Q c).measurable)
  have := sigmaFinite_sig (Q := Q) hc
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ x : Sph Q c, archMellin a (x : Fin N → ℝ) = 2 * ∫⁻ t, ENNReal.ofReal (Real.exp (a * t)) * gaussRe (Real.exp t • (x : Fin N → ℝ)) :=
    fun x => archMellin_eq a _
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ (by norm_num), ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  have : |c| ^ (-(1 + s)) * |c| ^ s * (2 * |c|) = 2 := by
    rw [← Real.rpow_add hcabs, show -(1 + s) + s = -1 by ring, Real.rpow_neg_one]
    field_simp
  rw [this]
  simp

/-- A real quadratic form is bounded by a multiple of $\sum_ix_i^2$. -/
theorem abs_eval_le_sum_sq {N : ℕ} (Q : QuadForm ℝ N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Fin N → ℝ, |Q.eval x| ≤ B * ∑ i, x i ^ 2 := by
  refine ⟨∑ i, ∑ j, |Q.coeff i j|, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x => ?_⟩
  have hn : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := sq_norm_le_sum_sq x
  calc |Q.eval x| ≤ ∑ i, ∑ j, |if i ≤ j then algebraMap ℝ ℝ (Q.coeff i j) * x i * x j else 0| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |Q.coeff i j| * ‖x‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · rw [Algebra.algebraMap_self_apply, abs_mul, abs_mul, sq]
          have h1 : |x i| ≤ ‖x‖ := by simpa using norm_le_pi_norm x i
          have h2 : |x j| ≤ ‖x‖ := by simpa using norm_le_pi_norm x j
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
        · simp only [abs_zero]; positivity
    _ = (∑ i, ∑ j, |Q.coeff i j|) * ‖x‖ ^ 2 := by simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- $u^se^{-bu}$ is bounded on $[0,\infty)$ for $s\ge0$, $b>0$. -/
theorem exists_bound_rpow_mul_exp {s b : ℝ} (hs : 0 ≤ s) (hb : 0 < b) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → u ^ s * Real.exp (-b * u) ≤ C := by
  have hlim : Tendsto (fun x : ℝ => x ^ s * Real.exp (-b * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb
  have hevent : ∀ᶠ x : ℝ in atTop, x ^ s * Real.exp (-b * x) ≤ 1 :=
    hlim.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  rcases Filter.eventually_atTop.1 hevent with ⟨R, hR⟩
  have hcont : Continuous fun x : ℝ => x ^ s * Real.exp (-b * x) :=
    (continuous_id.rpow_const fun _ => Or.inr hs).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hne : (Icc (0 : ℝ) (max R 0)).Nonempty := ⟨0, le_rfl, le_max_right R 0⟩
  rcases (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max R 0))).exists_isMaxOn hne hcont.continuousOn with ⟨x0, hx0, hxmax⟩
  refine ⟨max (x0 ^ s * Real.exp (-b * x0)) 1, fun x hx => ?_⟩
  by_cases hxR : x ≤ max R 0
  · exact (hxmax ⟨hx, hxR⟩).trans (le_max_left _ _)
  · exact (hR x (le_trans (le_max_left R 0) (le_of_not_ge hxR))).trans (le_max_right _ _)

/-- **Finiteness**: $\int_{cQ>0}|Q|^sG\,dx<\infty$ for $s\ge0$. -/
theorem lintegral_posSet_lt_top {N : ℕ} (Q : QuadForm ℝ N) (c : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ x in posSet Q c, ENNReal.ofReal (|Q.eval x| ^ s) * gaussRe x < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := abs_eval_le_sum_sq Q
  obtain ⟨C, hC⟩ := exists_bound_rpow_mul_exp hs (half_pos Real.pi_pos)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 1 zero_le_one)
  have hi : Integrable (fun x : Fin N → ℝ => B ^ s * C * ∏ i, Real.exp (-(Real.pi / 2) * x i ^ 2))
      (volume : Measure (Fin N → ℝ)) := by
    have hg : Integrable (fun x : Fin N → ℝ => ∏ i, Real.exp (-(Real.pi / 2) * x i ^ 2))
        (Measure.pi fun _ : Fin N => (volume : Measure ℝ)) :=
      Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq (half_pos Real.pi_pos)
    rw [← volume_pi] at hg
    exact hg.const_mul _
  refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (lt_of_le_of_lt ?_ hi.lintegral_lt_top)
  refine lintegral_mono fun x => ?_
  have hG : gaussRe x = ENNReal.ofReal (Real.exp (-Real.pi * ∑ i, x i ^ 2)) := rfl
  rw [hG, ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  set u := ∑ i, x i ^ 2 with hu
  have hu0 : 0 ≤ u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hprod : ∏ i, Real.exp (-(Real.pi / 2) * x i ^ 2) = Real.exp (-(Real.pi / 2) * u) := by
    rw [← Real.exp_sum, hu, Finset.mul_sum]
  rw [hprod]
  calc |Q.eval x| ^ s * Real.exp (-Real.pi * u)
      ≤ (B * u) ^ s * Real.exp (-Real.pi * u) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (hB x) hs) (Real.exp_pos _).le
    _ = B ^ s * (u ^ s * Real.exp (-(Real.pi / 2) * u)) * Real.exp (-(Real.pi / 2) * u) := by
        rw [Real.mul_rpow hB0 hu0]
        have : Real.exp (-Real.pi * u) = Real.exp (-(Real.pi / 2) * u) * Real.exp (-(Real.pi / 2) * u) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring
    _ ≤ B ^ s * C * Real.exp (-(Real.pi / 2) * u) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC u hu0) (Real.rpow_nonneg hB0 _))
          (Real.exp_pos _).le

/-- **The local identity at a real place**: $\int_{T(\rho)_w}M_{N+2s}\,d\sigma_w =
Z_w(s,\rho)/(|2\rho|_w|\rho|_w^s)$ with $Z_w$ = `sphArchAt` for the Gaussian. -/
theorem lintegral_archMellin_sigR {F : Type} [Field F] [NumberField F] {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1))
    (w : {w : InfinitePlace F // w.IsReal}) {ρ : F} (hρ : ρ ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ y, archMellin (((k + 1 : ℕ) : ℝ) + 2 * s) (y : Fin (k + 1) → ℝ) ∂sig (QRe Q₀ w) (σR w ρ) =
      ENNReal.ofReal (SphericalZeta.sphArchAt Q₀ w gaussFn (Siegel.realEmb w ρ) s /
        (|σR w (2 * ρ)| * |σR w ρ| ^ s)) := by
  have hc : σR w ρ ≠ 0 := (map_ne_zero _).mpr hρ
  have hcabs : 0 < |σR w ρ| := abs_pos.mpr hc
  rw [lintegral_archMellin_sig (QRe Q₀ w) hc (Nat.succ_pos k) hs]
  have hval : ∀ x : Fin (k + 1) → ℝ, GlobalZeta.realVal Q₀ w x = (QRe Q₀ w).eval x := by
    intro x
    simp [GlobalZeta.realVal, Siegel.realForm, QuadForm.evalIn, QuadForm.map, Siegel.realEmb, QRe]
  have hset : GlobalZeta.realVal Q₀ w ⁻¹' SphericalZeta.sqClass (σR w ρ) = posSet (QRe Q₀ w) (σR w ρ) := by
    ext x
    simp only [mem_preimage, SphericalZeta.mem_sqClass, posSet, mem_ofPred_eq, hval]
    generalize (QRe Q₀ w).eval x = v
    generalize σR w ρ = c' at hc ⊢
    have hc2 : 0 < c' * c' := mul_self_pos.mpr hc
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : 0 < y ^ 2 := by positivity
      nlinarith
    · intro h
      have hq : 0 < v / c' := by
        have : v / c' = c' * v / (c' * c') := by field_simp
        rw [this]; exact div_pos h hc2
      refine ⟨Real.sqrt (v / c'), (Real.sqrt_pos.mpr hq).ne', ?_⟩
      rw [Real.sq_sqrt hq.le]; field_simp
  have hdef : SphericalZeta.sphArchAt Q₀ w gaussFn (σR w ρ) s =
      2 * ∫ x in posSet (QRe Q₀ w) (σR w ρ), |(QRe Q₀ w).eval x| ^ s * gaussFn x := by
    rw [SphericalZeta.sphArchAt, hset]
    simp only [hval]
  have hlt := lintegral_posSet_lt_top (QRe Q₀ w) (σR w ρ) hs
  have hint : ∫ x in posSet (QRe Q₀ w) (σR w ρ), |(QRe Q₀ w).eval x| ^ s * gaussFn x =
      (∫⁻ x in posSet (QRe Q₀ w) (σR w ρ), ENNReal.ofReal (|(QRe Q₀ w).eval x| ^ s) * gaussRe x).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 2
      funext x
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
      rfl
    · exact Eventually.of_forall fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le
    · exact (((Siegel.continuous_eval_real (QRe Q₀ w)).measurable.abs.pow_const s).mul
        (Real.measurable_exp.comp (measurable_const.mul
          (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)))).aestronglyMeasurable
  rw [show Siegel.realEmb w ρ = σR w ρ from rfl, hdef, hint]
  conv_lhs => rw [← ENNReal.ofReal_toReal hlt.ne]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
  congr 1
  set J := (∫⁻ x in posSet (QRe Q₀ w) (σR w ρ), ENNReal.ofReal (|(QRe Q₀ w).eval x| ^ s) * gaussRe x).toReal
  rw [map_mul, map_ofNat, abs_mul, abs_two, Real.rpow_neg hcabs.le, Real.rpow_add hcabs, Real.rpow_one]
  field_simp

end QuadFormsKB.Tamagawa.Measure.Weil

end
