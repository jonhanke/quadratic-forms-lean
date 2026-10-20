/-
# The trivial-character case $E_2(z) - tE_2(tz)$ in the residue-weight framework

For $\psi = \varphi = 1$ the Diamond–Shurman weight has nonzero mass, and one uses instead the weight
$$w_t(c, d) = 1 - t\cdot\mathbf{1}_{t \mid c}\qquad(t \mid N),$$
whose total mass is $0$ (`totalSum_trivW`), so that
$E_{w_t}(z) = \sum_c\sum_d(cz+d)^{-2} - t\sum_c\sum_d(ctz+d)^{-2} = G_2(z) - tG_2(tz)$ (`eis2_trivW_eq_G2`, with Mathlib's
`EisensteinSeries.G2`) lies in $M_2(\Gamma_0(N))$ (`trivEisMF`).  Its $q$-expansion is (`trivEisMF_eq_qExpansion`)
$$E_{w_t}(z) = 2(1-t)\zeta(2) + 2(-2\pi i)^2\sum_{e \ge 1}\bigl(\sigma_1(e) - t\,\sigma_1(e/t)\bigr)q^e
  \quad\text{(as } \textstyle\sum_{d\mid e}w_t(e/d)\,d\text{)}.$$
For $t = 4$ this is $2\zeta(2)$ times the form `G4` $= E_2(z) - 4E_2(4z)$ of `Siegel/FourSquaresJacobi.lean`
(`trivEisMF_four_eq_G4`), and $\Theta_{I_4} = -\pi^{-2}E_{w_4}$ (`theta_sumSq_four_eq_trivEis`): the $I_4$ example,
whose coefficients are the local-density products $a_E(m)$ by `repNum_Q4_eq_aE`.
-/
import QuadFormsKB.Siegel.EisensteinWt2.Cusps
import QuadFormsKB.Siegel.FourSquaresSiegel
import QuadFormsKB.Siegel.FourSquaresJacobi

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups

namespace QuadFormsKB.Siegel.EisensteinWt2

variable {N : ℕ} [NeZero N]

/-- The weight $w_t(c, d) = 1 - t\cdot\mathbf{1}_{t \mid c}$. -/
noncomputable def trivF (t : ℕ) (c _d : ℤ) : ℂ := 1 - t * (if (t : ℤ) ∣ c then 1 else 0)

omit [NeZero N] in
lemma trivF_periodic {t : ℕ} (ht : t ∣ N) :
    (∀ c d, trivF t (c + N) d = trivF t c d) ∧ (∀ c d, trivF t c (d + N) = trivF t c d) := by
  refine ⟨fun c d => ?_, fun c d => rfl⟩
  have htN : (t : ℤ) ∣ N := by exact_mod_cast ht
  simp only [trivF]
  by_cases hc : (t : ℤ) ∣ c
  · simp [hc, dvd_add hc htN]
  · have : ¬ (t : ℤ) ∣ c + N := fun h => hc (by simpa using dvd_sub h htN)
    simp [hc, this]

/-- The residue weight $w_t$ on $(\mathbb{Z}/N)^2$. -/
noncomputable def trivW (t : ℕ) : ZMod N → ZMod N → ℂ := ofPer (trivF t)

lemma totalSum_trivW {t : ℕ} (ht0 : t ≠ 0) (ht : t ∣ N) : totalSum (trivW (N := N) t) = 0 := by
  have hp := trivF_periodic (N := N) ht
  rw [trivW, totalSum_ofPer hp.1 hp.2]
  have hinner : ∀ c ∈ Finset.range N, ∑ d ∈ Finset.range N, trivF t (c : ℤ) (d : ℤ) =
      N * trivF t (c : ℤ) 0 := by
    intro c _; simp only [trivF, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  suffices h : ∑ c ∈ Finset.range N, trivF t (c : ℤ) 0 = 0 by rw [h, mul_zero]
  obtain ⟨K, hK⟩ := ht
  rw [hK, sum_range_mul_split]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := Nat.exists_eq_succ_of_ne_zero ht0
  rw [Finset.sum_range_succ']
  have h1 : ∀ r ∈ Finset.range s, trivF (s + 1) (((s + 1) * j + (r + 1) : ℕ) : ℤ) 0 = 1 := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have : ¬ ((s + 1 : ℕ) : ℤ) ∣ (((s + 1) * j + (r + 1) : ℕ) : ℤ) := by
      intro h
      have h' : ((s + 1 : ℕ) : ℤ) ∣ ((r + 1 : ℕ) : ℤ) := by
        have := dvd_sub h (dvd_mul_right ((s + 1 : ℕ) : ℤ) (j : ℤ)); push_cast at this ⊢
        simpa using this
      have := Int.le_of_dvd (by positivity) h'
      push_cast at this
      omega
    push_cast at this
    simp [trivF, this]
  rw [Finset.sum_congr rfl h1]
  simp [trivF]

omit [NeZero N] in
lemma trivF_transform {t : ℕ} (ht : t ∣ N) (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) (c d : ℤ) :
    trivF t (c * γ 1 1 - d * γ 1 0) (-(c * γ 0 1) + d * γ 0 0) = trivF t c d := by
  have htγ : (t : ℤ) ∣ γ 1 0 := dvd_trans (by exact_mod_cast ht) hγ
  obtain ⟨g, hg⟩ := htγ
  have hdet := det_SL γ
  simp only [trivF]
  have hiff : (t : ℤ) ∣ c * γ 1 1 - d * γ 1 0 ↔ (t : ℤ) ∣ c := by
    constructor
    · intro h
      have h1 : (t : ℤ) ∣ c * γ 1 1 := by
        have : (t : ℤ) ∣ d * γ 1 0 := ⟨d * g, by rw [hg]; ring⟩
        simpa using dvd_add h this
      have h2 : (t : ℤ) ∣ c * γ 1 1 * γ 0 0 - c * γ 0 1 * γ 1 0 :=
        dvd_sub (dvd_mul_of_dvd_left h1 _) ⟨c * γ 0 1 * g, by rw [hg]; ring⟩
      have : c * γ 1 1 * γ 0 0 - c * γ 0 1 * γ 1 0 = c := by linear_combination c * hdet
      rwa [this] at h2
    · intro h
      exact dvd_sub (dvd_mul_of_dvd_left h _) ⟨d * g, by rw [hg]; ring⟩
  simp only [hiff]

/-- **$G_2(z) - tG_2(tz) \in M_2(\Gamma_0(N))$** for $t \mid N$, $t \ge 1$ (as $E_{w_t}$). -/
@[kb "diamondshurman2005" "§4.6, Thm 4.6.2 (ψ = φ = 1, E_2(z) − tE_2(tz)) [unverified]"]
noncomputable def trivEisMF (t : ℕ) (ht0 : t ≠ 0) (ht : t ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) 2 where
  toFun := eis2 (trivW t)
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    change eis2 (trivW t) ∣[(2 : ℤ)] γ = eis2 (trivW t)
    rw [eis2_slash _ (totalSum_trivW ht0 ht)]
    congr 1
    have hp := trivF_periodic (N := N) ht
    ext x y
    obtain ⟨c, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨d, rfl⟩ := ZMod.intCast_surjective y
    rw [trivW, slashW_ofPer_intCast hp.1 hp.2, ofPer_intCast hp.1 hp.2,
      trivF_transform ht γ (dvd_gamma10_of_mem hγ)]
  holo' := mdifferentiable_eis2 _
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [eis2_slash _ (totalSum_trivW ht0 ht)]
    exact isBoundedAtImInfty_eis2 _

lemma trivEisMF_apply {t : ℕ} (ht0 : t ≠ 0) (ht : t ∣ N) (z : ℍ) :
    trivEisMF t ht0 ht z = ∑' c : ℤ, ∑' d : ℤ, trivF t c d * (((c : ℂ) * z + d) ^ 2)⁻¹ := by
  have hp := trivF_periodic (N := N) ht
  change eis2 (trivW t) z = _
  simp only [eis2, trivW, wt_ofPer hp.1 hp.2]

/-- The row of $E_{w_t}$: $\sum_d w_t(c,d)(cz+d)^{-2} = w_t(c)\sum_d(cz+d)^{-2}$. -/
lemma rowW_trivW {t : ℕ} (ht : t ∣ N) (c : ℤ) (z : ℍ) :
    rowW (trivW (N := N) t) c z = trivF t c 0 * rowSum z 0 c := by
  have hp := trivF_periodic (N := N) ht
  simp only [rowW, trivW, wt_ofPer hp.1 hp.2, rowSum, fs_zero_left, ← tsum_mul_left]
  rfl

/-- **The $q$-expansion of $E_{w_t}$:**
$E_{w_t}(z) = (1-t)\sum_d d^{-2} + 2(-2\pi i)^2\sum_{e \ge 1}\sigma^{w_t,1}(e)\,q^e$, $\sigma^{w_t,1}(e) = \sum_{d \mid e}w_t(e/d)d$. -/
theorem trivEisMF_eq_qExpansion {t : ℕ} (ht0 : t ≠ 0) (ht : t ∣ N) (z : ℍ) :
    trivEisMF t ht0 ht z =
      (1 - t) * ∑' d : ℤ, ((d : ℂ) ^ 2)⁻¹ +
        2 * (-2 * π * I) ^ 2 * ∑' e : ℕ+, sigmaTw (fun m => trivF t m 0) (fun _ => 1) e *
          cexp (2 * π * I * z) ^ (e : ℕ) := by
  have hp := trivF_periodic (N := N) ht
  have heven : ∀ c d, wt (trivW (N := N) t) (-c) (-d) = wt (trivW (N := N) t) c d := by
    intro c d; simp only [trivW, wt_ofPer hp.1 hp.2, trivF, dvd_neg]
  change eis2 (trivW t) z = _
  rw [eis2_eq_row0_add heven z, rowW_trivW ht 0 z]
  congr 1
  · simp [trivF, rowSum, fs_zero_left]
  · set q := cexp (2 * π * I * z)
    have hq : ‖q‖ < 1 := by
      rw [norm_cexp_two_pi_I]; exact Real.exp_lt_one_iff.mpr (by
        have := z.im_pos; have := Real.pi_pos; simp only [UpperHalfPlane.coe_im]; nlinarith)
    have hrow : ∀ c : ℕ+, rowW (trivW (N := N) t) ((c : ℕ) : ℤ) z =
        (-2 * π * I) ^ 2 * (trivF t (c : ℕ) 0 * ∑' n : ℕ+, (fun _ => (1 : ℂ)) (n : ℕ) * (n : ℕ) *
          q ^ ((c : ℕ) * n)) := by
      intro c
      rw [rowW_trivW ht, rowSum_zero_natCast z c.pos]
      have hs : Summable fun k : ℕ => (k : ℂ) * cexp (2 * π * I * ((c : ℕ) * (z : ℂ))) ^ k := by
        have hqc : ‖cexp (2 * π * I * ((c : ℕ) * (z : ℂ)))‖ < 1 := by
          rw [norm_cexp_two_pi_mul]; exact pow_lt_one₀ (Real.exp_pos _).le (exp_neg_two_pi_lt_one z)
            c.ne_zero
        simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqc
      rw [← tsum_zero_pnat_eq_tsum_nat hs]
      simp only [Nat.cast_zero, zero_mul, zero_add, one_mul]
      have : ∀ n : ℕ+, (n : ℂ) * cexp (2 * π * I * ((c : ℕ) * (z : ℂ))) ^ (n : ℕ) =
          ((n : ℕ) : ℂ) * q ^ ((c : ℕ) * n) := by
        intro n
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
        congr 2; push_cast; ring
      simp_rw [this]
      ring
    simp_rw [hrow]
    rw [tsum_mul_left]
    have hA : ∀ n : ℕ, ‖trivF t (n : ℤ) 0‖ ≤ 1 + t := by
      intro n
      simp only [trivF]
      split_ifs
      · calc ‖1 - (t : ℂ) * 1‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * 1‖ := norm_sub_le _ _
          _ = 1 + t := by simp
      · simp
    rw [tsum_tsum_twisted_eq (a := fun m : ℕ => trivF t (m : ℤ) 0) (b := fun _ => (1 : ℂ)) hA
      (fun _ => by simp) hq]
    ring

/-! ### Relation with Mathlib's $G_2$ and the form `G4`; the $I_4$ example -/

omit [NeZero N] in
lemma G2_eq_tsum_rowSum (z : ℍ) : EisensteinSeries.G2 z = ∑' c : ℤ, rowSum z 0 c := by
  have he : ∀ c : ℤ, EisensteinSeries.e2Summand c z = rowSum z 0 c := by
    intro c
    simp only [EisensteinSeries.e2Summand, EisensteinSeries.eisSummand, rowSum, fs_zero_left]
    refine tsum_congr fun d => ?_
    simp [zpow_neg]
  simp only [EisensteinSeries.G2, he]
  exact tsum_eq_of_summable_unconditional (L := SummationFilter.symmetricIcc ℤ) (summable_rowSum_zero z)

/-- **$E_{w_t}(z) = G_2(z) - tG_2(tz)$.** -/
theorem eis2_trivW_eq_G2 {t : ℕ} (ht0 : t ≠ 0) (ht : t ∣ N) (z : ℍ) :
    trivEisMF t ht0 ht z = EisensteinSeries.G2 z -
      t * EisensteinSeries.G2 ⟨(t : ℂ) * z, by
        simpa using mul_pos (show (0 : ℝ) < t by exact_mod_cast Nat.pos_of_ne_zero ht0) z.im_pos⟩ := by
  set tz : ℍ := ⟨(t : ℂ) * z, by
    simpa using mul_pos (show (0 : ℝ) < t by exact_mod_cast Nat.pos_of_ne_zero ht0) z.im_pos⟩
  change eis2 (trivW t) z = _
  rw [eis2_eq_tsum_rowW, G2_eq_tsum_rowSum, G2_eq_tsum_rowSum]
  have hs := summable_rowSum_zero z
  have hrow : ∀ c, rowW (trivW (N := N) t) c z =
      rowSum z 0 c - t * (if (t : ℤ) ∣ c then rowSum z 0 c else 0) := by
    intro c; rw [rowW_trivW ht]; simp only [trivF]; split_ifs <;> ring
  simp_rw [hrow]
  have hsupp : Function.support (fun c : ℤ => if (t : ℤ) ∣ c then rowSum z 0 c else 0) ⊆
      Set.range (fun m : ℤ => (t : ℤ) * m) := by
    intro c hc
    by_contra h
    apply hc
    have : ¬ (t : ℤ) ∣ c := fun ⟨m, hm⟩ => h ⟨m, hm.symm⟩
    simp [this]
  have hinj : Function.Injective (fun m : ℤ => (t : ℤ) * m) :=
    fun a b h => mul_left_cancel₀ (by exact_mod_cast ht0) h
  have hsub : Summable fun c : ℤ => if (t : ℤ) ∣ c then rowSum z 0 c else 0 :=
    Summable.of_norm_bounded hs.norm fun c => by split_ifs <;> simp
  rw [Summable.tsum_sub hs (hsub.mul_left _), tsum_mul_left, ← hinj.tsum_eq hsupp]
  congr 2
  refine tsum_congr fun m => ?_
  simp only [dvd_mul_right, ↓reduceIte, rowSum, Int.cast_mul, Int.cast_natCast]
  refine tsum_congr fun d => ?_
  congr 2
  rw [show ((tz : ℍ) : ℂ) = (t : ℂ) * z from rfl]
  ring

/-- **$E_{w_4} = 2\zeta(2)\,G$** with $G = E_2(z) - 4E_2(4z)$ the level-4 form `G4`. -/
theorem trivEisMF_four_eq_G4 (z : ℍ) :
    trivEisMF (N := 4) 4 (by norm_num) dvd_rfl z = 2 * riemannZeta 2 * G4 z := by
  rw [eis2_trivW_eq_G2]
  change _ = 2 * riemannZeta 2 * G4fun z
  rw [G4fun_apply]
  have hE : ∀ w : ℍ, EisensteinSeries.G2 w = 2 * riemannZeta 2 * EisensteinSeries.E2 w := by
    intro w
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 * riemannZeta 2 : ℂ) ≠ 0 := by
      rw [riemannZeta_two]; exact mul_ne_zero two_ne_zero (div_ne_zero (pow_ne_zero 2 hπ) (by norm_num))
    have hz : riemannZeta 2 ≠ 0 := right_ne_zero_of_mul h2
    simp only [EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hM : (M4 • z : ℍ) = ⟨(4 : ℂ) * z, by
      simpa using mul_pos (show (0 : ℝ) < 4 by norm_num) z.im_pos⟩ := by
    ext; rw [coe_M4_smul]
  rw [hE, hE, hM]
  push_cast
  ring

/-- **The $I_4$ example:** $\Theta_{I_4} = -\pi^{-2}E_{w_4}$; hence the $q$-coefficients of the Eisenstein series
$E_{I_4} := -\pi^{-2}E_{w_4}$ are $r_{I_4}(m) = a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$ for $m \ge 1$
(`repNum_Q4_eq_aE`), and its constant term at $i\infty$ is $1$. -/
theorem theta_sumSq_four_eq_trivEis (z : ℍ) :
    theta (sumSq 4) z = -((π : ℂ) ^ 2)⁻¹ * trivEisMF (N := 4) 4 (by norm_num) dvd_rfl z := by
  rw [trivEisMF_four_eq_G4, ← thetaMF_sumSq_four_apply, thetaMF_sumSq_four_eq, riemannZeta_two]
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [smul_apply, smul_eq_mul]
  field_simp
  ring

end QuadFormsKB.Siegel.EisensteinWt2
