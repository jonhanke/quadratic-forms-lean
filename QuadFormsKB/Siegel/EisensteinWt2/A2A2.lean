/-
# The example $A_2 \oplus A_2$: level 3, trivial character (deliverable 4)

$Q = A_2 \oplus A_2 = x_0^2 + x_0x_1 + x_1^2 + x_2^2 + x_2x_3 + x_3^2$ (`a2a2`, level 3, $\chi_Q = 1$). The Eisenstein space of
$M_2(\Gamma_0(3))$ is spanned by $E_{w_3} = G_2(z) - 3G_2(3z)$ (`trivEisMF 3`), and
$$E_Q := -\frac{3}{2\pi^2}E_{w_3} = 1 + 12\sum_{e \ge 1}\bigl(\sigma_1(e) - 3\sigma_1(e/3)\bigr)q^e$$
(`eisA2A2_eq_qExpansion`, with $\sigma_1(e) - 3\sigma_1(e/3)$ written as $\sigma^{w_3,1}(e) = \sum_{d\mid e}w_3(e/d)\,d$).

**Cuspidality.** $\Theta_{\mathrm{Gen}(Q)} - E_Q$ vanishes at every cusp (`isZeroAtImInfty_thetaGen_sub_eisA2A2`). The cusps of
$\Gamma_0(3)$ are $\infty$ and $0$: every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $3 \nmid \gamma_{10}$ is $\gamma_0ST^k$ with
$\gamma_0 \in \Gamma_0(3)$ (`exists_gamma0_mul_S_mul_T`), so a $\Gamma_0(3)$-invariant $f$ has the constant term of
$f|S$ at $\gamma$ (`tendsto_slash_of_gamma0_prime`). The constant terms are
* at $\infty$: $1$ for both ($r_Q(0) = 1$; $E_Q$ normalized);
* at $0$: $\Theta_Q|S \to M_A(0, 1) = (-i/2)^2(\det A)^{-1/2} = -\tfrac14\cdot\tfrac43 = -\tfrac13$ (`tendsto_theta_cusp`,
  $\det A = 9/16$), and $E_Q|S \to -\frac{3}{2\pi^2}\sum_n\frac{1 - 3\cdot\mathbf 1_{3\mid n}}{n^2} = -\frac{3}{2\pi^2}\cdot\frac23\cdot\frac{\pi^2}{3} = -\tfrac13$
  (`tendsto_eis2_slash`).
Then $\Theta_{\mathrm{Gen}(Q)} = \Theta_Q - (\Theta_Q - \Theta_{\mathrm{Gen}(Q)})$ and the bracket vanishes at every cusp
(`isZeroAtImInfty_theta_sub_slash`).

*Not done here:* the identification of the $q$-coefficients $12\sigma^{w_3,1}(m)$ with the local-density products
$\beta_\infty(m)\prod_p\beta_p(m)$ (needs $\beta_2$, $\beta_3$ of $A_2\oplus A_2$), and $S_2(\Gamma_0(3)) = 0$.
-/
import QuadFormsKB.Siegel.EisensteinWt2.Trivial
import QuadFormsKB.Siegel.ThetaCharacter
import QuadFormsKB.Siegel.ThetaCuspidal
import Mathlib.NumberTheory.ModularForms.Identities
import QuadFormsKB.Siegel.GenusFinite

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups

namespace QuadFormsKB.Siegel.EisensteinWt2

open QuadFormsKB.Siegel

/-! ### Reduction of the cusps of $\Gamma_0(p)$ to $\infty$ and $0$ -/

/-- Every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $p \nmid \gamma_{10}$ ($p$ prime) is $\gamma_0\,S\,T^k$ with $\gamma_0 \in \Gamma_0(p)$. -/
lemma exists_gamma0_mul_S_mul_T {p : ℕ} [hp : Fact p.Prime] (γ : SL(2, ℤ)) (hγ : ¬ (p : ℤ) ∣ γ 1 0) :
    ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 p ∧ ∃ k : ℤ,
      γ = γ₀ * ModularGroup.S * ModularGroup.T ^ k := by
  have hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set k : ℤ := ((((γ 1 1 : ℤ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p)⁻¹).val : ℤ) with hkdef
  have hkx : ((k : ℤ) : ZMod p) = ((γ 1 1 : ℤ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p)⁻¹ := by
    rw [hkdef, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hk : (((γ 1 1 - k * γ 1 0 : ℤ)) : ZMod p) = 0 := by
    push_cast
    rw [hkx]
    field_simp
    ring
  have hSS : (ModularGroup.S * ModularGroup.S : SL(2, ℤ)) = -1 := by
    ext i j
    have := congr_fun (congr_fun ModularGroup.S_mul_S_eq i) j
    simpa using this
  refine ⟨-(γ * ModularGroup.T ^ (-k) * ModularGroup.S), ?_, k, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
    simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    rw [← neg_eq_zero, ← hk]
    push_cast
    ring
  · have e : -(γ * ModularGroup.T ^ (-k) * ModularGroup.S) * ModularGroup.S * ModularGroup.T ^ k =
        -(γ * ModularGroup.T ^ (-k) * (ModularGroup.S * ModularGroup.S) * ModularGroup.T ^ k) := by
      simp only [neg_mul, mul_assoc]
    rw [e, hSS, mul_neg, mul_one, neg_mul, neg_neg]
    group

/-- Slashing by $T^k$ does not change the limit at $i\infty$. -/
lemma tendsto_slash_T_zpow {g : ℍ → ℂ} {L : ℂ} (h : Tendsto g UpperHalfPlane.atImInfty (𝓝 L)) (k : ℤ) :
    Tendsto (g ∣[(2 : ℤ)] (ModularGroup.T ^ k)) UpperHalfPlane.atImInfty (𝓝 L) := by
  have hmap : Tendsto (fun τ : ℍ => ModularGroup.T ^ k • τ) UpperHalfPlane.atImInfty
      UpperHalfPlane.atImInfty := by
    rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
    refine (tendsto_comap (f := UpperHalfPlane.im)).congr fun τ => ?_
    show τ.im = (ModularGroup.T ^ k • τ).im
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  refine (h.comp hmap).congr fun τ => ?_
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, ModularGroup.coe_T_zpow]
  simp

/-- **Constant terms of a $\Gamma_0(p)$-invariant form** ($p$ prime, weight 2): if $f|\gamma_0 = f$ on $\Gamma_0(p)$,
$f \to L_\infty$ and $f|S \to L_0$ at $i\infty$, then $f|\gamma \to L_\infty$ if $p \mid \gamma_{10}$ and $\to L_0$ otherwise. -/
theorem tendsto_slash_of_gamma0_prime {p : ℕ} [Fact p.Prime] {f : ℍ → ℂ}
    (hf : ∀ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 p → f ∣[(2 : ℤ)] γ₀ = f) {L₁ L₂ : ℂ}
    (h₁ : Tendsto f UpperHalfPlane.atImInfty (𝓝 L₁))
    (h₂ : Tendsto (f ∣[(2 : ℤ)] ModularGroup.S) UpperHalfPlane.atImInfty (𝓝 L₂)) (γ : SL(2, ℤ)) :
    Tendsto (f ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (if (p : ℤ) ∣ γ 1 0 then L₁ else L₂)) := by
  split_ifs with h
  · have hγ : γ ∈ CongruenceSubgroup.Gamma0 p := by
      rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
    rw [hf γ hγ]; exact h₁
  · obtain ⟨γ₀, hγ₀, k, rfl⟩ := exists_gamma0_mul_S_mul_T γ h
    rw [SlashAction.slash_mul, SlashAction.slash_mul, hf γ₀ hγ₀]
    exact tendsto_slash_T_zpow h₂ k

/-! ### $A_2 \oplus A_2$ -/

theorem a2a2_eval (x : Fin 4 → ℤ) :
    a2a2.eval x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + x 2 ^ 2 + x 2 * x 3 + x 3 ^ 2 := by
  simp [QuadForm.evalIn, a2a2, QuadForm.ofUpper, Fin.sum_univ_four]
  ring

/-- $A_2 \oplus A_2$ is positive definite: $4Q = (2x_0+x_1)^2 + 3x_1^2 + (2x_2+x_3)^2 + 3x_3^2$. -/
theorem a2a2_posDef : IntQF.PosDef a2a2 := by
  intro x hx
  rw [a2a2_eval]
  by_contra hle
  rw [not_lt] at hle
  have h1 := sq_nonneg (2 * x 0 + x 1)
  have h2 := sq_nonneg (x 1)
  have h3 := sq_nonneg (2 * x 2 + x 3)
  have h4 := sq_nonneg (x 3)
  have e2 : x 1 ^ 2 = 0 := by nlinarith
  have e4 : x 3 ^ 2 = 0 := by nlinarith
  have e1 : (2 * x 0 + x 1) ^ 2 = 0 := by nlinarith
  have e3 : (2 * x 2 + x 3) ^ 2 = 0 := by nlinarith
  simp only [pow_eq_zero_iff two_ne_zero] at e1 e2 e3 e4
  apply hx
  ext i; fin_cases i <;> simp <;> omega

lemma isThetaLevel_a2a2 : IsThetaLevel a2a2 3 := level_a2a2 ▸ isThetaLevel_level a2a2_posDef

lemma thetaChi_a2a2 (d : ℤ) (hd : IsCoprime d (3 : ℕ)) : thetaChi a2a2 2 3 d = 1 := by
  obtain ⟨ho, hmod, hcop⟩ := oddRep_spec (by norm_num : 0 < 3) hd
  rw [thetaChi_eq_chi a2a2_posDef rfl (by norm_num) isThetaLevel_a2a2 hd ho hmod]
  exact chi_a2a2 (Nat.Coprime.symm hcop)

/-- $\Theta_{A_2\oplus A_2}\,|_2\,\gamma = \Theta_{A_2\oplus A_2}$ for $\gamma \in \Gamma_0(3)$. -/
lemma thetaH_a2a2_slash {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 3) :
    thetaH a2a2 ∣[(2 : ℤ)] γ = thetaH a2a2 := by
  have h := thetaH_slash_gamma0 a2a2_posDef (k := 2) rfl (by norm_num) isThetaLevel_a2a2 hγ
  have hcop : IsCoprime (γ 1 1) ((3 : ℕ) : ℤ) := isCoprime_of_gamma0 (dvd_gamma10_of_mem hγ)
  rw [thetaChi_a2a2 _ hcop] at h
  simpa using h

/-- The theta multiplier at the cusp $0$: $M_A(0, 1) = -1/3$. -/
lemma thetaMult_a2a2_zero_one : thetaMult (gramMatrix a2a2) 2 0 1 = -1 / 3 := by
  have hdet : (gramMatrix a2a2).det = 9 / 16 := by
    rw [det_gramMatrix, det_hessian_a2a2]; norm_num
  have hsq : Real.sqrt (9 / 16 : ℝ) = 3 / 4 := by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hG : gaussSum (gramMatrix a2a2) 0 1 0 = 1 := by
    simp [gaussSum]
  rw [thetaMult, hdet, hsq, hG]
  push_cast
  ring_nf
  rw [I_sq]; norm_num

lemma tendsto_thetaH_a2a2_S :
    Tendsto (thetaH a2a2 ∣[(2 : ℤ)] ModularGroup.S) UpperHalfPlane.atImInfty (𝓝 (-1 / 3)) := by
  have h := tendsto_theta_cusp a2a2_posDef (k := 2) rfl (a := 0) (b := -1) (d := 0) (c := 1)
    (by norm_num)
  rw [thetaMult_a2a2_zero_one] at h
  refine h.congr fun τ => ?_
  rw [SlashInvariantForm.slash_S_apply]
  simp only [thetaH]
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  push_cast
  rw [zpow_neg, zpow_two, ← sq]
  congr 2
  · simp only [add_zero, zero_mul, zero_add]
    field_simp
  · ring

/-- **The Eisenstein series of $A_2 \oplus A_2$:** $E_Q = -\frac{3}{2\pi^2}\bigl(G_2(z) - 3G_2(3z)\bigr) \in M_2(\Gamma_0(3))$. -/
@[kb "diamondshurman2005" "§4.6 (E_2(z) − 3E_2(3z), level 3) [unverified]"]
noncomputable def eisA2A2 : ModularForm (CongruenceSubgroup.Gamma0 3) 2 :=
  (-(3 / (2 * (π : ℂ) ^ 2))) • trivEisMF (N := 3) 3 (by norm_num) dvd_rfl

lemma tsum_int_inv_sq : ∑' n : ℤ, ((n : ℂ) ^ 2)⁻¹ = (π : ℂ) ^ 2 / 3 := by
  have h := EisensteinSeries.e2Summand_zero_eq_two_riemannZeta_two UpperHalfPlane.I
  rw [riemannZeta_two] at h
  rw [show (π : ℂ) ^ 2 / 3 = 2 * ((π : ℂ) ^ 2 / 6) by ring, ← h]
  simp [EisensteinSeries.e2Summand, EisensteinSeries.eisSummand, zpow_neg]

lemma tsum_int_inv_sq_three_dvd :
    ∑' n : ℤ, (if (3 : ℤ) ∣ n then ((n : ℂ) ^ 2)⁻¹ else 0) = (π : ℂ) ^ 2 / 27 := by
  have hsupp : Function.support (fun n : ℤ => if (3 : ℤ) ∣ n then ((n : ℂ) ^ 2)⁻¹ else 0) ⊆
      Set.range (fun m : ℤ => 3 * m) := by
    intro n hn
    by_contra h
    apply hn
    have : ¬ (3 : ℤ) ∣ n := fun ⟨m, hm⟩ => h ⟨m, hm.symm⟩
    simp [this]
  have hinj : Function.Injective (fun m : ℤ => 3 * m) := fun a b h => by simpa using h
  rw [← hinj.tsum_eq hsupp]
  simp only [dvd_mul_right, ↓reduceIte, Int.cast_mul, Int.cast_ofNat, mul_pow, mul_inv]
  rw [tsum_mul_left, tsum_int_inv_sq]
  ring

lemma eisA2A2_apply (z : ℍ) :
    eisA2A2 z = -(3 / (2 * (π : ℂ) ^ 2)) * eis2 (trivW (N := 3) 3) z := rfl

lemma tendsto_eisA2A2_atImInfty : Tendsto eisA2A2 UpperHalfPlane.atImInfty (𝓝 1) := by
  have hp := trivF_periodic (N := 3) (t := 3) dvd_rfl
  have h := (tendsto_eis2_atImInfty (trivW (N := 3) 3)).const_mul (-(3 / (2 * (π : ℂ) ^ 2)))
  simp only [trivW, wt_ofPer hp.1 hp.2, trivF, dvd_zero, ↓reduceIte] at h
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [tsum_mul_left, tsum_int_inv_sq] at h
  have hv : -(3 / (2 * (π : ℂ) ^ 2)) * ((1 - ((3 : ℕ) : ℂ) * 1) * ((π : ℂ) ^ 2 / 3)) = 1 := by
    field_simp; push_cast; ring
  rw [hv] at h
  exact h.congr fun x => (eisA2A2_apply x).symm

lemma tendsto_eisA2A2_S :
    Tendsto (⇑eisA2A2 ∣[(2 : ℤ)] ModularGroup.S) UpperHalfPlane.atImInfty (𝓝 (-1 / 3)) := by
  have hp := trivF_periodic (N := 3) (t := 3) dvd_rfl
  have h := tendsto_eis2_slash (trivW (N := 3) 3) (totalSum_trivW (by norm_num) dvd_rfl) ModularGroup.S
  have h' := h.const_mul (-(3 / (2 * (π : ℂ) ^ 2)))
  have hfun : (⇑eisA2A2 ∣[(2 : ℤ)] ModularGroup.S) =
      fun τ => -(3 / (2 * (π : ℂ) ^ 2)) * (eis2 (trivW (N := 3) 3) ∣[(2 : ℤ)] ModularGroup.S) τ := by
    ext τ
    rw [show (⇑eisA2A2 : ℍ → ℂ) = (-(3 / (2 * (π : ℂ) ^ 2))) • eis2 (trivW (N := 3) 3) from rfl,
      ModularForm.SL_smul_slash]
    rfl
  rw [hfun]
  convert h' using 2
  simp only [trivW, wt_ofPer hp.1 hp.2, trivF, ModularGroup.S]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, dvd_neg]
  have hs : ∑' n : ℤ, (1 - (3 : ℂ) * (if (3 : ℤ) ∣ n then 1 else 0)) * ((n : ℂ) ^ 2)⁻¹ =
      (π : ℂ) ^ 2 / 3 - 3 * ((π : ℂ) ^ 2 / 27) := by
    rw [← tsum_int_inv_sq, ← tsum_int_inv_sq_three_dvd]
    have hs1 : Summable fun n : ℤ => ((n : ℂ) ^ 2)⁻¹ := by
      have := EisensteinSeries.linear_right_summable (0 : ℂ) 0 (k := 2) le_rfl
      simpa [zpow_ofNat] using this
    have hs2 : Summable fun n : ℤ => if (3 : ℤ) ∣ n then ((n : ℂ) ^ 2)⁻¹ else 0 :=
      Summable.of_norm_bounded hs1.norm fun n => by split_ifs <;> simp; positivity
    rw [← Summable.tsum_mul_left _ hs2, ← Summable.tsum_sub hs1 (hs2.mul_left 3)]
    refine tsum_congr fun n => ?_
    split_ifs <;> ring
  push_cast
  rw [hs]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- **The $q$-expansion of $E_{A_2\oplus A_2}$:** $E_Q(z) = 1 + 12\sum_{e \ge 1}\sigma^{w_3,1}(e)\,q^e$, with
$\sigma^{w_3,1}(e) = \sum_{d\mid e}w_3(e/d)\,d = \sigma_1(e) - 3\sigma_1(e/3)$. -/
theorem eisA2A2_eq_qExpansion (z : ℍ) :
    eisA2A2 z = 1 + 12 * ∑' e : ℕ+, sigmaTw (fun m => trivF 3 m 0) (fun _ => 1) e *
      cexp (2 * π * I * z) ^ (e : ℕ) := by
  rw [eisA2A2_apply, show eis2 (trivW (N := 3) 3) z = trivEisMF (N := 3) 3 (by norm_num) dvd_rfl z from rfl,
    trivEisMF_eq_qExpansion, tsum_int_inv_sq]
  set S := ∑' e : ℕ+, sigmaTw (fun m => trivF 3 m 0) (fun _ => 1) e * cexp (2 * π * I * z) ^ (e : ℕ)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **$\Theta_{A_2\oplus A_2} - E_Q$ vanishes at every cusp.** -/
theorem isZeroAtImInfty_theta_sub_eisA2A2 (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty ((thetaH a2a2 - ⇑eisA2A2) ∣[(2 : ℤ)] γ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : ∀ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 3 →
      (thetaH a2a2 - ⇑eisA2A2) ∣[(2 : ℤ)] γ₀ = thetaH a2a2 - ⇑eisA2A2 := by
    intro γ₀ hγ₀
    rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, thetaH_a2a2_slash hγ₀,
      ← sub_eq_add_neg]
    congr 1
    exact SlashInvariantForm.slash_action_eqn eisA2A2 _ ⟨γ₀, hγ₀, rfl⟩
  have h₁ : Tendsto (thetaH a2a2 - ⇑eisA2A2) UpperHalfPlane.atImInfty (𝓝 (1 - 1)) :=
    (tendsto_theta_atImInfty a2a2_posDef).sub tendsto_eisA2A2_atImInfty
  have h₂ : Tendsto ((thetaH a2a2 - ⇑eisA2A2) ∣[(2 : ℤ)] ModularGroup.S) UpperHalfPlane.atImInfty
      (𝓝 (-1 / 3 - -1 / 3)) := by
    rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]
    exact tendsto_thetaH_a2a2_S.sub tendsto_eisA2A2_S
  have h := tendsto_slash_of_gamma0_prime hf h₁ h₂ γ
  simp only [sub_self, ite_self] at h
  exact h

/-- **$\Theta_{\mathrm{Gen}(A_2\oplus A_2)} - E_Q$ is cuspidal:** it vanishes at every cusp. -/
@[kb "hanke2004" "(4.3)–(4.5), p. 365 (Θ_Gen − E cuspidal), example A₂ ⊕ A₂ [unverified]"]
theorem isZeroAtImInfty_thetaGen_sub_eisA2A2 (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
      ((fun τ : ℍ => thetaGen a2a2 τ - eisA2A2 τ) ∣[(2 : ℤ)] γ) := by
  have hF := genusFinite a2a2_posDef
  have hsplit : (fun τ : ℍ => thetaGen a2a2 τ - eisA2A2 τ) =
      (thetaH a2a2 - ⇑eisA2A2) - fun τ : ℍ => ((mass a2a2 : ℂ))⁻¹ *
        ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℂ))⁻¹ * (thetaH a2a2 - thetaH c.out) τ := by
    ext τ
    simp only [Pi.sub_apply, thetaH]
    rw [← theta_sub_thetaGen a2a2_posDef hF]
    ring
  rw [hsplit, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]
  have h1 := isZeroAtImInfty_theta_sub_eisA2A2 γ
  suffices h2 : UpperHalfPlane.IsZeroAtImInfty ((fun τ : ℍ => ((mass a2a2 : ℂ))⁻¹ *
      ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℂ))⁻¹ * (thetaH a2a2 - thetaH c.out) τ) ∣[(2 : ℤ)] γ) by
    have := Filter.Tendsto.sub h1 h2
    rw [sub_zero] at this
    exact this
  have hlin : (fun τ : ℍ => ((mass a2a2 : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
      ((c.autCard : ℂ))⁻¹ * (thetaH a2a2 - thetaH c.out) τ) ∣[(2 : ℤ)] γ =
      fun τ => ((mass a2a2 : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
        ((c.autCard : ℂ))⁻¹ * ((thetaH a2a2 - thetaH c.out) ∣[(2 : ℤ)] γ) τ := by
    ext τ
    simp only [ModularForm.SL_slash_apply, Finset.sum_mul, mul_assoc]
  rw [hlin]
  have : Tendsto (fun τ : ℍ => ((mass a2a2 : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
      ((c.autCard : ℂ))⁻¹ * ((thetaH a2a2 - thetaH c.out) ∣[(2 : ℤ)] γ) τ)
      UpperHalfPlane.atImInfty (𝓝 (((mass a2a2 : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
        ((c.autCard : ℂ))⁻¹ * 0)) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun c hc => tendsto_const_nhds.mul ?_)
    exact isZeroAtImInfty_theta_sub_slash a2a2_posDef
      (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc)) (k := 2) rfl γ
  simp only [mul_zero, Finset.sum_const_zero] at this
  exact this

end QuadFormsKB.Siegel.EisensteinWt2
