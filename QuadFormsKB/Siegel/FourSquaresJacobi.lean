/-
# Jacobi's four-square theorem via modular forms

$r_4(m) = \#\{\vec{x} \in \mathbb{Z}^4 : x_0^2 + x_1^2 + x_2^2 + x_3^2 = m\} = 8 \sum_{d \mid m,\ 4 \nmid d} d$ for $m \ge 1$.

Route (Iwaniec, *Topics in Classical Automorphic Forms*, §3.4 / Ch. 11 [unverified]; Serre's argument for $E_8$
in `Siegel/E8.lean` adapted to level 4):

* `G4`: $G(\tau) = E_2(\tau) - 4E_2(4\tau) \in M_2(\Gamma_0(4))$, built from Mathlib's quasi-modular $E_2$
  (`EisensteinSeries.E2_slash_action`): with $M = \mathrm{diag}(4,1)$, $G = E_2 - E_2|_2 M$, and the defects
  $D_2(\gamma)$, $D_2(\gamma')|_2 M$ cancel for $\gamma \in \Gamma_0(4)$, $\gamma' = M\gamma M^{-1}$ (`G4fun_slash`).
* `qExpansion_G4_coeff`: $G = -3 - 24\sum_{n \ge 1}(\sigma_1(n) - 4\sigma_1(n/4))q^n$ (`g4c`).
* $f = \Theta_{I_4} + \tfrac13 G \in M_2(\Gamma_0(4))$ has $q$-expansion order $\ge 2$ ($r_4(0) = 1$, $r_4(1) = 8$), hence
  $f = 0$: its norm to level one (Mathlib's `ModularForm.norm`, `NormTrace.lean`) has weight $2[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(4)]
  \le 20$ (`index_Gamma0_four_le`: the index is $\le 10$, in fact $6$) and order $\ge 2$ at $\infty$, so vanishes by
  Mathlib's level-one Sturm bound (`eq_zero_of_qExpansion_coeff_zero_one`).
* `thetaMF_sumSq_four_eq`: $\Theta_{I_4} = -\tfrac13 G$; `repNum_sumSq_four_sigma`: $r_4(m) = 8\sigma_1(m) - 32\sigma_1(m/4)$;
  **`repNum_sumSq_four`**: $r_4(m) = 8\sum_{d \mid m,\ 4 \nmid d} d$ ($m \ge 1$).

The AWS notes' four-squares inputs (`Literature/AWS/FourSquares.lean`, `AWS.FourSquaresInputs`):
* `localDensity_Q4_two`: **the field `beta_two`** ($\beta_2(m) = 1$ for odd $m$, Lemma 2.7.6) is proved, from the dyadic
  Remark 3.4.1(a) at level 8 and an enumeration of $(\mathbb{Z}/8)^4$ (`decide +kernel`, no `native_decide`);
  `fourSquaresInputs_of_siegel`: only the field `siegel` remains an input.
* `r4_squarefree_of_jacobi`: the notes' conclusion (2.21)–(2.23), $r_Q(t) = 8\prod_{p\mid t}(p+1)$ for odd squarefree $t$,
  holds unconditionally (from Jacobi).
* Not done: the field `siegel` itself ($r_4(m) = \pi^2 m\prod_p\beta_p(m)$ for **all** $m \ge 1$) needs $\beta_p(m)$ for
  $p^2 \mid m$ and $\beta_2(m)$ for even $m$, which the local-density files do not yet compute.
-/
import QuadFormsKB.Siegel.ThetaGamma0
import QuadFormsKB.Siegel.E8
import QuadFormsKB.LocalDensity.BridgeDyadic

open Complex Matrix ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ArithmeticFunction.sigma Manifold
open SlashInvariantForm

namespace QuadFormsKB.Siegel

/-- $D_2(\gamma)$ is bounded at $i\infty$. -/
lemma isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) : IsBoundedAtImInfty (D2 γ) := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨2 * Real.pi, 1, fun z hz => ?_⟩
  by_cases hc : (γ 1 0 : ℝ) = 0
  · have : (γ 1 0 : ℂ) = 0 := by exact_mod_cast hc
    simp [D2, this, Real.pi_pos.le]
  · have hden : |(γ 1 0 : ℝ)| ≤ ‖denom γ z‖ := by
      have h1 : |(denom γ z).im| ≤ ‖denom γ z‖ := Complex.abs_im_le_norm _
      have h2 : (denom γ z).im = (γ 1 0 : ℝ) * z.im := by
        simp [ModularGroup.denom_apply]
      rw [h2, abs_mul, abs_of_pos z.im_pos] at h1
      nlinarith [abs_nonneg (γ 1 0 : ℝ)]
    have hpos : 0 < |(γ 1 0 : ℝ)| := abs_pos.mpr hc
    rw [D2, norm_div]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
      Complex.norm_intCast]
    rw [div_le_iff₀ (hpos.trans_le hden)]
    have := Real.pi_pos
    rw [Real.norm_eq_abs, abs_of_pos this]
    nlinarith


/-- $E_2 \mid_2 \gamma$ is bounded at $i\infty$ for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$. -/
lemma isBoundedAtImInfty_E2_slash (γ : SL(2, ℤ)) : IsBoundedAtImInfty (E2 ∣[(2 : ℤ)] γ) := by
  rw [E2_slash_action]
  exact isBoundedAtImInfty_E2.sub ((isBoundedAtImInfty_D2 γ).const_smul_left _)

/-- $E_2$ is bounded at every cusp of $\mathrm{SL}_2(\mathbb{Z})$. -/
lemma isBoundedAt_E2 {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : OnePoint.IsBoundedAt c E2 2 :=
  (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ => isBoundedAtImInfty_E2_slash γ

/-- The matrix $\mathrm{diag}(4, 1) \in \mathrm{GL}_2(\mathbb{R})$, acting by $\tau \mapsto 4\tau$. -/
noncomputable def M4 : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![4, 0; 0, 1] (by norm_num [det_fin_two])

lemma M4_det : (M4.det : ℝ) = 4 := by
  simp [M4, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_fin_two]

lemma coe_M4_smul (τ : ℍ) : ((M4 • τ : ℍ) : ℂ) = 4 * τ := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [M4_det]; norm_num)]
  simp [M4, Matrix.GeneralLinearGroup.mkOfDetNeZero, num, denom]

lemma M4_slash_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[(2 : ℤ)] M4) τ = 4 * f (M4 • τ) := by
  rw [ModularForm.slash_apply]
  have hd : denom M4 τ = 1 := by simp [M4, Matrix.GeneralLinearGroup.mkOfDetNeZero, denom]
  have hdet : 0 < (M4 : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp [M4, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_fin_two]
  have hσ : ∀ x, UpperHalfPlane.σ M4 x = x := by
    intro x; simp [UpperHalfPlane.σ, hdet]
  rw [hd, hσ, M4_det]
  norm_num
  ring


/-- For $\gamma = \begin{pmatrix} a & b \\ 4c_0 & d\end{pmatrix} \in \Gamma_0(4)$, the matrix
$\gamma' = \begin{pmatrix} a & 4b \\ c_0 & d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$, with $M\gamma = \gamma' M$ for
$M = \mathrm{diag}(4,1)$. -/
def conjM4 (γ : SL(2, ℤ)) (c0 : ℤ) (hc : γ 1 0 = 4 * c0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, 4 * γ 0 1; c0, γ 1 1], by
    have := γ.2; rw [det_fin_two] at this; rw [det_fin_two_of]; rw [hc] at this; linarith⟩

lemma mapGL_apply' (g : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (g i j : ℝ) :=
  rfl

lemma M4_mul_eq (γ : SL(2, ℤ)) (c0 : ℤ) (hc : γ 1 0 = 4 * c0) :
    M4 * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjM4 γ c0 hc) * M4 := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply']
  fin_cases i <;> fin_cases j <;>
    simp [M4, conjM4, Matrix.GeneralLinearGroup.mkOfDetNeZero, hc] <;> ring

lemma D2_conjM4_slash (γ : SL(2, ℤ)) (c0 : ℤ) (hc : γ 1 0 = 4 * c0) :
    D2 (conjM4 γ c0 hc) ∣[(2 : ℤ)] M4 = D2 γ := by
  ext τ
  rw [M4_slash_apply]
  have hden : denom (conjM4 γ c0 hc) ((M4 • τ : ℍ) : ℂ) = denom γ τ := by
    simp only [denom, coe_M4_smul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    simp [conjM4, hc, Matrix.SpecialLinearGroup.coe_mk]; ring
  simp only [D2, hden]
  simp [conjM4, hc]
  ring


/-- **The weight-2 level-4 Eisenstein series** $G(\tau) = E_2(\tau) - 4E_2(4\tau)$ (as a function on $\mathbb{H}$). -/
noncomputable def G4fun : ℍ → ℂ := E2 - E2 ∣[(2 : ℤ)] M4

lemma G4fun_apply (τ : ℍ) : G4fun τ = E2 τ - 4 * E2 (M4 • τ) := by
  simp [G4fun, M4_slash_apply]

lemma G4fun_slash (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    G4fun ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = G4fun := by
  have h4 : (4 : ℤ) ∣ γ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hγ
  obtain ⟨c0, hc⟩ := h4
  have hE : E2 ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
      E2 - (1 / (2 * riemannZeta 2)) • D2 γ := E2_slash_action γ
  have hEM : (E2 ∣[(2 : ℤ)] M4) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) =
      E2 ∣[(2 : ℤ)] M4 - (1 / (2 * riemannZeta 2)) • D2 γ := by
    rw [← SlashAction.slash_mul, M4_mul_eq γ c0 hc, SlashAction.slash_mul]
    have h1 : E2 ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (conjM4 γ c0 hc)) =
        E2 - (1 / (2 * riemannZeta 2)) • D2 (conjM4 γ c0 hc) := E2_slash_action _
    rw [h1, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.smul_slash,
      D2_conjM4_slash, ← sub_eq_add_neg]
    congr 2
    have hdet : 0 < (M4 : Matrix (Fin 2) (Fin 2) ℝ).det := by
      simp [M4, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_fin_two]
    simp [UpperHalfPlane.σ, hdet]
  rw [G4fun, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, hE, hEM]
  abel


open scoped Pointwise in
/-- $M\,\Gamma_0(4)\,M^{-1} \subseteq \mathrm{SL}_2(\mathbb{Z})$ for $M = \mathrm{diag}(4,1)$. -/
lemma conj_M4_Gamma0_le :
    ConjAct.toConjAct M4 • ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  intro x hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  obtain ⟨γ, hγ, hγx⟩ := hx
  have h4 : (4 : ℤ) ∣ γ 1 0 := by
    have hγ : γ ∈ CongruenceSubgroup.Gamma0 4 := hγ
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hγ
  obtain ⟨c0, hc⟩ := h4
  refine ⟨conjM4 γ c0 hc, ?_⟩
  have e : x = M4 * Matrix.SpecialLinearGroup.mapGL ℝ γ * M4⁻¹ := by
    have hγx' : Matrix.SpecialLinearGroup.mapGL ℝ γ = M4⁻¹ * x * M4 := by
      rw [hγx, ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv]
    rw [hγx']; group
  rw [e, M4_mul_eq γ c0 hc]; group

lemma OnePoint.IsBoundedAt.neg' {c : OnePoint ℝ} {f : ℍ → ℂ} {k : ℤ}
    (hf : OnePoint.IsBoundedAt c f k) : OnePoint.IsBoundedAt c (-f) k :=
  fun g hg => by
    have := (hf g hg).neg
    rw [SlashAction.neg_slash]; exact this

/-- **$G(\tau) = E_2(\tau) - 4E_2(4\tau) \in M_2(\Gamma_0(4))$.** Invariance: the defects $D_2$ of the
quasi-modular $E_2$ cancel (`G4fun_slash`); holomorphy from Mathlib's `E2_mdifferentiable`; boundedness at
every cusp from the boundedness of $E_2 \mid \gamma$ at $i\infty$ for $\gamma \in \mathrm{SL}_2(\mathbb{Z})$. -/
@[kb "iwaniec1997" "§3.4 / Ch. 11, Eisenstein series of weight 2 and level 4 [unverified]"]
noncomputable def G4 : ModularForm (CongruenceSubgroup.Gamma0 4) 2 where
  toFun := G4fun
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    exact G4fun_slash γ hγ
  holo' := E2_mdifferentiable.sub (E2_mdifferentiable.slash 2 M4)
  bdd_at_cusps' {c} hc := by
    have hc1 : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
    have hc2 : IsCusp (M4 • c) 𝒮ℒ := (hc.smul M4).mono conj_M4_Gamma0_le
    have h2 : OnePoint.IsBoundedAt c (E2 ∣[(2 : ℤ)] M4) 2 :=
      OnePoint.IsBoundedAt.smul_iff.mp (isBoundedAt_E2 hc2)
    rw [G4fun, sub_eq_add_neg]
    exact (isBoundedAt_E2 hc1).add (OnePoint.IsBoundedAt.neg' h2)


/-- The $q$-expansion coefficients of $E_2$: $1$, then $-24\sigma_1(m)$. -/
def e2c (m : ℕ) : ℂ := if m = 0 then 1 else -24 * σ 1 m

/-- The $q$-expansion coefficients of $G = E_2(\tau) - 4E_2(4\tau)$. -/
def g4c (n : ℕ) : ℂ := e2c n - 4 * (if 4 ∣ n then e2c (n / 4) else 0)

lemma qParam_one (τ : ℍ) : Function.Periodic.qParam 1 τ = cexp (2 * Real.pi * I * τ) := by
  simp [Function.Periodic.qParam]

lemma hasSum_E2 (τ : ℍ) :
    HasSum (fun m : ℕ => e2c m • Function.Periodic.qParam 1 τ ^ m) (E2 τ) := by
  simpa [qParam_one, e2c] using hasSum_qExpansion_E2 τ

lemma hasSum_E2_M4 (τ : ℍ) :
    HasSum (fun n : ℕ => (if 4 ∣ n then e2c (n / 4) else 0) • Function.Periodic.qParam 1 τ ^ n)
      (E2 (M4 • τ)) := by
  have h := hasSum_E2 (M4 • τ)
  have hq : Function.Periodic.qParam 1 (M4 • τ : ℍ) = Function.Periodic.qParam 1 τ ^ 4 := by
    rw [qParam_one, qParam_one, coe_M4_smul, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [hq] at h
  have hinj : Function.Injective (fun m : ℕ => 4 * m) := fun a b h => by simpa using h
  rw [← (hinj.hasSum_iff ?_)]
  · convert h using 2 with m
    simp [pow_mul]
  · intro n hn
    have : ¬ 4 ∣ n := by
      rintro ⟨m, rfl⟩; exact hn ⟨m, rfl⟩
    simp [this]

lemma hasSum_G4 (τ : ℍ) :
    HasSum (fun n : ℕ => g4c n • Function.Periodic.qParam 1 τ ^ n) (G4 τ) := by
  change HasSum _ (G4fun τ)
  rw [G4fun_apply]
  convert (hasSum_E2 τ).sub ((hasSum_E2_M4 τ).mul_left 4) using 1
  funext n
  simp only [g4c, smul_eq_mul]
  ring

lemma one_mem_strictPeriods_Gamma0 :
    (1 : ℝ) ∈ (((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  simp

/-- **The $q$-expansion of $G$:** $(qExpansion\ G)_n = $ `g4c n`. -/
lemma qExpansion_G4_coeff (n : ℕ) : (qExpansion 1 G4).coeff n = g4c n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0 hasSum_G4 n).symm

/-! ### The theta series side -/

lemma hasSum_thetaMF_sumSq_four (τ : ℍ) :
    HasSum (fun m : ℕ => (repNum (sumSq 4) m : ℂ) • Function.Periodic.qParam 1 τ ^ m)
      (thetaMF_sumSq_four τ) := by
  rw [thetaMF_sumSq_four_apply]
  convert hasSum_theta posDef_sumSq τ.im_pos using 2 with m
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- The $q$-expansion coefficients of $\Theta_{I_4}$ are $r_4(m)$. -/
lemma qExpansion_thetaMF_sumSq_four_coeff (m : ℕ) :
    (qExpansion 1 thetaMF_sumSq_four).coeff m = repNum (sumSq 4) m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0
    hasSum_thetaMF_sumSq_four m).symm

/-- The vectors $\pm\vec{e}_i$: $(i, s) \mapsto s\,\vec{e}_i$. -/
def signedBasis {n : ℕ} (p : Fin n × ℤˣ) : repSet (sumSq n) 1 :=
  ⟨fun j => if j = p.1 then (p.2 : ℤ) else 0, by
    change (sumSq n).eval _ = 1
    rw [eval_sumSq, Finset.sum_eq_single p.1 (fun j _ hj => by simp [hj]) (by simp)]
    simpa using Int.units_eq_one_or p.2⟩

/-- **$r_{I_n}(1) = 2n$:** the vectors of norm 1 are exactly the $\pm\vec{e}_i$. -/
theorem repNum_sumSq_one (n : ℕ) : repNum (sumSq n) 1 = 2 * n := by
  have hbij : Function.Bijective (signedBasis (n := n)) := by
    constructor
    · rintro ⟨i, s⟩ ⟨j, t⟩ h
      have h' := congrArg (fun v : repSet (sumSq n) 1 => (v : Fin n → ℤ)) h
      have hi := congrFun h' i
      simp only [signedBasis, ite_true] at hi
      by_cases hij : i = j
      · subst hij
        simp only [ite_true] at hi
        exact Prod.ext rfl (Units.ext hi)
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hij)] at hi
        exact absurd hi (Units.ne_zero s)
    · rintro ⟨v, hv⟩
      have hv' : ∑ i, v i ^ 2 = 1 := by
        have : (sumSq n).eval v = 1 := hv
        rwa [eval_sumSq] at this
      obtain ⟨i, hi1, hi0⟩ := exists_unique_nonzero_of_sum_sq_eq_one v hv'
      have hu : IsUnit (v i) := isUnit_iff_exists_inv.mpr ⟨v i, by rw [← sq]; exact hi1⟩
      refine ⟨(i, hu.unit), Subtype.ext (funext fun j => ?_)⟩
      by_cases hj : j = i
      · subst hj; simp [signedBasis]
      · simp [signedBasis, hj, hi0 j hj]
  rw [repNum, ← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Fintype.card_units_int, mul_comm]

/-! ### The index of $\Gamma_0(4)$ -/

/-- The first column of $g$ mod 4, up to sign. -/
def col4 (g : SL(2, ℤ)) : Finset (ZMod 4 × ZMod 4) :=
  {((g 0 0 : ZMod 4), (g 1 0 : ZMod 4)), (-(g 0 0 : ZMod 4), -(g 1 0 : ZMod 4))}

lemma col4_mem (g : SL(2, ℤ)) :
    col4 g ∈ (Finset.univ : Finset (ZMod 4 × ZMod 4)).image (fun w => ({w, -w} : Finset _)) :=
  Finset.mem_image.mpr ⟨((g 0 0 : ZMod 4), (g 1 0 : ZMod 4)), Finset.mem_univ _, rfl⟩

lemma card_image_pm : ((Finset.univ : Finset (ZMod 4 × ZMod 4)).image
    (fun w => ({w, -w} : Finset _))).card = 10 := by decide

lemma inv_mul_mem_Gamma0_of_col4 {g g' : SL(2, ℤ)} (h : col4 g = col4 g') :
    g⁻¹ * g' ∈ CongruenceSubgroup.Gamma0 4 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  have hm : ((g' 0 0 : ZMod 4), (g' 1 0 : ZMod 4)) ∈ col4 g := by rw [h]; simp [col4]
  have e : ((g⁻¹ * g') 1 0 : ℤ) = -g 1 0 * g' 0 0 + g 0 0 * g' 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp
  rw [e]
  push_cast
  simp only [col4, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> ring

/-- **$[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(4)] \le 10$** (in fact $= 6$): a coset $g\Gamma_0(4)$ is determined by the first
column of $g$ mod 4 up to sign. -/
theorem index_Gamma0_four_le : (CongruenceSubgroup.Gamma0 4).index ≤ 10 := by
  classical
  set S := (Finset.univ : Finset (ZMod 4 × ZMod 4)).image (fun w => ({w, -w} : Finset _))
  let ψ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 4 → S := fun Q => ⟨col4 Q.out, col4_mem _⟩
  have hψ : Function.Injective ψ := by
    intro Q Q' hQ
    have h : col4 Q.out = col4 Q'.out := congrArg Subtype.val hQ
    rw [← Quotient.out_eq Q, ← Quotient.out_eq Q']
    exact (QuotientGroup.eq).mpr (inv_mul_mem_Gamma0_of_col4 h)
  rw [Subgroup.index_eq_card]
  calc Nat.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 4) ≤ Nat.card S :=
        Nat.card_le_card_of_injective ψ hψ
    _ = 10 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_image_pm]

/-! ### Vanishing of forms in $M_2(\Gamma_0(4))$ of order $\ge 2$ at $\infty$ -/

local notation "𝒢4" => ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

lemma card_quot_Gamma0_four_le : Nat.card (𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) ≤ 10 := by
  have e : Nat.card (𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) = (𝒢4).relIndex 𝒮ℒ := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
  rw [e, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]
  exact index_Gamma0_four_le

lemma isBoundedAtImInfty_quotientFunc (f : ModularForm 𝒢4 2) (q : 𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) :
    IsBoundedAtImInfty (quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    rw [quotientFunc_mk]
    have hr : (r.val)⁻¹ ∈ 𝒮ℒ := inv_mem r.2
    have hc : IsCusp ((r.val)⁻¹ • OnePoint.infty) 𝒢4 := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact (isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩).smul_of_mem hr
    exact (OnePoint.isBoundedAt_iff rfl).mp (ModularFormClass.bdd_at_cusps f hc)

lemma mdiff_quotientFunc (f : ModularForm 𝒢4 2) (q : 𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) :
    MDiff (quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r => rw [quotientFunc_mk]; exact (ModularFormClass.holo f).slash 2 _

lemma T_mem_SL : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) ∈ 𝒮ℒ := ⟨_, rfl⟩

lemma T_mem_G4 : (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T) ∈ 𝒢4 :=
  ⟨ModularGroup.T, by
    show ModularGroup.T ∈ CongruenceSubgroup.Gamma0 4
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T], rfl⟩

lemma quotientFunc_T_apply (f : ModularForm 𝒢4 2) (q : 𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) (τ : ℍ) :
    quotientFunc f q (ModularGroup.T • τ) =
      quotientFunc f ((⟨_, T_mem_SL⟩ : 𝒮ℒ)⁻¹ • q) τ := by
  rw [← quotientFunc_smul f T_mem_SL q]
  change _ = (quotientFunc f q ∣[(2 : ℤ)] ModularGroup.T) τ
  rw [SL_slash_apply]
  have : denom ModularGroup.T τ = 1 := by
    simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    simp [ModularGroup.T]
  rw [this]; simp

/-- **A form in $M_2(\Gamma_0(4))$ whose $q$-expansion starts at $q^2$ vanishes.** Its norm to level one has weight
$2\,[\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(4)] \le 20$ and $q$-expansion order $\ge 2$ ($f$ times the product of the other
translates, which is $1$-periodic, holomorphic and bounded at $i\infty$), so it vanishes by Mathlib's level-one
Sturm bound (`ModularForm.sturm_bound_levelOne`); a form with zero norm is zero (`ModularForm.norm_eq_zero_iff`). -/
theorem eq_zero_of_qExpansion_coeff_zero_one (f : ModularForm 𝒢4 2)
    (h0 : (qExpansion 1 f).coeff 0 = 0) (h1 : (qExpansion 1 f).coeff 1 = 0) : f = 0 := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ)
  set x0 : 𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ := ⟦1⟧ with hx0
  set P : ℍ → ℂ := ∏ q ∈ Finset.univ.erase x0, quotientFunc f q with hP
  have hf0 : quotientFunc f x0 = f := by simp [hx0]
  have hN : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) = (f : ℍ → ℂ) * P := by
    rw [ModularForm.coe_norm, ← hf0, hP, Finset.mul_prod_erase _ _ (Finset.mem_univ x0)]
  -- P is 1-periodic
  have hPT : ∀ τ : ℍ, P (ModularGroup.T • τ) = P τ := by
    intro τ
    set g : 𝒮ℒ := (⟨_, T_mem_SL⟩ : 𝒮ℒ)⁻¹
    have hg : g • x0 = x0 := by
      rw [hx0]
      change (⟦g * 1⟧ : 𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) = ⟦1⟧
      rw [mul_one]
      refine Quotient.sound ((QuotientGroup.leftRel_apply).mpr ?_)
      rw [Subgroup.mem_subgroupOf]
      simp [g]
    simp only [hP, Finset.prod_apply, quotientFunc_T_apply]
    refine Finset.prod_nbij' (fun q => g • q) (fun q => g⁻¹ • q) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
      intro h; apply hq; rw [← hg] at h; exact smul_left_cancel g h
    · intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq ⊢
      intro h; apply hq; rw [← hg, ← h, smul_inv_smul]
    · intro q _; simp
    · intro q _; simp
    · intro q _; rfl
  have hPper : Function.Periodic (P ∘ ofComplex) 1 :=
    periodic_comp_ofComplex fun τ => by rw [← modular_T_smul, hPT]
  have hPhol : MDiff P := by
    rw [hP]
    exact MDifferentiable.prod fun q _ => mdiff_quotientFunc f q
  have hPbdd : IsBoundedAtImInfty P := by
    change P ∈ boundedAtImInftySubalgebra ℂ
    rw [hP]
    exact Subalgebra.prod_mem _ fun q _ => isBoundedAtImInfty_quotientFunc f q
  have hfA := ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_Gamma0
  have hPA := analyticAt_cuspFunction_zero one_pos hPper hPhol hPbdd
  have hq : qExpansion 1 (ModularForm.norm 𝒮ℒ f) = qExpansion 1 f * qExpansion 1 P := by
    rw [hN]; exact qExpansion_mul hfA hPA
  have hord : (2 : ℕ∞) ≤ (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order := by
    rw [hq, PowerSeries.order_mul]
    have : ((2 : ℕ) : ℕ∞) ≤ (qExpansion 1 f).order := by
      refine PowerSeries.nat_le_order _ _ fun i hi => ?_
      interval_cases i
      · exact h0
      · exact h1
    exact le_add_right this
  have hN0 : ModularForm.norm 𝒮ℒ f = 0 := by
    refine sturm_bound_levelOne (lt_of_lt_of_le ?_ hord)
    have hc := card_quot_Gamma0_four_le
    have : ((2 * (Nat.card (𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12) ≤ 1 := by
      rw [show (2 * (Nat.card (𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) : ℤ)).toNat =
        2 * Nat.card (𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) by omega]
      omega
    calc ((((2 * (Nat.card (𝒮ℒ ⧸ (𝒢4).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12 : ℕ)) : ℕ∞) ≤ (1 : ℕ) := by
          exact_mod_cast this
      _ < 2 := by norm_num
  have hz := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp hN0
  ext τ
  simpa using congrFun hz τ

/-! ### Jacobi's theorem -/

/-- **$\Theta_{I_4} = -\tfrac13 G$**, $G(\tau) = E_2(\tau) - 4E_2(4\tau)$. -/
@[kb "iwaniec1997" "§3.4 / Ch. 11, theta^4 as an Eisenstein series [unverified]"]
theorem thetaMF_sumSq_four_eq : thetaMF_sumSq_four = (-(1 / 3 : ℂ)) • G4 := by
  have hΓ := one_mem_strictPeriods_Gamma0
  have h := eq_zero_of_qExpansion_coeff_zero_one (thetaMF_sumSq_four + (1 / 3 : ℂ) • G4) ?_ ?_
  · ext τ
    have := congrArg (fun F : ModularForm _ 2 => F τ) h
    simp only [_root_.add_apply, _root_.smul_apply, _root_.zero_apply,
      smul_eq_mul] at this ⊢
    linear_combination this
  all_goals
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos hΓ, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos hΓ, map_add, PowerSeries.coeff_smul,
      qExpansion_thetaMF_sumSq_four_coeff, qExpansion_G4_coeff]
  · rw [Nat.cast_zero, repNum_zero_of_posDef posDef_sumSq]
    simp [g4c, e2c]; norm_num
  · rw [Nat.cast_one, repNum_sumSq_one]
    simp [g4c, e2c]; norm_num

/-- $r_4(m) = 8\sigma_1(m) - 32\sigma_1(m/4)$ (the last term only when $4 \mid m$), $m \ge 1$. -/
theorem repNum_sumSq_four_sigma {m : ℕ} (hm : 1 ≤ m) :
    (repNum (sumSq 4) m : ℂ) = 8 * σ 1 m - 32 * (if 4 ∣ m then (σ 1 (m / 4) : ℂ) else 0) := by
  have h := qExpansion_thetaMF_sumSq_four_coeff m
  rw [thetaMF_sumSq_four_eq, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Gamma0, PowerSeries.coeff_smul,
    qExpansion_G4_coeff] at h
  rw [← h]
  have hm0 : m ≠ 0 := by omega
  by_cases h4 : 4 ∣ m
  · have : m / 4 ≠ 0 := by omega
    simp [g4c, e2c, hm0, h4, this]; ring
  · simp [g4c, e2c, hm0, h4]; ring

/-- $\sum_{d \mid m,\ 4 \mid d} d = 4\sigma_1(m/4)$ if $4 \mid m$, else $0$. -/
lemma sum_divisors_four_dvd (m : ℕ) :
    ∑ d ∈ m.divisors.filter (4 ∣ ·), d = if 4 ∣ m then 4 * σ 1 (m / 4) else 0 := by
  split_ifs with h4
  · obtain ⟨k, rfl⟩ := h4
    have e : (4 * k).divisors.filter (4 ∣ ·) = k.divisors.map ⟨(4 * ·), mul_right_injective₀ (by norm_num)⟩ := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨hd, hk⟩, ⟨e, rfl⟩⟩
        refine ⟨e, ⟨(Nat.mul_dvd_mul_iff_left (by norm_num)).mp hd, by omega⟩, rfl⟩
      · rintro ⟨e, ⟨he, hk⟩, rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left 4 he, by omega⟩, dvd_mul_right 4 e⟩
    rw [e, Finset.sum_map, ArithmeticFunction.sigma_apply, Finset.mul_sum,
      show 4 * k / 4 = k by omega]
    simp
  · refine Finset.sum_eq_zero fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) h4

/-- $\sigma_1(m) = \sum_{d \mid m,\ 4 \nmid d} d + 4\sigma_1(m/4)\,[4 \mid m]$. -/
lemma sigma_one_eq_four (m : ℕ) :
    σ 1 m = ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d + (if 4 ∣ m then 4 * σ 1 (m / 4) else 0) := by
  rw [← sum_divisors_four_dvd, ArithmeticFunction.sigma_apply, add_comm,
    Finset.sum_filter_add_sum_filter_not]
  simp

/-- **Jacobi's four-square theorem:** for $m \ge 1$,
$$r_4(m) = \#\{\vec{x} \in \mathbb{Z}^4 : x_0^2 + x_1^2 + x_2^2 + x_3^2 = m\} = 8\sum_{d \mid m,\ 4 \nmid d} d.$$
*Proof:* $\Theta_{I_4} = -\tfrac13\bigl(E_2(\tau) - 4E_2(4\tau)\bigr)$ in $M_2(\Gamma_0(4))$ (`thetaMF_sumSq_four_eq`); compare
$q$-expansion coefficients ($E_2 = 1 - 24\sum\sigma_1(n)q^n$, Mathlib's `EisensteinSeries.E2_eq_tsum_cexp`). -/
@[kb "iwaniec1997" "§3.4, Thm. 3.4 / Ch. 11 (Jacobi's four squares theorem) [unverified]"]
theorem repNum_sumSq_four {m : ℕ} (hm : 1 ≤ m) :
    repNum (sumSq 4) m = 8 * ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d := by
  have h := repNum_sumSq_four_sigma hm
  have e := sigma_one_eq_four m
  have : (repNum (sumSq 4) m : ℂ) = ((8 * ∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d : ℕ) : ℂ) := by
    rw [h]
    have e' : (σ 1 m : ℂ) = ((∑ d ∈ m.divisors.filter (¬ 4 ∣ ·), d : ℕ) : ℂ) +
        (if 4 ∣ m then 4 * (σ 1 (m / 4) : ℂ) else 0) := by
      rw [e]; push_cast; split_ifs <;> simp
    rw [e']
    split_ifs <;> push_cast <;> ring
  exact_mod_cast this

/-- Sanity check: $r_4(4) = 24$ ($\pm 2\vec{e}_i$ and $(\pm1,\pm1,\pm1,\pm1)$; divisors $1, 2$ of $4$ not divisible by $4$). -/
theorem repNum_sumSq_four_four : repNum (sumSq 4) 4 = 24 := by
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, repNum_sumSq_four (by norm_num)]; decide

/-! ### The AWS notes' four-squares inputs: $\beta_2(m) = 1$ for odd $m$, and (2.21)–(2.23) from Jacobi -/

section AWSInputs

open LocalDensity
open scoped ArithmeticFunction.sigma

set_option maxRecDepth 100000 in
/-- Enumeration of $(\mathbb{Z}/8)^4$: each odd residue $c$ has $512$ representations as $x_0^2+x_1^2+x_2^2+x_3^2$. -/
lemma card_sumFourSq_zmod8 : ∀ c : ZMod 8, c.val % 2 = 1 →
    (Finset.univ.filter (fun x : ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8 =>
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + x.2.2.2 ^ 2 = c)).card = 512 := by
  decide +kernel

/-- $(\alpha^4) \simeq \alpha \times \alpha \times \alpha \times \alpha$. -/
def fin4Equiv (α : Type*) : (Fin 4 → α) ≃ α × α × α × α where
  toFun x := (x 0, x 1, x 2, x 3)
  invFun y := ![y.1, y.2.1, y.2.2.1, y.2.2.2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv y := rfl

/-- $r_{8}(m) = 512$ for $x_0^2+\dots+x_3^2$ and $m$ odd. -/
theorem repCount_Q4_eight {m : ℤ} (hm : Odd m) : repCount AWS.Q4 2 3 m = 512 := by
  classical
  unfold repCount
  have hc : ((m : ZMod (2 ^ 3))).val % 2 = 1 := by
    have h8 : (((m : ZMod 8)).val : ℤ) = m % 8 := ZMod.val_intCast m
    change ((m : ZMod 8)).val % 2 = 1
    obtain ⟨k, rfl⟩ := hm; omega
  have : ∀ x : Fin 4 → ZMod (2 ^ 3), AWS.Q4.evalIn (ZMod (2 ^ 3)) x = ((m : ℤ) : ZMod (2 ^ 3)) ↔
      (fin4Equiv _ x).1 ^ 2 + (fin4Equiv _ x).2.1 ^ 2 + (fin4Equiv _ x).2.2.1 ^ 2 +
        (fin4Equiv _ x).2.2.2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3)) := by
    intro x
    simp [AWS.Q4, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, sq,
      fin4Equiv]
  rw [Nat.card_congr ((Equiv.subtypeEquivRight this).trans ((fin4Equiv _).subtypeEquiv (q := fun y : ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) =>
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2.1 ^ 2 + y.2.2.2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3))) (fun _ => Iff.rfl))),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_sumFourSq_zmod8 _ hc

/-- **Lemma 2.7.6 of the AWS notes: $\beta_2(m) = 1$ for $m$ odd**, for $Q = x_0^2+\dots+x_3^2$.
*Proof:* dyadic Remark 3.4.1(a) (`DVR.localDensity_unit_unimodular`, level $K = 2e+1 = 3$) gives
$\beta_2(m) = r_8(m)/8^3$, and $r_8(m) = 512$ by enumerating $(\mathbb{Z}/8)^4$. -/
@[kb "hanke2011aws" "§2.7.5, Lemma 2.7.6, p. 39"]
theorem localDensity_Q4_two {m : ℤ} (hm : Odd m) : localDensity AWS.Q4 2 m = 1 := by
  have hd : AWS.Q4.map (Int.castRingHom ℤ_[2]) = QuadForm.diag fun _ : Fin 4 => (1 : ℤ_[2]) := by
    ext i j; simp only [AWS.Q4, QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hJ := DVR.isJordanFormW_diag_unit (fun _ : Fin 4 => (1 : ℤ_[2])) padic_two_irreducible
    (fun _ => not_two_dvd_one_padic)
  have he : (2 : ℤ_[2]) ^ 1 ∣ 2 ∧ ¬ (2 : ℤ_[2]) ^ (1 + 1) ∣ 2 := by
    have := padicInt_not_sq_dvd_two 2
    exact ⟨by simp, by exact_mod_cast this⟩
  have hm2 : ¬ (2 : ℤ_[2]) ∣ ((m : ℤ) : ℤ_[2]) := by
    intro h
    have h' := (padic_pow_dvd_int_iff 2 1 m).mp (by simpa using h)
    obtain ⟨k, rfl⟩ := hm
    omega
  have h := DVR.localDensity_unit_unimodular (QuadForm.diag fun _ : Fin 4 => (1 : ℤ_[2])) 2
    padic_two_irreducible ∅ hJ 1 (DVR.gradBound_ord_two hJ 1 he) _ hm2 3 le_rfl
  rw [localDensity_eq_padic]
  have hr := (repCount_eq_padic AWS.Q4 2 ∅ 3 m).1
  rw [hd] at hr
  rw [hd, Nat.cast_ofNat, h, q_padicInt]
  push_cast at hr
  rw [← hr, repCount_Q4_eight hm]
  norm_num

/-- For $m$ odd, $\sum_{d \mid m,\ 4 \nmid d} d = \sigma_1(m)$, so Jacobi gives $r_4(m) = 8\sigma_1(m)$. -/
theorem repNum_sumSq_four_odd {m : ℕ} (hm : Odd m) : repNum (sumSq 4) m = 8 * σ 1 m := by
  have h1 : 1 ≤ m := hm.pos
  have h4 : ¬ 4 ∣ m := by
    rintro ⟨k, rfl⟩; exact (Nat.not_even_iff_odd.mpr hm) ⟨2 * k, by ring⟩
  rw [repNum_sumSq_four h1, sigma_one_eq_four]
  simp [h4]

/-- **The AWS notes' (2.21)–(2.23) unconditionally:** $r_Q(t) = 8\prod_{p \mid t}(p+1)$ for odd squarefree $t$, from
Jacobi's theorem (no `FourSquaresInputs` needed; compare `AWS.r4_squarefree`). -/
@[kb "hanke2011aws" "§2.7.5, (2.21)-(2.23), p. 40"]
theorem r4_squarefree_of_jacobi (t : ℕ) (ht : Odd t) (hsq : Squarefree t) :
    (AWS.r4 t : ℂ) = 8 * ∏ p ∈ t.primeFactors, ((p : ℂ) + 1) := by
  rw [← repNum_Q4, ← sumSq_four, repNum_sumSq_four_odd ht,
    ← ArithmeticFunction.IsMultiplicative.prod_primeFactors ArithmeticFunction.isMultiplicative_sigma hsq]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hpp
  rw [pow_one] at this
  rw [this]
  simp [Finset.sum_range_succ, add_comm]

/-- **The `beta_two` field of `AWS.FourSquaresInputs` is discharged:** only Siegel's formula for $I_4$
(the field `siegel`) remains an input. -/
theorem fourSquaresInputs_of_siegel
    (h : ∀ m : ℕ, 0 < m → (AWS.r4 m : ℂ) = ((Real.pi ^ 2 * m : ℝ) : ℂ) *
      ∏' p : AWS.PrimeIdx, ((localDensity AWS.Q4 p m : ℝ) : ℂ)) :
    AWS.FourSquaresInputs :=
  ⟨h, fun m hm => localDensity_Q4_two (by exact_mod_cast hm.natCast)⟩

end AWSInputs

end QuadFormsKB.Siegel
