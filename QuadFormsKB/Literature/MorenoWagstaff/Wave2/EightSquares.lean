/-
# Moreno–Wagstaff 2005, (6.4): Jacobi's eight-squares formula

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), (6.4), printed p. 186.

**Statement.** For $n \ge 1$,
$$r_8(n) = \#\{\vec{x} \in \mathbb{Z}^8 : x_0^2 + \dots + x_7^2 = n\} = 16\sum_{d \mid n} (-1)^{n+d} d^3,$$
with $r_8(n)$ = `Siegel.repNum (Siegel.sumSq 8) n`.

**Route** (the weight-4 analogue of Jacobi's four-squares theorem, `Siegel/FourSquaresJacobi.lean`, whose proof pattern
is copied here and generalized from weight 2 to weight 4):
* `thetaMF_sumSq_eight`: $\Theta_{I_8} \in M_4(\Gamma_0(4))$ (`thetaMFGamma0`; $\det H = 2^8 = 16^2$, trivial character).
* `Eis8`: $\mathcal{E} = E_4(\tau) - 2E_4(2\tau) + 16E_4(4\tau) \in M_4(\Gamma_0(4))$, built from Mathlib's level-one
  $E_4$ by slashing with $\mathrm{diag}(2,1)$ and $\mathrm{diag}(4,1)$ (`ModularForm.translate`,
  `ModularForm.restrict`), using $E_4 \mid_4 \mathrm{diag}(d,1) = d^3 E_4(d\tau)$. As $E_4$ is a genuine modular form
  there is no $E_2$-type defect.
* `eq_zero_of_qExpansion_coeff_lt_four`: a form in $M_4(\Gamma_0(4))$ whose $q$-expansion coefficients $0,1,2,3$ vanish is
  zero (norm to level one has weight $\le 40$, Mathlib's level-one Sturm bound `ModularForm.sturm_bound_levelOne`;
  index bound `index_Gamma0_four_le` $\le 10$).
* The coefficients $r_8(0) = 1$, $r_8(1) = 16$ (`repNum_sumSq_one`), $r_8(2) = 112$, $r_8(3) = 448$ (a finite count over
  $\{-1,0,1\}^8$, `decide +kernel`) match $\tfrac1{15}\mathcal{E}$, so $\Theta_{I_8} = \tfrac1{15}\mathcal{E}$
  (`thetaMF_sumSq_eight_eq`).
* `repNum_sumSq_eight_sigma`: $r_8(n) = 16\bigl(\sigma_3(n) - 2\sigma_3(n/2) + 16\sigma_3(n/4)\bigr)$ (terms with
  non-integral argument omitted); `sum_neg_one_pow_divisors`: this equals $16\sum_{d\mid n}(-1)^{n+d}d^3$ (uses the Hecke
  relation $\sigma_3(n) = 9\sigma_3(n/2) - 8\sigma_3(n/4)$ for even $n$, proved from divisor sums);
  **`repNum_sumSq_eight`**: (6.4); `repNum_sumSq_eight_odd`: $r_8(n) = 16\sigma_3(n)$ for $n$ odd.

Unconditional: no input structures are assumed.
-/
import QuadFormsKB.Siegel.FourSquaresJacobi
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Statements

open Complex Matrix ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ArithmeticFunction.sigma Manifold
open SlashInvariantForm

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

local notation "𝒢₄" => ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-! ### The matrix $\mathrm{diag}(2,1)$ -/

/-- The matrix $\mathrm{diag}(2, 1) \in \mathrm{GL}_2(\mathbb{R})$, acting by $\tau \mapsto 2\tau$. -/
noncomputable def M2 : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, 0; 0, 1] (by norm_num [det_fin_two])

lemma M2_det : (M2.det : ℝ) = 2 := by
  simp [M2, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_fin_two]

lemma coe_M2_smul (τ : ℍ) : ((M2 • τ : ℍ) : ℂ) = 2 * τ := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [M2_det]; norm_num)]
  simp [M2, Matrix.GeneralLinearGroup.mkOfDetNeZero, num, denom]

/-- $(f \mid_4 \mathrm{diag}(d,1))(\tau) = d^3 f(d\tau)$ for $d = 2$. -/
lemma M2_slash_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[(4 : ℤ)] M2) τ = 8 * f (M2 • τ) := by
  rw [ModularForm.slash_apply]
  have hd : denom M2 τ = 1 := by simp [M2, Matrix.GeneralLinearGroup.mkOfDetNeZero, denom]
  have hdet : 0 < (M2 : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp [M2, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_fin_two]
  have hσ : ∀ x, UpperHalfPlane.σ M2 x = x := by
    intro x; simp [UpperHalfPlane.σ, hdet]
  rw [hd, hσ, M2_det]
  norm_num
  ring

/-- $(f \mid_4 \mathrm{diag}(4,1))(\tau) = 64 f(4\tau)$. -/
lemma M4_slash_apply_four (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[(4 : ℤ)] M4) τ = 64 * f (M4 • τ) := by
  rw [ModularForm.slash_apply]
  have hd : denom M4 τ = 1 := by simp [M4, Matrix.GeneralLinearGroup.mkOfDetNeZero, denom]
  have hdet : 0 < (M4 : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp [M4, Matrix.GeneralLinearGroup.mkOfDetNeZero, det_fin_two]
  have hσ : ∀ x, UpperHalfPlane.σ M4 x = x := by
    intro x; simp [UpperHalfPlane.σ, hdet]
  rw [hd, hσ, M4_det]
  norm_num
  ring

/-- For $\gamma = \begin{pmatrix} a & b \\ 2c_0 & d\end{pmatrix}$, the matrix
$\begin{pmatrix} a & 2b \\ c_0 & d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$, with $M\gamma = \gamma' M$ for
$M = \mathrm{diag}(2,1)$. -/
def conjM2 (γ : SL(2, ℤ)) (c0 : ℤ) (hc : γ 1 0 = 2 * c0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, 2 * γ 0 1; c0, γ 1 1], by
    have := γ.2; rw [det_fin_two] at this; rw [det_fin_two_of]; rw [hc] at this; linarith⟩

lemma M2_mul_eq (γ : SL(2, ℤ)) (c0 : ℤ) (hc : γ 1 0 = 2 * c0) :
    M2 * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjM2 γ c0 hc) * M2 := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply']
  fin_cases i <;> fin_cases j <;>
    simp [M2, conjM2, Matrix.GeneralLinearGroup.mkOfDetNeZero, hc] <;> ring

open scoped Pointwise in
/-- $M\,\Gamma_0(4)\,M^{-1} \subseteq \mathrm{SL}_2(\mathbb{Z})$ for $M = \mathrm{diag}(2,1)$. -/
lemma conj_M2_Gamma0_le :
    ConjAct.toConjAct M2 • ((CongruenceSubgroup.Gamma0 4 : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  intro x hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  obtain ⟨γ, hγ, hγx⟩ := hx
  have h4 : (2 : ℤ) ∣ γ 1 0 := by
    have hγ : γ ∈ CongruenceSubgroup.Gamma0 4 := hγ
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    exact (dvd_trans (by norm_num : (2 : ℤ) ∣ 4) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hγ))
  obtain ⟨c0, hc⟩ := h4
  refine ⟨conjM2 γ c0 hc, ?_⟩
  have e : x = M2 * Matrix.SpecialLinearGroup.mapGL ℝ γ * M2⁻¹ := by
    have hγx' : Matrix.SpecialLinearGroup.mapGL ℝ γ = M2⁻¹ * x * M2 := by
      rw [hγx, ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv]
    rw [hγx']; group
  rw [e, M2_mul_eq γ c0 hc]; group

open scoped Pointwise in
/-- If $g\,\Gamma_0(4)\,g^{-1} \subseteq \mathrm{SL}_2(\mathbb{Z})$ then $\Gamma_0(4) \subseteq g^{-1}\mathrm{SL}_2(\mathbb{Z})\,g$. -/
lemma Gamma0_le_conj (g : GL (Fin 2) ℝ) (h : ConjAct.toConjAct g • 𝒢₄ ≤ 𝒮ℒ) :
    𝒢₄ ≤ ConjAct.toConjAct g⁻¹ • 𝒮ℒ := by
  intro x hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff]
  exact h (Subgroup.smul_mem_pointwise_smul _ _ _ hx)

lemma Gamma0_le_SL : 𝒢₄ ≤ 𝒮ℒ := by
  rintro x ⟨γ, -, rfl⟩
  exact ⟨γ, rfl⟩

/-! ### The Eisenstein side: $\mathcal{E} = E_4(\tau) - 2E_4(2\tau) + 16E_4(4\tau)$ -/

/-- $E_4$ restricted to $\Gamma_0(4)$. -/
noncomputable def E4r : ModularForm 𝒢₄ 4 := ModularForm.restrict Gamma0_le_SL E₄

/-- $(E_4 \mid_4 \mathrm{diag}(2,1))(\tau) = 8E_4(2\tau)$, as an element of $M_4(\Gamma_0(4))$. -/
noncomputable def E4M2 : ModularForm 𝒢₄ 4 :=
  ModularForm.restrict (Gamma0_le_conj M2 conj_M2_Gamma0_le) (ModularForm.translate E₄ M2)

/-- $(E_4 \mid_4 \mathrm{diag}(4,1))(\tau) = 64E_4(4\tau)$, as an element of $M_4(\Gamma_0(4))$. -/
noncomputable def E4M4 : ModularForm 𝒢₄ 4 :=
  ModularForm.restrict (Gamma0_le_conj M4 conj_M4_Gamma0_le) (ModularForm.translate E₄ M4)

lemma E4r_apply (τ : ℍ) : E4r τ = E₄ τ := rfl

lemma E4M2_apply (τ : ℍ) : E4M2 τ = 8 * E₄ (M2 • τ) :=
  M2_slash_apply (E₄ : ℍ → ℂ) τ

lemma E4M4_apply (τ : ℍ) : E4M4 τ = 64 * E₄ (M4 • τ) :=
  M4_slash_apply_four (E₄ : ℍ → ℂ) τ

/-- **$\mathcal{E}(\tau) = E_4(\tau) - 2E_4(2\tau) + 16E_4(4\tau) \in M_4(\Gamma_0(4))$.** -/
noncomputable def Eis8 : ModularForm 𝒢₄ 4 :=
  E4r + (-(1 / 4 : ℂ)) • E4M2 + (1 / 4 : ℂ) • E4M4

lemma Eis8_apply (τ : ℍ) :
    Eis8 τ = E₄ τ - 2 * E₄ (M2 • τ) + 16 * E₄ (M4 • τ) := by
  simp only [Eis8, _root_.add_apply, _root_.smul_apply, E4r_apply, E4M2_apply, E4M4_apply, smul_eq_mul]
  ring

/-- The $q$-expansion coefficients of $E_4$: $1$, then $240\sigma_3(m)$. -/
def e4c (m : ℕ) : ℂ := if m = 0 then 1 else 240 * σ 3 m

/-- The $q$-expansion coefficients of $\mathcal{E}$. -/
def eisc (n : ℕ) : ℂ :=
  e4c n - 2 * (if 2 ∣ n then e4c (n / 2) else 0) + 16 * (if 4 ∣ n then e4c (n / 4) else 0)

lemma hasSum_E4 (τ : ℍ) :
    HasSum (fun m : ℕ => e4c m • Function.Periodic.qParam 1 τ ^ m) (E₄ τ) := by
  have h := ModularForm.hasSum_qExpansion (f := E₄) one_pos one_mem_strictPeriods_SL τ
  have h1 := E₄_qExpansion_coeff_one
  rw [E_qExpansion_coeff (k := 4) _ ⟨2, rfl⟩] at h1
  simp only [one_ne_zero, ↓reduceIte,
    show (σ (4 - 1) 1 : ℂ) = 1 by simp [ArithmeticFunction.sigma_apply], mul_one] at h1
  convert h using 2 with m
  rw [E_qExpansion_coeff (k := 4) _ ⟨2, rfl⟩, qParam_one]
  simp only [e4c, h1, smul_eq_mul]

lemma hasSum_E4_scaled (d : ℕ) (hd : 0 < d) (τ τ' : ℍ)
    (hq : Function.Periodic.qParam 1 τ' = Function.Periodic.qParam 1 τ ^ d) :
    HasSum (fun n : ℕ => (if d ∣ n then e4c (n / d) else 0) • Function.Periodic.qParam 1 τ ^ n)
      (E₄ τ') := by
  have h := hasSum_E4 τ'
  rw [hq] at h
  have hinj : Function.Injective (fun m : ℕ => d * m) := fun a b h => by
    simpa [hd.ne'] using h
  rw [← (hinj.hasSum_iff ?_)]
  · convert h using 2 with m
    simp only [Function.comp]
    rw [if_pos (dvd_mul_right d m), Nat.mul_div_cancel_left m hd, pow_mul]
  · intro n hn
    have : ¬ d ∣ n := by
      rintro ⟨m, rfl⟩; exact hn ⟨m, rfl⟩
    simp [this]

lemma hasSum_Eis8 (τ : ℍ) :
    HasSum (fun n : ℕ => eisc n • Function.Periodic.qParam 1 τ ^ n) (Eis8 τ) := by
  rw [Eis8_apply]
  have hq2 : Function.Periodic.qParam 1 (M2 • τ : ℍ) = Function.Periodic.qParam 1 τ ^ 2 := by
    rw [qParam_one, qParam_one, coe_M2_smul, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hq4 : Function.Periodic.qParam 1 (M4 • τ : ℍ) = Function.Periodic.qParam 1 τ ^ 4 := by
    rw [qParam_one, qParam_one, coe_M4_smul, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  convert ((hasSum_E4 τ).sub ((hasSum_E4_scaled 2 (by norm_num) τ _ hq2).mul_left 2)).add
    ((hasSum_E4_scaled 4 (by norm_num) τ _ hq4).mul_left 16) using 1
  funext n
  simp only [eisc, smul_eq_mul]
  ring

lemma qExpansion_Eis8_coeff (n : ℕ) : (qExpansion 1 Eis8).coeff n = eisc n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0 hasSum_Eis8 n).symm

/-! ### The theta series $\Theta_{I_8}$ -/

/-- $\chi_{I_8}$ is trivial: $\det H = 2^8 = 16^2$ and $\Delta = (-1)^4\det H$. -/
lemma thetaChi_sumSq_eight (d : ℤ) (hd : IsCoprime d (4 : ℕ)) : thetaChi (sumSq 8) 4 4 d = 1 := by
  obtain ⟨ho, -, -⟩ := oddRep_spec (by norm_num : 0 < 4) hd
  have hdet : (sumSq 8).hessian.det = 16 ^ 2 := by
    rw [hessian_sumSq, det_smul, det_one]; norm_num
  have hΔ : thetaDisc (sumSq 8) 4 = 16 ^ 2 := by
    rw [thetaDisc, hdet]; norm_num
  rw [thetaChi, hΔ]
  refine jacobiSym.sq_one' ?_
  rw [Int.gcd, Int.natAbs_natCast]
  have : Nat.Coprime (2 ^ 4) (oddRep 4 d) := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
  simpa using this

/-- **$\Theta_{I_8} \in M_4(\Gamma_0(4))$** (trivial character). -/
noncomputable def thetaMF_sumSq_eight : ModularForm (CongruenceSubgroup.Gamma0 4) 4 :=
  thetaMFGamma0 posDef_sumSq (n := 8) (k := 4) rfl (by norm_num) isThetaLevel_sumSq
    thetaChi_sumSq_eight

@[simp] theorem thetaMF_sumSq_eight_apply (τ : UpperHalfPlane) :
    thetaMF_sumSq_eight τ = theta (sumSq 8) τ := rfl

lemma hasSum_thetaMF_sumSq_eight (τ : ℍ) :
    HasSum (fun m : ℕ => (repNum (sumSq 8) m : ℂ) • Function.Periodic.qParam 1 τ ^ m)
      (thetaMF_sumSq_eight τ) := by
  rw [thetaMF_sumSq_eight_apply]
  convert hasSum_theta posDef_sumSq τ.im_pos using 2 with m
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- The $q$-expansion coefficients of $\Theta_{I_8}$ are $r_8(m)$. -/
lemma qExpansion_thetaMF_sumSq_eight_coeff (m : ℕ) :
    (qExpansion 1 thetaMF_sumSq_eight).coeff m = repNum (sumSq 8) m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0
    hasSum_thetaMF_sumSq_eight m).symm

/-! ### Small values: $r_8(2) = 112$, $r_8(3) = 448$ -/

/-- For $m \le 3$ the vectors of norm $m$ lie in $\{-1,0,1\}^8$, so $r_8(m)$ is a finite count. -/
lemma repNum_sumSq_eight_small (m : ℕ) (hm : m ≤ 3) :
    repNum (sumSq 8) m =
      ((Fintype.piFinset (fun _ : Fin 8 => Finset.Icc (-1 : ℤ) 1)).filter
        (fun x => ∑ i, x i ^ 2 = (m : ℤ))).card := by
  classical
  rw [repNum]
  have : repSet (sumSq 8) m =
      ↑((Fintype.piFinset (fun _ : Fin 8 => Finset.Icc (-1 : ℤ) 1)).filter
        (fun x => ∑ i, x i ^ 2 = (m : ℤ))) := by
    ext x
    simp only [repSet, Set.mem_setOf_eq, eval_sumSq, Finset.coe_filter, Fintype.mem_piFinset,
      Finset.mem_Icc]
    constructor
    · intro h
      refine ⟨fun i => ?_, h⟩
      have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
        Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have h2 : (m : ℤ) ≤ 3 := by exact_mod_cast hm
      constructor <;> nlinarith
    · exact fun h => h.2
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

lemma repNum_sumSq_eight_two : repNum (sumSq 8) 2 = 112 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, repNum_sumSq_eight_small 2 (by norm_num)]
  decide +kernel

lemma repNum_sumSq_eight_three : repNum (sumSq 8) 3 = 448 := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, repNum_sumSq_eight_small 3 (by norm_num)]
  decide +kernel

/-! ### Vanishing of forms in $M_4(\Gamma_0(4))$ of order $\ge 4$ at $\infty$ -/

lemma isBoundedAtImInfty_quotientFunc_four (f : ModularForm 𝒢₄ 4) (q : 𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) :
    IsBoundedAtImInfty (quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    rw [quotientFunc_mk]
    have hr : (r.val)⁻¹ ∈ 𝒮ℒ := inv_mem r.2
    have hc : IsCusp ((r.val)⁻¹ • OnePoint.infty) 𝒢₄ := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact (isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩).smul_of_mem hr
    exact (OnePoint.isBoundedAt_iff rfl).mp (ModularFormClass.bdd_at_cusps f hc)

lemma mdiff_quotientFunc_four (f : ModularForm 𝒢₄ 4) (q : 𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) :
    MDiff (quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r => rw [quotientFunc_mk]; exact (ModularFormClass.holo f).slash 4 _

lemma quotientFunc_T_apply_four (f : ModularForm 𝒢₄ 4) (q : 𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) (τ : ℍ) :
    quotientFunc f q (ModularGroup.T • τ) =
      quotientFunc f ((⟨_, T_mem_SL⟩ : 𝒮ℒ)⁻¹ • q) τ := by
  rw [← quotientFunc_smul f T_mem_SL q]
  change _ = (quotientFunc f q ∣[(4 : ℤ)] ModularGroup.T) τ
  rw [SL_slash_apply]
  have : denom ModularGroup.T τ = 1 := by
    simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    simp [ModularGroup.T]
  rw [this]; simp

/-- **A form in $M_4(\Gamma_0(4))$ whose $q$-expansion starts at $q^4$ vanishes.** Its norm to level one has weight
$4\,[\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(4)] \le 40$ and $q$-expansion order $\ge 4$, so vanishes by Mathlib's level-one
Sturm bound ($\lfloor 40/12 \rfloor = 3 < 4$); a form with zero norm is zero. Weight-4 copy of
`eq_zero_of_qExpansion_coeff_zero_one`. -/
theorem eq_zero_of_qExpansion_coeff_lt_four (f : ModularForm 𝒢₄ 4)
    (h0 : (qExpansion 1 f).coeff 0 = 0) (h1 : (qExpansion 1 f).coeff 1 = 0)
    (h2 : (qExpansion 1 f).coeff 2 = 0) (h3 : (qExpansion 1 f).coeff 3 = 0) : f = 0 := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ)
  set x0 : 𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ := ⟦1⟧ with hx0
  set P : ℍ → ℂ := ∏ q ∈ Finset.univ.erase x0, quotientFunc f q with hP
  have hf0 : quotientFunc f x0 = f := by simp [hx0]
  have hN : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) = (f : ℍ → ℂ) * P := by
    rw [ModularForm.coe_norm, ← hf0, hP, Finset.mul_prod_erase _ _ (Finset.mem_univ x0)]
  have hPT : ∀ τ : ℍ, P (ModularGroup.T • τ) = P τ := by
    intro τ
    set g : 𝒮ℒ := (⟨_, T_mem_SL⟩ : 𝒮ℒ)⁻¹
    have hg : g • x0 = x0 := by
      rw [hx0]
      change (⟦g * 1⟧ : 𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) = ⟦1⟧
      rw [mul_one]
      refine Quotient.sound ((QuotientGroup.leftRel_apply).mpr ?_)
      rw [Subgroup.mem_subgroupOf]
      simp [g]
    simp only [hP, Finset.prod_apply, quotientFunc_T_apply_four]
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
    exact MDifferentiable.prod fun q _ => mdiff_quotientFunc_four f q
  have hPbdd : IsBoundedAtImInfty P := by
    change P ∈ boundedAtImInftySubalgebra ℂ
    rw [hP]
    exact Subalgebra.prod_mem _ fun q _ => isBoundedAtImInfty_quotientFunc_four f q
  have hfA := ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_Gamma0
  have hPA := analyticAt_cuspFunction_zero one_pos hPper hPhol hPbdd
  have hq : qExpansion 1 (ModularForm.norm 𝒮ℒ f) = qExpansion 1 f * qExpansion 1 P := by
    rw [hN]; exact qExpansion_mul hfA hPA
  have hord : (4 : ℕ∞) ≤ (qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order := by
    rw [hq, PowerSeries.order_mul]
    have : ((4 : ℕ) : ℕ∞) ≤ (qExpansion 1 f).order := by
      refine PowerSeries.nat_le_order _ _ fun i hi => ?_
      interval_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    exact le_add_right this
  have hN0 : ModularForm.norm 𝒮ℒ f = 0 := by
    refine sturm_bound_levelOne (lt_of_lt_of_le ?_ hord)
    have hc := card_quot_Gamma0_four_le
    have : ((4 * (Nat.card (𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12) ≤ 3 := by
      rw [show (4 * (Nat.card (𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) : ℤ)).toNat =
        4 * Nat.card (𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) by omega]
      omega
    calc ((((4 * (Nat.card (𝒮ℒ ⧸ (𝒢₄).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12 : ℕ)) : ℕ∞) ≤ (3 : ℕ) := by
          exact_mod_cast this
      _ < 4 := by norm_num
  have hz := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp hN0
  ext τ
  simpa using congrFun hz τ

/-! ### $\Theta_{I_8} = \tfrac1{15}\mathcal{E}$ -/

lemma sigma3_one : (σ 3 1 : ℂ) = 1 := by simp [ArithmeticFunction.sigma_apply]
lemma sigma3_two : (σ 3 2 : ℂ) = 9 := by
  rw [ArithmeticFunction.sigma_apply, Nat.Prime.divisors Nat.prime_two]; norm_num
lemma sigma3_three : (σ 3 3 : ℂ) = 28 := by
  rw [ArithmeticFunction.sigma_apply, Nat.Prime.divisors Nat.prime_three]; norm_num

lemma coeff_combo (m : ℕ) :
    (qExpansion 1 ⇑(thetaMF_sumSq_eight + (-(1 / 15 : ℂ)) • Eis8)).coeff m =
      (repNum (sumSq 8) m : ℂ) + (-(1 / 15 : ℂ)) * eisc m := by
  have hΓ := one_mem_strictPeriods_Gamma0
  rw [FunLike.coe_add,
    ModularForm.qExpansion_add one_pos hΓ thetaMF_sumSq_eight ((-(1 / 15 : ℂ)) • Eis8),
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ, map_add, PowerSeries.coeff_smul,
    qExpansion_thetaMF_sumSq_eight_coeff, qExpansion_Eis8_coeff, smul_eq_mul]

/-- **$\Theta_{I_8} = \tfrac1{15}\bigl(E_4(\tau) - 2E_4(2\tau) + 16E_4(4\tau)\bigr)$** in $M_4(\Gamma_0(4))$. -/
theorem thetaMF_sumSq_eight_eq : thetaMF_sumSq_eight = (1 / 15 : ℂ) • Eis8 := by
  have h := eq_zero_of_qExpansion_coeff_lt_four
    (thetaMF_sumSq_eight + (-(1 / 15 : ℂ)) • Eis8) ?_ ?_ ?_ ?_
  · ext τ
    have := congrArg (fun F : ModularForm _ 4 => F τ) h
    simp only [_root_.add_apply, _root_.smul_apply, _root_.zero_apply,
      smul_eq_mul] at this ⊢
    linear_combination this
  · rw [coeff_combo, Nat.cast_zero, repNum_zero_of_posDef posDef_sumSq]
    norm_num [eisc, e4c]
  · rw [coeff_combo, Nat.cast_one, repNum_sumSq_one]
    norm_num [eisc, e4c, sigma3_one]
  · rw [coeff_combo, show repNum (sumSq 8) ((2 : ℕ) : ℤ) = 112 from repNum_sumSq_eight_two]
    norm_num [eisc, e4c, sigma3_one, sigma3_two]
  · rw [coeff_combo, show repNum (sumSq 8) ((3 : ℕ) : ℤ) = 448 from repNum_sumSq_eight_three]
    norm_num [eisc, e4c, sigma3_one, sigma3_three]

/-- $r_8(m) = 16\bigl(\sigma_3(m) - 2\sigma_3(m/2) + 16\sigma_3(m/4)\bigr)$ for $m \ge 1$ (the term with $\sigma_3(m/d)$
only when $d \mid m$). -/
theorem repNum_sumSq_eight_sigma {m : ℕ} (hm : 1 ≤ m) :
    (repNum (sumSq 8) m : ℤ) =
      16 * ((σ 3 m : ℤ) - 2 * (if 2 ∣ m then (σ 3 (m / 2) : ℤ) else 0) +
        16 * (if 4 ∣ m then (σ 3 (m / 4) : ℤ) else 0)) := by
  have h := qExpansion_thetaMF_sumSq_eight_coeff m
  rw [thetaMF_sumSq_eight_eq, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_Gamma0, PowerSeries.coeff_smul,
    qExpansion_Eis8_coeff, smul_eq_mul] at h
  have hm0 : m ≠ 0 := by omega
  have h2 : 2 ∣ m → m / 2 ≠ 0 := fun ⟨k, hk⟩ => by omega
  have h4 : 4 ∣ m → m / 4 ≠ 0 := fun ⟨k, hk⟩ => by omega
  have key : (repNum (sumSq 8) m : ℂ) =
      16 * ((σ 3 m : ℂ) - 2 * (if 2 ∣ m then (σ 3 (m / 2) : ℂ) else 0) +
        16 * (if 4 ∣ m then (σ 3 (m / 4) : ℂ) else 0)) := by
    rw [← h]
    by_cases c2 : 2 ∣ m <;> by_cases c4 : 4 ∣ m
    · simp only [eisc, e4c, hm0, c2, c4, h2 c2, h4 c4, if_true, if_false]; ring
    · simp only [eisc, e4c, hm0, c2, c4, h2 c2, if_true, if_false]; ring
    · exact absurd (dvd_trans (by norm_num : 2 ∣ 4) c4) c2
    · simp only [eisc, e4c, hm0, c2, c4, if_true, if_false]; ring
  by_cases c2 : 2 ∣ m <;> by_cases c4 : 4 ∣ m <;> simp only [c2, c4, if_true, if_false] at key ⊢ <;>
    exact_mod_cast key

/-! ### The divisor-sum form -/

/-- $\sum_{d \mid m,\ 2 \mid d} d^3 = 8\sigma_3(m/2)$ if $2 \mid m$, else $0$. -/
lemma sum_divisors_two_dvd (m : ℕ) :
    ∑ d ∈ m.divisors.filter (2 ∣ ·), d ^ 3 = if 2 ∣ m then 8 * σ 3 (m / 2) else 0 := by
  split_ifs with h2
  · obtain ⟨k, rfl⟩ := h2
    have e : (2 * k).divisors.filter (2 ∣ ·) =
        k.divisors.map ⟨(2 * ·), mul_right_injective₀ (by norm_num)⟩ := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨hd, hk⟩, ⟨e, rfl⟩⟩
        refine ⟨e, ⟨(Nat.mul_dvd_mul_iff_left (by norm_num)).mp hd, by omega⟩, rfl⟩
      · rintro ⟨e, ⟨he, hk⟩, rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left 2 he, by omega⟩, dvd_mul_right 2 e⟩
    rw [e, Finset.sum_map, ArithmeticFunction.sigma_apply, Finset.mul_sum,
      show 2 * k / 2 = k by omega]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Function.Embedding.coeFn_mk]
    ring
  · refine Finset.sum_eq_zero fun d hd => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) h2

/-- The odd divisors of $2m$ are the odd divisors of $m$. -/
lemma odd_divisors_double (m : ℕ) :
    (2 * m).divisors.filter (¬ 2 ∣ ·) = m.divisors.filter (¬ 2 ∣ ·) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, hk⟩, hodd⟩
    have hcop : Nat.Coprime d 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    refine ⟨⟨(Nat.Coprime.dvd_mul_left hcop).mp hd, by omega⟩, hodd⟩
  · rintro ⟨⟨hd, hk⟩, hodd⟩
    exact ⟨⟨Dvd.dvd.mul_left hd 2, by omega⟩, hodd⟩

/-- **The Hecke-type identity**: for $n \ge 1$,
$\sum_{d \mid n}(-1)^{n+d}d^3 = \sigma_3(n) - 2\sigma_3(n/2)[2 \mid n] + 16\sigma_3(n/4)[4 \mid n]$. -/
theorem sum_neg_one_pow_divisors {n : ℕ} (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 =
      (σ 3 n : ℤ) - 2 * (if 2 ∣ n then (σ 3 (n / 2) : ℤ) else 0) +
        16 * (if 4 ∣ n then (σ 3 (n / 4) : ℤ) else 0) := by
  classical
  set E : ℕ → ℕ := fun n => ∑ d ∈ n.divisors.filter (2 ∣ ·), d ^ 3 with hE
  set O : ℕ → ℕ := fun n => ∑ d ∈ n.divisors.filter (¬ 2 ∣ ·), d ^ 3 with hO
  have hσ : ∀ n, σ 3 n = E n + O n := fun n => by
    simp only [hE, hO]
    rw [ArithmeticFunction.sigma_apply, Finset.sum_filter_add_sum_filter_not]
  have hEs : ∀ n, E n = if 2 ∣ n then 8 * σ 3 (n / 2) else 0 := sum_divisors_two_dvd
  -- the signed sum
  have hT : ∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 = (-1) ^ n * ((E n : ℤ) - O n) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.divisors (2 ∣ ·)]
    have h1 : ∑ d ∈ n.divisors.filter (2 ∣ ·), (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 =
        (-1) ^ n * (E n : ℤ) := by
      simp only [hE]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd2 : 2 ∣ d := (Finset.mem_filter.mp hd).2
      have : (-1 : ℤ) ^ d = 1 := Even.neg_one_pow (even_iff_two_dvd.mpr hd2)
      rw [pow_add, this, mul_one]
    have h2 : ∑ d ∈ n.divisors.filter (¬ 2 ∣ ·), (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 =
        -((-1) ^ n * (O n : ℤ)) := by
      simp only [hO]
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd2 : ¬ 2 ∣ d := (Finset.mem_filter.mp hd).2
      have : (-1 : ℤ) ^ d = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
      rw [pow_add, this]; ring
    rw [h1, h2]; ring
  rw [hT]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · -- n = m + m, even
    have hnm : n = 2 * m := by omega
    subst hnm
    have hm1 : 1 ≤ m := by omega
    have h2n : 2 ∣ 2 * m := dvd_mul_right 2 m
    have e1 : (2 * m) / 2 = m := by omega
    have hE2 : E (2 * m) = 8 * σ 3 m := by rw [hEs, if_pos h2n, e1]
    have hO2 : O (2 * m) = O m := by simp only [hO]; rw [odd_divisors_double]
    have hσm : σ 3 m = E m + O m := hσ m
    have hσ2 : σ 3 (2 * m) = E (2 * m) + O (2 * m) := hσ _
    have e4 : (2 * m) / 4 = m / 2 := by omega
    have a1 : (E (2 * m) : ℤ) = 8 * (σ 3 m : ℤ) := by exact_mod_cast hE2
    have a2 : (O (2 * m) : ℤ) = (O m : ℤ) := by exact_mod_cast hO2
    have a3 : (σ 3 m : ℤ) = E m + O m := by exact_mod_cast hσm
    have a4 : (σ 3 (2 * m) : ℤ) = E (2 * m) + O (2 * m) := by exact_mod_cast hσ2
    rw [Even.neg_one_pow ⟨m, by ring⟩, if_pos h2n, e1, e4, one_mul]
    by_cases hh : 2 ∣ m
    · have h44 : 4 ∣ 2 * m := by omega
      have a5 : (E m : ℤ) = 8 * (σ 3 (m / 2) : ℤ) := by
        rw [hEs, if_pos hh]; push_cast; ring
      rw [if_pos h44]
      linarith
    · have h44 : ¬ 4 ∣ 2 * m := by omega
      have a5 : (E m : ℤ) = 0 := by rw [hEs, if_neg hh]; simp
      rw [if_neg h44]
      linarith
  · have c2 : ¬ 2 ∣ n := by rcases hodd with ⟨k, hk⟩; omega
    have c4 : ¬ 4 ∣ n := by rcases hodd with ⟨k, hk⟩; omega
    have a5 : (E n : ℤ) = 0 := by rw [hEs, if_neg c2]; simp
    have a3 : (σ 3 n : ℤ) = E n + O n := by exact_mod_cast hσ n
    rw [Odd.neg_one_pow hodd, if_neg c2, if_neg c4]
    linarith

/-- **Jacobi's eight-squares formula** (Moreno–Wagstaff (6.4), p. 186): for $n \ge 1$,
$$r_8(n) = 16\sum_{d \mid n} (-1)^{n+d} d^3.$$
*Proof:* $\Theta_{I_8} = \tfrac1{15}\bigl(E_4(\tau) - 2E_4(2\tau) + 16E_4(4\tau)\bigr)$ in $M_4(\Gamma_0(4))$
(`thetaMF_sumSq_eight_eq`, by a Sturm-bound argument), compare $q$-expansion coefficients
(`repNum_sumSq_eight_sigma`) and rewrite the divisor sums (`sum_neg_one_pow_divisors`). Unconditional. -/
@[kb "morenowagstaff2005" "(6.4), r_8(n), p. 186"]
theorem repNum_sumSq_eight {n : ℕ} (hn : 1 ≤ n) :
    (repNum (sumSq 8) n : ℤ) = 16 * ∑ d ∈ n.divisors, (-1 : ℤ) ^ (n + d) * (d : ℤ) ^ 3 := by
  rw [sum_neg_one_pow_divisors hn]
  exact repNum_sumSq_eight_sigma hn

/-- $r_8(n) = 16\sigma_3(n)$ for odd $n$, $\sigma_3(n) = \sum_{d \mid n} d^3$. -/
theorem repNum_sumSq_eight_odd {n : ℕ} (hn : Odd n) : repNum (sumSq 8) n = 16 * σ 3 n := by
  have h1 : 1 ≤ n := hn.pos
  have c2 : ¬ 2 ∣ n := by rcases hn with ⟨k, hk⟩; omega
  have c4 : ¬ 4 ∣ n := by rcases hn with ⟨k, hk⟩; omega
  have h := repNum_sumSq_eight_sigma h1
  rw [if_neg c2, if_neg c4] at h
  have : (repNum (sumSq 8) n : ℤ) = ((16 * σ 3 n : ℕ) : ℤ) := by rw [h]; push_cast; ring
  exact_mod_cast this

end QuadFormsKB.MorenoWagstaff
