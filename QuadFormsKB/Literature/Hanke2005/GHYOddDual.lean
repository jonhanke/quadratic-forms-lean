/-
# The dual index of a maximal lattice of odd rank, at every place

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), (6.6), (6.10), (6.11), (6.13);
G. Shimura, *An exact mass formula for orthogonal groups*, Duke Math. J. 97 (1999), (3.1.9), (3.2.1).

For $n = 2k+1\ge3$ and $\Lambda = \mathcal O_F^n$ maximal, at every finite place $\mathfrak p$ ($\pi^e\,\|\,2$):
$$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = |2|_\mathfrak p^{-1}\,q^{c},\qquad
c = \begin{cases}0 & \det\varphi\ \text{a unit times a square},\ t_\mathfrak p = 1,\\
2 & \det\varphi\ \text{a unit times a square},\ t_\mathfrak p = 3,\\
1 & \det\varphi\ \text{not a unit times a square}\end{cases}$$
(`dualIndexAt_odd`), and $t_\mathfrak p\in\{1,3\}$. These are the lattices $\Delta^k\perp A$, $\Delta^{k-1}\perp\Lambda_\delta$ of Gan–Hanke–Yu
(6.6), (6.10). *Proof:* $\Lambda_\mathfrak p\simeq\mathbb H^k\perp N$ (`exists_hypSum_shape`); $|\det H_N| = |2|\,q^{-\nu}$ with
$\nu\le1$ for $r = 1$ (maximality) and $\nu\in\{1,2\}$ for $r = 3$ (the two shapes at a dyadic place; diagonalization at a
non-dyadic place, where $\nu = 0$ would make $N$ unimodular, hence isotropic); and $\det H_N/2^r$ is a unit times a square iff
$\nu$ is even (`detSq_iff_even`). Indices are 0-based.
-/
import QuadFormsKB.Literature.Hanke2005.GHYOddLocal

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\|2\|$ in $F_\mathfrak p$ is $q^{-e}$ for $\pi^e\,\|\,2$. -/
theorem norm_two_Fv {e : ℕ} (he : NF.π v ^ e ∣ (2 : 𝔬)) (he' : ¬ NF.π v ^ (e + 1) ∣ (2 : 𝔬)) :
    ‖(2 : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := by
  rw [← Tamagawa.norm_coe_of_pow_dvd v he he', ← map_ofNat (algebraMap 𝔬 Fv) 2]; rfl

/-- **Shimura's condition for a kernel of odd rank is the parity of $\nu$:** if $|\det H_N| = |2|\,q^{-\nu}$ and $r$ is odd,
then $\det H_N/2^r$ is a unit times a square iff $\nu$ is even. -/
theorem detSq_iff_even {r : ℕ} (hr : Odd r) (N : QuadForm 𝔬 r) (ν : ℕ)
    (hN : ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ ν)⁻¹) :
    (∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ r * c ^ 2‖ = 1) ↔ Even ν := by
  have hπ := NF.irreducible_π v
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ (two_ne_zero_O v)
  have h2 := norm_two_Fv v he he'
  have hQ1 : 1 < (DVR.q 𝔬 : ℝ) := by rw [DensitySD.q_eq v]; exact one_lt_normQ v
  have hQ0 : (0 : ℝ) < DVR.q 𝔬 := lt_trans zero_lt_one hQ1
  have hqA : (DVR.q 𝔬 : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by rw [NF.q_completion]
  obtain ⟨j, rfl⟩ := hr
  have hbase : ∀ c : Fv, ‖dN v N / 2 ^ (2 * j + 1) * c ^ 2‖ =
      (DVR.q 𝔬 : ℝ) ^ ((2 * j * e : ℕ) : ℤ) * ((DVR.q 𝔬 : ℝ) ^ (ν : ℤ))⁻¹ * ‖c‖ ^ 2 := by
    intro c
    rw [norm_mul, norm_div, norm_pow, norm_pow, hN, h2]
    rw [zpow_natCast, zpow_natCast]
    have hq0 : (DVR.q 𝔬 : ℝ) ≠ 0 := hQ0.ne'
    generalize (DVR.q 𝔬 : ℝ) = Q at hq0 ⊢
    rw [inv_pow, div_inv_eq_mul, ← pow_mul]
    field_simp
    ring
  constructor
  · rintro ⟨c, hc0, hc⟩
    rw [hbase] at hc
    by_contra hν
    rw [Nat.not_even_iff_odd] at hν
    apply norm_sq_ne_odd_pow v hc0 (k := (ν : ℤ) - ((2 * j * e : ℕ) : ℤ))
    · obtain ⟨i, hi⟩ := hν
      exact ⟨(i : ℤ) - (j * e : ℕ), by push_cast [hi]; ring⟩
    · rw [← hqA, zpow_sub₀ hQ0.ne']
      field_simp at hc ⊢
      linear_combination hc
  · rintro ⟨i, rfl⟩
    have hπ0 : ((NF.π v : 𝔬) : Fv) ≠ 0 := pi_ne_zero_Fv v
    have hnπ : ‖((NF.π v : 𝔬) : Fv)‖ = (DVR.q 𝔬 : ℝ)⁻¹ := by
      have := norm_pi_pow_Fv v 1; simpa using this
    refine ⟨((NF.π v : 𝔬) : Fv) ^ ((j * e : ℕ) : ℤ) * (((NF.π v : 𝔬) : Fv) ^ i)⁻¹,
      mul_ne_zero (zpow_ne_zero _ hπ0) (inv_ne_zero (pow_ne_zero _ hπ0)), ?_⟩
    rw [hbase, norm_mul, norm_zpow, norm_inv, norm_pow, hnπ, _root_.inv_zpow', zpow_natCast, zpow_natCast]
    rw [show ((-((j * e : ℕ) : ℤ))) = -(((j * e : ℕ) : ℕ) : ℤ) by rfl, _root_.zpow_neg, zpow_natCast]
    have hq0 : (DVR.q 𝔬 : ℝ) ≠ 0 := hQ0.ne'
    field_simp
    simp only [one_div, inv_pow]
    field_simp
    ring

/-! ### The kernel determinants -/

/-- **Rank one:** $|\det H_N| = |2|\,q^{-\nu}$ with $\nu\le1$ (maximality). -/
theorem norm_dN_one (N : QuadForm 𝔬 1) (hN : N.Nondegenerate) (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv))) :
    ∃ ν : ℕ, ν ≤ 1 ∧ ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ ν)⁻¹ := by
  have hπ := NF.irreducible_π v
  have hN' : N = DVR.unary (N.coeff 0 0) := diag_of_rank_one N
  have hc0 : N.coeff 0 0 ≠ 0 := by
    intro h
    apply hN
    rw [hN', h, hessian_unary_det, mul_zero]
  obtain ⟨ν, hν, hν'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hc0
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ hν hν'
  have hmax' : MaxProp v ((QuadForm.diag fun _ : Fin 1 => NF.π v ^ ν * u).map (algebraMap 𝔬 Fv)) := by
    have e : (QuadForm.diag fun _ : Fin 1 => NF.π v ^ ν * u) = N := by rw [← hu, hN']; rfl
    rw [e]; exact hmax
  refine ⟨ν, nu_le_one v (fun _ => ν) (fun _ => u) hmax' 0, ?_⟩
  unfold dN
  conv_lhs => rw [hN', hessian_unary_det, hu]
  push_cast
  rw [norm_mul, show ((2 : 𝔬) : Fv) = 2 from map_ofNat (algebraMap 𝔬 Fv) 2,
    show ((NF.π v : 𝔬) : Fv) ^ ν * ((u : 𝔬) : Fv) = (((NF.π v ^ ν * u : 𝔬)) : Fv) by push_cast; ring,
    norm_pi_pow_mul_unit v ν huu]

/-- **Rank three, dyadic:** $|\det H_N| = |2|\,q^{-1}$ (top shape $\langle\pi c\rangle\perp T$) or $|2|\,q^{-2}$ (bottom shape
$\langle u\rangle\perp\pi S$). -/
theorem norm_dN_three_dyadic (h2 : ¬ IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 3)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 3 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0) :
    ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ ∨ ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  have han' := aniso_integral v N han
  have hmax' := hmax_of_maxProp v h2 N hmax han'
  set W := resZeroSub hπ h2π h20 N han' with hW
  set s := Module.finrank (IsLocalRing.ResidueField 𝔬) W with hs
  have hlo := le_finrank_resZeroSub_add_two hπ h2π h20 N han'
  have hhi := finrank_resZeroSub_le_two hπ h2π h20 N han' hmax'
  rw [← hW, ← hs] at hlo hhi
  have h2c : ‖(2 : Fv)‖ = ‖((2 : 𝔬) : Fv)‖ := by rw [← map_ofNat (algebraMap 𝔬 Fv) 2]; rfl
  rw [h2c]
  rcases (show s = 1 ∨ s = 2 by omega) with hs1 | hs2
  · left
    obtain ⟨M, T, hTu, hTan, hMd, hM⟩ := exists_shape_top (m := 1) hπ h2π h20 N han' hs1
    have hMc : M = DVR.unary (M.coeff 0 0) := diag_of_rank_one M
    have hc : NF.π v ∣ M.coeff 0 0 := by
      have := hMd (Pi.single 0 1); rwa [Tamagawa.eval_single_rd] at this
    obtain ⟨c', hc'⟩ := hc
    have hmax2 := hmax_of_isGLEquiv hM hmax'
    have hc'u : IsUnit c' := by
      refine dvr_isUnit_of_not_dvd hπ fun h => ?_
      have h1 := hmax2 (Fin.append (Pi.single 0 1) 0) ?_ (Fin.castAdd 2 0)
      · simp at h1; exact hπ.not_isUnit (isUnit_of_dvd_one h1)
      · rw [eval_orthSum_append, Tamagawa.eval_single_rd, hc']
        obtain ⟨d, hd⟩ := h
        refine ⟨d, ?_⟩
        rw [hd]; simp [QuadForm.eval, QuadForm.evalIn]; ring
    rw [dN, norm_det_of_isGLEquiv v hM, Hanke2011Structure.hessian_orthSum_det, hMc, hessian_unary_det, hc',
      show (2 : 𝔬) * (NF.π v * c') * T.hessian.det = 2 * (NF.π v ^ 1 * (c' * T.hessian.det)) by ring]
    push_cast
    rw [norm_mul]
    congr 1
    exact_mod_cast norm_pi_pow_mul_unit v 1 (hc'u.mul hTu)
  · right
    obtain ⟨M, S, hSu, hSan, hM⟩ := exists_shape_bottom (m := 1) hπ h2π h20 N han' hmax' hs2
    have hMc : M = DVR.unary (M.coeff 0 0) := diag_of_rank_one M
    set u := M.coeff 0 0 with hu
    have hmax2 := hmax_of_isGLEquiv hM hmax'
    have han2 := aniso_of_isGLEquiv hM han'
    have huu : IsUnit u := by
      refine dvr_isUnit_of_not_dvd hπ fun hc => ?_
      have htop : resZeroSub hπ h2π h20 _ han2 = ⊤ := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨x', rfl⟩ := res_surj_vec x
        rw [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ, QuadForm.eval, evalIn_orthSum]
        refine dvd_add ?_ ?_
        · rw [hMc]
          simp [DVR.unary, QuadForm.diag, QuadForm.evalIn]
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hc _) _
        · change NF.π v ∣ (NF.π v • S).eval _
          rw [eval_smul_form]; exact dvd_mul_right _ _
      have := finrank_resZeroSub_le_two hπ h2π h20 _ han2 hmax2
      rw [htop, finrank_top, Module.finrank_fin_fun] at this
      omega
    rw [dN, norm_det_of_isGLEquiv v hM, Hanke2011Structure.hessian_orthSum_det, hMc, hessian_unary_det,
      hessian_smul_det_two, show (2 : 𝔬) * u * (NF.π v ^ 2 * S.hessian.det) = 2 * (NF.π v ^ 2 * (u * S.hessian.det)) by
        ring]
    push_cast
    rw [norm_mul]
    congr 1
    exact_mod_cast norm_pi_pow_mul_unit v 2 (huu.mul hSu)

/-- **Rank three, non-dyadic:** $|\det H_N| = q^{-1}$ or $q^{-2}$ (diagonalization $\langle u'\rangle\perp\langle\pi w\rangle$ with
$b\in\{1,2\}$ entries divisible by $\pi$; $b = 0$ would make $N$ unimodular, hence isotropic). -/
theorem norm_dN_three_odd (h2 : IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 3) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 3 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0) :
    ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ ∨ ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
  have hπ := NF.irreducible_π v
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  have h2n : ‖(2 : Fv)‖ = 1 := by
    have := norm_coe_unit v h2
    rwa [show (((2 : 𝔬)) : Fv) = 2 from map_ofNat (algebraMap 𝔬 Fv) 2] at this
  rw [h2n, one_mul, one_mul]
  obtain ⟨ν, u, hu, hE⟩ := exists_diag_pi N hN hπ hπ2
  have MP1 := maxProp_of_isGLEquiv v hE hmax
  have hν := nu_le_one v ν u MP1
  obtain ⟨a, b, h, u', w, hu', hw, hE2⟩ := exists_shape_of_nu (NF.π v) ν hν u hu
  have hb3 : b ≤ 3 := by omega
  interval_cases b
  · -- `b = 0`: unimodular, hence isotropic
    exfalso
    obtain rfl : a = 3 := by omega
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 3 u') := hE.trans hE2
    have hdet : IsUnit N.hessian.det := by
      obtain ⟨U, hU, hUe⟩ := hE3
      have hH := DVR.hessian_eq_of_eval hUe
      have hd : (unitSum (QuadForm.diag fun j => NF.π v * w j) 3 u').hessian.det =
          U.det * U.det * N.hessian.det := by
        rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
      have hu3 : IsUnit (unitSum (QuadForm.diag fun j => NF.π v * w j) 3 u').hessian.det := by
        rw [det_hessian_unitSum, DVR.det_hessian_diag]
        simp only [Finset.univ_eq_empty, Finset.prod_empty, pow_zero, mul_one]
        exact (h2.pow 3).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => hu' i)
      rw [hd] at hu3
      exact isUnit_of_mul_isUnit_right hu3
    obtain ⟨y, hy0, hy⟩ := isotropicIn_of_isLocalLevel_zero (Fv) N hπ (two_ne_zero_O v)
      (isLocalLevel_zero_of_isUnit_det N (NF.π v) hdet) le_rfl
    apply hy0
    apply han y
    rw [← hy, QuadForm.eval, evalIn_eq_eval_map' (algebraMap 𝔬 Fv) N y rfl]
  · obtain rfl : a = 2 := by omega
    left
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 2 u') := hE.trans hE2
    rw [dN, norm_det_of_isGLEquiv v hE3, norm_det_unitSum_pi v h2 u' hu' w hw]
  · obtain rfl : a = 1 := by omega
    right
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 1 u') := hE.trans hE2
    rw [dN, norm_det_of_isGLEquiv v hE3, norm_det_unitSum_pi v h2 u' hu' w hw]
  · exfalso
    obtain rfl : a = 0 := by omega
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 0 u') := hE.trans hE2
    have MP2 := maxProp_of_isGLEquiv v hE3 hmax
    have A := aniso_of_maxProp v w MP2
    have := rank_le_two v w A
    omega

end QuadFormsKB.Hanke2005
