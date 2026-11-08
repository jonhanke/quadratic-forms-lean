/-
# The anisotropic maximal kernel when $\det$ is not a unit times a square (odd rank)

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), (6.6), (6.11), Table 4
(odd rank, $\delta\notin A^\times$); J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine
Angew. Math. 584 (2005), Theorem 5.1 (the case excluded by Shimura's hypothesis).

At a finite place $\mathfrak p$, a maximal lattice is $\mathbb H^k\perp N$ with $N$ anisotropic and maximal
(`exists_hypSum_shape`, any place). For an odd-rank $N$ whose determinant $\det H_N/2^r$ is **not** a unit times a square
(the case Shimura's hypothesis excludes) we determine $N$:

* $r = 1$: $N = \langle\pi u\rangle$, $u$ a unit (`kernel_one_of_not_detSq`; maximality gives $\operatorname{ord}N(e_0)\le1$);
* $r = 3$: $N\simeq\langle\pi c\rangle\perp T$ with $c$ a unit, $T$ unimodular binary and $\bar T$ anisotropic, at a dyadic
  place (`kernel_three_dyadic_of_not_detSq`: the residue zero space has dimension $1$, `exists_shape_top`; dimension $2$
  gives $\langle u\rangle\perp\pi S$, whose determinant is a unit times a square) and at a non-dyadic place
  (`kernel_three_odd_of_not_detSq`: diagonalization $\langle u_0,u_1\rangle\perp\langle\pi w\rangle$; $\langle u_0,u_1\rangle$ is
  residually anisotropic, else Hensel gives an isotropic vector).

These are Gan–Hanke–Yu's lattices $\Delta^k\perp A$ (form $\delta x^2$) and $\Delta^k\perp\Lambda_\delta$ for $\delta$ a uniformizer
times a unit. Indices are 0-based.
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelAniso
import QuadFormsKB.Literature.Hanke2005.DensityOddJordan
import QuadFormsKB.Tamagawa.SphericalLocal

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\|\pi^a\| = q^{-a}$ in $F_\mathfrak p$. -/
theorem norm_pi_pow_Fv (a : ℕ) : ‖((NF.π v : 𝔬) : Fv) ^ a‖ = ((DVR.q 𝔬 : ℝ) ^ a)⁻¹ := by
  have := norm_pi_pow_mul_unit v a isUnit_one
  rw [mul_one] at this
  rw [← this]; push_cast; rfl

/-! ### Rank one -/

/-- **The rank-one kernel** (Gan–Hanke–Yu 2001, (6.6), the form $\delta x^2$, $\delta\notin A^\times$): a nondegenerate unary $N$ with
the extension property whose determinant is not a unit times a square is $\langle\pi u\rangle$ with $u$ a unit. -/
@[kb "ganhankeyu2001" "(6.6), (6.11) (odd rank, δ ∉ A×: the kernel δx²)"]
theorem kernel_one_of_not_detSq (N : QuadForm 𝔬 1) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (hdet : ¬ ∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ 1 * c ^ 2‖ = 1) :
    ∃ u : 𝔬, IsUnit u ∧ N = DVR.unary (NF.π v * u) := by
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
  have hle := nu_le_one v (fun _ => ν) (fun _ => u) hmax' 0
  have hν1 : ν = 1 := by
    rcases (by omega : ν = 0 ∨ ν = 1) with h0 | h1
    · exfalso
      apply hdet
      refine ⟨1, one_ne_zero, ?_⟩
      have hd : dN v N = 2 * (((N.coeff 0 0 : 𝔬)) : Fv) := by
        unfold dN
        conv_lhs => rw [hN', hessian_unary_det]
        push_cast; rfl
      rw [hd, hu, h0, pow_zero, one_mul, one_pow, mul_one, pow_one,
        mul_div_cancel_left₀ _ (two_ne_zero : (2 : Fv) ≠ 0)]
      exact norm_coe_unit v huu
    · exact h1
  exact ⟨u, huu, by rw [hN', hu, hν1, pow_one]⟩

/-! ### Rank three, dyadic -/

/-- **The ternary kernel at a dyadic place** (Gan–Hanke–Yu 2001, (6.10), (6.11), $\delta\notin A^\times$): an anisotropic ternary $N$
with the extension property whose determinant $\det H_N/8$ is not a unit times a square is $\langle\pi c\rangle\perp T$, $c$ a
unit, $T$ unimodular with $\bar T$ anisotropic. *Proof:* the residue zero space has dimension $1$ or $2$; dimension $2$ gives
$\langle u\rangle\perp\pi S$ (`exists_shape_bottom`), with $|\det H_N| = q^{-(e+2)}$ so that $\det H_N/8\cdot\pi^{2(e-1)}$ is a
unit; dimension $1$ gives $M\perp T$ with $\pi\mid M$ (`exists_shape_top`) and maximality makes $M = \langle\pi c\rangle$. -/
@[kb "ganhankeyu2001" "(6.10), (6.11) (odd rank, δ ∉ A×, w = −1: the ternary kernel at a dyadic place)"]
theorem kernel_three_dyadic_of_not_detSq (h2 : ¬ IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 3)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 3 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hdet : ¬ ∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ 3 * c ^ 2‖ = 1) :
    ∃ (c : 𝔬) (T : QuadForm 𝔬 2), IsUnit c ∧ IsUnit T.hessian.det ∧
      (∀ s : Fin 2 → 𝔬, NF.π v ∣ T.eval s → ∀ i, NF.π v ∣ s i) ∧
      DVR.IsGLEquiv N (splitForm (NF.π v * c) T) := by
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
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h20
  have hn2 : ‖((2 : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := Tamagawa.norm_coe_of_pow_dvd v he he'
  have h2c : ‖(2 : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := by rw [← hn2, ← map_ofNat (algebraMap 𝔬 Fv) 2]; rfl
  have hQ0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast DVR.q_pos
  rcases (show s = 1 ∨ s = 2 by omega) with hs1 | hs2
  · obtain ⟨M, T, hTu, hTan, hMd, hM⟩ := exists_shape_top (m := 1) hπ h2π h20 N han' hs1
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
    refine ⟨c', T, hc'u, hTu, hTan, ?_⟩
    rw [hMc, hc', orthSum_unary_eq_splitForm] at hM
    exact hM
  · exfalso
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
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; exact absurd (by simpa using h2π) he'
      · exact h0
    have hdetN : ‖dN v N‖ = ((DVR.q 𝔬 : ℝ) ^ (e + 2))⁻¹ := by
      rw [dN, norm_det_of_isGLEquiv v hM, Hanke2011Structure.hessian_orthSum_det, hMc, hessian_unary_det,
        hessian_smul_det_two]
      obtain ⟨w, hw⟩ := he
      have hwu : IsUnit w := dvr_isUnit_of_not_dvd hπ fun h => he' (by
        rw [hw, pow_succ]; exact mul_dvd_mul_left _ h)
      rw [hw, show NF.π v ^ e * w * u * (NF.π v ^ 2 * S.hessian.det) =
        NF.π v ^ (e + 2) * (w * u * S.hessian.det) by ring]
      exact norm_pi_pow_mul_unit v (e + 2) ((hwu.mul huu).mul hSu)
    apply hdet
    have hπ0 : ((NF.π v : 𝔬) : Fv) ≠ 0 := pi_ne_zero_Fv v
    refine ⟨((NF.π v : 𝔬) : Fv) ^ (e - 1), pow_ne_zero _ hπ0, ?_⟩
    rw [norm_mul, norm_div, norm_pow, norm_pow, hdetN, h2c, norm_pi_pow_Fv]
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    field_simp
    ring

/-! ### Rank three, non-dyadic -/

/-- **A residually isotropic unit plane is isotropic** ($\pi\nmid2$): if $\pi\mid u_0s_0^2+u_1s_1^2$ with $s\not\equiv0$, then
$u_0y^2+u_1 = 0$ has a root $y\in\mathfrak o$ (local square theorem). -/
theorem exists_zero_of_res_isotropic (h2 : IsUnit (2 : 𝔬)) {u₀ u₁ : 𝔬} (hu₀ : IsUnit u₀) (hu₁ : IsUnit u₁)
    (s : Fin 2 → 𝔬) (hs : NF.π v ∣ u₀ * s 0 ^ 2 + u₁ * s 1 ^ 2) (hs' : ¬ ∀ i, NF.π v ∣ s i) :
    ∃ y : 𝔬, u₀ * y ^ 2 + u₁ = 0 := by
  have hπ := NF.irreducible_π v
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  have hp := hπ.prime
  have hunit : IsUnit (s 0) ∧ IsUnit (s 1) := by
    by_contra hcon
    apply hs'
    have key : NF.π v ∣ s 0 ↔ NF.π v ∣ s 1 := by
      constructor
      · intro h0
        have : NF.π v ∣ u₁ * s 1 ^ 2 := by
          have := dvd_sub hs (dvd_mul_of_dvd_right (dvd_pow h0 two_ne_zero) u₀)
          simpa using this
        rcases hp.dvd_or_dvd this with h | h
        · exact absurd (isUnit_of_dvd_unit h hu₁) hπ.not_isUnit
        · exact hp.dvd_of_dvd_pow h
      · intro h1
        have : NF.π v ∣ u₀ * s 0 ^ 2 := by
          have := dvd_sub hs (dvd_mul_of_dvd_right (dvd_pow h1 two_ne_zero) u₁)
          simpa using this
        rcases hp.dvd_or_dvd this with h | h
        · exact absurd (isUnit_of_dvd_unit h hu₀) hπ.not_isUnit
        · exact hp.dvd_of_dvd_pow h
    intro i
    by_cases h0 : NF.π v ∣ s 0
    · fin_cases i
      · exact h0
      · exact key.1 h0
    · exfalso
      apply hcon
      exact ⟨dvr_isUnit_of_not_dvd hπ h0, dvr_isUnit_of_not_dvd hπ fun h1 => h0 (key.2 h1)⟩
  obtain ⟨h0, h1⟩ := hunit
  obtain ⟨i0, a1⟩ : ∃ i0 : 𝔬, u₀ * i0 = 1 := ⟨_, hu₀.mul_val_inv⟩
  obtain ⟨j0, a2⟩ : ∃ j0 : 𝔬, s 0 * j0 = 1 := ⟨_, h0.mul_val_inv⟩
  obtain ⟨j1, a3⟩ : ∃ j1 : 𝔬, s 1 * j1 = 1 := ⟨_, h1.mul_val_inv⟩
  have hm1 : NF.π v ∣ -u₁ * i0 * s 1 ^ 2 * j0 ^ 2 - 1 := by
    have e : -u₁ * i0 * s 1 ^ 2 * j0 ^ 2 - 1 = -(u₀ * s 0 ^ 2 + u₁ * s 1 ^ 2) * i0 * j0 ^ 2 := by
      linear_combination (s 0 * j0) ^ 2 * a1 + (s 0 * j0 + 1) * a2
    rw [e]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_neg.mpr hs) _) _
  obtain ⟨a, ha⟩ := LocalZeta.exists_sq_of_dvd_sub_one v hπ2 hm1
  refine ⟨a * s 0 * j1, ?_⟩
  linear_combination (-u₀ * s 0 ^ 2 * j1 ^ 2) * ha + (-u₁ * (s 0 * j0) ^ 2 * (s 1 * j1) ^ 2) * a1 +
    (-u₁ * (s 0 * j0 + 1) * (s 1 * j1) ^ 2) * a2 + (-u₁ * (s 1 * j1 + 1)) * a3

/-- $|\det H(\langle u\rangle\perp\langle\pi w\rangle)| = q^{-b}$ when $2$, the $u_i$ and the $w_j$ are units. -/
theorem norm_det_unitSum_pi (h2 : IsUnit (2 : 𝔬)) {a b : ℕ} (u' : Fin a → 𝔬) (hu' : ∀ i, IsUnit (u' i))
    (w : Fin b → 𝔬) (hw : ∀ j, IsUnit (w j)) :
    ‖(((unitSum (QuadForm.diag fun j => NF.π v * w j) a u').hessian.det : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ b)⁻¹ := by
  rw [det_hessian_unitSum, DVR.det_hessian_diag, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hU : IsUnit (2 ^ a * (∏ i, u' i) * (2 ^ b * ∏ j, w j)) :=
    ((h2.pow a).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => hu' i)).mul
      ((h2.pow b).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => hw j))
  rw [show 2 ^ a * (∏ i, u' i) * (2 ^ b * (NF.π v ^ b * ∏ j, w j)) =
    NF.π v ^ b * (2 ^ a * (∏ i, u' i) * (2 ^ b * ∏ j, w j)) by ring]
  exact norm_pi_pow_mul_unit v b hU

/-- An even valuation of the determinant makes $\det H/8$ a unit times a square ($2$ a unit, rank $3$). -/
theorem detSq_of_even (h2 : IsUnit (2 : 𝔬)) (N X : QuadForm 𝔬 3) (hE : DVR.IsGLEquiv N X) {b : ℕ} (hb : Even b)
    (hX : ‖((X.hessian.det : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ b)⁻¹) :
    ∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ 3 * c ^ 2‖ = 1 := by
  obtain ⟨j, rfl⟩ := hb
  have hπ0 : ((NF.π v : 𝔬) : Fv) ≠ 0 := pi_ne_zero_Fv v
  have h2n : ‖(2 : Fv)‖ = 1 := by
    have := norm_coe_unit v h2
    rwa [show (((2 : 𝔬)) : Fv) = 2 from map_ofNat (algebraMap 𝔬 Fv) 2] at this
  have hQ0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast DVR.q_pos
  refine ⟨(((NF.π v : 𝔬) : Fv) ^ j)⁻¹, inv_ne_zero (pow_ne_zero _ hπ0), ?_⟩
  rw [dN, norm_mul, norm_div, norm_det_of_isGLEquiv v hE, norm_pow, norm_pow, norm_inv, hX, h2n, norm_pi_pow_Fv]
  field_simp
  ring

/-- **The ternary kernel at a non-dyadic place** (Gan–Hanke–Yu 2001, (6.10), (6.11), $\delta\notin A^\times$): an anisotropic ternary
$N$ with the extension property whose determinant is not a unit times a square is $\langle\pi c\rangle\perp T$ with $c$ a unit and
$T = \langle u_0,u_1\rangle$ unimodular with $\bar T$ anisotropic. *Proof:* diagonalize, $N\simeq\langle u'\rangle\perp\langle\pi w\rangle$
(`exists_diag_pi`, `nu_le_one`, `exists_shape_of_nu`); $b\le2$ (`aniso_of_maxProp`, `rank_le_two`), $b$ odd (determinant), so
$b = 1$; $\langle u'_0,u'_1\rangle$ is residually anisotropic by Hensel (`exists_zero_of_res_isotropic`). -/
@[kb "ganhankeyu2001" "(6.10), (6.11) (odd rank, δ ∉ A×, w = −1: the ternary kernel at a non-dyadic place)"]
theorem kernel_three_odd_of_not_detSq (h2 : IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 3) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 3 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hdet : ¬ ∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ 3 * c ^ 2‖ = 1) :
    ∃ (c : 𝔬) (T : QuadForm 𝔬 2), IsUnit c ∧ IsUnit T.hessian.det ∧
      (∀ s : Fin 2 → 𝔬, NF.π v ∣ T.eval s → ∀ i, NF.π v ∣ s i) ∧
      DVR.IsGLEquiv N (splitForm (NF.π v * c) T) := by
  have hπ := NF.irreducible_π v
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  have han' := aniso_integral v N han
  obtain ⟨ν, u, hu, hE⟩ := exists_diag_pi N hN hπ hπ2
  have MP1 := maxProp_of_isGLEquiv v hE hmax
  have hν := nu_le_one v ν u MP1
  obtain ⟨a, b, h, u', w, hu', hw, hE2⟩ := exists_shape_of_nu (NF.π v) ν hν u hu
  have hb3 : b ≤ 3 := by omega
  interval_cases b
  · obtain rfl : a = 3 := by omega
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 3 u') := hE.trans hE2
    exact absurd (detSq_of_even v h2 N _ hE3 ⟨0, rfl⟩ (norm_det_unitSum_pi v h2 u' hu' w hw)) hdet
  · obtain rfl : a = 2 := by omega
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 2 u') := hE.trans hE2
    -- the residue anisotropy of `⟨u'₀, u'₁⟩`
    have hTan : ∀ s : Fin 2 → 𝔬, NF.π v ∣ (QuadForm.diag u').eval s → ∀ i, NF.π v ∣ s i := by
      intro s hs
      by_contra hs'
      have hs2 : NF.π v ∣ u' 0 * s 0 ^ 2 + u' 1 * s 1 ^ 2 := by
        have e : (QuadForm.diag u').eval s = u' 0 * s 0 ^ 2 + u' 1 * s 1 ^ 2 := by
          simp [QuadForm.diag, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, Matrix.diagonal_apply]; ring
        rwa [e] at hs
      obtain ⟨y, hy⟩ := exists_zero_of_res_isotropic v h2 (hu' 0) (hu' 1) s hs2 hs'
      -- the isotropic vector `(y, 1, 0)` of `⟨u'₀, u'₁⟩ ⊥ ⟨πw⟩`
      have hz := aniso_of_isGLEquiv hE3 han' ![y, 1, 0] (by
        rw [unitSum_diag]
        simp [QuadForm.diag, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_three, Matrix.diagonal_apply, cseq,
          Fin.tail]
        linear_combination hy)
      have := congrFun hz 1
      simp at this
    refine ⟨w 0, QuadForm.diag u', hw 0, ?_, hTan, ?_⟩
    · rw [DVR.det_hessian_diag]
      exact (h2.pow 2).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => hu' i)
    · refine hE3.trans ?_
      rw [unitSum_diag]
      have e2 : splitForm (NF.π v * w 0) (QuadForm.diag u') =
          QuadForm.diag (Fin.cons (NF.π v * w 0) u' : Fin 3 → 𝔬) := by
        rw [diag_succ (Fin.cons (NF.π v * w 0) u' : Fin 3 → 𝔬), Fin.cons_zero, Fin.tail_cons]
      have e : (Fin.cons (NF.π v * w 0) u' : Fin 3 → 𝔬) =
          cseq (fun j : Fin 1 => NF.π v * w j) 2 u' ∘ (finRotate 3).symm := by
        funext i; fin_cases i <;> rfl
      rw [e2, e]
      exact isGLEquiv_diag_perm _ _
  · obtain rfl : a = 1 := by omega
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 1 u') := hE.trans hE2
    exact absurd (detSq_of_even v h2 N _ hE3 ⟨1, rfl⟩ (norm_det_unitSum_pi v h2 u' hu' w hw)) hdet
  · obtain rfl : a = 0 := by omega
    have hE3 : DVR.IsGLEquiv N (unitSum (QuadForm.diag fun j => NF.π v * w j) 0 u') := hE.trans hE2
    have MP2 := maxProp_of_isGLEquiv v hE3 hmax
    have A := aniso_of_maxProp v w MP2
    have := rank_le_two v w A
    omega

end QuadFormsKB.Hanke2005
