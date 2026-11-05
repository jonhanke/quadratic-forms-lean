/-
# Hanke 2005, (3.3) at one place: Shimura's condition is only needed at the place itself

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005), (3.3)
(locators refer to the 1999 thesis of the same title); G. Shimura, *Exact mass formulas
for orthogonal groups*, 1999, Thm 8.6(3) and Prop. 3.9.

Shimura's local factor (3.3) of the maximal lattice $\Lambda=\mathcal O_F^n$,
$$\alpha_\mathfrak p(\Lambda,\Lambda) = [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\;\xi_\mathfrak p,$$
is proved in the library, but every earlier interface (`siegelDensity_dyadicBad`, `siegelDensity_oddRamified`,
`shimuraMaximalDensity_of_rest`, ...) takes Shimura's hypothesis `ShimuraDetHyp Q₀` *globally* (at every finite place when $n$
is odd). The proofs only use it at the place $\mathfrak p$ under consideration. This file records that:

* `siegelDensity_eq_at`: for $3\le n$, $\Lambda$ maximal and a finite place $v$, if $n$ is odd and $\det H/2^n$ is a unit times a
  square at $v$ (`DetUnitSqAt v Q₀`), then `NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀`. The hypothesis is at $v$
  only, and is absent for even $n$.
* `shimuraMaximalDensity_proved : ShimuraMaximalDensity F`, the global statement, derived from it via `shimuraDetHyp_iff`.

Case split: non-dyadic / dyadic and $[\widetilde\Lambda:\Lambda]=1$ (`siegelDensity_selfDual_nondyadic`,
`siegelDensity_selfDual_dyadic`, no hypothesis); dyadic with index $\ne1$ (`siegelDensity_dyadicBad_at`, a copy of
`siegelDensity_dyadicBad` using `exists_hypSum_shape` and `dyadicKernelDensity_of_low`); non-dyadic with index $\ne1$
(`siegelDensity_oddRamified_at`, a copy of `siegelDensity_oddRamified` with the Jordan shape `oddMaximalShape_at`).
No named input remains.
-/
import QuadFormsKB.Literature.Hanke2005.GHYOddLocal
import QuadFormsKB.Literature.Hanke2005.DyadicR2Ram
import QuadFormsKB.Literature.Hanke2005.DensityDyadicWitt
import QuadFormsKB.Literature.Hanke2005.DensityDyadicSelfDual
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelShape
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelLow
import QuadFormsKB.Literature.Hanke2005.DensityOddWitt
import QuadFormsKB.Literature.Hanke2005.DensityOddShape
import QuadFormsKB.Literature.Hanke2005.DensityOddJordan

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

variable {F : Type} [Field F] [NumberField F]

/-- **Shimura's condition at one place forces an even valuation of the determinant** (odd $n$, $\mathfrak p\nmid2$): if
`DetUnitSqAt v Q₀` and $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]=q^b$, then $b$ is even. Per-place copy of
`even_of_shimuraDetHyp` (which only used its hypothesis at $v$). -/
@[kb "hanke2005crelle" "abstract, p. 1; §3, p. 7 (Shimura's condition on det φ at one place, valuation parity)"]
theorem even_of_detUnitSqAt (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)
    (hv : DetUnitSqAt v Q₀) (h2 : IsUnit (2 : v.adicCompletionIntegers F)) {b : ℕ}
    (hdual : dualIndexAt v Q₀ = (normQ v) ^ b) : Even b := by
  obtain ⟨c, hc0, hc⟩ := hv
  set D := (NF.Qp v Q₀).hessian.det with hDdef
  have key : algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) = (D : v.adicCompletion F) := by
    rw [hDdef, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have h2n : ‖(2 : v.adicCompletion F)‖ = 1 := by
    have := norm_coe_unit v h2
    have e : (((2 : v.adicCompletionIntegers F)) : v.adicCompletion F) = 2 :=
      map_ofNat (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) 2
    rwa [e] at this
  have hDn : ‖(D : v.adicCompletion F)‖ = ((normQ v) ^ b)⁻¹ := by
    unfold dualIndexAt at hdual
    rw [← hDdef] at hdual
    rw [← inv_inv ‖(D : v.adicCompletion F)‖, hdual]
  rw [map_div₀, map_pow, map_ofNat, key, norm_mul, norm_div, norm_pow, h2n, norm_pow, hDn] at hc
  simp only [one_pow, div_one] at hc
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  have hcz := QuadFormsKB.LocalZeta.norm_eq_absNorm_pow v hc0
  have hA : normQ v = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← DensitySD.q_eq v, NF.q_completion]
  rw [hcz, ← hA] at hc
  set z := WithZero.log (Valued.v c) with hz
  have hc' : (normQ v) ^ (2 * z) = (normQ v) ^ (b : ℤ) := by
    have hb : (normQ v) ^ b ≠ 0 := pow_ne_zero _ hq0.ne'
    have h3 : ((normQ v) ^ z) ^ 2 = (normQ v) ^ b := by
      have : ((normQ v) ^ b)⁻¹ * ((normQ v) ^ z) ^ 2 = 1 := hc
      field_simp at this
      linarith
    rw [two_mul, zpow_add₀ hq0.ne', zpow_natCast, ← h3]
    ring
  have := zpow_right_injective₀ hq0 (one_lt_normQ v).ne' hc'
  exact ⟨b / 2, by omega⟩

/-- **The Jordan shape and Witt data of a maximal lattice at an odd place, without Shimura's hypothesis** (O'Meara 91:2, §92,
§63; proved). The conclusion of `OddMaximalShape.shape` for a single place $v$ with $2$ a unit and
$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\ne1$; the hypothesis `ShimuraDetHyp` of `oddMaximalJordan` was never used. -/
@[kb "omeara1963" "91:2, §92, §63 (Jordan shape U ⊥ πW and Witt type of a maximal lattice at an odd place; proved, no det hypothesis)"]
theorem oddMaximalShape_at {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (v : HeightOneSpectrum (𝓞 F)) (h2 : IsUnit (2 : v.adicCompletionIntegers F))
    (h1 : dualIndexAt v Q₀ ≠ 1) :
    ∃ (a b : ℕ) (h : b + a = n) (u : Fin a → v.adicCompletionIntegers F)
        (W T : QuadForm (v.adicCompletionIntegers F) b),
        (∀ i, IsUnit (u i)) ∧ IsUnit W.hessian.det ∧ (∀ i j, T.coeff i j = NF.π v * W.coeff i j) ∧
        (b = 1 ∨ b = 2) ∧ (b = 2 → chiDisc W = -1) ∧
        IsGLEquiv (NF.Qp v Q₀) (h ▸ unitSum T a u) ∧
        (b = 1 → Even n → anisoDim v Q₀ = 2 ∧ IsRamifiedAt v Q₀) ∧
        (b = 2 → ¬ IsRamifiedAt v Q₀ ∧
          (Even a → (chiDisc (QuadForm.diag u) = 1 → anisoDim v Q₀ = 2) ∧
            (chiDisc (QuadForm.diag u) = -1 → anisoDim v Q₀ = 4)) ∧
          (Odd a → anisoDim v Q₀ = 3)) := by
  have hπ := NF.irreducible_π v
  have hπ2 := DensitySD.not_dvd_two v h2
  have hQp := NF.nondegenerate_Qp v hQ
  have MP0 := maxProp_Qp v Q₀ hQ hmax
  obtain ⟨ν, u, hu, hE⟩ := exists_diag_pi (NF.Qp v Q₀) hQp hπ hπ2
  have MP1 := maxProp_of_isGLEquiv v hE MP0
  have hν := nu_le_one v ν u MP1
  obtain ⟨a, b, h, u', w, hu', hw, hE2⟩ := exists_shape_of_nu (NF.π v) ν hν u hu
  have hEq := hE.trans hE2
  subst h
  have MP2 := maxProp_of_isGLEquiv v hEq MP0
  have MP3 := maxProp_of_unitSum v (QuadForm.diag fun j => NF.π v * w j) a u' MP2
  have A := aniso_of_maxProp v w MP3
  have hb2 := rank_le_two v w A
  have hWdet : IsUnit (QuadForm.diag w).hessian.det := by
    rw [DVR.det_hessian_diag]
    exact (h2.pow b).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hw i))
  have hT : ∀ i j, (QuadForm.diag fun j => NF.π v * w j).coeff i j = NF.π v * (QuadForm.diag w).coeff i j := by
    intro i j
    simp only [QuadForm.diag, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hb1 : 1 ≤ b := by
    by_contra hb0
    have hb0' : b = 0 := by omega
    obtain ⟨w0, hw0, hD⟩ := det_shape v h2 u' hu' (QuadForm.diag w) (QuadForm.diag fun j => NF.π v * w j)
      hWdet hT (NF.Qp v Q₀) hEq
    rw [show NF.π v ^ b = 1 by rw [hb0', pow_zero], one_mul] at hD
    apply h1
    unfold dualIndexAt
    rw [hD, norm_coe_unit v hw0, inv_one]
  have hχ : b = 2 → chiDisc (QuadForm.diag w) = -1 := by
    intro hb
    subst hb
    exact chiDisc_diag_two v h2 w hw A
  have hb12 : b = 1 ∨ b = 2 := by omega
  obtain ⟨w', hw', hD⟩ := det_shape v h2 u' hu' (QuadForm.diag w) (QuadForm.diag fun j => NF.π v * w j)
    hWdet hT (NF.Qp v Q₀) hEq
  refine ⟨a, b, rfl, u', QuadForm.diag w, QuadForm.diag fun j => NF.π v * w j, hu', hWdet, hT, hb12, hχ, hEq,
    fun hb1' hev => ?_, fun hb2' => ?_⟩
  · subst hb1'
    obtain ⟨hns, hram⟩ := not_isSquare_and_ramified_of_odd v Q₀ h2 odd_one hw' (by simpa using hD)
    exact ⟨(anisoDim_eq_two_iff v Q₀ hQ hev).2 hns, hram⟩
  · subst hb2'
    refine ⟨not_ramified_of_two v Q₀ h2 hw' hD, ?_⟩
    exact (oddWittType F).witt Q₀ hQ v h2 a rfl u' (QuadForm.diag w) (QuadForm.diag fun j => NF.π v * w j) hu'
      hWdet hT (hχ rfl) ⟨w, rfl, rfl⟩ hEq

open DensitySD in
/-- **Siegel's density at a non-dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, Shimura's condition at that
place only:** $\alpha_\mathfrak p=[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi$. Per-place copy of `siegelDensity_oddRamified`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (non-dyadic places with Λ̃_p ≠ Λ_p; Shimura's condition at the place only)"]
theorem siegelDensity_oddRamified_at (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀)
    (hv : Odd n → DetUnitSqAt v Q₀)
    (h2 : IsUnit (2 : v.adicCompletionIntegers F)) (h1 : dualIndexAt v Q₀ ≠ 1) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  obtain ⟨a, b, h, u, W, T, hu, hW, hT, hb, hχW, hequiv, hb1, hb2⟩ := oddMaximalShape_at hn Q₀ hQ hmax v h2 h1
  subst h
  have hπ := NF.irreducible_π v
  have hπ2 := not_dvd_two v h2
  have hq := q_eq v
  have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
  obtain ⟨U, hU, hUe⟩ := hequiv
  have hiso : Siegel.IsometricGL (NF.Qp v Q₀) (unitSum T a u) :=
    ⟨Matrix.nonsingInvUnit U hU, fun x => (hUe x).symm⟩
  have hβ : DVR.localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v) =
      DVR.localDensityForm (unitSum T a u) (unitSum T a u) (NF.π v) :=
    (DVR.localDensityForm_congr_left hiso (NF.Qp v Q₀) (NF.π v)).trans
      (DVR.localDensityForm_congr_right (unitSum T a u) hiso (NF.π v))
  -- the dual index is q^b
  obtain ⟨w, hwc, hD2⟩ := det_shape v h2 u hu W T hW hT (NF.Qp v Q₀) ⟨U, hU, hUe⟩
  set D := (NF.Qp v Q₀).hessian.det with hDdef
  have hnorm : ‖((D : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ b)⁻¹ :=
    norm_coe_of_pow_dvd v ⟨_, hD2⟩ (by
      rw [hD2, pow_succ]
      intro hd
      exact hπ.not_isUnit (isUnit_of_dvd_unit ((mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 hd) hwc))
  have hdual : dualIndexAt v Q₀ = (normQ v) ^ b := by
    unfold dualIndexAt
    rw [← hDdef, hnorm, inv_inv, hq]
  have hdiagU : ¬ NF.π v ∣ (QuadForm.diag u).hessian.det := by
    rw [det_hessian_diag]
    exact DVR.dvr_not_dvd_of_isUnit hπ
      ((h2.pow a).mul (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hu i)))
  have hWnd : ¬ NF.π v ∣ W.hessian.det := DVR.dvr_not_dvd_of_isUnit hπ hW
  rw [hdual, NF.siegelDensity, if_pos rfl, NF.localDensityForm_eq_completion, hβ,
    density_oddShape hπ hπ2 u hu W T hW hT, hq]
  unfold xiAt
  rw [eq_false h1]
  rcases hb with rfl | rfl
  · have hev : Even (1 + a) := by
      by_contra hne
      rw [Nat.not_even_iff_odd] at hne
      have := even_of_detUnitSqAt v Q₀ (hv hne) h2 (b := 1) (by rw [hdual, pow_one])
      exact Nat.not_even_one this
    obtain ⟨ht, hram⟩ := hb1 rfl hev
    obtain ⟨m, hm⟩ := hev
    obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨m - 1, by omega⟩
    have hd := localDensityForm_self_odd (NF.π v) k (QuadForm.diag u) hπ hπ2 hdiagU
    have hw1 := localDensityForm_self_odd (NF.π v) 0 W hπ hπ2 hWnd
    rw [hd, hw1]
    simp only [hq]
    rw [ht]
    simp only [xiShimura]
    rw [if_pos hram]
    have hm' : (1 + (2 * k + 1)) / 2 - 1 = k := by omega
    rw [hm', ppow_eq hq0]
    norm_num
    ring
  · obtain ⟨hram, hEven, hOdd⟩ := hb2 rfl
    have hχ := hχW rfl
    have hw2 := localDensityForm_self_even (NF.π v) 1 le_rfl W hπ hπ2 hWnd
    rw [hχ] at hw2
    rw [hw2]
    simp only [hq]
    rcases Nat.even_or_odd' a with ⟨k, rfl | rfl⟩
    · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
      have hd := localDensityForm_self_even (NF.π v) (l + 1) (by omega) (QuadForm.diag u) hπ hπ2 hdiagU
      rw [hd]
      simp only [hq]
      have hm' : (2 + 2 * (l + 1)) / 2 = l + 2 := by omega
      have hy : normQ v ^ (l + 2) = normQ v ^ (l + 1) * normQ v := by ring
      have hy2 : normQ v ^ (2 * (l + 1)) = (normQ v ^ (l + 1)) ^ 2 := by ring
      have hP : ppow (normQ v) (l + 1) = (∏ i ∈ Finset.range l, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) *
          (1 - ((normQ v ^ (l + 1)) ^ 2)⁻¹) := by
        rw [ppow_eq hq0, Finset.prod_range_succ, hy2]
      have hr : normQ v ^ (1 - ((l + 2 : ℕ) : ℝ)) = (normQ v ^ (l + 1))⁻¹ := by
        rw [Real.rpow_sub hq0, Real.rpow_one, Real.rpow_natCast, hy]
        field_simp
      have hyp : 0 < normQ v ^ (l + 1) := pow_pos hq0 _
      rcases chiDisc_pm hπ hπ2 (QuadForm.diag u) hdiagU with he | he
      · rw [(hEven (even_two_mul _)).1 he]
        simp only [xiShimura, hm', hram, if_false, ite_false]
        rw [show l + 2 - 1 = l + 1 from rfl, hP, hr, he]
        simp only [Nat.add_sub_cancel, Finset.range_zero, Finset.prod_empty, mul_one]
        norm_num
        generalize (∏ i ∈ Finset.range l, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) = P
        generalize normQ v ^ (l + 1) = y at *
        generalize normQ v = x at *
        field_simp
        ring
      · rw [(hEven (even_two_mul _)).2 he]
        simp only [xiShimura, hm']
        have hlt := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (one_lt_normQ v) (by omega : l + 1 ≠ 0))
        have hne : 1 - (normQ v ^ (l + 1))⁻¹ ≠ 0 := sub_ne_zero.2 (ne_of_gt hlt)
        have hy1 : 1 < normQ v ^ (l + 1) := one_lt_pow₀ (one_lt_normQ v) (by omega : l + 1 ≠ 0)
        have hne2 : normQ v ^ (l + 1) - 1 ≠ 0 := sub_ne_zero.2 hy1.ne'
        have hne3 : -1 + normQ v ^ (l + 1) ≠ 0 := by intro h; apply hne2; linarith
        have hne' : 1 - normQ v ^ (1 - ((l + 2 : ℕ) : ℝ)) ≠ 0 := by rw [hr]; exact hne
        rw [show l + 2 - 1 = l + 1 from rfl, hP, he]
        rw [hr] at hne' ⊢
        simp only [Nat.add_sub_cancel, Finset.range_zero, Finset.prod_empty, mul_one]
        norm_num
        generalize (∏ i ∈ Finset.range l, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) = P
        generalize normQ v ^ (l + 1) = y at *
        generalize normQ v = x at *
        field_simp
        ring
    · have hd := localDensityForm_self_odd (NF.π v) k (QuadForm.diag u) hπ hπ2 hdiagU
      rw [hd]
      simp only [hq]
      have ht := hOdd (odd_two_mul_add_one k)
      have hm' : (2 + (2 * k + 1)) / 2 = k + 1 := by omega
      rw [ht]
      simp only [xiShimura, hm', Nat.add_sub_cancel, ppow_eq hq0]
      norm_num
      generalize (∏ i ∈ Finset.range k, (1 - ((normQ v) ^ (2 * (i + 1)))⁻¹)) = P
      generalize normQ v = x at *
      field_simp
      ring

open DensitySD in
/-- **Siegel's density at a dyadic place with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, Shimura's condition at that
place only:** $\alpha_\mathfrak p=[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi$. Per-place copy of
`siegelDensity_dyadicBad` with the shape from `exists_hypSum_shape` and the kernel density `dyadicKernelDensity_of_low`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p ≠ Λ_p; Shimura's condition at the place only)"]
theorem siegelDensity_dyadicBad_at (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hv : Odd n → DetUnitSqAt v Q₀)
    (h2 : ¬ IsUnit (2 : v.adicCompletionIntegers F)) (h1 : dualIndexAt v Q₀ ≠ 1) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  have IB : DyadicKernelDensity F := dyadicKernelDensity_of_low (R2Ram.dyadicKernelDensityLow_proved (F := F))
  obtain ⟨k, r, h, N, hNnd, hNmax, hNan, hequiv⟩ :=
    exists_hypSum_shape v n (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) (maxProp_Qp v Q₀ hQ hmax)
  subst h
  have ht := anisoDim_of_hypSum v Q₀ hQ N hNan hequiv
  obtain ⟨U, hU, hUe⟩ := hequiv
  have hiso : Siegel.IsometricGL (NF.Qp v Q₀) (hypSum N k) :=
    ⟨Matrix.nonsingInvUnit U hU, fun x => (hUe x).symm⟩
  have hβ : DVR.localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v) =
      DVR.localDensityForm (hypSum N k) (hypSum N k) (NF.π v) :=
    (DVR.localDensityForm_congr_left hiso (NF.Qp v Q₀) (NF.π v)).trans
      (DVR.localDensityForm_congr_right (hypSum N k) hiso (NF.π v))
  -- the determinants
  set DQ := (NF.Qp v Q₀).hessian.det with hDQ
  set DH := (hypSum N k).hessian.det with hDH
  have hHess := DVR.hessian_eq_of_eval hUe
  have hDHeq : DH = U.det * U.det * DQ := by
    rw [hDH, hHess, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hcoe : ((DH : v.adicCompletionIntegers F) : v.adicCompletion F) =
      ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ^ 2 *
        ((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hDHeq]; push_cast; ring
  have hnormU := norm_coe_unit v hU
  have hnormDH : ‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
      ‖((DQ : v.adicCompletionIntegers F) : v.adicCompletion F)‖ := by
    rw [hcoe, norm_mul, norm_pow, hnormU, one_pow, one_mul]
  have hdual : dualIndexAt v Q₀ = ‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ := by
    unfold dualIndexAt
    rw [← hDQ, hnormDH]
  -- the cast of the global determinant
  have key : algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) =
      ((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hDQ, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hdisc : algebraMap F (v.adicCompletion F) (discK Q₀) =
      (-1) ^ ((r + 2 * k) / 2) * (((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k)) := by
    unfold discK
    rw [map_mul, map_div₀, map_pow, map_pow, map_neg, map_one, map_ofNat, key]
  -- ramification
  have hram : IsRamifiedAt v Q₀ ↔ ¬ IsUnramSqrt v ((-1) ^ ((r + 2 * k) / 2) *
      ((((DH : v.adicCompletionIntegers F) : v.adicCompletion F)) / 2 ^ (r + 2 * k))) := by
    unfold IsRamifiedAt
    rw [hdisc, hcoe]
    refine not_congr ?_
    have : (-1 : v.adicCompletion F) ^ ((r + 2 * k) / 2) *
        (((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ^ 2 *
          ((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k)) =
        ((-1) ^ ((r + 2 * k) / 2) *
          (((DQ : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k))) *
          ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ^ 2 := by ring
    rw [this]
    exact (isUnramSqrt_mul_unit_sq v _ _ hU).symm
  -- Shimura's hypothesis for the kernel sum, from the condition at v
  have hdetH : Odd (r + 2 * k) → ∃ c : v.adicCompletion F, c ≠ 0 ∧
      ‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k) * c ^ 2‖ = 1 := by
    intro hodd
    obtain ⟨c, hc0, hc⟩ := hv hodd
    rw [map_div₀, map_pow, map_ofNat, key] at hc
    have hs0 : ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnormU
      exact zero_ne_one hnormU
    refine ⟨c / ((U.det : v.adicCompletionIntegers F) : v.adicCompletion F), div_ne_zero hc0 hs0, ?_⟩
    rw [← hc, hcoe]
    congr 1
    field_simp
  have hB := IB.density v h2 hn N hNnd hNmax hNan (by rw [← hdual]; exact h1) hdetH
  have hxi : xiAt v Q₀ = xiShimura (normQ v) (r + 2 * k) r
      (¬ IsUnramSqrt v ((-1) ^ ((r + 2 * k) / 2) *
        ((((DH : v.adicCompletionIntegers F) : v.adicCompletion F)) / 2 ^ (r + 2 * k))))
      (‖((DH : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ = 1) := by
    unfold xiAt
    rw [ht, hdual]
    congr 1
    exact propext hram
  rw [NF.siegelDensity, if_pos rfl, NF.localDensityForm_eq_completion, hβ, hB, hxi, hdual, ← hDH]
  ring

/-- **(3.3) at one place, under Shimura's condition at that place only** (Hanke 2005, (3.3), p. 8; Shimura 1999, Thm 8.6(3),
Prop. 3.9): for $3\le n$, $\Lambda=\mathcal O_F^n$ maximal and a finite place $v$ such that, if $n$ is odd, $\det H/2^n$ is a unit
times a square at $v$ (`DetUnitSqAt v Q₀`), Siegel's density is
$\alpha_v(\Lambda,\Lambda)=[\widetilde\Lambda_v:\Lambda_v]\,\xi_v$. Unconditional apart from this per-place condition. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (at one place, under Shimura's condition at that place)"]
theorem siegelDensity_eq_at {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (v : HeightOneSpectrum (𝓞 F)) (hv : Odd n → DetUnitSqAt v Q₀) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAt v Q₀ := by
  by_cases h2 : IsUnit (2 : v.adicCompletionIntegers F)
  · by_cases h1 : dualIndexAt v Q₀ = 1
    · exact siegelDensity_selfDual_nondyadic v hn Q₀ hQ h2 h1
    · exact siegelDensity_oddRamified_at v hn Q₀ hQ hmax hv h2 h1
  · by_cases h1 : dualIndexAt v Q₀ = 1
    · exact siegelDensity_selfDual_dyadic (dyadicOrthogonalOrder_uncond F) v hn Q₀ hQ h2 h1
    · exact siegelDensity_dyadicBad_at v hn Q₀ hQ hmax hv h2 h1

/-- **Shimura's maximal-lattice density (3.3), proved:** `ShimuraMaximalDensity F` holds with no named input, from
`siegelDensity_eq_at` (the global `ShimuraDetHyp` gives `DetUnitSqAt` at every place by `shimuraDetHyp_iff`). -/
@[kb "hanke2005crelle" "(3.3), p. 8 (all places; proved)"]
theorem shimuraMaximalDensity_proved : ShimuraMaximalDensity F := by
  refine ⟨fun {n} hn Q₀ hQ hmax hdet v => ?_⟩
  rw [hankeBeta_gramV v Q₀ hQ, siegelDensity_eq_at hn Q₀ hQ hmax v (fun hodd => hdet hodd v)]
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow]
  have ha : 0 < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  generalize ‖(2 : v.adicCompletion F)‖ = a at *
  have hN : ((n * (n - 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    have hev : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    rw [Nat.cast_div hev (by norm_num)]
    rcases n with _ | n
    · simp
    · push_cast; simp
  have e : (a ^ n) ^ (((n : ℝ) + 1) / 2) * (a ^ n)⁻¹ = a ^ (n * (n - 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast a (n * (n - 1) / 2), hN, ← Real.rpow_mul ha.le,
      ← Real.rpow_neg (by positivity), ← Real.rpow_add ha]
    congr 1; ring
  rw [e]; ring

end QuadFormsKB.Hanke2005
