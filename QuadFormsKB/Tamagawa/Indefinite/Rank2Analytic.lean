/-
# Siegel's formula with a rank-2 stabilizer: the analytic input and the characters

**Layer:** number fields. $F$ a number field, $\chi$ a real function on the finite places with $|\chi|\le1$.

**Proves**
* `not_hasProd_lamL_zero`: if $L(1,\chi) = \lim_{s\to1^+}L_F(s,\chi)$ exists (`HasLOne`), then the product
  $\prod_v(1-\chi(v)/Nv)$ does **not** converge unconditionally to $0$. *Proof:* otherwise the factors with $\chi(v)<0$
  (which are $>1$) have a convergent product, and comparing the partial products with those of
  $L_F(s,\chi)^{-1} = \prod_v(1-\chi(v)Nv^{-s})$ gives $L_F(s,\chi)\to\infty$ as $s\to1^+$.
* `finFactor_one_pos_of_anisotropicF`: for a nondegenerate **anisotropic** binary $Q_0$, the normalizing constant
  $\prod'_v\alpha_v(L,L)$ of `muTam Q₀ hQ 1` is positive (it is either Mathlib's junk value $1$ of a non-convergent product,
  or a convergent product, whose value is then not $0$ by the first item and `eventually_muLocSO_lamL_chiE`).
  So `muTam Q₀ hQ 1` (no convergence factors; **not** Weil's measure in rank 2) is a positive multiple of Weil's
  measure `muTamBin` (`muTam_one_eq_smul_muTamChi`), which is all the frame machinery needs.
* `chiForms` over every number field: $L(1,\chi)$ exists and is positive (`lOne_chiForms_nf`), and $\chi$ is the
  character `chiP` of the binary complement of any adapted frame off a finite set (`chiP_frame_eq_chiForms_nf`).
-/
import QuadFormsKB.Tamagawa.FrameSiegelReg
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTauTwoUncond
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereFibProof

open Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.RegProd NFEuler QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-! ### The analytic lemma -/

section Analytic

variable {χ : HeightOneSpectrum (𝓞 F) → ℝ}

theorem one_sub_mul_rpow_le_one_of_nonneg {c s : ℝ} (hc : 0 ≤ c) (v : HeightOneSpectrum (𝓞 F)) :
    1 - c * (normP v : ℝ) ^ (-s) ≤ 1 := by
  have : 0 ≤ (normP v : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem one_sub_mul_rpow_le_lam_of_neg {c s : ℝ} (hc : c < 0) (hs : 1 ≤ s) (v : HeightOneSpectrum (𝓞 F)) :
    1 - c * (normP v : ℝ) ^ (-s) ≤ 1 - c / (normP v : ℝ) := by
  have hN : (1 : ℝ) ≤ (normP v : ℝ) := by have := two_le_normP v; exact_mod_cast (by omega : 1 ≤ normP v)
  have h1 : (normP v : ℝ) ^ (-s) ≤ (normP v : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  rw [Real.rpow_neg_one] at h1
  rw [div_eq_mul_inv]
  nlinarith

/-- **The product $\prod_v(1-\chi(v)/Nv)$ does not converge unconditionally to $0$** when $L(1,\chi)$ exists. -/
theorem not_hasProd_lamL_zero (hχ : ∀ v, |χ v| ≤ 1) {c : ℝ} (hL : HasLOne χ c) : ¬ HasProd (lamL χ) 0 := by
  classical
  intro h0
  set ε : ℝ := 1 / (|c| + 2) with hε
  have hεpos : 0 < ε := by positivity
  -- a finite set beyond which all partial products are `< ε`
  obtain ⟨T0, hT0⟩ : ∃ T0 : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, T0 ⊆ T → ∏ v ∈ T, lamL χ v < ε := by
    have := (h0.eventually (gt_mem_nhds hεpos))
    rw [SummationFilter.unconditional_filter, Filter.eventually_atTop] at this
    exact this
  set a : ℝ → HeightOneSpectrum (𝓞 F) → ℝ := fun s v => 1 - χ v * (normP v : ℝ) ^ (-s) with ha
  have ha1 : ∀ v, a 1 v = lamL χ v := fun v => by
    simp only [ha, lamL, Real.rpow_neg_one, div_eq_mul_inv]
  have hapos : ∀ s, 1 ≤ s → ∀ v, 0 < a s v := fun s hs v => one_sub_mul_rpow_pos (hχ v) hs v
  have hlpos : ∀ v, 0 < lamL χ v := lamL_pos hχ
  set P0 : ℝ := ∏ v ∈ T0, lamL χ v with hP0
  have hP0pos : 0 < P0 := Finset.prod_pos fun v _ => hlpos v
  -- the bound on every partial product beyond `T0`
  have hbound : ∀ s, 1 < s → ∀ T, T0 ⊆ T → ∏ v ∈ T, a s v ≤ (∏ v ∈ T0, a s v) * (ε / P0) := by
    intro s hs T hT
    set Tn := (T \ T0).filter fun v => χ v < 0 with hTn
    have hdisj : Disjoint T0 Tn := Finset.disjoint_left.2 fun v hv hv' => by
      rw [hTn, Finset.mem_filter, Finset.mem_sdiff] at hv'
      exact hv'.1.2 hv
    have hsplit : ∏ v ∈ T, a s v = (∏ v ∈ T0, a s v) * ∏ v ∈ T \ T0, a s v := by
      rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hT]
    have hrest : ∏ v ∈ T \ T0, a s v ≤ ∏ v ∈ Tn, lamL χ v := by
      rw [hTn, ← Finset.prod_filter_mul_prod_filter_not (T \ T0) fun v => χ v < 0]
      have h1 : ∏ v ∈ (T \ T0).filter (fun v => χ v < 0), a s v ≤
          ∏ v ∈ (T \ T0).filter (fun v => χ v < 0), lamL χ v :=
        Finset.prod_le_prod₀ (fun v _ => (hapos s hs.le v).le) fun v hv => by
          rw [Finset.mem_filter] at hv
          simp only [ha, lamL]
          exact one_sub_mul_rpow_le_lam_of_neg hv.2 hs.le v
      have h2 : ∏ v ∈ (T \ T0).filter (fun v => ¬ χ v < 0), a s v ≤ 1 :=
        Finset.prod_le_one₀ (fun v _ => (hapos s hs.le v).le) fun v hv => by
          rw [Finset.mem_filter] at hv
          exact one_sub_mul_rpow_le_one_of_nonneg (not_lt.1 hv.2) v
      calc (∏ v ∈ (T \ T0).filter (fun v => χ v < 0), a s v) *
            ∏ v ∈ (T \ T0).filter (fun v => ¬ χ v < 0), a s v
          ≤ (∏ v ∈ (T \ T0).filter (fun v => χ v < 0), lamL χ v) * 1 :=
            mul_le_mul h1 h2 (Finset.prod_nonneg fun v _ => (hapos s hs.le v).le)
              (Finset.prod_nonneg fun v _ => (hlpos v).le)
        _ = _ := mul_one _
    have hTn' : P0 * ∏ v ∈ Tn, lamL χ v < ε := by
      rw [hP0, ← Finset.prod_union hdisj]
      refine hT0 _ Finset.subset_union_left
    have hTn'' : ∏ v ∈ Tn, lamL χ v ≤ ε / P0 := by
      rw [le_div_iff₀ hP0pos, mul_comm]; exact hTn'.le
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (hrest.trans hTn'') (Finset.prod_nonneg fun v _ => (hapos s hs.le v).le)
  -- hence `L(s, χ) ≥ P0 / (ε ∏_{T0} a s)`
  have hLs : ∀ s, 1 < s → P0 / (ε * ∏ v ∈ T0, a s v) ≤ LFunctionNF χ s := by
    intro s hs
    have hA : 0 < ∏ v ∈ T0, a s v := Finset.prod_pos fun v _ => hapos s hs.le v
    refine ge_of_tendsto (hasProd_LFunctionNF hχ hs) ?_
    rw [SummationFilter.unconditional_filter, Filter.eventually_atTop]
    refine ⟨T0, fun T hT => ?_⟩
    have hB := hbound s hs T hT
    have hTpos : 0 < ∏ v ∈ T, a s v := Finset.prod_pos fun v _ => hapos s hs.le v
    have he : ∏ v ∈ T, lFactor χ s v = (∏ v ∈ T, a s v)⁻¹ := by
      rw [← Finset.prod_inv_distrib]; rfl
    rw [he, div_le_iff₀ (mul_pos hεpos hA)]
    calc P0 = (∏ v ∈ T, a s v)⁻¹ * (∏ v ∈ T, a s v) * P0 := by field_simp
      _ ≤ (∏ v ∈ T, a s v)⁻¹ * ((∏ v ∈ T0, a s v) * (ε / P0)) * P0 := by gcongr
      _ = (∏ v ∈ T, a s v)⁻¹ * (ε * ∏ v ∈ T0, a s v) := by field_simp
  -- pass to the limit `s → 1⁺`
  have hcont : Tendsto (fun s => P0 / (ε * ∏ v ∈ T0, a s v)) (𝓝[>] 1) (𝓝 (P0 / (ε * P0))) := by
    have hprod : Tendsto (fun s => ∏ v ∈ T0, a s v) (𝓝[>] (1 : ℝ)) (𝓝 P0) := by
      have h : Tendsto (fun s => ∏ v ∈ T0, a s v) (𝓝 (1 : ℝ)) (𝓝 (∏ v ∈ T0, a 1 v)) := by
        refine tendsto_finsetProd T0 fun v _ => ?_
        have hN : (normP v : ℝ) ≠ 0 := by have := two_le_normP v; positivity
        exact (continuousAt_const.sub (continuousAt_const.mul
          ((Real.continuousAt_const_rpow hN).comp continuous_neg.continuousAt))).tendsto
      rw [Finset.prod_congr rfl fun v _ => ha1 v] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact tendsto_const_nhds.div (tendsto_const_nhds.mul hprod) (mul_pos hεpos hP0pos).ne'
  have hle : P0 / (ε * P0) ≤ c :=
    le_of_tendsto_of_tendsto hcont hL (eventually_nhdsWithin_of_forall fun s hs => hLs s hs)
  have : P0 / (ε * P0) = |c| + 2 := by
    rw [hε]; field_simp
  rw [this] at hle
  have := le_abs_self c
  linarith

end Analytic


/-! ### The normalizing constant of `muTam Q₀ hQ 1` for an anisotropic binary form -/

section Binary

variable (Q₀ : QuadForm (𝓞 F) 2)

/-- **$\prod'_v\alpha_v(L,L) > 0$ for a nondegenerate anisotropic binary form** (every number field). The product is not
absolutely convergent; Mathlib's `tprod` is either its junk value $1$ or a limit, and the limit is not $0$
(`not_hasProd_lamL_zero`, since $\alpha_v = 1-\chi_E(v)/Nv$ off a finite set). -/
theorem finFactor_one_pos_of_anisotropicF (hQ : Q₀.Nondegenerate) (h : AnisotropicF Q₀) :
    0 < finFactor Q₀ (fun _ => 1) := by
  classical
  obtain ⟨E, _, _, _, hE⟩ := exists_isDiscField_of_anisotropicF h
  have hχ := abs_chiE_le hE.finrank_eq_two
  obtain ⟨S, hS⟩ := eventually_muLocSO_lamL_chiE Q₀ hQ hE
  rw [finFactor_one Q₀ hQ]
  set f : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀ with hf
  have hfpos : ∀ v, 0 < f v := fun v => siegelDensity_self_pos' Q₀ hQ v
  by_cases hm : Multipliable f
  · refine lt_of_le_of_ne (tprod_nonneg fun v => (hfpos v).le) fun h0 => ?_
    set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => f v / lamL (chiE F E) v with hg
    have hg1 : ∀ v ∉ S, g v = 1 := fun v hv => by
      have := hS v hv
      rw [muLocSO_soStabSO, ← ENNReal.ofReal_one] at this
      have h' := (ENNReal.ofReal_eq_ofReal_iff (div_pos (hfpos v) (lamL_pos hχ v)).le zero_le_one).1 this
      exact h'
    have hgP : HasProd g (∏ v ∈ S, g v) := hasProd_prod_of_ne_finset_one hg1
    have hgpos : 0 < ∏ v ∈ S, g v := Finset.prod_pos fun v _ => div_pos (hfpos v) (lamL_pos hχ v)
    have hfP : HasProd f 0 := by rw [h0]; exact hm.hasProd
    have hdiv := hfP.div₀ hgP hgpos.ne'
    rw [zero_div] at hdiv
    have he : (fun v => f v / g v) = lamL (chiE F E) := funext fun v => by
      simp only [hg]; field_simp [(hfpos v).ne', (lamL_pos hχ v).ne']
    rw [he] at hdiv
    exact not_hasProd_lamL_zero hχ (lOne_chiE hE.finrank_eq_two).2 hdiv
  · rw [tprod_eq_one_of_not_multipliable hm]; exact one_pos

theorem muTam_one_ne_zero_of_anisotropicF (hQ : Q₀.Nondegenerate) (h : AnisotropicF Q₀) :
    muTam Q₀ hQ (fun _ => 1) ≠ 0 := by
  intro h0
  have h1 : muTam Q₀ hQ (fun _ => 1) (Set.univ ×ˢ (KSO Q₀ : Set (SOAf Q₀))) = 0 := by rw [h0]; rfl
  rw [muTam, MeasureTheory.Measure.prod_prod, muFin_KSO] at h1
  exact (mul_ne_zero (muArchTamSO_univ_ne_zero Q₀ hQ)
    (ENNReal.ofReal_pos.mpr (finFactor_one_pos_of_anisotropicF Q₀ hQ h)).ne') h1

end Binary

end QuadFormsKB.Tamagawa.Indefinite
