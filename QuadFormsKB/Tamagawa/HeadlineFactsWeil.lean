/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Measure.ProductSO
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoSimilar
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoFacts
import QuadFormsKB.Tamagawa.Indefinite.Rank2Measures
import QuadFormsKB.Tamagawa.Classical.Basic
import QuadFormsKB.Siegel.FourSquares
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteNF
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankZero
import QuadFormsKB.Tamagawa.FrameHM

/-!
# The side conditions of the 0.2.0 headline statements

The Tamagawa measures in the 0.2.0 headlines (`Challenge.lean`) contain the real product
$\prod'_v\mu_v(SO(L_v))$ (`Measure.finFactor`, a `tprod`, which is $1$ when the product does not converge), and some
contain $L_F(1,\chi)$ (`RegProd.LOne`, a limit, junk if the limit does not exist). This file collects, in the form
used by the headlines, the facts that rule out these default values. Each is a short consequence of library lemmas:

* `multipliable_muLocSO_lamL_chiE`: for a binary form with discriminant field $E$, the local masses
  $L_v(1,\chi_E)\,\mu_v(SO(L_v))$ are $1$ for almost all $v$ (`eventually_muLocSO_lamL_chiE`), so their product
  converges;
* `hasLOne_chiE`: $L_F(1,\chi_E) = \lim_{s\to1^+}L_F(s,\chi_E)$ exists and equals $\rho_E/\rho_F > 0$
  (`RegProd.hasLOne_relChar`, `lOne_chiE_eq`);
* `multipliable_muLocSO_lamV_of_isotropicF`: for an isotropic binary form the local masses
  $\zeta_{F,v}(1)\,\mu_v(SO(L_v))$ have a convergent product (`multipliable_siegelDensity_div_lamV`);
* `finite_repSet_sumTwoSqZ`: $x_0^2 + x_1^2 = m$ has finitely many integer solutions;
* `multipliable_localDensityForm_of_frame`, `multipliable_localDensityForm_corank1`,
  `multipliable_localDensityForm_half_corank0`: for a nondegenerate $Q_0$ over $\mathcal O_F$ of any signature and
  $T_0$ represented over $F$, the product $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)$ converges when $N - r\ge3$ or
  $N - r = 1$, and $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)/2$ converges when $N = r\ge3$ (the products of the local
  factors in the proofs of `siegelIndefiniteForms_uncond`, `siegelIndefiniteForms_corank1_uncond` and
  `siegelIndefiniteForms_corank0_uncond`, times factors that are $1$ off a finite set);
* `tsum_unitVolume_ne_zero_top_binary`: $0 < \sum_iv(M_i) < \infty$ for an anisotropic binary form, from
  $\tau(SO(V)) = 2$ with the convergence factors $L_v(1,\chi_E)$ (`tauTwoBinaryAll_uncond`);
* `multipliable_siegelDensity_forms`: for totally positive definite $Q_0$, $T_0$ with $N\ge3$, $N - r\ne2$, the
  product $\prod_\mathfrak p\alpha_\mathfrak p(Q_0,T_0)$ converges (from the three lemmas above when $Q_0$ represents
  $T_0$ over $F$; otherwise a factor is $0$).
-/

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Tamagawa.Measure QuadFormsKB.RegProd QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-- For a binary form $Q_0$ with discriminant field $E$, the product of the local masses
$\lambda_v^{-1}\mu_v(SO(L_v))$, $\lambda_v = 1 - \chi_E(v)/Nv$, converges (its factors are $1$ off a finite set). -/
theorem multipliable_muLocSO_lamL_chiE {Q₀ : QuadForm (𝓞 F) 2} (hQ : Q₀.Nondegenerate) {E : Type} [Field E]
    [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E) :
    Multipliable fun v => (muLocSO v Q₀ (lamL (chiE F E) v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal := by
  obtain ⟨S, hS⟩ := chiP_eq_chiE Q₀ hE
  exact Indefinite.multipliable_muLocSO_lamL Q₀ hQ (abs_chiE_le hE.finrank_eq_two) S hS

/-- $L_F(1,\chi_E)$ exists (as the limit $s\to1^+$) and is positive, for a quadratic extension $E/F$. -/
theorem hasLOne_chiE {E : Type} [Field E] [NumberField E] [Algebra F E] (hdeg : Module.finrank F E = 2) :
    HasLOne (chiE F E) (LOne (chiE F E)) ∧ 0 < LOne (chiE F E) := by
  rw [lOne_chiE_eq hdeg]
  exact ⟨hasLOne_relChar hdeg, div_pos (dedekindZeta_residue_pos E) (dedekindZeta_residue_pos F)⟩

/-- For an isotropic binary form $Q_0$, the product of the local masses $\lambda_v^{-1}\mu_v(SO(L_v))$,
$\lambda_v = 1 - N(v)^{-1}$, converges. -/
theorem multipliable_muLocSO_lamV_of_isotropicF {Q₀ : QuadForm (𝓞 F) 2} (hQ : Q₀.Nondegenerate)
    (hI : IsotropicF Q₀) :
    Multipliable fun v => (muLocSO v Q₀ (lamV v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal := by
  refine (multipliable_siegelDensity_div_lamV hQ ((isotropicF_iff_isSquare Q₀).mp hI)).congr fun v => ?_
  rw [muLocSO_soStabSO, ENNReal.toReal_ofReal (div_nonneg (siegelDensity_self_pos' Q₀ hQ v).le (lamV_pos v).le)]

end QuadFormsKB.Tamagawa.Measure.Weil

namespace QuadFormsKB.Tamagawa.Classical

/-- $x_0^2 + x_1^2$ is the sum of two squares `Siegel.sumSq 2`. -/
theorem sumTwoSqZ_eq_sumSq : sumTwoSqZ = Siegel.sumSq 2 := by
  unfold sumTwoSqZ Siegel.sumSq
  congr 1
  funext i
  fin_cases i <;> rfl

/-- $x_0^2 + x_1^2 = m$ has finitely many solutions in $\mathbb Z^2$. -/
theorem finite_repSet_sumTwoSqZ (m : ℤ) : (Siegel.repSet sumTwoSqZ m).Finite := by
  rw [sumTwoSqZ_eq_sumSq]
  exact IntQF.PosDef.repSet_finite Siegel.posDef_sumSq m

end QuadFormsKB.Tamagawa.Classical

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames QuadFormsKB.LocalDensity QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000 in
open Classical in
/-- For $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + n'$ variables, $n'\ge3$, and $T_0$ nondegenerate of rank
$r$ with a rational frame $\Xi$, the product $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)$ converges: it is the product
of the local factors of `siegelIndefiniteForms_uncond` (`multipliable_frameLocFactor`) times
$|\det H_{T_0}|_\mathfrak p^{n'}|\det g|_\mathfrak p^{-(n'+1)}$, which is $1$ off a finite set. -/
theorem multipliable_localDensityForm_of_frame {r n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (hn' : 3 ≤ n') (Ξ : RatFrame Q₀ T₀) :
    Multipliable fun v => NF.localDensityForm v Q₀ T₀ := by
  set D := chosenTower Q₀ hQ T₀ hT hn' Ξ with hD
  set g := (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det with hgdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  have hg : g ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have ha : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v g‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hg)
  have hb : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v h‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
  have hfa := mulSupport_finite_norm (F := F) hg
  have hfb := mulSupport_finite_norm (F := F) hh
  have hpow : ∀ (f : HeightOneSpectrum (𝓞 F) → ℝ) (k : ℕ), (Function.mulSupport f).Finite →
      (Function.mulSupport fun v => f v ^ k).Finite := fun f k hf => hf.subset fun v hv => by
    intro h1
    apply hv
    show f v ^ k = 1
    rw [show f v = 1 from h1, one_pow]
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v h‖ ^ n' * (‖σV v g‖ ^ (n' + 1))⁻¹ with hu
  have hpa := hpow _ (n' + 1) hfa
  have hpb := hpow _ n' hfb
  have hpai : (Function.mulSupport fun v => (‖σV v g‖ ^ (n' + 1))⁻¹).Finite := by
    refine hpa.subset fun v hv => ?_
    intro h1
    apply hv
    show (‖σV v g‖ ^ (n' + 1))⁻¹ = 1
    rw [show ‖σV v g‖ ^ (n' + 1) = 1 from h1, inv_one]
  have hufin : (Function.mulSupport u).Finite := by
    refine (hpb.union hpai).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show u v = 1
    simp only [hu, hcon.1, hcon.2, one_mul]
  have hβ : ∀ v, NF.localDensityForm v Q₀ T₀ = frameLocFactor Q₀ hQ T₀ Ξ D hT v * u v := fun v => by
    have := ha v
    have := hb v
    simp only [frameLocFactor, hu]
    rw [← hgdef, ← hhdef]
    field_simp
  exact ((multipliable_frameLocFactor Q₀ hQ T₀ Ξ D hT hn').mul (multipliable_of_hasFiniteMulSupport hufin)).congr
    fun v => (hβ v).symm

set_option synthInstance.maxHeartbeats 400000 in
open Classical in
/-- For $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 1\ge3$ variables and $T_0$ nondegenerate of rank $r$ with a
rational frame $\Xi$, the product $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)$ converges: it is the product of the
local factors of `siegelIndefiniteForms_corank1_uncond` (`count_mul_tprod`) times
$|\det g|_\mathfrak p^{-2}|\det H_{T_0}|_\mathfrak p$, which is $1$ off a finite set. -/
theorem multipliable_localDensityForm_corank1 {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) (hr : 2 ≤ r) :
    Multipliable fun v => NF.localDensityForm v Q₀ T₀ := by
  set D := towerCorankOne Q₀ hQ T₀ hT Ξ with hD
  have hN : 3 ≤ r + 1 := by omega
  obtain ⟨hmf, -⟩ := count_mul_tprod Q₀ hQ T₀ hT Ξ (fun _ => 1) (fun _ => one_pos)
    (by simpa only [div_one] using multipliable_aSO hN Q₀ hQ)
  simp only [div_one] at hmf
  set G := (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det with hGdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  have hG : G ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have hGv : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v G‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hG)
  have hhv : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v h‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
  have hfG := mulSupport_finite_norm (F := F) hG
  have hfh := mulSupport_finite_norm (F := F) hh
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v G‖ ^ 2 * ‖σV v h‖⁻¹ with hu
  have hufin : (Function.mulSupport u).Finite := by
    refine (hfG.union hfh).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show ‖σV v G‖ ^ 2 * ‖σV v h‖⁻¹ = 1
    rw [hcon.1, hcon.2]; norm_num
  have huinvfin : (Function.mulSupport fun v => (u v)⁻¹).Finite := hufin.subset fun v hv => by
    intro h1; apply hv; show (u v)⁻¹ = 1; rw [show u v = 1 from h1, inv_one]
  have hu0 : ∀ v, u v ≠ 0 := fun v => mul_ne_zero (pow_ne_zero _ (hGv v)) (inv_ne_zero (hhv v))
  have hfu : ∀ v, frameLocFactor Q₀ hQ T₀ Ξ D hT v = NF.localDensityForm v Q₀ T₀ * u v := by
    intro v
    simp only [frameLocFactor, hu, ← hGdef, ← hhdef, pow_one]
    field_simp
  refine (hmf.mul (multipliable_of_hasFiniteMulSupport huinvfin)).congr fun v => ?_
  rw [hfu, mul_assoc, mul_inv_cancel₀ (hu0 v), mul_one]

set_option synthInstance.maxHeartbeats 400000 in
open Classical in
/-- For $Q_0$ nondegenerate over $\mathcal O_F$ in $N\ge3$ variables and $T_0$ nondegenerate in $N$ variables with a
rational frame $\Xi$, the product $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)/2$ converges (`count_mul_tprod_zero`, the
count in the proof of `siegelIndefiniteForms_corank0_uncond`). -/
theorem multipliable_localDensityForm_half_corank0 {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) (hN : 3 ≤ N) :
    Multipliable fun v => NF.localDensityForm v Q₀ T₀ / 2 := by
  have h := (count_mul_tprod_zero Q₀ hQ T₀ hT (by omega) Ξ (fun _ => 1)
    (by simpa only [div_one] using multipliable_aSO hN Q₀ hQ)).1
  simpa only [div_one] using h

set_option synthInstance.maxHeartbeats 400000 in
/-- For an anisotropic binary form $Q_0$ with discriminant field $E$, $0 < \sum_iv(M_i) < \infty$: by
$\tau(SO(V)) = 2$ with the convergence factors $L_v(1,\chi_E)$ (`tauTwoBinaryAll_uncond`),
$L_F(1,\chi_E)^{-1}\prod_v\big(L_v(1,\chi_E)\,a_v\big)\sum_iv(M_i) = 2$, and the product is a finite positive number
(as in the proof of `siegelIndefinite_binary_uncond`). -/
theorem tsum_unitVolume_ne_zero_top_binary (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E) :
    (∑' i, unitVolume Q₀ hQ i) ≠ 0 ∧ (∑' i, unitVolume Q₀ hQ i) ≠ ⊤ := by
  set lam := lamL (chiE F E) with hlamdef
  have hlam : ∀ v, 0 < lam v := lamL_pos (abs_chiE_le hE.finrank_eq_two)
  obtain ⟨hL, -⟩ := lOne_chiE (F := F) (E := E) hE.finrank_eq_two
  obtain ⟨S, hS⟩ := eventually_muLocSO_lamL_chiE Q₀ hQ hE
  have haS : ∀ v ∉ S, aSO Q₀ v / lam v = 1 := by
    intro v hv
    have h := hS v hv
    have h0 : 0 ≤ NF.siegelDensity v Q₀ Q₀ / lam v :=
      div_nonneg (siegelDensity_self_pos' Q₀ hQ v).le (hlam v).le
    rw [muLocSO_soStabSO, ← ENNReal.ofReal_one] at h
    rw [aSO_eq_siegelDensity Q₀ hQ v]
    exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).mp h
  have hafin : (Function.mulSupport fun v => aSO Q₀ v / lam v).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (haS v h)
  have hApos : 0 < ∏' v, aSO Q₀ v / lam v := by
    rw [tprod_eq_prod (s := hafin.toFinset) (fun v hv => by
      by_contra hne; exact hv (hafin.mem_toFinset.2 hne))]
    exact Finset.prod_pos fun v _ => div_pos (aSO_pos Q₀ hQ v) (hlam v)
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v / lam v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  set V := ∑' i, unitVolume Q₀ hQ i with hV
  have hτ : ENNReal.ofReal (LOne (chiE F E))⁻¹ * (A * V) = 2 := by
    have h := tauTwoBinaryAll_uncond F Q₀ hQ hA E hE
    rw [muTamBin, muTamChi, covolume_smul_muTam, covolume_muTam_eq_muFin_mul, muFin_KSO,
      finFactor_eq_tprod_aSO Q₀ hQ hlam] at h
    exact h
  have hL0 : ENNReal.ofReal (LOne (chiE F E))⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hL)).ne'
  refine ⟨fun h0 => ?_, fun ht => ?_⟩
  · rw [h0, mul_zero, mul_zero] at hτ
    exact two_ne_zero hτ.symm
  · rw [ht, ENNReal.mul_top hA0, ENNReal.mul_top hL0] at hτ
    exact ENNReal.top_ne_ofNat hτ

end QuadFormsKB.Tamagawa.Indefinite

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite Lattices LocalDensity

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000 in
/-- For $Q_0$ and $T_0$ totally positive definite over $\mathcal O_F$ in $N\ge3$ and $r\le N$ variables, $N - r\ne2$,
the product $\prod_\mathfrak p\alpha_\mathfrak p(Q_0,T_0)$ of Siegel's densities converges. If $Q_0$ represents $T_0$
over $F$ (a rational frame), this is `multipliable_localDensityForm_of_frame` ($N - r\ge3$),
`multipliable_localDensityForm_corank1` ($N - r = 1$) or `multipliable_localDensityForm_half_corank0` ($N = r$);
otherwise some $\alpha_\mathfrak p(Q_0,T_0)$ is $0$ (`exists_local_not_rep`, `localDensityForm_eq_zero_of_not_rep`). -/
theorem multipliable_siegelDensity_forms [IsTotallyReal F] {N r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) (hN : 3 ≤ N)
    (h2 : N ≠ r + 2) (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    Multipliable fun v => NF.siegelDensity v Q₀ T₀ := by
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  by_cases h : ∃ X : Matrix (Fin N) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    rcases (by omega : N = r ∨ N = r + 1 ∨ r + 3 ≤ N) with h0 | h1 | h3
    · subst h0
      refine (multipliable_localDensityForm_half_corank0 Q₀ hQ T₀ hT ⟨X, hX⟩ hN).congr fun v => ?_
      simp only [NF.siegelDensity, if_true]
      ring
    · subst h1
      refine (multipliable_localDensityForm_corank1 Q₀ hQ T₀ hT ⟨X, hX⟩ (by omega)).congr fun v => ?_
      simp [NF.siegelDensity]
    · obtain ⟨n', rfl⟩ : ∃ n', N = r + n' := ⟨N - r, by omega⟩
      refine (multipliable_localDensityForm_of_frame Q₀ hQ T₀ hT (by omega) ⟨X, hX⟩).congr fun v => ?_
      have hne : r + n' ≠ r := by omega
      simp only [NF.siegelDensity, if_neg hne, one_mul]
  · obtain ⟨v, hv⟩ := exists_local_not_rep Q₀ T₀ hpd hpdT h
    have h0 := localDensityForm_eq_zero_of_not_rep v Q₀ T₀ hT hrN hv
    exact multipliable_of_exists_eq_zero ⟨v, by unfold NF.siegelDensity; rw [h0]; simp⟩

end QuadFormsKB.Tamagawa.Frames
