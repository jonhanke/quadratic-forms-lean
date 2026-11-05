/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummed
import QuadFormsKB.Tamagawa.SiegelLatRank2

/-!
# Hanke 2011, Lemma 7.8 for $n = 2$, step 1: the mass of one binary genus

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §6, Corollary 6.3, and §7, Lemma 7.8, p. 32.

**Setting.** $F$ a totally real number field of degree $d = [F:\mathbb Q]$, $(Q, L)$ a totally positive definite binary
quadratic space over $F$ with an $\mathcal O_F$-valued lattice $L$ (any Steinitz class), $S = \det_H(L)$, and
$G_{\mathfrak p}$ the local genus of $L_{\mathfrak p}$ at the prime $\mathfrak p$ of $\mathcal O_F$.

**The problem in rank $2$.** The proof of Lemma 7.8 applies Corollary 6.3 with $n = 2$:
$\mathrm{Mass}(L) = C(S)\prod_{\mathfrak p}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$. For $n = 2$ the factors are
$\beta_{G_{\mathfrak p}}^{-1} = (1 - \chi(\mathfrak p)/N\mathfrak p)^{-1}$ at almost every prime, $\chi$ a quadratic character, so the
product converges only conditionally (Lemma 3.6, proof: it is $L^T_F(1,\chi)$ up to finitely many factors), and its
unconditional value (Mathlib's `tprod`) is meaningless. Hanke 2005's Theorem 2.1, used for the repository's
Corollary 6.3, needs $n \ge 3$.

**The regularized product** (`RegProd.regProd`): for a character $\chi$ with $|\chi| \le 1$,
$$\mathrm{regProd}(\chi, 1, f) = L_F(1,\chi)\cdot\prod_{\mathfrak p}f(\mathfrak p)\bigl(1 - \chi(\mathfrak p)/N\mathfrak p\bigr),$$
the second product being absolutely convergent (here: with finite support). Given `NaturalOrderEulerOne χ` it is the
limit of the partial products of $f$ over $N\mathfrak p \le X$ (`RegProd.hasProd_normOrder_regProd`).

**Results.**
* `IsRegChar t χ`: $\chi$ regularizes the tuple $t$ of local genera ($|\chi| \le 1$ and
  $\beta(t_{\mathfrak p}) = 1 - \chi(\mathfrak p)/N\mathfrak p$ at all but finitely many $\mathfrak p$); `invDensityReg χ t`
  $= \mathrm{regProd}(\chi, 1, \beta(t_{\cdot})^{-1})$, the regularized $\prod_{\mathfrak p}\beta(t_{\mathfrak p})^{-1}$.
* `massConst_mul_detFactor_mul_arch`: the constant identity behind Corollary 6.3 (every rank $n$).
* `mass_core_two`: for $Q_0$ over $\mathcal O_F$ totally positive definite binary,
  $\mathrm{Mass}(L) = C(S)\cdot\mathrm{regProd}(\chi_{Q_0}, 1, \beta(G_{\cdot})^{-1})$, from the binary mass formula with the
  regularized Tamagawa number $\tau^{\mathrm{reg}}(SO_2) = 2$ (`Tamagawa.binaryTamagawaTwoReg_nf`,
  `Tamagawa.SiegelLat.tamagawaKRegLat_mul_mass`) and the local identity $\alpha_{\mathfrak p}(Q_0)\,r_{\mathfrak p}(L) =
  \beta(G_{\mathfrak p})\,\|2\|_{\mathfrak p}^{-1}\|\det P_{\mathfrak p}\|^3$ (`Tamagawa.SiegelLat.alpha_mul_normDet_eq`).
* **`mass_of_rep_two`** (Corollary 6.3 for $n = 2$, one genus, any realization over $F$, any regularizing character):
  $$\mathrm{Mass}(L) = \frac{|\Delta_F|^{1/2}}{V(2)^{d}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{3/2}}{(2^{d})^{3}}\cdot
    \mathrm{regProd}\bigl(\chi, 1, \beta(G_{\cdot})^{-1}\bigr).$$
  The value does not depend on the regularizing character $\chi$ (`exists_isRegChar_of_rep` gives one).

All results are unconditional.
-/

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.HilbertModular Real
open QuadFormsKB.NFEuler QuadFormsKB.RegProd

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### Regularizing characters and the regularized density product -/

/-- **$\chi$ regularizes the tuple $t$ of binary local genera**: $|\chi(\mathfrak p)| \le 1$ at every prime, and
$\beta_{t_{\mathfrak p},\mathfrak p}(t_{\mathfrak p}) = 1 - \chi(\mathfrak p)/N\mathfrak p$ at all but finitely many primes $\mathfrak p$
(so that $\prod_{\mathfrak p}\beta(t_{\mathfrak p})^{-1}(1 - \chi(\mathfrak p)/N\mathfrak p)$ has finite support).

Fields (of the conjunction):
- `abs_le`: $|\chi(\mathfrak p)| \le 1$ for every $\mathfrak p$;
- `finite`: the set of $\mathfrak p$ with $\beta(t_{\mathfrak p}) \ne 1 - \chi(\mathfrak p)/N\mathfrak p$ is finite.

A *condition* on the pair $(t,\chi)$; for the tuple of local genera of a lattice it is satisfied by the character of
$F(\sqrt{-\det H})/F$ (`exists_isRegChar_of_rep`). -/
def IsRegChar (t : LocTuple F 2) (χ : HeightOneSpectrum (𝓞 F) → ℝ) : Prop :=
  (∀ v, |χ v| ≤ 1) ∧ {v | (t v).beta ≠ 1 - χ v / (normP v : ℝ)}.Finite

/-- **The regularized product of the inverse local densities of a binary tuple** $t$ of local genera:
$$\mathrm{regProd}\bigl(\chi, 1, \beta(t_{\cdot})^{-1}\bigr) = L_F(1,\chi)\cdot\prod_{\mathfrak p}
  \beta_{t_{\mathfrak p},\mathfrak p}(t_{\mathfrak p})^{-1}\bigl(1 - \chi(\mathfrak p)/N\mathfrak p\bigr),$$
the repository's reading of the conditionally convergent product $\prod_{\mathfrak p}\beta(t_{\mathfrak p})^{-1}$ of Definitions 3.4
and 3.5 for $n = 2$ (where `invDensityTuple`, built on Mathlib's unconditional `tprod`, is $0$). For a regularizing $\chi$
(`IsRegChar`) the second product has finite support. -/
@[kb "hanke2011structure" "Def. 3.4, p. 12 (n = 2, regularized product)"]
def invDensityReg (χ : HeightOneSpectrum (𝓞 F) → ℝ) (t : LocTuple F 2) : ℝ :=
  regProd χ 1 fun v => ((t v).beta)⁻¹

/-! ### The constant of Corollary 6.3 -/

section Const

variable [IsTotallyReal F] {n : ℕ}

/-- **The constant identity of Corollary 6.3** (every rank $n$): with $P_{\mathfrak p}$ the local basis of $L_{\mathfrak p}$ and
$k = n(n-1)/2$,
$$C(S)\cdot\prod_{\mathfrak p}\|2\|_{\mathfrak p}^{-k}\|\det P_{\mathfrak p}\|_{\mathfrak p}^{n+1}\cdot|\Delta_F|^{-n(n-1)/4}
\prod_{\sigma}\mathrm{vol}(SO(V_\sigma)) = 1,\qquad S = \det_H(L).$$
(The computation of `mass_eq_local` without the local densities.) -/
theorem massConst_mul_detFactor_mul_arch (Q₀ : QuadForm (𝓞 F) n) (hQ : (formF Q₀).hessian.det ≠ 0)
    (L : Lat F n) :
    massConst F n (detH (formF Q₀) hQ L) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), (‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2))⁻¹ *
        ‖(locBasis v L).val.det‖ ^ (n + 1)) *
      (|(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) *
        ∏ σ : F →ₐ[ℚ] ℂ, Tamagawa.archVolSO n (Tamagawa.detGram Q₀ σ)) = 1 := by
  classical
  set d := Module.finrank ℚ F with hd
  set k := n * (n - 1) / 2 with hk
  set S := detH (formF Q₀) hQ L with hSdef
  set D : F := (formF Q₀).hessian.det with hD
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (‖(2 : v.adicCompletion F)‖ ^ k)⁻¹ * ‖(locBasis v L).val.det‖ ^ (n + 1) with ha
  have hX : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ D‖ := Finset.prod_pos fun σ _ =>
    norm_pos_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hQ)
  set X := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ D‖ with hXdef
  have hnormD : ∀ v : HeightOneSpectrum (𝓞 F), 0 < ‖algebraMap F (v.adicCompletion F) D‖ := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr hQ)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) D‖ *
      ‖(locBasis v L).val.det‖ ^ 2 = ((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ := by
    intro v
    have hc := detH_comp (formF Q₀) hQ L v (locBasis_spec v L)
    rw [← norm_eq_of_comp v S hc, localHessDet, Units.val_mk0, norm_mul, norm_pow]
  have hfinD : {v : HeightOneSpectrum (𝓞 F) | ‖algebraMap F (v.adicCompletion F) D‖ ≠ 1}.Finite := by
    have := (Tamagawa.finite_valuation_ne_one hQ)
    refine this.subset fun v hv => ?_
    intro h
    apply hv
    exact Tamagawa.norm_algebraMap_eq_one' h
  have hfin2 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖).Finite :=
    Hanke2005.hasFiniteMulSupport_norm_two (F := F)
  set T₀ : Finset (HeightOneSpectrum (𝓞 F)) :=
    (finite_mulSupport_detFactor L k).toFinset ∪ hfinD.toFinset ∪ (supp_finite S).toFinset ∪ hfin2.toFinset
    with hT₀
  have hout : ∀ v ∉ T₀, a v = 1 ∧ ‖algebraMap F (v.adicCompletion F) D‖ = 1 ∧ adelicOrd v S = 0 ∧
      ‖(2 : v.adicCompletion F)‖ = 1 := by
    intro v hv
    simp only [hT₀, Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h1
    · simpa using h2
    · simpa [supp] using h3
    · simpa using h4
  have hA : ∏ᶠ v, a v = ∏ v ∈ T₀, a v := Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).1
  have hNS : normAssoc S = ∏ v ∈ T₀, (Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S := by
    unfold normAssoc
    exact Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => by rw [(hout v hv).2.2.1, zpow_zero]
  have hXT : ∏ v ∈ T₀, ‖algebraMap F (v.adicCompletion F) D‖ = X⁻¹ := by
    rw [← Tamagawa.finprod_norm_eq D hQ]
    exact (Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).2.1).symm
  have h2T : ∏ v ∈ T₀, ‖(2 : v.adicCompletion F)‖ = ((2 : ℝ) ^ d)⁻¹ := by
    rw [← Hanke2005.tprod_norm_two, tprod_eq_finprod (L := SummationFilter.unconditional _) hfin2]
    exact (Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).2.2.2).symm
  have hdetP : ∀ v : HeightOneSpectrum (𝓞 F), ‖(locBasis v L).val.det‖ ^ (n + 1) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ / ‖algebraMap F (v.adicCompletion F) D‖) ^
        (((n : ℝ) + 1) / 2) := by
    intro v
    have h := hloc v
    have hsq : ‖(locBasis v L).val.det‖ ^ 2 =
        ((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ / ‖algebraMap F (v.adicCompletion F) D‖ := by
      rw [← h]; field_simp [(hnormD v).ne']
    rw [← hsq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1; push_cast; ring
  have hprodA : ∏ v ∈ T₀, a v = (2 : ℝ) ^ (d * k) * (X / normAssoc S) ^ (((n : ℝ) + 1) / 2) := by
    simp only [ha, Finset.prod_mul_distrib, hdetP]
    rw [Finset.prod_inv_distrib, Finset.prod_pow, h2T, Real.finsetProd_rpow _ _ (fun v _ =>
        div_nonneg (inv_nonneg.mpr (zpow_nonneg (Nat.cast_nonneg _) _)) (norm_nonneg _)),
      Finset.prod_div_distrib, Finset.prod_inv_distrib, ← hNS, hXT, inv_pow, inv_inv, ← pow_mul]
    congr 1
    rw [div_inv_eq_mul, inv_mul_eq_div]
  have hDcast : algebraMap (𝓞 F) F Q₀.hessian.det = D := by
    rw [hD, QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hgram : ∀ σ : F →ₐ[ℚ] ℂ, Tamagawa.detGram Q₀ σ = ‖σ D‖ / 2 ^ n := by
    intro σ
    unfold Tamagawa.detGram
    rw [hDcast, map_div₀, map_pow, map_ofNat, norm_div, norm_pow, Complex.norm_two]
  have harch : ∏ σ : F →ₐ[ℚ] ℂ, Tamagawa.archVolSO n (Tamagawa.detGram Q₀ σ) =
      (X / (2 : ℝ) ^ (n * d)) ^ (-((n : ℝ) + 1) / 2) * (volV n / 2 ^ k) ^ d := by
    simp only [hgram]
    have hav : ∀ σ : F →ₐ[ℚ] ℂ, Tamagawa.archVolSO n (‖σ D‖ / 2 ^ n) =
        (‖σ D‖ / 2 ^ n) ^ (-((n : ℝ) + 1) / 2) * Tamagawa.archVolSO n 1 :=
      fun σ => Hanke2005.archVolSO_eq_rpow_mul n _
    rw [Finset.prod_congr rfl (fun σ _ => hav σ), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      AlgHom.card]
    rw [Real.finsetProd_rpow _ _ (fun σ _ => div_nonneg (norm_nonneg _) (by positivity)), Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, AlgHom.card, ← pow_mul, mul_comm n d, ← hXdef]
    congr 1
    rw [volV_eq_tauR, Hanke2005.tauR_eq_two_pow_mul_archVolSO, ← hk,
      mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ k ≠ 0)]
  -- assemble
  show massConst F n S * (∏ᶠ v, a v) * _ = 1
  rw [hA, hprodA, harch]
  have hNSpos : 0 < normAssoc S := by
    rw [hNS]
    exact Finset.prod_pos fun v _ =>
      zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))) _
  have hV : 0 < volV n := by rw [volV_eq_tauR]; exact Hanke2005.tauR_pos n
  have hΔ : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have h2nd : (0 : ℝ) < 2 ^ (n * d) := by positivity
  have e1 : ((2 : ℝ) ^ (n * d)) ^ (((n : ℝ) + 1) / 2) = ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have e2 : (X / (2 : ℝ) ^ (n * d)) ^ (-((n : ℝ) + 1) / 2) = ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) /
      X ^ (((n : ℝ) + 1) / 2) := by
    rw [show -((n : ℝ) + 1) / 2 = -(((n : ℝ) + 1) / 2) by ring, Real.rpow_neg (by positivity),
      Real.div_rpow hX.le h2nd.le, e1, inv_div]
  have e3 : (X / normAssoc S) ^ (((n : ℝ) + 1) / 2) =
      X ^ (((n : ℝ) + 1) / 2) / normAssoc S ^ (((n : ℝ) + 1) / 2) :=
    Real.div_rpow hX.le hNSpos.le _
  have e4 : |(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) = (|(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4))⁻¹ :=
    Real.rpow_neg hΔ.le _
  rw [e2, e3, e4]
  have hXp : 0 < X ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hX _
  have hNp : 0 < normAssoc S ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hNSpos _
  have h2p : 0 < ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) := by positivity
  have hΔp : 0 < |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) := Real.rpow_pos_of_pos hΔ _
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hVd : 0 < volV n ^ d := pow_pos hV d
  unfold massConst
  rw [← hd, div_pow, ← pow_mul, mul_comm k d]
  field_simp

end Const

/-! ### The mass of one binary genus -/

section Core

variable [IsTotallyReal F]

/-- **The local identity** $\alpha_{\mathfrak p}(Q_0)\,r_{\mathfrak p}(L) = \beta(G_{\mathfrak p})\cdot\|2\|_{\mathfrak p}^{-1}\|\det P_{\mathfrak p}\|^3$
for a binary form $Q_0$ over $\mathcal O_F$ and a lattice $L$ with local basis $P_{\mathfrak p}$ (`locBasis`), $G_{\mathfrak p}$ the local
genus of $L_{\mathfrak p}$ and $r_{\mathfrak p}(L)$ the local index ratio (`Tamagawa.SiegelLat.locRatio`). -/
theorem siegelDensity_mul_locRatio_two (Q₀ : QuadForm (𝓞 F) 2) (hQ₀ : Q₀.Nondegenerate)
    (hQ : (formF Q₀).hessian.det ≠ 0) (L : Lat F 2) (hL : IsIntegral (formF Q₀) L.1) (v : HeightOneSpectrum (𝓞 F)) :
    LocalDensity.NF.siegelDensity v Q₀ Q₀ * Tamagawa.SiegelLat.locRatio v Q₀ L =
      (locGenusOf v (formF Q₀) L hL).beta *
        ((‖(2 : v.adicCompletion F)‖ ^ (2 * (2 - 1) / 2))⁻¹ * ‖(locBasis v L).val.det‖ ^ (2 + 1)) := by
  have hT : (QuadForm.toO v (localForm (formF Q₀) v (locBasis v L))
      (localForm_coeff_integral v _ L hL (locBasis_spec v L))).map (algebraMap _ (v.adicCompletion F)) =
      ((LocalDensity.NF.Qp v Q₀).map (algebraMap _ (v.adicCompletion F))).compMat (locBasis v L).val := by
    rw [QuadForm.map_toO, Tamagawa.map_Qp_eq]; rfl
  have h1 := Tamagawa.SiegelLat.alpha_mul_normDet_eq v Q₀ hQ₀ (locBasis v L) _ hT
  rw [← locBasis_spec v L] at h1
  have hb := beta_locGenusOf_eq v (formF Q₀) hQ L hL
  have h2v : (‖(2 : v.adicCompletion F)‖ ^ (2 * (2 - 1) / 2)) ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr two_ne_zero)
  calc LocalDensity.NF.siegelDensity v Q₀ Q₀ * Tamagawa.SiegelLat.locRatio v Q₀ L
      = (1 / 2 : ℝ) * LocalDensity.DVR.localDensityForm
          (QuadForm.toO v (localForm (formF Q₀) v (locBasis v L))
            (localForm_coeff_integral v _ L hL (locBasis_spec v L)))
          (QuadForm.toO v (localForm (formF Q₀) v (locBasis v L))
            (localForm_coeff_integral v _ L hL (locBasis_spec v L))) (LocalDensity.NF.π v) *
          ‖(locBasis v L).val.det‖ ^ (2 + 1) := h1.symm
    _ = _ := by
      rw [hb]
      field_simp

/-- **Corollary 6.3 for $n = 2$, one genus, a form over $\mathcal O_F$** (regularized product): for $Q_0$ totally positive
definite binary over $\mathcal O_F$ ($F$ totally real), $L$ an $\mathcal O_F$-valued lattice on $(F^2, Q_0)$, $S = \det_H(L)$,
$G_{\mathfrak p}$ the local genera of $L$ and $\chi_{Q_0}$ = `Tamagawa.chiP · Q₀` (the character of $F(\sqrt{-\det H})/F$):
$$\mathrm{Mass}(L) = C(S)\cdot\mathrm{regProd}\bigl(\chi_{Q_0}, 1, \beta(G_{\cdot})^{-1}\bigr),$$
and the corrected product $\beta(G_{\mathfrak p})^{-1}(1 - \chi_{Q_0}(\mathfrak p)/N\mathfrak p)$ has finite support. -/
theorem mass_core_two (Q₀ : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q₀))
    (hQ : (formF Q₀).hessian.det ≠ 0) (L : Lat F 2) (hL : IsIntegral (formF Q₀) L.1) :
    Lattices.mass (formF Q₀) L = massConst F 2 (detH (formF Q₀) hQ L) *
        regProd (fun v => Tamagawa.chiP v Q₀) 1 (fun v => ((locGenusOf v (formF Q₀) L hL).beta)⁻¹) ∧
      Function.HasFiniteMulSupport (fun v => ((locGenusOf v (formF Q₀) L hL).beta)⁻¹ *
        (1 - Tamagawa.chiP v Q₀ / (normP v : ℝ)) ^ (1 : ℤ)) := by
  classical
  have hQ₀ : Q₀.Nondegenerate := Tamagawa.nondegenerate_of_map hpd.nondegenerate
  set χ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Tamagawa.chiP v Q₀ with hχdef
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (locGenusOf v (formF Q₀) L hL).beta with hβ
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (‖(2 : v.adicCompletion F)‖ ^ (2 * (2 - 1) / 2))⁻¹ * ‖(locBasis v L).val.det‖ ^ (2 + 1) with ha
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => LocalDensity.NF.siegelDensity v Q₀ Q₀ with hα
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Tamagawa.SiegelLat.locRatio v Q₀ L with hr
  set lam : HeightOneSpectrum (𝓞 F) → ℝ := fun v => 1 - χ v / (normP v : ℝ) with hlam
  have hlampos : ∀ v, 0 < lam v := fun v => one_sub_div_pos (Tamagawa.abs_chiP_le Q₀ v) v
  have hloc : ∀ v, α v * r v = β v * a v := fun v => siegelDensity_mul_locRatio_two Q₀ hQ₀ hQ L hL v
  have hαpos : ∀ v, 0 < α v := fun v => Tamagawa.siegelDensity_pos v Q₀ hQ₀
  have hrpos : ∀ v, 0 < r v := fun v => Tamagawa.SiegelLat.locRatio_pos (n := 1) v hQ₀ L hL
  have hapos : ∀ v, 0 < a v := fun v => by
    have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
    have hd : 0 < ‖(locBasis v L).val.det‖ :=
      norm_pos_iff.mpr ((locBasis v L).isUnit.map Matrix.detMonoidHom).ne_zero
    simp only [ha]
    positivity
  have hβpos : ∀ v, 0 < β v := fun v => by
    have h := hloc v
    have : 0 < β v * a v := h ▸ mul_pos (hαpos v) (hrpos v)
    exact pos_of_mul_pos_left this (hapos v).le
  -- finite supports
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α v * lam v ^ (-1 : ℤ) with hg
  have hgfin : Function.HasFiniteMulSupport g :=
    Tamagawa.hasFiniteMulSupport_siegelDensity_binary_reg hQ₀ ∅ fun _ _ => rfl
  have hrfin : Function.HasFiniteMulSupport r := by
    refine (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).subset fun v hv => ?_
    by_contra h
    exact hv (Tamagawa.SiegelLat.locRatio_eq_one v Q₀ L (by simpa using h))
  have hafin : Function.HasFiniteMulSupport a := finite_mulSupport_detFactor L _
  have hfp : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → HasProd f (∏ᶠ v, f v) :=
    fun {f} hf => by
      have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hf).hasProd
      rwa [tprod_eq_finprod hf] at this
  have hfpos : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → (∀ v, 0 < f v) →
      0 < ∏ᶠ v, f v := fun {f} hf hpos => by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hpos v
  have hgpos : ∀ v, 0 < g v := fun v => by
    simp only [hg, _root_.zpow_neg_one]; exact mul_pos (hαpos v) (inv_pos.mpr (hlampos v))
  have hG : 0 < ∏ᶠ v, g v := hfpos hgfin hgpos
  have hR : 0 < ∏ᶠ v, r v := hfpos hrfin hrpos
  -- `β⁻¹ λ = a / (g r)`
  have hβeq : ∀ v, (β v)⁻¹ * lam v ^ (1 : ℤ) = a v / (g v * r v) := fun v => by
    have h := hloc v
    have := hβpos v; have := hapos v; have := hrpos v; have := hlampos v; have := hαpos v
    simp only [hg, zpow_one, _root_.zpow_neg_one]
    field_simp
    linear_combination h
  have hβp : HasProd (fun v => (β v)⁻¹ * lam v ^ (1 : ℤ)) ((∏ᶠ v, a v) / ((∏ᶠ v, g v) * ∏ᶠ v, r v)) :=
    ((hfp hafin).div₀ ((hfp hgfin).mul (hfp hrfin)) (mul_pos hG hR).ne').congr_fun fun v => hβeq v
  have hβfin : Function.HasFiniteMulSupport fun v => (β v)⁻¹ * lam v ^ (1 : ℤ) := by
    refine ((hafin.union hgfin).union hrfin).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at h
    apply hv
    show (β v)⁻¹ * lam v ^ (1 : ℤ) = 1
    rw [hβeq v, h.1.1, h.1.2, h.2]
    norm_num
  refine ⟨?_, hβfin⟩
  -- the mass formula `μ^reg(K(L)) · 2 Mass(L) = τ^reg = 2`
  have hmass := Tamagawa.SiegelLat.tamagawaKRegLat_mul_mass Q₀ hQ₀ hpd L hL
  rw [Tamagawa.binaryTamagawaTwoReg_nf.tau_eq_two Q₀ hpd] at hmass
  obtain ⟨hL0, -⟩ := Tamagawa.lOne_chiP_binary hpd
  have hregα : regProd χ (-1) α = (LOne χ)⁻¹ * ∏ᶠ v, g v := by
    show LOne χ ^ (-1 : ℤ) * ∏' v, α v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = _
    rw [(hfp hgfin).tprod_eq, _root_.zpow_neg_one]
  have hreg1 : regProd χ 1 (fun v => (β v)⁻¹) = LOne χ * ((∏ᶠ v, a v) / ((∏ᶠ v, g v) * ∏ᶠ v, r v)) := by
    show LOne χ ^ (1 : ℤ) * ∏' v, (β v)⁻¹ * (1 - χ v / (normP v : ℝ)) ^ (1 : ℤ) = _
    rw [hβp.tprod_eq, zpow_one]
  have hK : Tamagawa.SiegelLat.tamagawaKRegLat Q₀ L =
      |(discr F : ℝ)| ^ (-((2 : ℝ) * (2 - 1) / 4)) *
        (∏ σ : F →ₐ[ℚ] ℂ, Tamagawa.archVolSO 2 (Tamagawa.detGram Q₀ σ)) *
          ((LOne χ)⁻¹ * ∏ᶠ v, g v) * ∏ᶠ v, r v := by
    unfold Tamagawa.SiegelLat.tamagawaKRegLat
    rw [Tamagawa.SiegelLat.relRatio_locStab_eq_finprod]
    unfold Tamagawa.tamagawaKReg
    rw [hregα]
  have hC := massConst_mul_detFactor_mul_arch Q₀ hQ L
  simp only [Nat.cast_ofNat] at hC
  rw [hK] at hmass
  show Lattices.mass (formF Q₀) L = massConst F 2 (detH (formF Q₀) hQ L) * regProd χ 1 (fun v => (β v)⁻¹)
  rw [hreg1]
  have hL0' := hL0.ne'
  have hG' := hG.ne'
  have hR' := hR.ne'
  set A := ∏ᶠ v, a v
  set M := Lattices.mass (formF Q₀) L
  set C := massConst F 2 (detH (formF Q₀) hQ L)
  set E := |(discr F : ℝ)| ^ (-((2 : ℝ) * (2 - 1) / 4)) *
    ∏ σ : F →ₐ[ℚ] ℂ, Tamagawa.archVolSO 2 (Tamagawa.detGram Q₀ σ)
  have hC' : C * A * E = 1 := hC
  set Gp := ∏ᶠ v, g v
  set Rp := ∏ᶠ v, r v
  have hm' : E * ((LOne χ)⁻¹ * Gp) * Rp * (2 * M) = 2 := by
    linear_combination hmass
  have hLL : LOne χ * (LOne χ)⁻¹ = 1 := mul_inv_cancel₀ hL0'
  have h1 : E * Gp * Rp * M = LOne χ := by
    linear_combination (LOne χ / 2) * hm' - (E * Gp * Rp * M) * hLL
  rw [show C * (LOne χ * (A / (Gp * Rp))) = C * LOne χ * A / (Gp * Rp) by ring,
    eq_div_iff (mul_ne_zero hG' hR')]
  linear_combination (-(M * Gp * Rp)) * hC' + (C * A) * h1

/-- **The local densities at almost every prime:** $\beta(G_{\mathfrak p}) = 1 - \chi_{Q_0}(\mathfrak p)/N\mathfrak p$ outside a finite set
(where $L_{\mathfrak p} = \mathcal O_{\mathfrak p}^2$, $\mathfrak p \nmid 2\det H_{Q_0}$). -/
theorem finite_beta_ne_chiP (Q₀ : QuadForm (𝓞 F) 2) (hQ₀ : Q₀.Nondegenerate) (L : Lat F 2)
    (hL : IsIntegral (formF Q₀) L.1) :
    {v | (locGenusOf v (formF Q₀) L hL).beta ≠ 1 - Tamagawa.chiP v Q₀ / (normP v : ℝ)}.Finite := by
  have h1 : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  have h2 := Hanke2005.hasFiniteMulSupport_norm_two (F := F)
  have h3 := Tamagawa.finite_badPrimes Q₀ hQ₀
  refine ((h1.union h2).union h3).subset fun v hv => ?_
  by_contra h
  rw [Set.mem_union, Set.mem_union, not_or, not_or] at h
  obtain ⟨⟨ha, hb⟩, hc⟩ := h
  have ha' : loc v L.1 = std v := by simpa using ha
  have hb' : ‖(2 : v.adicCompletion F)‖ = 1 := by simpa using hb
  apply hv
  show (locGenusOf v (formF Q₀) L hL).beta = 1 - Tamagawa.chiP v Q₀ / (normP v : ℝ)
  rw [beta_locGenusOf_of_std v Q₀ L hL ha', localBeta, Hanke2005.hankeBeta_gramV v Q₀ hQ₀, hb', one_pow, one_mul,
    Tamagawa.siegelDensity_binary_good Q₀ hQ₀ v hc]

/-- **Corollary 6.3 for $n = 2$, a form over $\mathcal O_F$, any regularizing character** $\chi$:
$\mathrm{Mass}(L) = C(S)\cdot\mathrm{regProd}(\chi, 1, \beta(G_\cdot)^{-1})$. -/
theorem mass_core_two_reg (Q₀ : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q₀))
    (hQ : (formF Q₀).hessian.det ≠ 0) (L : Lat F 2) (hL : IsIntegral (formF Q₀) L.1)
    {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : IsRegChar (fun v => locGenusOf v (formF Q₀) L hL) χ) :
    Lattices.mass (formF Q₀) L = massConst F 2 (detH (formF Q₀) hQ L) *
      invDensityReg χ (fun v => locGenusOf v (formF Q₀) L hL) := by
  have hQ₀ : Q₀.Nondegenerate := Tamagawa.nondegenerate_of_map hpd.nondegenerate
  obtain ⟨hm, hfin⟩ := mass_core_two Q₀ hpd hQ L hL
  rw [hm]
  congr 1
  have hE := finite_beta_ne_chiP Q₀ hQ₀ L hL
  set Sf := (hχ.2.union hE).toFinset
  have hS : ∀ v ∉ Sf, χ v = Tamagawa.chiP v Q₀ := fun v hv => by
    simp only [Sf, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
    have h := hv.1.symm.trans hv.2
    have hN : (normP v : ℝ) ≠ 0 := by have := two_le_normP v; positivity
    have h' : χ v / (normP v : ℝ) = Tamagawa.chiP v Q₀ / (normP v : ℝ) := by linarith
    rwa [div_left_inj' hN] at h'
  exact (Tamagawa.regProd_congr_finite hχ.1 (fun v => Tamagawa.abs_chiP_le Q₀ v) Sf hS
    (Tamagawa.lOne_chiP_binary hpd).2 1 _ (multipliable_of_hasFiniteMulSupport hfin)).symm

end Core

/-! ### Any realization over $F$ -/

section Rep

variable [IsTotallyReal F]

/-- **Corollary 6.3 for $n = 2$, one genus, any realization over $F$** (Hanke 2011, Cor. 6.3, p. 26, and the proof of
Lemma 7.8, p. 32; regularized product): for a binary form $Q$ over $F$ of the totally positive definite signature, an
$\mathcal O_F$-valued lattice $L$ on $(F^2, Q)$ with $S = \det_H(L)$ and local genera $G_{\mathfrak p}$, and any character $\chi$
regularizing $(G_{\mathfrak p})_{\mathfrak p}$ (`IsRegChar`),
$$\mathrm{Mass}(L) = \frac{|\Delta_F|^{1/2}}{V(2)^{[F:\mathbb Q]}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{3/2}}{(2^{[F:\mathbb Q]})^{3}}\cdot
  L_F(1,\chi)\prod_{\mathfrak p}\beta(G_{\mathfrak p})^{-1}\bigl(1 - \chi(\mathfrak p)/N\mathfrak p\bigr).$$
**Unconditional** (from $\tau^{\mathrm{reg}}(SO_2) = 2$, `Tamagawa.binaryTamagawaTwoReg_nf`). -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26, and Lemma 7.8, proof, p. 32 (n = 2, one genus, regularized product)"]
theorem mass_of_rep_two {Q : QuadForm F 2} (hQ : Q.hessian.det ≠ 0) (L : Lat F 2) (hL : IsIntegral Q L.1)
    (hσ : HasSignature Q (totPosSig F 2)) {χ : HeightOneSpectrum (𝓞 F) → ℝ}
    (hχ : IsRegChar (fun v => locGenusOf v Q L hL) χ) :
    Lattices.mass Q L = massConst F 2 (detH Q hQ L) * invDensityReg χ (fun v => locGenusOf v Q L hL) := by
  obtain ⟨g, Q₀, hQ₀⟩ := exists_integral_model Q
  have step : ∀ Q' : QuadForm F 2, formF Q₀ = Q' → ∀ (hQ' : Q'.hessian.det ≠ 0) (L' : Lat F 2)
      (hL' : IsIntegral Q' L'.1), IsTotallyPosDef Q' → IsRegChar (fun v => locGenusOf v Q' L' hL') χ →
      Lattices.mass Q' L' = massConst F 2 (detH Q' hQ' L') *
        invDensityReg χ (fun v => locGenusOf v Q' L' hL') := by
    intro Q' h
    subst h
    intro hQ' L' hL' hpd hχ'
    exact mass_core_two_reg Q₀ hpd hQ' L' hL' hχ'
  have hpd : IsTotallyPosDef (Q.compMat g.val) :=
    isTotallyPosDef_of_hasSignature (hasSignature_compMat Q g hσ)
  have e : (fun v => locGenusOf v (Q.compMat g.val) (Lat.image g⁻¹ L) (isIntegral_transport Q g hL)) =
      fun v => locGenusOf v Q L hL := funext fun v => locGenusOf_transport Q g v L hL
  have hχ' : IsRegChar (fun v => locGenusOf v (Q.compMat g.val) (Lat.image g⁻¹ L)
      (isIntegral_transport Q g hL)) χ := by rw [e]; exact hχ
  have := step (Q.compMat g.val) hQ₀ (hessian_det_compMat_ne Q g hQ) (Lat.image g⁻¹ L)
    (isIntegral_transport Q g hL) hpd hχ'
  rw [mass_transport, detH_transport Q g hQ L, e] at this
  exact this

/-- **Regularizing characters exist** for the tuple of local genera of every realization (the character
$\chi_{Q_0}$ of an $\mathcal O_F$-model $Q_0 = Q\circ g$). -/
theorem exists_isRegChar_of_rep {Q : QuadForm F 2} (L : Lat F 2) (hL : IsIntegral Q L.1)
    (hσ : HasSignature Q (totPosSig F 2)) : ∃ χ, IsRegChar (fun v => locGenusOf v Q L hL) χ := by
  obtain ⟨g, Q₀, hQ₀⟩ := exists_integral_model Q
  have hpd : IsTotallyPosDef (Q.compMat g.val) :=
    isTotallyPosDef_of_hasSignature (hasSignature_compMat Q g hσ)
  have e : (fun v => locGenusOf v (Q.compMat g.val) (Lat.image g⁻¹ L) (isIntegral_transport Q g hL)) =
      fun v => locGenusOf v Q L hL := funext fun v => locGenusOf_transport Q g v L hL
  rw [← e]
  refine ⟨fun v => Tamagawa.chiP v Q₀, fun v => Tamagawa.abs_chiP_le Q₀ v, ?_⟩
  generalize isIntegral_transport Q g hL = hL'
  revert hL'
  rw [← hQ₀]
  intro hL'
  rw [← hQ₀] at hpd
  exact finite_beta_ne_chiP Q₀ (Tamagawa.nondegenerate_of_map hpd.nondegenerate) _ hL'

end Rep

end

end QuadFormsKB.Hanke2011Structure
