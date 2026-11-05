/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Beta
import QuadFormsKB.Literature.ConwaySloane.Mass.OddProof
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal

/-!
# Paper 6, Lemma 7.3: $\mathfrak p$-masses and local densities, over $\mathbb Q$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Lemma 7.3, p. 29.

Lemma 7.3: for a primitive local genus $G_{\mathfrak p}$ of nondegenerate binary forms with $I(\det_H G_{\mathfrak p}) = \mathfrak p^\nu$,
$$\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1} = 2\,m_{\mathfrak p}(G_{\mathfrak p})\,q^{-\frac{3\nu}2 + 3\operatorname{ord}_{\mathfrak p}(2)},$$
$m_{\mathfrak p}$ the Conway–Sloane $\mathfrak p$-mass. Formalized over $\mathbb Q$ (every prime $p$, $F_{\mathfrak p} = \mathbb Q_p$), for the genus of
an integral form $Q$ with Hessian $H$ ($\det H \ne 0$), and in fact for every rank $n$:
$$\beta(G)^{-1} = 2\,m_p(H)\,p^{-\frac{(n+1)\nu}2 + \frac{n(n+1)}2\operatorname{ord}_p(2)},\qquad \nu = \operatorname{ord}_p\det H$$
(`invBeta_eq_pMass`); $m_p(H)$ is the $p$-mass of §12 of Conway–Sloane (`pMassDensity`), equal to the symbol formula (3)
by `pMassFormulaOdd` / `pMassFormulaTwo` (both proved). `lemma_7_3` is the binary case. Primitivity is not needed.
-/

open IsDedekindDomain NumberField Matrix

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.ConwaySloane.Mass

noncomputable section

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- **Hanke's density of the genus of an integral form via Conway–Sloane's $\alpha_p$:**
$\beta(G) = \lVert 2\rVert_v^{n(n+1)/2}\cdot\tfrac12\,\alpha_p(H)$, $H$ the Hessian. -/
theorem beta_mk_int {n : ℕ} (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) :
    (LocGenus.mk (Q.map (algebraMap ℤ (v.adicCompletionIntegers ℚ)))).beta =
      ‖(2 : v.adicCompletion ℚ)‖ ^ (n * (n + 1) / 2) * ((1 / 2 : ℝ) * alphaP (pv v) Q.hessian) := by
  rw [LocGenus.beta_mk]
  unfold betaForm Hanke2005.gramOf
  rw [QuadForm.hessian_map']
  have hsymm : Q.hessian.IsSymm := LocalDensity.hessian_isSymm Q
  set M : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ) :=
    ((Q.hessian).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) with hM
  have hMs : ((1 / 2 : v.adicCompletion ℚ) • M)ᵀ = (1 / 2 : v.adicCompletion ℚ) • M := by
    rw [Matrix.transpose_smul]
    congr 1
    rw [hM, ← Matrix.transpose_map, ← Matrix.transpose_map, hsymm.eq]
  have hMd : ((1 / 2 : v.adicCompletion ℚ) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using hdet
  rw [Hanke2005.hankeBeta_std_smul v hMs hMd (c := 2) two_ne_zero, smul_smul,
    show (2 : v.adicCompletion ℚ) * (1 / 2) = 1 by norm_num, one_smul, hM,
    hankeBeta_eq_half_alphaP v hsymm hdet]

/-- $\lVert 2\rVert_v = p^{-\operatorname{ord}_p 2}$. -/
theorem norm_two_eq_zpow : ‖(2 : v.adicCompletion ℚ)‖ = ((pv v : ℝ) ^ padicValNat (pv v) 2)⁻¹ := by
  by_cases h2 : pv v = 2
  · have h2' : (2 : 𝓞 ℚ) ∈ v.asIdeal := by
      have := (Tamagawa.RatHeadline3.intCast_mem_iff v 2).mpr (by
        show ((pv v : ℕ) : ℤ) ∣ 2
        rw [h2]; norm_num)
      exact_mod_cast this
    rw [Dyadic7.norm_two_completion v h2', h2]
    simp
  · rw [norm_two_completion v h2]
    have hp := (Rat.HeightOneSpectrum.prime_natGenerator v : (pv v).Prime)
    have h0 : padicValNat (pv v) 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun hd => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
    rw [h0]
    simp

/-- **Paper 6, Lemma 7.3 over $\mathbb Q$, every rank:** for an integral form $Q$ in $n$ variables with Hessian $H$,
$\det H \ne 0$, $\nu = \operatorname{ord}_p\det H$,
$$\beta(G)^{-1} = 2\,m_p(H)\,p^{-\frac{(n+1)\nu}{2}}\cdot p^{\frac{n(n+1)}2\operatorname{ord}_p(2)}.$$ -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (F = Q, every rank n); conwaysloane1988 §12, pp. 281–282"]
theorem invBeta_eq_pMass {n : ℕ} (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) :
    ((LocGenus.mk (Q.map (algebraMap ℤ (v.adicCompletionIntegers ℚ)))).beta)⁻¹ =
      2 * pMassDensity (pv v) Q.hessian *
        (pv v : ℝ) ^ (-(((padicValInt (pv v) Q.hessian.det : ℝ) * ((n : ℝ) + 1)) / 2)) *
        ((pv v : ℝ) ^ padicValNat (pv v) 2) ^ (n * (n + 1) / 2) := by
  have hp := (Rat.HeightOneSpectrum.prime_natGenerator v : (pv v).Prime)
  have hα := (alphaP_pos hp (LocalDensity.hessian_isSymm Q) hdet).ne'
  have hp0 : (0 : ℝ) < pv v := by exact_mod_cast hp.pos
  rw [beta_mk_int v Q hdet, norm_two_eq_zpow, pMassDensity, Real.rpow_neg hp0.le]
  have hP : (0 : ℝ) < (pv v : ℝ) ^ padicValNat (pv v) 2 := by positivity
  have hR : (0 : ℝ) < (pv v : ℝ) ^ (((padicValInt (pv v) Q.hessian.det : ℝ) * ((n : ℝ) + 1)) / 2) :=
    Real.rpow_pos_of_pos hp0 _
  rw [inv_pow]
  field_simp

/-- **Paper 6, Lemma 7.3 (binary forms, $F = \mathbb Q$):** $\beta(G)^{-1} = 2\,m_p(G)\,p^{-3\nu/2}\cdot p^{3\operatorname{ord}_p(2)}$,
with $m_p(G)$ given by Conway–Sloane's formula (3) for a $p$-adic symbol $\sigma$ of the Hessian ($p$ odd). -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (n = 2, F = Q, p odd; m_p from formula (3))"]
theorem lemma_7_3_odd (hp2 : pv v ≠ 2) (Q : QuadForm ℤ 2) (hdet : Q.hessian.det ≠ 0)
    (σ : ConwaySloane.OddSymbol) (N : ℕ)
    (hσ : ConwaySloane.IsOddSymbolOf (pv v) (Q.hessian.map (Int.cast : ℤ → ℚ_[pv v])) σ)
    (hN : ∀ k, N ≤ k → σ k = ConwaySloane.OddFactor.trivial) :
    ((LocGenus.mk (Q.map (algebraMap ℤ (v.adicCompletionIntegers ℚ)))).beta)⁻¹ =
      2 * pMassOdd (pv v) σ N * (pv v : ℝ) ^ (-((padicValInt (pv v) Q.hessian.det : ℝ) * 3 / 2)) := by
  haveI := Fact.mk (Rat.HeightOneSpectrum.prime_natGenerator v : (pv v).Prime)
  have hp := (Rat.HeightOneSpectrum.prime_natGenerator v : (pv v).Prime)
  have h0 : padicValNat (pv v) 2 = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
  rw [invBeta_eq_pMass v Q hdet, (pMassFormulaOdd hp2).pMass_eq _ (LocalDensity.hessian_isSymm Q) hdet σ N hσ hN,
    h0]
  norm_num

/-- **Paper 6, Lemma 7.3 (binary forms, $F_{\mathfrak p} = \mathbb Q_2$):** $\beta(G)^{-1} = 2\,m_2(G)\,2^{-3\nu/2}\cdot2^{3}$, with $m_2(G)$
given by Conway–Sloane's formula (3) for a 2-adic symbol $\sigma$ of the Hessian. -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (n = 2, F_p = Q_2; m_2 from formula (3))"]
theorem lemma_7_3_two (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (Q : QuadForm ℤ 2) (hdet : Q.hessian.det ≠ 0)
    (σ : ConwaySloane.TwoSymbol) (N : ℕ)
    (hσ : ConwaySloane.IsTwoSymbolOf (Q.hessian.map (Int.cast : ℤ → ℚ_[2])) σ) (hN : σ.SupportedBelow N) :
    ((LocGenus.mk (Q.map (algebraMap ℤ (v.adicCompletionIntegers ℚ)))).beta)⁻¹ =
      2 * pMassTwo σ N * (2 : ℝ) ^ (-((padicValInt 2 Q.hessian.det : ℝ) * 3 / 2)) * 2 ^ 3 := by
  have hp2 : pv v = 2 := pv_eq_two_of_two_mem v h2
  have e := invBeta_eq_pMass v Q hdet
  rw [hp2] at e
  rw [e, Two.pMassFormulaTwo_holds.pMass_eq _ (LocalDensity.hessian_isSymm Q) hdet σ N hσ hN]
  norm_num

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.invBeta_eq_pMass
#print axioms QuadFormsKB.Hanke2011Structure.lemma_7_3_odd
#print axioms QuadFormsKB.Hanke2011Structure.lemma_7_3_two
