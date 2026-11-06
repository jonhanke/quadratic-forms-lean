/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Blocks
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm

/-!
# Paper 7 at $p = 2$: Hanke's local density of a block genus from the Conway–Sloane 2-mass

For the place $v \mid 2$ of $\mathbb Q$ and a block decomposition $D$ (exponents $\ge 0$, no block $2^0ux^2$) of the
Hessian $H_D$ of the form $Q_D$ (`Dyadic7.formZ`):

* `beta_genusOf`: $\beta(G_D) = 2^{-n(n+1)/2}\cdot\tfrac12\,\alpha_2(H_D)$. *Proof:* Hanke's $\beta$ is computed in Gram
  coordinates $\tfrac12 H_D$; Hanke's Lemma 3.1 (`Hanke2005.hankeBeta_std_smul`, $c = 2$, $\lVert 2\rVert_v = \tfrac12$)
  and $\beta = \tfrac12\alpha_p$ for integral matrices (`ConwaySloane.Mass.hankeBeta_eq_half_alphaP`).
* `beta_genusOf_three`: for $n = 3$, given the named input `ConwaySloane.Mass.PMassFormulaTwo` (Conway–Sloane's (3) at
  $p = 2$), $\beta(G_D) = 2^{2h-7}/m_2(D)$, $h = \operatorname{ord}_2\det H_D$ (`valSum D`), $m_2$ = `pMassTwo` of the
  2-adic symbol of $D$.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal

noncomputable section

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem norm_two_completion (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ‖(2 : v.adicCompletion ℚ)‖ = 1 / 2 := by
  have h := norm_prime_completion v
  rw [pv_eq_two_of_two_mem v h2] at h
  simpa using h

theorem hessZ_isSymm {n : ℕ} {D : List DyBlock} (hn : dyDim D = n) : (hessZ n D).IsSymm :=
  hessZ_transpose hn

theorem unitProd_ne_zero {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid) : unitProd D ≠ 0 := by
  intro h
  exact odd_unitProd D hD (h ▸ dvd_zero 2)

theorem det_hessZ_ne_zero {n : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hn : dyDim D = n) : (hessZ n D).det ≠ 0 := by
  rw [det_hessZ hn h0]
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (unitProd_ne_zero hD)

theorem padicValInt_det_hessZ {n : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hn : dyDim D = n) : padicValInt 2 (hessZ n D).det = valSum D := by
  rw [det_hessZ hn h0]
  have hu := odd_unitProd D hD
  rw [padicValInt.mul (pow_ne_zero _ two_ne_zero) (unitProd_ne_zero hD)]
  have h1 : padicValInt 2 (unitProd D) = 0 := padicValInt.eq_zero_of_not_dvd hu
  rw [h1, add_zero]
  have : ((2 : ℤ) ^ valSum D) = ((2 ^ valSum D : ℕ) : ℤ) := by push_cast; rfl
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

/-- **Hanke's density of the genus of a block decomposition** at $v \mid 2$:
$\beta(G_D) = 2^{-n(n+1)/2}\cdot\tfrac12\,\alpha_2(H_D)$, $H_D$ = `hessZ n D` the Hessian. -/
@[kb "hanke2005crelle" "Lemma 3.1, p. 7 (scaling); conwaysloane1988 §12, p. 281 (beta = alpha/2)"]
theorem beta_genusOf (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid)
    (h0 : ∀ b ∈ D, 0 ≤ blockExp b) (hn : dyDim D = n) (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) :
    (genusOf v n D).beta = (1 / 2 : ℝ) ^ (n * (n + 1) / 2) * ((1 / 2 : ℝ) * alphaP 2 (hessZ n D)) := by
  unfold genusOf
  rw [LocGenus.beta_mk]
  unfold betaForm Hanke2005.gramOf
  rw [QuadForm.hessian_map', hessian_formZ hn h0 hev]
  set M : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ) :=
    ((hessZ n D).map (algebraMap ℤ (v.adicCompletionIntegers ℚ))).map
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) with hM
  have hMs : ((1 / 2 : v.adicCompletion ℚ) • M)ᵀ = (1 / 2 : v.adicCompletion ℚ) • M := by
    rw [Matrix.transpose_smul]
    congr 1
    rw [hM, ← Matrix.transpose_map, ← Matrix.transpose_map, hessZ_transpose hn]
  have hMd : ((1 / 2 : v.adicCompletion ℚ) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have := det_hessZ_ne_zero hD h0 hn
    simpa using this
  rw [Hanke2005.hankeBeta_std_smul v hMs hMd (c := 2) two_ne_zero, smul_smul,
    show (2 : v.adicCompletion ℚ) * (1 / 2) = 1 by norm_num, one_smul, norm_two_completion v h2,
    hM, hankeBeta_eq_half_alphaP v (hessZ_isSymm hn) (det_hessZ_ne_zero hD h0 hn), pv_eq_two_of_two_mem v h2]

/-- $\alpha_2(H) = 2^{s(n+1)/2}/m_2(H)$ (definition of the 2-mass), $s = \operatorname{ord}_2\det H$. -/
theorem alphaP_eq_div_pMassDensity {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    alphaP 2 A = (2 : ℝ) ^ (((padicValInt 2 A.det : ℝ) * ((n : ℝ) + 1)) / 2) / pMassDensity 2 A := by
  have hα := (alphaP_pos Nat.prime_two hA hdet).ne'
  unfold pMassDensity
  have : (0 : ℝ) < (2 : ℝ) ^ (((padicValInt 2 A.det : ℝ) * ((n : ℝ) + 1)) / 2) := by positivity
  push_cast
  field_simp

theorem isTwoSymbolOf_hessZ {n : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hn : dyDim D = n) : IsTwoSymbolOf ((hessZ n D).map (Int.cast : ℤ → ℚ_[2])) (blockSymbol D) := by
  refine ⟨D, hD, h0, hn, ?_, rfl⟩
  rw [hessZ_of hn, ← map_dyMatInt D h0]
  exact ZpEquiv.refl _

/-- **Hanke's density of a ternary block genus from the Conway–Sloane 2-mass**, given `PMassFormulaTwo`:
$\beta(G_D) = 2^{2h-7}/m_2(D)$, $h$ = `valSum D` (the Hessian valuation). -/
@[kb "conwaysloane1988" "(3), p. 263, and §12, p. 281 (2-mass and density), at p = 2"]
theorem beta_genusOf_three (hCS : PMassFormulaTwo) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {D : List DyBlock}
    (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b) (hn : dyDim D = 3)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) {N : ℕ} (hN : (blockSymbol D).SupportedBelow N) :
    (genusOf v 3 D).beta = (2 : ℝ) ^ (2 * valSum D) / 2 ^ 7 / pMassTwo (blockSymbol D) N := by
  rw [beta_genusOf v h2 hD h0 hn hev, alphaP_eq_div_pMassDensity (hessZ_isSymm hn) (det_hessZ_ne_zero hD h0 hn),
    hCS.pMass_eq _ (hessZ_isSymm hn) (det_hessZ_ne_zero hD h0 hn) _ N (isTwoSymbolOf_hessZ hD h0 hn) hN,
    padicValInt_det_hessZ hD h0 hn]
  simp only [Nat.cast_ofNat]
  have e : (valSum D : ℝ) * (3 + 1) / 2 = ((2 * valSum D : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  norm_num
  ring

end

end QuadFormsKB.Dyadic7

#print axioms QuadFormsKB.Dyadic7.beta_genusOf
#print axioms QuadFormsKB.Dyadic7.beta_genusOf_three

