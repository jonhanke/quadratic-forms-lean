/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoNFSeries
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoGenus
import QuadFormsKB.Literature.Hanke2011Structure.TernaryRational

/-!
# Paper 6, Lemma 7.3 at a prime $\mathfrak p \mid 2$ of a number field with $F_{\mathfrak p} \cong \mathbb Q_2$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Lemma 7.3, p. 29.

Let $\mathfrak p$ be a prime of a number field $F$ with $N\mathfrak p = 2$, $2 \notin \mathfrak p^2$ (`IsQ2Prime`), so
$F_{\mathfrak p} \cong \mathbb Q_2$, $q = 2$, $\operatorname{ord}_{\mathfrak p}(2) = 1$.  Transport a nondegenerate local
genus $G$ along $\mathcal O_{\mathfrak p} \cong \mathbb Z_2$ (`locMap`; it preserves $\beta$ and $\det_H$) to the genus $G'$
over the 2-adic prime $w_2$ of $\mathbb Q$.  The $\mathfrak p$-mass $m_{\mathfrak p}(G)$ is the Conway–Sloane 2-mass
`pMassTwo` of the 2-adic symbol `blockSymbol (rep G')` of $G'$ (Conway–Sloane (3) with $p = q = 2$).
Indices are 0-based.

Proved here: `invBeta_two_nf_sqrt`, `lemma_7_3_two_nf` (for $\det_H(G) = [2^\nu w]$, $w$ a unit), the existence of
such $\nu, w$ for every nondegenerate $G$ (`exists_det_eq_sqNF`), and the corollaries with no hypothesis on
$\det_H$ (`invBeta_two_nf_sqrt_exists`, `lemma_7_3_two_nf_exists`).
-/

open Finset IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.Lemma73NFTwo

open QuadFormsKB QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Structure.RatTwoNF
  QuadFormsKB.Hanke2011Structure.RatTwo QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass

noncomputable section

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝔬" => v.adicCompletionIntegers F

/-- **Paper 6, Lemma 7.3 at $F_{\mathfrak p} \cong \mathbb Q_2$, every rank $n$ (square-root form).**  Let $G$ be a
nondegenerate local genus of rank $n$ at $\mathfrak p$ with `IsQ2Prime v`, $w_2$ the 2-adic prime of $\mathbb Q$,
$\sigma : \mathcal O_{\mathfrak p} \cong \mathcal O_{w_2}$ the ring isomorphism through $\mathbb Z_2$, $G' = \sigma_*G$,
$D$ = `rep G'` its block list and $\sigma_D$ = `blockSymbol D` its 2-adic symbol (trivial from scale $2^N$ on).
If $\det_H(G) = [2^\nu w]$ with $\nu = \operatorname{ord}_{\mathfrak p}\det_H(G)$ ($2$ is a uniformizer) and
$w \in \mathcal O_{\mathfrak p}^\times$, then
$$\beta(G)^{-1} = 2\,\sqrt2^{\,n(n+1)}\,m_2(\sigma_D)\,/\,\sqrt2^{\,\nu(n+1)}.$$ -/
theorem invBeta_two_nf_sqrt (hv : IsQ2Prime v) (w₂ : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ w₂.asIdeal)
    {n : ℕ} (G : LocGenus v n) (hG : G.Nondeg) {ν : ℕ} {w : 𝔬} (hw : IsUnit w)
    (hdet : G.det = RatND.sqNF ((2 : 𝔬) ^ ν * w)) {N : ℕ}
    (hN : (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))).SupportedBelow N) :
    (G.beta)⁻¹ = 2 * Real.sqrt 2 ^ (n * (n + 1)) *
      pMassTwo (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))) N /
        Real.sqrt 2 ^ (ν * (n + 1)) := by
  set σ : 𝔬 ≃+* w₂.adicCompletionIntegers ℚ := hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm with hσ
  set G' := locMap σ G with hG'
  have hG'n : G'.Nondeg := (nondeg_locMap σ G).2 hG
  have hrep := isRep_rep h2 hG'n
  have hβ : G'.beta = G.beta := beta_locMap hv (isQ2Prime_rat w₂ h2) σ G hG
  have hinv := invBeta_genusOf h2 hrep.1 hrep.2.1 hN
  rw [hrep.2.2, hβ] at hinv
  rw [hinv]
  -- identify valSum (rep G') with ν
  obtain ⟨w', hw', hcl⟩ := sqMap_two_pow_mul hv w₂ h2 σ hw
  have e1 : G'.det = Dyadic7.zSqCl w₂ (2 ^ ν * w') := by
    rw [hG', det_locMap, hdet, hcl]
  have e2 := hrep.det h2
  have e3 := e1.symm.trans e2
  have hpv : pv w₂ = 2 := pv_eq_two_of_two_mem w₂ h2
  have hnd1 : ¬ (pv w₂ : ℤ) ∣ w' := by
    rw [hpv]; intro hd; exact (Int.not_even_iff_odd.mpr hw') (even_iff_two_dvd.mpr (by exact_mod_cast hd))
  have hnd2 : ¬ (pv w₂ : ℤ) ∣ unitProd (rep G') := by
    rw [hpv]; intro hd
    exact (Int.not_even_iff_odd.mpr (odd_unitProd' hrep.1)) (even_iff_two_dvd.mpr (by exact_mod_cast hd))
  have o1 := ordZ_zSqCl_pow_mul w₂ hnd1 ν
  have o2 := ordZ_zSqCl_pow_mul w₂ hnd2 (valSum (rep G'))
  rw [hpv] at o1 o2
  have : valSum (rep G') = ν := by
    have := congrArg (SqCl.ordZ (localOrd w₂) (localUnits_le_ker w₂)) e3
    push_cast at o1 o2
    rw [o1, o2] at this
    exact_mod_cast this.symm
  rw [this]

/-- **Paper 6, Lemma 7.3 at $F_{\mathfrak p} \cong \mathbb Q_2$, binary forms ($n = 2$), the paper's form:**
under the hypotheses of `invBeta_two_nf_sqrt` with $n = 2$,
$$\beta(G)^{-1} = 2\,m_2(G)\,2^{-3\nu/2}\cdot 2^{3},$$
$m_2(G) = $ `pMassTwo` of the 2-adic symbol of the transported genus (Conway–Sloane (3) with $p = q = 2$),
$\nu = \operatorname{ord}_{\mathfrak p}\det_H(G)$, $2^3 = q^{3\operatorname{ord}_{\mathfrak p}(2)}$. -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (n = 2, F_p = Q_2 via IsQ2Prime, every number field)"]
theorem lemma_7_3_two_nf (hv : IsQ2Prime v) (w₂ : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ w₂.asIdeal)
    (G : LocGenus v 2) (hG : G.Nondeg) {ν : ℕ} {w : 𝔬} (hw : IsUnit w)
    (hdet : G.det = RatND.sqNF ((2 : 𝔬) ^ ν * w)) {N : ℕ}
    (hN : (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))).SupportedBelow N) :
    (G.beta)⁻¹ =
      2 * pMassTwo (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))) N *
        (2 : ℝ) ^ (-((ν : ℝ) * 3 / 2)) * 2 ^ 3 := by
  rw [invBeta_two_nf_sqrt hv w₂ h2 G hG hw hdet hN]
  have hs : Real.sqrt 2 ^ (ν * (2 + 1)) = (2 : ℝ) ^ (((ν : ℝ) * 3) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have h6 : Real.sqrt 2 ^ (2 * (2 + 1)) = 8 := by
    have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc Real.sqrt 2 ^ (2 * (2 + 1)) = (Real.sqrt 2 ^ 2) ^ 3 := by rw [← pow_mul]
      _ = 8 := by rw [this]; norm_num
  rw [hs, h6, Real.rpow_neg (by norm_num)]
  have : (0 : ℝ) < (2 : ℝ) ^ (((ν : ℝ) * 3) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  field_simp
  ring

/-- **Existence of the determinant representative.**  For a nondegenerate local genus $G$ at $\mathfrak p$ with
`IsQ2Prime v` there are $\nu \in \mathbb N$ and $w \in \mathcal O_{\mathfrak p}^\times$ with
$\det_H(G) = [2^\nu w]$ in $\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$: the Hessian
determinant of a representative is a nonzero element of the DVR $\mathcal O_{\mathfrak p}$, whose uniformizer is
$2$ up to a unit (`IsQ2Prime.associated`). -/
theorem exists_det_eq_sqNF (hv : IsQ2Prime v) {n : ℕ} (G : LocGenus v n) (hG : G.Nondeg) :
    ∃ (ν : ℕ) (w : 𝔬), IsUnit w ∧ G.det = RatND.sqNF ((2 : 𝔬) ^ ν * w) := by
  induction G using Quotient.inductionOn with
  | _ T =>
    have hT : T.hessian.det ≠ 0 := hG
    have hne : algebraMap 𝔬 (v.adicCompletion F) T.hessian.det ≠ 0 := algebraMap_ne_zero_iff.2 hT
    have hπ := LocalDensity.NF.irreducible_π v
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hT hπ
    obtain ⟨c, hc⟩ := hv.associated
    have hπ2 : LocalDensity.NF.π v = 2 * ((c⁻¹ : 𝔬ˣ) : 𝔬) := by
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨k, u * ((c⁻¹ : 𝔬ˣ) : 𝔬) ^ k, u.isUnit.mul ((c⁻¹).isUnit.pow k), ?_⟩
    have hx : T.hessian.det = (2 : 𝔬) ^ k * (u * ((c⁻¹ : 𝔬ˣ) : 𝔬) ^ k) := by
      rw [hu, hπ2, mul_pow]; ring
    rw [← hx]
    change detSqForm T = _
    rw [detSqForm_of_ne hne, RatND.sqNF_of_ne hT]
    rfl

/-- **Paper 6, Lemma 7.3 at $F_{\mathfrak p} \cong \mathbb Q_2$, every rank $n$, unconditional in $\nu, w$:** for every
nondegenerate $G$ there are $\nu \in \mathbb N$, $w \in \mathcal O_{\mathfrak p}^\times$ with $\det_H(G) = [2^\nu w]$ and
$\beta(G)^{-1} = 2\,\sqrt2^{\,n(n+1)}\,m_2(\sigma_D)\,/\,\sqrt2^{\,\nu(n+1)}$ (notation of `invBeta_two_nf_sqrt`). -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (number fields, F_p ≅ Q_2, determinant normal form proved)"]
theorem invBeta_two_nf_sqrt_exists (hv : IsQ2Prime v) (w₂ : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∈ w₂.asIdeal) {n : ℕ} (G : LocGenus v n) (hG : G.Nondeg) {N : ℕ}
    (hN : (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))).SupportedBelow N) :
    ∃ (ν : ℕ) (w : 𝔬), IsUnit w ∧ G.det = RatND.sqNF ((2 : 𝔬) ^ ν * w) ∧
      (G.beta)⁻¹ = 2 * Real.sqrt 2 ^ (n * (n + 1)) *
        pMassTwo (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))) N /
          Real.sqrt 2 ^ (ν * (n + 1)) := by
  obtain ⟨ν, w, hw, hdet⟩ := exists_det_eq_sqNF hv G hG
  exact ⟨ν, w, hw, hdet, invBeta_two_nf_sqrt hv w₂ h2 G hG hw hdet hN⟩

/-- **Paper 6, Lemma 7.3 at $F_{\mathfrak p} \cong \mathbb Q_2$, binary forms, unconditional in $\nu, w$:** for every
nondegenerate binary $G$ there are $\nu \in \mathbb N$, $w \in \mathcal O_{\mathfrak p}^\times$ with
$\det_H(G) = [2^\nu w]$ and $\beta(G)^{-1} = 2\,m_2(G)\,2^{-3\nu/2}\cdot 2^3$ (notation of `lemma_7_3_two_nf`). -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (number fields, F_p ≅ Q_2, determinant normal form proved)"]
theorem lemma_7_3_two_nf_exists (hv : IsQ2Prime v) (w₂ : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∈ w₂.asIdeal) (G : LocGenus v 2) (hG : G.Nondeg) {N : ℕ}
    (hN : (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))).SupportedBelow N) :
    ∃ (ν : ℕ) (w : 𝔬), IsUnit w ∧ G.det = RatND.sqNF ((2 : 𝔬) ^ ν * w) ∧
      (G.beta)⁻¹ =
        2 * pMassTwo (blockSymbol (rep (locMap (hv.equiv.trans (isQ2Prime_rat w₂ h2).equiv.symm) G))) N *
          (2 : ℝ) ^ (-((ν : ℝ) * 3 / 2)) * 2 ^ 3 := by
  obtain ⟨ν, w, hw, hdet⟩ := exists_det_eq_sqNF hv G hG
  exact ⟨ν, w, hw, hdet, lemma_7_3_two_nf hv w₂ h2 G hG hw hdet hN⟩

end

end QuadFormsKB.Hanke2011Structure.Lemma73NFTwo

#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NFTwo.invBeta_two_nf_sqrt
#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NFTwo.lemma_7_3_two_nf
#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NFTwo.exists_det_eq_sqNF
#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NFTwo.invBeta_two_nf_sqrt_exists
#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NFTwo.lemma_7_3_two_nf_exists
